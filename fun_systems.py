"""
Roast system and Court system (entertainment only; the Auto-Ads/Promotion blocker lives in extra.py).

Kept in its own file so none of the existing moderation code had to be rewritten.
Wired up from nova.py with one line:   fun_systems.register(app, deps)

Everything here reuses nova's own helpers (admin checks) - they are handed in through `deps`,
the same way extra.register() receives its helpers, so this file never imports nova (which would re-run it).

    ROAST        /roast /roastme /cook /burn /finisher /comeback /roastbattle /roastvote
                 /roastscore /roaststats /roastking
    COURT        /court /trial /guilty /innocent /verdict /crime /evidence /alibi /sentence
                 /bail /pardon /appeal /execute /wanted      (pure comedy - NEVER touches real
                 Telegram rights)

The bot's name is never hard-coded: every header uses the bot's live display name
(context.bot.first_name), so renaming the bot to "Rose" gives "ROSE COURT", "ROSE COMEBACK"...
"""
import asyncio
import html
import logging
import random
import re
import threading
import time
from collections import Counter, defaultdict, deque

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.error import TelegramError
from telegram.ext import (
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

import extra  # reused: extra.resolve_target (reply / text-mention / @username / numeric ID)
import migrate_to_mongo as M  # MongoDB collections (roast_* and court_*)

log = logging.getLogger("fun_systems")
D = None  # helpers handed in by nova.py (see register)

CMD_COOLDOWN = 4          # seconds between comedy commands per user
ROAST_ACCEPT_SECS = 60    # opponent has this long to accept a battle
ROAST_FIGHT_SECS = 60     # time to send your roast once the battle starts
ROAST_VOTE_SECS = 30      # crowd voting window
COURT_OPEN_SECS = 300     # a trial closes by itself after this long
COURT_MIN_JURY = 2        # fewer jury votes than this = NOT PROVEN

# ---------------------------------------------------------------- database (MongoDB)
# Collections: roast_profiles, roast_battles, roast_results, roast_votes, court_cases, court_votes,
# court_verdicts (indexes are created by migrate_to_mongo.connect()). Mongo omits unset fields, so
# rows come back with every column present (None when unset), exactly like the old SQL rows.
_PROFILE_ZERO = dict(points=0, wins=0, losses=0, draws=0, streak=0, best_streak=0,
                     roasts_given=0, roasts_received=0)
_PROFILE_COLS = ("chat_id", "user_id", "name") + tuple(_PROFILE_ZERO)
_BATTLE_COLS = ("id", "chat_id", "challenger_id", "challenger_name", "opponent_id", "opponent_name",
                "status", "text_a", "text_b", "algo_a", "algo_b", "created", "deadline", "message_id")
_RESULT_COLS = ("id", "battle_id", "chat_id", "winner_id", "loser_id", "final_a", "final_b",
                "votes_a", "votes_b", "outcome", "ts")
_CASE_COLS = ("id", "chat_id", "case_no", "defendant_id", "defendant_name", "opened_by", "opened_by_name",
              "charge", "evidence", "plea", "status", "bail", "sentence", "appeals", "message_id",
              "opened", "closes")
_VERDICT_COLS = ("id", "case_id", "chat_id", "defendant_id", "verdict", "guilty_votes", "innocent_votes",
                 "plea", "sentence", "ts")
_profile_lock = threading.Lock()


def _fill(doc, cols):
    if doc is None:
        return None
    doc.pop("_id", None)
    for c in cols:
        doc.setdefault(c, None)
    return doc


def _one(name, flt, cols=(), sort=None):
    return _fill(M.col(name).find_one(flt, sort=sort), cols)


def _many(name, flt, cols=(), sort=None, limit=0):
    return [_fill(d, cols) for d in M.col(name).find(flt, sort=sort, limit=limit)]


def _tally(name, key_field, key, field):
    """[{field: value, "n": count}] - the old GROUP BY."""
    counts = {}
    for d in M.col(name).find({key_field: key}):
        counts[d[field]] = counts.get(d[field], 0) + 1
    return [{field: v, "n": n} for v, n in counts.items()]


def _battle(bid, chat_id=None):
    flt = {"id": bid} if chat_id is None else {"id": bid, "chat_id": chat_id}
    return _one("roast_battles", flt, _BATTLE_COLS)


def _battle_set(bid, **fields):
    M.col("roast_battles").update_one({"id": bid}, {"$set": fields})


def _battle_move(bid, frm, to, **extra):
    """Atomic status change (only if the battle is still in `frm`); True if this call did it."""
    r = M.col("roast_battles").update_one({"id": bid, "status": frm}, {"$set": {"status": to, **extra}})
    return r.matched_count > 0


def _add_result(**fields):
    doc = dict.fromkeys(_RESULT_COLS)
    doc.update(fields, id=M.next_id("roast_results"), ts=int(time.time()))
    M.col("roast_results").insert_one(doc)


def _case(flt, sort=None):
    return _one("court_cases", flt, _CASE_COLS, sort)


def _case_set(cid, **fields):
    M.col("court_cases").update_one({"id": cid}, {"$set": fields})


def _case_move(cid, frm, to, **extra):
    r = M.col("court_cases").update_one({"id": cid, "status": frm}, {"$set": {"status": to, **extra}})
    return r.matched_count > 0


def _add_verdict(**fields):
    doc = dict.fromkeys(_VERDICT_COLS)
    doc.update(fields, id=M.next_id("court_verdicts"), ts=int(time.time()))
    M.col("court_verdicts").insert_one(doc)


# ----------------------------------------------------------------- helpers
_esc = html.escape
_tasks = set()
_recent = defaultdict(lambda: deque(maxlen=12))
_cool_log = {}
_award_log = {}


def _spawn(coro):
    """Background timer that can't be garbage-collected."""
    t = asyncio.get_running_loop().create_task(coro)
    _tasks.add(t)
    t.add_done_callback(_tasks.discard)
    return t


def _bn(bot):
    """The bot's live display name - never hard-coded."""
    return (getattr(bot, "first_name", None) or "Bot").strip() or "Bot"


def _head(bot, suffix, icon):
    return f"{icon} <b>{_esc(_bn(bot).upper())} {suffix}</b>"


def _pick(pool, key):
    """Random item that wasn't used in the last few picks for this chat+pool."""
    seen = _recent[key]
    choices = [x for x in pool if x not in seen]
    if not choices:
        seen.clear()
        choices = list(pool)
    item = random.choice(choices)
    seen.append(item)
    return item


def _mention(uid, name):
    return f'<a href="tg://user?id={uid}">{_esc(name or "someone")}</a>'


def _who(user):
    return user.id, user.full_name or user.first_name or "someone"


async def _group(update):
    if update.effective_chat.type == "private":
        await update.effective_message.reply_text("This one is for groups - bring me into a chat with friends!")
        return False
    return True


async def _cool(update, secs=CMD_COOLDOWN):
    user = update.effective_user
    key = (update.effective_chat.id, user.id)
    now = time.monotonic()
    if now - _cool_log.get(key, 0) < secs:
        await update.effective_message.reply_text("⏳ Easy there - give it a few seconds.")
        return False
    if len(_cool_log) > 5000:
        _cool_log.clear()
    _cool_log[key] = now
    return True


async def _resolve(update, context):
    """(info, error). info = (id, name, mention) or None when nobody was named."""
    try:
        tgt, err = await extra.resolve_target(update, context)
    except TelegramError:
        return None, "I couldn't look that user up."
    if err:
        return None, err
    if tgt is None:
        return None, None
    if getattr(tgt, "type", None) in ("channel", "group", "supergroup"):
        return None, "I can only pick on people, not chats."
    name = (getattr(tgt, "full_name", None) or getattr(tgt, "first_name", None)
            or getattr(tgt, "title", None) or getattr(tgt, "username", None) or "someone")
    return (tgt.id, name, _mention(tgt.id, name)), None


async def _target(update, context, usage, allow_self=False):
    """Required target for a command. Replies with the reason and returns None if unusable."""
    msg = update.effective_message
    info, err = await _resolve(update, context)
    if err:
        await msg.reply_html(err)
        return None
    if info is None:
        await msg.reply_html(usage)
        return None
    if info[0] == context.bot.id:
        await msg.reply_text(random.choice([
            "Nice try - I'm the referee, not the contestant. 😌",
            "I don't do self-roasting. I'm perfect. Next!",
        ]))
        return None
    if info[0] == update.effective_user.id and not allow_self:
        await msg.reply_text("You can't target yourself here - pick someone else (or use /roastme).")
        return None
    return info


async def _target_or_self(update, context):
    """Optional target for stat commands: defaults to the sender."""
    info, err = await _resolve(update, context)
    if err:
        await update.effective_message.reply_html(err)
        return None
    if info is None:
        uid, name = _who(update.effective_user)
        return uid, name, _mention(uid, name)
    return info


async def _send(bot, chat_id, text, **kw):
    try:
        return await bot.send_message(chat_id, text, parse_mode="HTML", disable_web_page_preview=True, **kw)
    except TelegramError as e:
        log.warning("Couldn't send message to chat %s: %s", chat_id, e)
        return None


async def _edit(bot, chat_id, message_id, text, markup=None):
    try:
        await bot.edit_message_text(text, chat_id=chat_id, message_id=message_id,
                                    parse_mode="HTML", reply_markup=markup)
    except TelegramError:
        pass  # message gone, unchanged or too old - harmless


async def _delete_later(msg, secs):
    await asyncio.sleep(secs)
    try:
        await msg.delete()
    except TelegramError:
        pass


# =====================================================================
#  2. ROAST SYSTEM
# =====================================================================
ROASTS = [
    "{n} has the energy of a phone at 1% that still says \"I'll be fine\".",
    "{n} types \"brb\" and returns three business days later with zero explanation.",
    "{n}'s Wi-Fi password is probably \"password123\", and their opinions are about as secure.",
    "{n} is the human version of a loading icon: lots of movement, no progress.",
    "{n} walked into the chat and the typing bubble gave up out of secondhand embarrassment.",
    "{n} has the confidence of someone who never read the group rules.",
    "{n} is the reason the mute button exists, and honestly it's a very popular feature.",
    "{n}'s jokes come with a loading bar and still arrive late.",
    "{n} replies \"lol\" to everything like a customer-service bot with trust issues.",
    "{n} is proof that autocorrect never gives up on a person.",
    "{n} sends voice notes longer than most podcasts, with fewer facts.",
    "{n} treats every group poll like a hostage negotiation.",
    "{n} has 3% battery, a charger that is \"somewhere\", and still starts a 40-message debate.",
    "{n} brings main-character energy with NPC dialogue options.",
    "{n} replies so slowly that carrier pigeons are filing complaints.",
    "{n} leaves people on read so often it counts as cardio.",
    "{n} types at 120 WPM, but the point arrives at 3.",
    "{n} could trip over a wireless connection.",
    "{n} is what happens when you press \"I'm Feeling Lucky\" on a personality.",
    "{n} has the stability of a table with three legs and a dream.",
    "{n}'s browser has 87 tabs open and not one of them is the answer.",
    "{n} said \"good morning\" at 4 PM and expected applause.",
    "{n} runs on \"trust me bro\" with \"source: dreams\".",
    "If {n} were a font, they'd be Comic Sans in a legal document.",
    "{n}'s spelling makes dictionaries nervous.",
    "{n} says \"quick question\" and delivers a 14-part series.",
    "{n} has more unread notifications than a haunted mailbox.",
    "{n} read the first page of the manual and called it expertise.",
    "{n}'s plans are like their battery: dramatic, brief, and gone by evening.",
    "{n} calls it multitasking when it's just opening six apps and finishing none.",
]
ROAST_TAGS = [
    "Respectfully. 🫡", "No notes. 📝", "Sit down, champ.", "Skill issue.", "Anyway, hydrate. 💧",
    "Tragic. Iconic. Unavoidable.", "Ratio incoming. 📉", "That's the tweet.",
    "Cry about it (lovingly). 😌", "The jury is still laughing.", "Served medium-rare. 🥩",
    "Press F for the ego. 🫡",
]
BURNS = [
    "{n} just got burned so badly the fire department sent a thank-you note.",
    "That one was so hot {n} needs a cold shower and a new personality.",
    "{n}'s comeback is still buffering. Try again in 2-3 business days.",
    "Somewhere a smoke alarm just clapped for {n}'s performance.",
    "{n} has been toasted, buttered, and served with a side of silence.",
    "The group chat just collectively said \"ooooh\" at {n}.",
    "{n} walked into the flames voluntarily and asked for seconds.",
    "Even the marshmallows are staying away from {n} today.",
    "{n} got flambéed and the chef didn't even look up.",
    "{n}'s ego took a hit and it's filing a complaint with customer support.",
    "Weather report: 100% chance of burn, with {n} as the forecast.",
    "That was a crime scene, and the culprit is a flamethrower named Sass. {n} was nearby.",
    "{n} just spawned in the burn unit with no starter kit.",
    "Someone call a fire truck, {n} is trending for all the wrong reasons.",
    "{n} tried to light a candle and accidentally became the whole bonfire.",
    "The ice-cream truck left the area the moment {n} got burned.",
    "{n} has been roasted so well the chicken is taking notes.",
    "{n}'s dignity left the chat and took the charger with it.",
    "Doctors recommend aloe vera and a long walk for {n}.",
    "Plot twist: the toaster was {n} all along.",
]
BURN_LEVELS = [
    "Lightly toasted 🍞", "Spicy 🌶️", "Extra crispy 🍗", "Volcanic 🌋", "Surface of the sun ☀️",
    "Crème brûlée 🍮", "Well-done 🥩", "Campfire 🔥", "Jalapeño popper 🫑", "Dragon breath 🐉",
]
FINISHERS = [
    "{n}, the algorithm called. It wants its worst recommendation back.",
    "{n} came, saw, and immediately asked \"wait, what are we talking about?\".",
    "{n} is the \"before\" picture in every self-improvement ad.",
    "{n} brought a spoon to a group-chat sword fight. And dropped it.",
    "Congratulations {n}, you've unlocked: the achievement \"Participant\".",
    "{n} just lost an argument to an autocorrect typo. Game over.",
    "{n}, the only thing you're winning is the \"most likely to say 'nvm'\" award.",
    "{n} is the plot hole in the group's story.",
    "{n}'s final form is a 2 AM \"we need to talk\" with no follow-up.",
    "{n} got out-argued by a sticker. A sticker. 🫠",
    "{n}, even the \"seen\" checkmark feels sorry for you.",
    "This has been {n}'s final boss fight. The boss was a Tuesday.",
    "{n} walked so the memes could run, and the memes sprinted away.",
    "Fatality... of dignity. {n} will be fine tomorrow. Probably.",
    "{n}'s comeback was typed, deleted, retyped, deleted, and then went to sleep.",
    "{n}, you've been officially downgraded to a \"typing...\" indicator.",
    "And with that, {n} has been gently placed in the group's \"remember when\" folder.",
    "Game, set, match. {n} is still looking for the ball.",
]
COMEBACKS = [
    "I'd explain it to you, but I left my crayons at home.",
    "Wow, you typed that with your whole chest and none of your brain.",
    "I'd agree with you, but then we'd both be wrong.",
    "Your opinion is like a pop-up ad: loud, unrequested, and I'm already closing it.",
    "That's a bold take for someone whose last good idea was in 2019.",
    "You bring so much to the table. Mostly crumbs, but still.",
    "I'm not ignoring you, I'm just buffering your point. It's taking a while.",
    "If I wanted a tragedy I'd reread your messages.",
    "I'd call that a comeback, but it's more of a comeback-adjacent whisper.",
    "Interesting. Anyway, back to topics with substance.",
    "You're like a software update: nobody asked, and it takes forever.",
    "Thanks for the input. It has been recycled into something useful.",
    "Is that your best? Because I've seen better defense from a screen door.",
    "Your confidence is impressive. Your evidence, less so.",
    "Cool story. Want me to make it interesting?",
    "I've seen smarter arguments from a microwave beeping at 3 AM.",
    "You're entitled to your opinion, and I'm entitled to a refund on the last 30 seconds.",
    "I'd roast you back, but my mom said not to burn out the small candles.",
    "Careful, that burn almost warmed the room.",
    "Oh, you're serious? Let me get my surprised face. Found it. Nope, wrong one.",
    "You came with a spark and left with a participation sticker.",
    "I'd respond, but I'd hate to ruin your streak of being wrong.",
    "That line was dead on arrival, but I appreciate the delivery driver's effort.",
    "Sorry, I only respond to messages that passed quality control.",
]
ROASTME = [
    "{n} asked to be roasted, which is the most confident thing they've done all week.",
    "{n} volunteered as tribute for a roast, and the jury is already regretting its popcorn.",
    "{n} walked in, lit the grill, and politely asked us to cook them. Alright.",
    "Bold of {n} to request feedback from a group that still hasn't forgiven the last meme.",
    "{n} is the kind of person who says \"be honest\" and then stops reading at \"honestly\".",
    "{n}'s search history says \"how to be interesting\" and the results are still loading.",
    "{n} has the fashion sense of a browser with 14 toolbars installed.",
    "{n} said \"roast me\" and the bot sighed in binary.",
    "{n} has main-character confidence and a supporting-cast sleep schedule.",
    "{n} is 40% caffeine, 30% sarcasm, 20% procrastination and 10% \"I'll do it tomorrow\".",
    "{n}'s phone has 9,000 photos and the only good one is a screenshot.",
    "{n}'s motivation is on airplane mode, and the flight is delayed.",
    "{n} argues with strangers online and loses to people with cartoon avatars.",
    "{n} has a gym membership, a snack drawer, and a deep belief in the second one.",
    "{n} sends \"on my way\" while still looking for their shoes.",
    "{n} called it a power nap and woke up in a different decade.",
]
COOK_DONE = [
    "is extremely well-done", "is carbonized on the edges and crispy in the middle",
    "has been slow-roasted for 8 hours of regret", "is pan-seared with a side of lost arguments",
    "has been microwaved for 40 minutes at full power", "is deep-fried in pure embarrassment",
    "is flambéed and still somehow talking", "is overcooked: the smoke alarm is clapping",
    "has been air-fried at maximum chaos", "is fully cooked, plated and served with garnish",
]
COOK_INGREDIENTS = [
    "a pinch of misplaced confidence", "two cups of unread messages", "one bag of \"trust me bro\" seasoning",
    "a drizzle of bad takes", "freshly chopped excuses", "a dash of \"I was just joking\"",
    "three spoonfuls of procrastination", "a handful of unfinished plans", "extra-crunchy hot takes",
    "one slice of unearned swagger", "a sprinkle of \"per my last message\"", "half a litre of secondhand embarrassment",
    "a whole bunch of \"k.\" replies", "a heaping spoon of \"I'll do it tomorrow\"",
]
COOK_REVIEWS = [
    "Chef's kiss. The ego was rare, now it's well-done.",
    "Needs more salt, but the burn is perfect.",
    "Five stars for the cooking, zero stars for the survivor.",
    "Served hot, eaten cold, remembered forever.",
    "The sizzle was audible from the next group chat.",
    "Michelin-starred in the art of getting cooked.",
    "I've seen toast with more defence than that.",
    "Delicious tragedy with a side of fries.",
    "Absolutely crispy. Handle with oven mitts.",
    "A masterpiece. The judges are speechless and slightly hungry.",
    "That kitchen smelled like victory and burnt ego.",
    "Rare talent: getting cooked and still asking for the recipe.",
]
COOK_STATUS = ["COOKED 🔥", "OVERCOOKED 🔥🔥", "CHARRED 🔥🔥🔥", "CRISPY 🍗", "FLAMBÉ 🍷🔥", "MEDIUM WELL 🥩", "GOLDEN BROWN 🍞"]

_UNPLAYFUL_RE = re.compile(
    r"\b(?:kill\s+(?:yourself|urself)|kys|i(?:'ll|\s+will|\s+am\s+going\s+to)\s+(?:kill|hurt|beat|stab|shoot|find)\s+you"
    r"|rape\w*|suicid\w*|go\s+die|die\s+in\s+a\s+fire)\b", re.I)
_WORD_RE = re.compile(r"[^\W_]+(?:'[^\W_]+)?", re.U)
_SIMILE_RE = re.compile(r"\b(?:like|than|as if|as though|imagine|if you were|looks like|sounds like|"
                        r"reminds me|so \w+ that|the human version|version of)\b", re.I)
_EMOJI_RE = re.compile("[\U0001F300-\U0001FAFF\u2600-\u27BF]")


def score_roast(text, opponent_name="", other_text=""):
    """Judge one roast 0-100. The SAME rules apply to both fighters - the function never sees
    who wrote the text, so it cannot favour anyone.
    Rewards: sweet-spot length, original vocabulary, similes/comparisons, speaking to the
    opponent, some punch (emoji/punctuation). Penalises: repetition, ALL CAPS, links, copying
    the opponent, and anything hateful or threatening (scores 0)."""
    t = (text or "").strip()
    notes = []
    if _UNPLAYFUL_RE.search(t):
        return 0.0, ["off-limits content"]
    words = _WORD_RE.findall(t.lower())
    n = len(words)
    if n < 3:
        return 5.0, ["too short"]
    s = 25 * n / 12 if n < 12 else (25 if n <= 35 else max(5, 25 - (n - 35) * 0.7))
    s += 20 * min(1.0, (len(set(words)) / n) / 0.85)                       # originality
    s += min(10, 2 * sum(1 for w in set(words) if len(w) >= 7))            # vocabulary
    s += min(15, 5 * len(_SIMILE_RE.findall(t)))                           # comparisons / wit
    addressed = 0
    for tok in _WORD_RE.findall((opponent_name or "").lower()):
        if len(tok) >= 3 and tok in words:
            addressed = 10
            break
    if not addressed and any(w in ("you", "your", "you're", "youre", "ur", "u") for w in words):
        addressed = 6
    s += addressed                                                         # speaks to the target
    s += min(5, 2 * len(_EMOJI_RE.findall(t)))
    if t[-1:] in "!?.…" or _EMOJI_RE.match(t[-1:] or " "):
        s += 3
    if len({c for c in t if c in "!?.,;:-—'\""}) >= 3:
        s += 2
    repeats = sum(1 for w, c in Counter(w for w in words if len(w) > 3).items() if c > 3)
    if repeats:
        s -= min(12, 3 * repeats)
        notes.append("repetitive")
    letters = [c for c in t if c.isalpha()]
    if len(letters) >= 8 and sum(c.isupper() for c in letters) / len(letters) > 0.6:
        s -= 8
        notes.append("all caps")
    if re.search(r"https?://|www\.|t\.me/", t, re.I):
        s -= 15
        notes.append("link")
    if other_text:
        a, b = set(words), set(_WORD_RE.findall(other_text.lower()))
        if a and b and len(a & b) / len(a | b) > 0.6:
            s -= 20
            notes.append("copycat")
    return round(max(0.0, min(100.0, s)), 1), notes


def _ensure_profile(chat_id, uid, name):
    M.col("roast_profiles").update_one({"chat_id": chat_id, "user_id": uid},
                                       {"$set": {"name": name}, "$setOnInsert": dict(_PROFILE_ZERO)},
                                       upsert=True)


def _bump(chat_id, uid, **inc):
    """UPDATE roast_profiles SET x = x + n (does nothing if the profile doesn't exist)."""
    M.col("roast_profiles").update_one({"chat_id": chat_id, "user_id": uid}, {"$inc": inc})


def _award_command(chat_id, roaster, roaster_name, target, target_name):
    """+1 point per roast, but only once a minute per roaster->target pair (no point farming)."""
    _ensure_profile(chat_id, target, target_name)
    _bump(chat_id, target, roasts_received=1)
    key = (chat_id, roaster, target)
    now = time.time()
    if len(_award_log) > 5000:
        _award_log.clear()
    if now - _award_log.get(key, 0) < 60:
        return
    _award_log[key] = now
    _ensure_profile(chat_id, roaster, roaster_name)
    _bump(chat_id, roaster, points=1, roasts_given=1)


async def _roast_line(update, context, kind):
    if not await _group(update) or not await _cool(update):
        return
    usage = f"Usage: /{kind} @user  (or reply to someone's message)"
    tgt = await _target(update, context, usage)
    if not tgt:
        return
    uid, name, mention = tgt
    chat, bot = update.effective_chat, context.bot
    ruid, rname = _who(update.effective_user)
    k = chat.id
    if kind == "roast":
        line = _pick(ROASTS, f"{k}:roast").format(n=mention)
        if random.random() < 0.4:
            line += " " + _pick(ROAST_TAGS, f"{k}:rtag")
        text = f"{_head(bot, 'ROAST', '🔥')}\n\n{line}"
    elif kind == "burn":
        line = _pick(BURNS, f"{k}:burn").format(n=mention)
        level = _pick(BURN_LEVELS, f"{k}:burnlvl")
        text = f"{_head(bot, 'BURN', '🌡️')}\n\n{line}\n\n🔥 Burn level: <b>{level}</b>"
    elif kind == "finisher":
        line = _pick(FINISHERS, f"{k}:fin").format(n=mention)
        text = f"{_head(bot, 'FINISHER', '💥')}\n\n{line}\n\n🏁 <i>Flawless finish.</i>"
    else:  # cook
        ingredients = random.sample(COOK_INGREDIENTS, 3)
        text = (f"🍳 <b>{_esc(_bn(bot).upper())}'S KITCHEN</b>\n\n"
                f"👨‍🍳 Today's special: {mention} {_pick(COOK_DONE, f'{k}:cd')}.\n"
                f"🧂 Ingredients: {ingredients[0]}, {ingredients[1]} and {ingredients[2]}.\n"
                f"🌡️ Core temperature: <b>{random.randint(250, 999)}°</b>\n"
                f"📝 Chef's review: <i>{_pick(COOK_REVIEWS, f'{k}:cr')}</i>\n\n"
                f"Status: <b>{random.choice(COOK_STATUS)}</b>")
    await update.effective_message.reply_html(text)
    _award_command(chat.id, ruid, rname, uid, name)


async def roast_cmd(update, context):
    await _roast_line(update, context, "roast")


async def burn_cmd(update, context):
    await _roast_line(update, context, "burn")


async def finisher_cmd(update, context):
    await _roast_line(update, context, "finisher")


async def cook_cmd(update, context):
    await _roast_line(update, context, "cook")


async def roastme_cmd(update, context):
    if not await _group(update) or not await _cool(update):
        return
    uid, name = _who(update.effective_user)
    line = _pick(ROASTME, f"{update.effective_chat.id}:rme").format(n=_mention(uid, name))
    await update.effective_message.reply_html(f"{_head(context.bot, 'ROAST', '🔥')}\n\n{line}")
    _ensure_profile(update.effective_chat.id, uid, name)
    _bump(update.effective_chat.id, uid, roasts_received=1)


async def comeback_cmd(update, context):
    """/comeback: reply to someone's message for a comeback aimed at them, or use it alone."""
    if not await _group(update) or not await _cool(update):
        return
    msg, bot = update.effective_message, context.bot
    line = _pick(COMEBACKS, f"{update.effective_chat.id}:cb")
    rep = msg.reply_to_message
    if rep and rep.from_user and rep.from_user.id not in (update.effective_user.id, bot.id):
        line = f"{_mention(*_who(rep.from_user))}: {line}"
    await msg.reply_html(f"{_head(bot, 'COMEBACK', '😎')}\n\n{line}")


# ------------------------------------------------------------ roast battles
_BATTLE = {}  # chat_id -> {"id", "phase", "a", "b", "got", "vote_msg"}  (fast path for the text listener)


def _battle_names(row):
    return row["challenger_name"], row["opponent_name"]


async def roastbattle_cmd(update, context):
    if not await _group(update) or not await _cool(update):
        return
    tgt = await _target(update, context, "Usage: /roastbattle @user  (or reply to them)")
    if not tgt:
        return
    chat, msg, bot = update.effective_chat, update.effective_message, context.bot
    if chat.id in _BATTLE:
        await msg.reply_text("A roast battle is already running here. Wait for it to finish!")
        return
    uid, name, mention = tgt
    cuid, cname = _who(update.effective_user)
    now = int(time.time())
    _BATTLE[chat.id] = {"id": 0, "phase": "pending", "a": cuid, "b": uid, "got": {}, "vote_msg": None}
    try:
        await _open_battle(bot, chat, msg, cuid, cname, uid, name, mention, now)
    except Exception:
        _BATTLE.pop(chat.id, None)  # never leave the chat stuck "in battle"
        raise


async def _open_battle(bot, chat, msg, cuid, cname, uid, name, mention, now):
    bid = M.next_id("roast_battles")
    doc = dict.fromkeys(_BATTLE_COLS)
    doc.update(id=bid, chat_id=chat.id, challenger_id=cuid, challenger_name=cname, opponent_id=uid,
               opponent_name=name, status="pending", created=now, deadline=now + ROAST_ACCEPT_SECS)
    M.col("roast_battles").insert_one(doc)
    _BATTLE[chat.id]["id"] = bid
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("⚔️ Accept", callback_data=f"rb:acc:{bid}"),
                                InlineKeyboardButton("🏳️ Decline", callback_data=f"rb:dec:{bid}")]])
    sent = await msg.reply_html(
        f"{_head(bot, 'ROAST BATTLE', '⚔️')}\n\n{_mention(cuid, cname)} challenges {mention} to a roast battle!\n"
        f"{mention}, you have {ROAST_ACCEPT_SECS}s to accept.", reply_markup=kb)
    _battle_set(bid, message_id=sent.message_id)
    _spawn(_pending_timer(bot, chat.id, bid, sent.message_id))


async def _pending_timer(bot, chat_id, bid, message_id):
    await asyncio.sleep(ROAST_ACCEPT_SECS)
    rc = _battle_move(bid, "pending", "expired")
    if rc:
        _BATTLE.pop(chat_id, None)
        await _edit(bot, chat_id, message_id,
                    f"{_head(bot, 'ROAST BATTLE', '⚔️')}\n\n⌛ Challenge expired - nobody showed up to fight.")


async def _fight_timer(bot, chat_id, bid):
    await asyncio.sleep(ROAST_FIGHT_SECS)
    st = _BATTLE.get(chat_id)
    if not st or st["id"] != bid or st["phase"] != "fighting" or len(st["got"]) == 2:
        return
    await _forfeit(bot, chat_id, bid)


async def _forfeit(bot, chat_id, bid):
    st = _BATTLE.get(chat_id)
    rc = _battle_move(bid, "fighting", "done")
    if not rc or not st:
        return
    row = _battle(bid)
    _BATTLE.pop(chat_id, None)
    a, b, got = row["challenger_id"], row["opponent_id"], st["got"]
    an, bn = _battle_names(row)
    head = _head(bot, "ROAST BATTLE", "⚔️")
    if not got:
        _add_result(battle_id=bid, chat_id=chat_id, outcome="no-show")
        await _send(bot, chat_id, f"{head}\n\n🐔 Neither fighter showed up. Battle cancelled, no points changed.")
        return
    winner = next(iter(got))
    loser = b if winner == a else a
    wname, lname = (an, bn) if winner == a else (bn, an)
    _apply_result(chat_id, winner, wname, loser, lname, "win", 5)
    _add_result(battle_id=bid, chat_id=chat_id, winner_id=winner, loser_id=loser, outcome="forfeit")
    await _send(bot, chat_id, f"{head}\n\n🏳️ {_mention(loser, lname)} ran out of time.\n"
                f"🏆 {_mention(winner, wname)} wins by forfeit! (+5 points)")


def _apply_result(chat_id, w, wname, l, lname, outcome, win_points=10):
    _ensure_profile(chat_id, w, wname)
    _ensure_profile(chat_id, l, lname)
    if outcome == "win":
        with _profile_lock:  # the new best streak is computed from the current streak
            cur = _one("roast_profiles", {"chat_id": chat_id, "user_id": w}, _PROFILE_COLS) or {}
            M.col("roast_profiles").update_one(
                {"chat_id": chat_id, "user_id": w},
                {"$inc": {"wins": 1, "points": win_points, "streak": 1},
                 "$max": {"best_streak": (cur.get("streak") or 0) + 1}})
        M.col("roast_profiles").update_one(
            {"chat_id": chat_id, "user_id": l},
            {"$inc": {"losses": 1, "points": 2 if win_points >= 10 else 0}, "$set": {"streak": 0}})
    else:  # draw: w and l are just the two fighters
        for uid in (w, l):
            _bump(chat_id, uid, draws=1, points=5)


async def battle_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Collects each fighter's roast: their next plain message (3+ words) during the fight."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not msg.text or not user or not chat:
        return
    st = _BATTLE.get(chat.id)
    if not st or st["phase"] != "fighting" or user.id not in (st["a"], st["b"]) or user.id in st["got"]:
        return
    if len(msg.text.split()) < 3:
        return
    st["got"][user.id] = msg.text.strip()[:600]
    try:
        await msg.reply_text("🎤 Roast locked in!")
    except TelegramError:
        pass
    if len(st["got"]) == 2:
        await _start_voting(context.bot, chat.id, st["id"])


async def _start_voting(bot, chat_id, bid):
    st = _BATTLE.get(chat_id)
    rc = _battle_move(bid, "fighting", "voting", deadline=int(time.time()) + ROAST_VOTE_SECS)
    if not rc or not st:
        return
    row = _battle(bid)
    a, b = row["challenger_id"], row["opponent_id"]
    an, bn = _battle_names(row)
    ta, tb = st["got"][a], st["got"][b]
    sa, na = score_roast(ta, bn, tb)
    sb, nb = score_roast(tb, an, ta)
    _battle_set(bid, text_a=ta, text_b=tb, algo_a=sa, algo_b=sb)
    st["phase"] = "voting"

    def note(ns):
        return f" <i>({', '.join(ns)})</i>" if ns else ""
    kb = InlineKeyboardMarkup([[InlineKeyboardButton(f"🅰️ {an[:14]}", callback_data=f"rb:v:{bid}:1"),
                                InlineKeyboardButton(f"🅱️ {bn[:14]}", callback_data=f"rb:v:{bid}:2")]])
    sent = await _send(
        bot, chat_id,
        f"{_head(bot, 'ROAST BATTLE', '⚔️')} - round over!\n\n"
        f"🅰️ <b>{_esc(an)}</b>: {_esc(ta)}\n🤖 Judge: <b>{sa}</b>/100{note(na)}\n\n"
        f"🅱️ <b>{_esc(bn)}</b>: {_esc(tb)}\n🤖 Judge: <b>{sb}</b>/100{note(nb)}\n\n"
        f"🗳 Crowd vote for {ROAST_VOTE_SECS}s: tap a button or send /roastvote 1 or /roastvote 2.\n"
        f"Final = 70% judge + 30% crowd. Fighters can't vote.", reply_markup=kb)
    st["vote_msg"] = sent.message_id if sent else None
    _spawn(_vote_timer(bot, chat_id, bid))


async def _vote_timer(bot, chat_id, bid):
    await asyncio.sleep(ROAST_VOTE_SECS)
    await _finish_battle(bot, chat_id, bid)


async def _finish_battle(bot, chat_id, bid):
    rc = _battle_move(bid, "voting", "done")
    if not rc:
        return
    st = _BATTLE.pop(chat_id, None) or {}
    row = _battle(bid)
    a, b = row["challenger_id"], row["opponent_id"]
    an, bn = _battle_names(row)
    votes = _tally("roast_votes", "battle_id", bid, "choice")
    va = next((v["n"] for v in votes if v["choice"] == 1), 0)
    vb = next((v["n"] for v in votes if v["choice"] == 2), 0)
    total = va + vb
    ca, cb = (100 * va / total, 100 * vb / total) if total else (50.0, 50.0)
    fa = round(0.7 * row["algo_a"] + 0.3 * ca, 1)
    fb = round(0.7 * row["algo_b"] + 0.3 * cb, 1)
    head = _head(bot, "ROAST BATTLE", "⚔️")
    if abs(fa - fb) < 2:
        outcome, winner, loser = "draw", None, None
        _apply_result(chat_id, a, an, b, bn, "draw")
        verdict = "🤝 <b>It's a DRAW!</b> Both fighters get +5 points."
    else:
        outcome = "win"
        winner, loser = (a, b) if fa > fb else (b, a)
        wname, lname = (an, bn) if winner == a else (bn, an)
        _apply_result(chat_id, winner, wname, loser, lname, "win")
        verdict = f"🏆 <b>{_esc(wname)} WINS!</b> +10 points (loser gets +2 for bravery)."
    _add_result(battle_id=bid, chat_id=chat_id, winner_id=winner, loser_id=loser, final_a=fa, final_b=fb,
                votes_a=va, votes_b=vb, outcome=outcome)
    if st.get("vote_msg"):
        try:
            await bot.edit_message_reply_markup(chat_id=chat_id, message_id=st["vote_msg"], reply_markup=None)
        except TelegramError:
            pass
    await _send(bot, chat_id, f"{head} - FINAL\n\n🅰️ {_esc(an)}: <b>{fa}</b> (judge {row['algo_a']}, votes {va})\n"
                f"🅱️ {_esc(bn)}: <b>{fb}</b> (judge {row['algo_b']}, votes {vb})\n\n{verdict}")


def _cast_roast_vote(chat_id, voter_id, bid, choice):
    """Returns an error string, or None when the vote was counted."""
    st = _BATTLE.get(chat_id)
    if not st or st["id"] != bid or st["phase"] != "voting":
        return "Voting is closed."
    if voter_id in (st["a"], st["b"]):
        return "Fighters can't vote in their own battle."
    M.col("roast_votes").replace_one(
        {"battle_id": bid, "voter_id": voter_id},
        {"battle_id": bid, "chat_id": chat_id, "voter_id": voter_id, "choice": choice, "ts": int(time.time())},
        upsert=True)
    return None


async def roastvote_cmd(update, context):
    if not await _group(update):
        return
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    st = _BATTLE.get(chat.id)
    if not st or st["phase"] != "voting":
        await msg.reply_text("No roast battle is open for voting right now.")
        return
    choice = None
    arg = (context.args[0].lower() if context.args else "")
    if arg in ("1", "a"):
        choice = 1
    elif arg in ("2", "b"):
        choice = 2
    else:
        info, _ = await _resolve(update, context)
        if info and info[0] == st["a"]:
            choice = 1
        elif info and info[0] == st["b"]:
            choice = 2
    if choice is None:
        await msg.reply_text("Usage: /roastvote 1  or  /roastvote 2  (or reply to / @mention the fighter you pick).")
        return
    err = _cast_roast_vote(chat.id, user.id, st["id"], choice)
    await msg.reply_text(err or f"🗳 Vote counted for {'🅰️' if choice == 1 else '🅱️'}!")


async def roast_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    parts = (q.data or "").split(":")
    if len(parts) < 3 or not q.message:
        await q.answer()
        return
    action, chat_id = parts[1], q.message.chat_id
    try:
        bid = int(parts[2])
    except ValueError:
        await q.answer()
        return
    row = _battle(bid, chat_id)
    if not row:
        await q.answer("This battle is gone.", show_alert=True)
        return
    uid, bot = q.from_user.id, context.bot
    if action == "v":
        if len(parts) < 4:
            await q.answer()
            return
        err = _cast_roast_vote(chat_id, uid, bid, 1 if parts[3] == "1" else 2)
        await q.answer(err or "Vote counted! 🗳", show_alert=bool(err))
        return
    if row["status"] != "pending":
        await q.answer("Too late - that challenge is already settled.", show_alert=True)
        return
    an, bn = _battle_names(row)
    head = _head(bot, "ROAST BATTLE", "⚔️")
    if action == "dec":
        if uid not in (row["challenger_id"], row["opponent_id"]):
            await q.answer("Only the two fighters can cancel this.", show_alert=True)
            return
        rc = _battle_move(bid, "pending", "declined")
        if rc:
            _BATTLE.pop(chat_id, None)
            await q.answer()
            await _edit(bot, chat_id, q.message.message_id, f"{head}\n\n🏳️ The challenge was declined.")
        else:
            await q.answer("Too late - that challenge is already settled.", show_alert=True)
        return
    if action == "acc":
        if uid != row["opponent_id"]:
            await q.answer(f"Only {bn} can accept this challenge.", show_alert=True)
            return
        rc = _battle_move(bid, "pending", "fighting", deadline=int(time.time()) + ROAST_FIGHT_SECS)
        if not rc:
            await q.answer("Too late!", show_alert=True)
            return
        st = _BATTLE.setdefault(chat_id, {"id": bid, "a": row["challenger_id"], "b": row["opponent_id"],
                                          "got": {}, "vote_msg": None})
        st["phase"], st["got"] = "fighting", {}
        await q.answer("FIGHT!")
        await _edit(bot, chat_id, q.message.message_id,
                    f"{head}\n\n🥊 {_mention(row['challenger_id'], an)} vs {_mention(row['opponent_id'], bn)}\n\n"
                    f"🎤 Each fighter: send ONE roast about your opponent as a normal message (3+ words, "
                    f"don't reply to me) within {ROAST_FIGHT_SECS}s. The first one counts!\n"
                    "Be playful: no hate, threats or low blows - those score 0.")
        _spawn(_fight_timer(bot, chat_id, bid))


async def roastscore_cmd(update, context):
    if not await _group(update):
        return
    tgt = await _target_or_self(update, context)
    if not tgt:
        return
    uid, name, mention = tgt
    p = _one("roast_profiles", {"chat_id": update.effective_chat.id, "user_id": uid}, _PROFILE_COLS)
    head = _head(context.bot, "ROAST SCORE", "🏆")
    if not p:
        await update.effective_message.reply_html(f"{head}\n\n{mention} has no roast record in this chat yet.")
        return
    await update.effective_message.reply_html(
        f"{head}\n\n{mention}\n⭐ Points: <b>{p['points']}</b>\n"
        f"⚔️ Battles: <b>{p['wins']}W - {p['losses']}L - {p['draws']}D</b>\n"
        f"🔥 Win streak: <b>{p['streak']}</b> (best {p['best_streak']})")


async def roaststats_cmd(update, context):
    if not await _group(update):
        return
    tgt = await _target_or_self(update, context)
    if not tgt:
        return
    uid, name, mention = tgt
    cid = update.effective_chat.id
    head = _head(context.bot, "ROAST STATS", "📊")
    p = _one("roast_profiles", {"chat_id": cid, "user_id": uid}, _PROFILE_COLS)
    if not p:
        await update.effective_message.reply_html(f"{head}\n\n{mention} has no roast stats in this chat yet.")
        return
    rank = M.col("roast_profiles").count_documents({"chat_id": cid, "points": {"$gt": p["points"]}}) + 1
    played = p["wins"] + p["losses"] + p["draws"]
    rate = f"{round(100 * p['wins'] / played)}%" if played else "-"
    await update.effective_message.reply_html(
        f"{head}\n\n{mention}\n🏅 Rank: <b>#{rank}</b>  ⭐ Points: <b>{p['points']}</b>\n"
        f"⚔️ Battles: {played} ({p['wins']}W / {p['losses']}L / {p['draws']}D) - win rate {rate}\n"
        f"🔥 Streak: {p['streak']} (best {p['best_streak']})\n"
        f"🎤 Roasts given: {p['roasts_given']}  🎯 Roasts received: {p['roasts_received']}")


async def roastking_cmd(update, context):
    if not await _group(update):
        return
    rows = _many("roast_profiles", {"chat_id": update.effective_chat.id, "points": {"$gt": 0}}, _PROFILE_COLS,
                 sort=[("points", -1), ("wins", -1)], limit=5)
    head = _head(context.bot, "ROAST KING", "👑")
    if not rows:
        await update.effective_message.reply_html(f"{head}\n\nNo roasters yet - start with /roast @user!")
        return
    medals = ["👑", "🥈", "🥉", "4️⃣", "5️⃣"]
    lines = [f"{medals[i]} {_mention(r['user_id'], r['name'])} - <b>{r['points']}</b> pts ({r['wins']} wins)"
             for i, r in enumerate(rows)]
    await update.effective_message.reply_html(f"{head}\n\n" + "\n".join(lines))


# =====================================================================
#  3. COURT SYSTEM  (fictional comedy only - never touches real rights)
# =====================================================================
CHARGES = [
    "Grand theft of the last slice of pizza", "Aggravated overuse of the word \"literally\"",
    "Reckless endangerment of group-chat peace", "Unlawful possession of 47 unread voice notes",
    "First-degree sending \"k\" as a full reply", "Conspiracy to ghost a group poll",
    "Impersonating a person who replies on time", "Smuggling spicy takes across the border of common sense",
    "Unauthorized borrowing of a charger (never returned)", "Public performance of off-key shower songs",
    "Operating a meme without a license", "Starting a typing bubble and never following up",
    "Hoarding stickers beyond lawful limits", "Disturbing the peace with a 3 AM \"hey\"",
    "Possession of a dangerously sarcastic tone", "Failure to react ❤️ to a friend's good news",
    "Sneaking pineapple onto a pizza in the dark", "Counterfeit \"I'm on my way\" messages",
    "Aiding and abetting a terrible pun", "Hijacking the chat for a 200-message debate about cereal",
    "Tax evasion: owes 14 imaginary cookies", "Laughing at their own joke before the punchline",
    "Selling premium vibes without a permit", "Reckless driving of a shopping cart",
    "Contempt of court (sneezed during the anthem)", "Obstruction of justice by hiding the remote",
    "Illegal parking in the \"seen\" zone", "Excessive use of the 🥲 emoji in a public place",
]
EVIDENCE = [
    "Exhibit A: a blurry photo of a suspiciously guilty-looking sandwich",
    "Exhibit B: 14 screenshots, all cropped dramatically",
    "A witness duck that quacked \"yes\" three times",
    "Security footage of a person who is 80% the defendant and 20% a lamp",
    "A crumb trail leading directly to the defendant's keyboard",
    "Fingerprints on the cookie jar (and on the jar next to it)",
    "A diary entry reading \"I did it, lol\"",
    "A receipt for 9 cheese puffs bought at 2 AM",
    "The defendant's search history: \"how to look innocent\"",
    "A sticky note: \"Do NOT blame me\" (in the defendant's handwriting)",
    "Testimony from a parrot with a grudge",
    "A sworn statement from autocorrect",
    "A suspicious 😏 sent at 11:59 PM",
    "DNA evidence: glitter. So much glitter.",
    "A folder labeled \"Definitely Innocent\" that is suspiciously empty",
    "Muddy flip-flop prints leading from the crime scene to the fridge",
    "A confession typed entirely in lowercase",
    "A forensic report stating \"it was probably Steve\" (no Steve was found)",
    "Eyewitness: a goldfish that has seen things",
    "A thumbs-up sent at the worst possible moment",
    "A suspicious bag of popcorn found at the scene, still warm",
    "A voice note of someone saying \"trust me\" 11 times",
    "The defendant's browser history: 87 tabs, all titled \"alibi ideas\"",
    "A receipt for one (1) comically large foam finger",
    "A cat that looked at the defendant and then looked away. Suspicious.",
    "A hand-drawn map with an X marked \"snacks\"",
]
ALIBIS = [
    "I was at home, alone, rehearsing a surprise party for no one.",
    "I was busy teaching my plant to dance.",
    "I was in a very important staring contest with a wall.",
    "My dog ate the evidence, and also my homework, and also my phone.",
    "I was in the bathroom. For 3 hours. Hydration is important.",
    "I was at a seminar called \"How to Not Be Here\".",
    "I can't be guilty, I was buffering.",
    "I was walking my invisible dog.",
    "I was stuck in an elevator that only exists in my imagination.",
    "I was knitting a sweater for a snail. It's a long-term project.",
    "I was losing an argument to a parrot. Check the footage.",
    "I was busy composing a symphony of microwave beeps.",
    "I was at a family reunion... of my houseplants.",
    "I was in a long meeting with my own thoughts. We didn't agree on anything.",
    "I was alphabetizing my cereal collection. It took all day.",
    "I was on hold with customer support. I'm still on hold.",
    "I was chasing a butterfly that owed me money.",
    "I was doing yoga so advanced that I'm technically in two places at once.",
    "I was loading. Please wait.",
    "I was at the library, loudly.",
    "I was napping, which is a legal alibi in at least three imaginary countries.",
    "I was at a cooking class for water.",
    "I was in a witness protection programme for my own snacks.",
    "I was rehearsing my \"I'm innocent\" face in the mirror.",
]
SENTENCES = [
    "Wear the imaginary title \"Chief Clown Officer 🤡\" until sunrise.",
    "Solve a silly quiz: name 5 fruits that aren't bananas. No pressure.",
    "Write a heartfelt poem about a spoon and share it with the jury.",
    "Compliment the next 3 people who talk. Sincerely.",
    "Narrate your next message in a dramatic documentary voice.",
    "End every sentence with \"respectfully\" for one hour.",
    "Community service: bring imaginary snacks for the whole jury.",
    "Write \"I will not leave messages on read\" 50 times (in your imagination).",
    "Hug a virtual cactus. It is very soft. Allegedly.",
    "Sing the alphabet in a robot voice.",
    "Do 10 imaginary jumping jacks while the jury judges quietly.",
    "Rename your imaginary pet to \"Your Honor\".",
    "Tell the group your most embarrassing (harmless) fact. Fruit-related if possible.",
    "Send the group a wholesome meme and defend it with a speech.",
    "Wear socks on your hands for 5 minutes (optional, the court trusts you).",
    "Learn one useless fact and present it like breaking news.",
    "Be the group's official hype person for the next hour.",
    "Declare \"I am a menace\" in a calm, professional tone.",
    "Walk the plank... made of cardboard, into a pool of confetti.",
    "Serve the jury an imaginary five-course meal. Review: 2 stars.",
    "Confess to a crime so tiny it needs a magnifying glass.",
    "Dance (in your head) to the worst song you know.",
    "Pay the court 25 imaginary cookies. 🍪",
    "Become the court jester for 24 hours (a very prestigious job).",
    "Say \"banana\" every time someone says your name. Only in your heart.",
    "Eat a slice of metaphorical humble pie. Gluten-free.",
]
INNOCENT_LINES = [
    "walks free with a complimentary balloon 🎈", "is cleared and receives an imaginary medal 🏅",
    "is innocent! The jury is sorry and bakes cookies 🍪", "is free to go. The duck witness has been sent home 🦆",
    "is acquitted and awarded 100 imaginary cookies 🍪", "is innocent, and the real culprit was a sneaky raccoon 🦝",
]
NOT_PROVEN_LINES = [
    "The evidence was \"mostly vibes\", so the court shrugs 🤷",
    "The jury couldn't agree, so everyone gets a sticker and a nap 😴",
    "Case closed due to a shortage of drama. Come back with more snacks 🍿",
    "The judge lost the paperwork. Allegedly. Probably the cat 🐈",
    "Not enough proof, too many opinions. The court is adjourning for lunch 🥪",
]
CHAOS_OUTCOMES = [
    "The judge's cat walked across the keyboard and typed \"guilty-ish\". The court refuses to elaborate.",
    "Verdict decided by rock-paper-scissors. The defendant played paper. Nobody knows what paper did.",
    "The jury turned into pigeons and flew away. Case dismissed by flapping.",
    "The gavel broke, so everyone is declared guilty of laughing. Court adjourned.",
    "A wild goose burst in with a megaphone and shouted \"HONK\". Legally binding.",
    "A time traveler arrived to say the defendant was innocent in the future. The court is confused.",
    "The judge asked the Magic 8-Ball. It said \"ask again later\". The court is still waiting.",
    "The defendant, the jury and the judge swapped places. Nobody noticed. Case closed.",
]
WANTED_TRAITS = [
    "Smells faintly of cookies", "Answers \"lol\" to serious questions", "Has 3 emotional-support snacks",
    "Last seen laughing at their own joke", "Allergic to replying on time", "Dangerously good at memes",
    "May moonwalk when startled", "Always has one earbud in", "Collects stickers like trading cards",
    "Talks to pigeons", "Has the aura of a main character", "Cannot resist the last slice",
    "Wears socks with sandals, defiantly", "Speaks fluent sarcasm", "Dances in elevators",
    "Is never fully charged", "Hides snacks in unexpected places", "Whistles off-key",
    "Carries a suspiciously large water bottle", "Sends 14 emojis for a single word",
    "Claims to be \"five minutes away\" from everywhere", "Gets lost in their own house",
    "Laughs \"haha\" but means \"hmm\"", "Says \"I'm fine\" while holding a snack tower",
]
WANTED_SEEN = [
    "near the snack aisle, acting suspiciously calm", "inside a cardboard box labeled \"Not Me\"",
    "dancing in a parking lot", "queuing for a sale that ended last week",
    "behind a suspiciously small plant", "at a buffet, \"just looking\"",
    "in the typing... bubble, never to return", "running away from a group poll on a hoverboard (rumored)",
]
EXECUTIONS = [
    "{n} was executed by 47 angry ducks 🦆 - they quacked until morale improved.",
    "{n} was executed by a squadron of aggressive tickle-feathers 🪶. Survivors are laughing.",
    "{n} was executed by a tidal wave of confetti 🎉 and left sparkling.",
    "{n} faced the Great Pillow Fight Tribunal 🛏️ and lost with dignity.",
    "{n} was executed by a stampede of tiny hamsters in helmets 🐹.",
    "{n} was executed via 9,000 dad jokes read aloud. 😩",
    "{n} was executed by a pie to the face 🥧. The pie pleaded no contest.",
    "{n} was executed by a marching band of kazoos 🎺. The encore was worse.",
    "{n} was executed by a conga line of penguins 🐧. Dignity not recovered.",
    "{n} was sent to the shadow realm, which is just a very quiet library 📚.",
    "{n} was executed by a bubble-wrap barrage 🫧. Pop pop, case closed.",
    "{n} was executed by a goose with a megaphone 🪿📢. HONK was the final word.",
    "{n} was executed by a squad of ninjas armed with feather dusters 🥷🪶.",
    "{n} was executed by an avalanche of marshmallows ☁️. Surprisingly soft.",
    "{n} was executed by 12 slow-clapping flamingos 🦩. Humiliating, yet elegant.",
    "{n} was executed by a very polite raccoon with a tiny gavel 🦝.",
    "{n} was executed by an army of rubber chickens 🐔. Honk-adjacent.",
    "{n} was executed by a blast of glitter 💥✨. They'll be finding it for years.",
]
PLEAS = {
    "i": "😇 Pleads NOT GUILTY: \"I'm innocent, I tell you!\"",
    "g": "😭 Pleads GUILTY: \"I did it, I'm sorry!\"",
    "n": "🤫 Says NO COMMENT and stares into the distance.",
}


def _decide(g, i, plea):
    """Fictional verdict. Guilty plea = confession; otherwise the jury decides."""
    if plea == "g":
        return "GUILTY"
    total = g + i
    if total < COURT_MIN_JURY:
        return "NOT PROVEN"
    if g == i:
        return "CHAOS VERDICT"
    if max(g, i) / total < 0.6:
        return "NOT PROVEN"
    return "GUILTY" if g > i else "INNOCENT"


def _case_text(bot, case):
    mins = max(1, COURT_OPEN_SECS // 60)
    plea = f"\n🗣 <b>Plea:</b> {PLEAS[case['plea']]}" if case["plea"] else ""
    appeal = " (APPEAL TRIAL)" if case["appeals"] else ""
    return (f"{_head(bot, 'COURT', '⚖️')}\n"
            f"📂 <b>Case #{case['case_no']}</b>{appeal} - The People vs. {_mention(case['defendant_id'], case['defendant_name'])}\n"
            f"👨‍⚖️ Judge: {_esc(_bn(bot))}  🧑‍💼 Prosecutor: {_mention(case['opened_by'], case['opened_by_name'])}\n\n"
            f"📜 <b>Charge:</b> {_esc(case['charge'])}\n🧾 <b>Evidence:</b> {_esc(case['evidence'])}{plea}\n\n"
            f"🗳 <b>Jury:</b> everyone but the defendant - /guilty or /innocent (reply to this message, or add @user)\n"
            f"⏳ Court closes in about {mins} min, or when an admin/prosecutor calls /verdict.\n"
            "🎭 <i>Pure comedy: no real bans, mutes or kicks. Ever.</i>")


def _plea_keyboard(case_id):
    # one button per row so the full label always fits on a phone screen
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("😇 I'M INNOCENT", callback_data=f"ct:plea:{case_id}:i")],
        [InlineKeyboardButton("😭 PLEAD GUILTY", callback_data=f"ct:plea:{case_id}:g")],
        [InlineKeyboardButton("🤫 NO COMMENT", callback_data=f"ct:plea:{case_id}:n")],
    ])


async def court_cmd(update, context):
    """/court @user and /trial @user: opens a fictional trial."""
    if not await _group(update) or not await _cool(update):
        return
    tgt = await _target(update, context, "Usage: /court @user  (or reply to someone's message)")
    if not tgt:
        return
    uid, name, mention = tgt
    chat, msg, bot = update.effective_chat, update.effective_message, context.bot
    if _case({"chat_id": chat.id, "defendant_id": uid, "status": "open"}):
        await msg.reply_html(f"{mention} is already on trial here!")
        return
    k = chat.id
    now = int(time.time())
    no = ((_case({"chat_id": k}, sort=[("case_no", -1)]) or {}).get("case_no") or 0) + 1
    pid, pname = _who(update.effective_user)
    cid = M.next_id("court_cases")
    case = dict.fromkeys(_CASE_COLS)
    case.update(id=cid, chat_id=k, case_no=no, defendant_id=uid, defendant_name=name, opened_by=pid,
                opened_by_name=pname, charge=_pick(CHARGES, f"{k}:charge"), evidence=_pick(EVIDENCE, f"{k}:evid"),
                status="open", bail=0, appeals=0, opened=now, closes=now + COURT_OPEN_SECS)
    M.col("court_cases").insert_one(dict(case))
    sent = await msg.reply_html(_case_text(bot, case), reply_markup=_plea_keyboard(cid))
    _case_set(cid, message_id=sent.message_id)
    _spawn(_court_timer(bot, k, cid, COURT_OPEN_SECS))


async def _court_timer(bot, chat_id, case_id, secs):
    await asyncio.sleep(secs)
    text = _close_case(bot, case_id)
    if text:
        await _send(bot, chat_id, "⏰ <i>Time's up - the court rules by itself.</i>\n\n" + text)


def _close_case(bot, case_id):
    """Tally the jury, store the verdict, return the announcement (None if already closed)."""
    rc = _case_move(case_id, "open", "closing")
    if not rc:
        return None
    case = _case({"id": case_id})
    k = case["chat_id"]
    votes = _tally("court_votes", "case_id", case_id, "vote")
    g = next((v["n"] for v in votes if v["vote"] == "g"), 0)
    i = next((v["n"] for v in votes if v["vote"] == "i"), 0)
    verdict = _decide(g, i, case["plea"])
    sentence = None
    if verdict == "GUILTY":
        sentence = _pick(SENTENCES, f"{k}:sentence")
        if case["bail"]:
            sentence = f"Suspended because bail was posted (it would have been: {sentence})"
    _case_set(case_id, status="closed", sentence=sentence)
    _add_verdict(case_id=case_id, chat_id=k, defendant_id=case["defendant_id"], verdict=verdict,
                 guilty_votes=g, innocent_votes=i, plea=case["plea"], sentence=sentence)
    who = _mention(case["defendant_id"], case["defendant_name"])
    if verdict == "GUILTY":
        body = f"🔴 <b>GUILTY!</b>\n📜 Sentence: {_esc(sentence)}"
    elif verdict == "INNOCENT":
        body = f"🟢 <b>INNOCENT!</b> {who} {_pick(INNOCENT_LINES, f'{k}:inn')}"
    elif verdict == "NOT PROVEN":
        body = f"🟡 <b>NOT PROVEN.</b> {_pick(NOT_PROVEN_LINES, f'{k}:np')}"
    else:
        body = f"🌀 <b>CHAOS VERDICT!</b>\n{_pick(CHAOS_OUTCOMES, f'{k}:chaos')}"
    plea = f"\n🗣 Plea: {PLEAS[case['plea']]}" if case["plea"] else ""
    return (f"{_head(bot, 'COURT', '⚖️')} - VERDICT\n📂 <b>Case #{case['case_no']}</b> - {who}\n"
            f"🔴 Guilty votes: <b>{g}</b>   🟢 Innocent votes: <b>{i}</b>{plea}\n\n{body}\n\n"
            "🎭 <i>Fictional ruling - nothing real happened to anyone.</i>")


async def _find_case(update, context, statuses=("open",)):
    """Pick the case a command is about: the replied court message, the named user, or the chat's
    only open case. Replies with the reason and returns None if it can't."""
    msg, chat = update.effective_message, update.effective_chat
    rep = msg.reply_to_message
    if rep and rep.from_user and rep.from_user.id == context.bot.id:
        case = _case({"chat_id": chat.id, "message_id": rep.message_id, "status": {"$in": list(statuses)}})
        if case:
            return case
    info, err = await _resolve(update, context)
    if err:
        await msg.reply_html(err)
        return None
    if info and info[0] != context.bot.id:
        case = _case({"chat_id": chat.id, "defendant_id": info[0], "status": {"$in": list(statuses)}},
                     sort=[("id", -1)])
        if not case:
            await msg.reply_html(f"{info[2]} has no matching case here.")
        return case
    cases = _many("court_cases", {"chat_id": chat.id, "status": {"$in": list(statuses)}}, _CASE_COLS,
                  sort=[("id", -1)])
    open_cases = [c for c in cases if c["status"] == "open"]
    if len(open_cases) == 1:
        return open_cases[0]
    if not open_cases and len(statuses) > 1 and cases:
        return cases[0]  # nothing running: the chat's most recent case
    await msg.reply_text("No case is running here. Start one with /court @user." if not cases else
                         "Several cases are running - name the defendant, e.g. /verdict @user.")
    return None


async def _jury_vote(update, context, vote):
    if not await _group(update):
        return
    case = await _find_case(update, context)
    if not case:
        return
    msg, user = update.effective_message, update.effective_user
    if user.id == case["defendant_id"]:
        await msg.reply_text("The defendant can't sit on their own jury! Use the plea buttons instead. 😇")
        return
    M.col("court_votes").replace_one(
        {"case_id": case["id"], "voter_id": user.id},
        {"case_id": case["id"], "chat_id": case["chat_id"], "voter_id": user.id, "vote": vote,
         "ts": int(time.time())}, upsert=True)
    votes = _tally("court_votes", "case_id", case["id"], "vote")
    g = next((v["n"] for v in votes if v["vote"] == "g"), 0)
    i = next((v["n"] for v in votes if v["vote"] == "i"), 0)
    icon = "🔴 GUILTY" if vote == "g" else "🟢 INNOCENT"
    await msg.reply_html(f"{user.mention_html()} votes {icon} on Case #{case['case_no']}  (🔴 {g} - 🟢 {i})")


async def guilty_cmd(update, context):
    await _jury_vote(update, context, "g")


async def innocent_cmd(update, context):
    await _jury_vote(update, context, "i")


async def verdict_cmd(update, context):
    """/verdict: closes a case early (admin or prosecutor), or shows the last verdict."""
    if not await _group(update):
        return
    msg, chat, user, bot = update.effective_message, update.effective_chat, update.effective_user, context.bot
    case = await _find_case(update, context, statuses=("open", "closed", "pardoned"))
    if not case:
        return
    if case["status"] != "open":
        v = _one("court_verdicts", {"case_id": case["id"]}, _VERDICT_COLS, sort=[("id", -1)])
        who = _mention(case["defendant_id"], case["defendant_name"])
        await msg.reply_html(f"{_head(bot, 'COURT', '⚖️')}\n📂 Case #{case['case_no']} - {who}\n"
                             f"Last verdict: <b>{_esc(v['verdict']) if v else 'none'}</b>"
                             + (f"\n📜 Sentence: {_esc(v['sentence'])}" if v and v["sentence"] else ""))
        return
    if user.id != case["opened_by"] and not await D.is_admin(chat, user.id):
        await msg.reply_text("Only an admin or the prosecutor can call the verdict early - "
                             "or just wait for the jury timer.")
        return
    text = _close_case(bot, case["id"])
    if text:
        await msg.reply_html(text)


async def court_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """The defendant's plea buttons."""
    q = update.callback_query
    parts = (q.data or "").split(":")
    if len(parts) < 4 or parts[1] != "plea" or parts[3] not in PLEAS or not q.message:
        await q.answer()
        return
    case = _case({"id": int(parts[2]), "chat_id": q.message.chat_id})
    if not case or case["status"] != "open":
        await q.answer("This trial is already over.", show_alert=True)
        return
    if q.from_user.id != case["defendant_id"]:
        await q.answer("Only the defendant can enter a plea!", show_alert=True)
        return
    rc = M.col("court_cases").update_one({"id": case["id"], "status": "open", "plea": None},
                                         {"$set": {"plea": parts[3]}}).matched_count
    if not rc:
        await q.answer("You already entered a plea.", show_alert=True)
        return
    case["plea"] = parts[3]
    await q.answer("Plea entered!")
    await _edit(context.bot, q.message.chat_id, q.message.message_id, _case_text(context.bot, case))


async def sentence_cmd(update, context):
    """/sentence @user: a harmless fictional sentence (also stored on their latest guilty case)."""
    if not await _group(update) or not await _cool(update):
        return
    tgt = await _target(update, context, "Usage: /sentence @user", allow_self=True)
    if not tgt:
        return
    uid, name, mention = tgt
    k = update.effective_chat.id
    s = _pick(SENTENCES, f"{k}:sentence")
    case = _case({"chat_id": k, "defendant_id": uid, "status": "closed"}, sort=[("id", -1)])
    if case:
        _case_set(case["id"], sentence=s)
    await update.effective_message.reply_html(
        f"{_head(context.bot, 'COURT', '⚖️')} - SENTENCING\n\n{mention}, the court sentences you to:\n"
        f"📜 <b>{_esc(s)}</b>\n\n🎭 <i>Fictional and harmless.</i>")


async def _generator(update, context, title, icon, build, usage):
    if not await _group(update) or not await _cool(update):
        return
    tgt = await _target(update, context, usage, allow_self=True)
    if not tgt:
        return
    await update.effective_message.reply_html(
        f"{_head(context.bot, title, icon)}\n\n" + build(tgt[2], update.effective_chat.id))


async def crime_cmd(update, context):
    await _generator(update, context, "COURT - CRIME REPORT", "🚨", lambda m, k: (
        f"Suspect: {m}\n📜 Alleged crime: <b>{_esc(_pick(CHARGES, f'{k}:charge'))}</b>\n"
        f"😈 Severity: <b>{random.randint(1, 10)}/10</b>\n<i>Use /court to put them on trial.</i>"),
        "Usage: /crime @user")


async def evidence_cmd(update, context):
    await _generator(update, context, "COURT - EVIDENCE", "🧾", lambda m, k: (
        f"Against: {m}\n🔎 <b>{_esc(_pick(EVIDENCE, f'{k}:evid'))}</b>\n"
        f"📊 Reliability: <b>{random.randint(1, 99)}%</b>"), "Usage: /evidence @user")


async def alibi_cmd(update, context):
    await _generator(update, context, "COURT - ALIBI", "🕵️", lambda m, k: (
        f"{m} says:\n💬 <i>\"{_esc(_pick(ALIBIS, f'{k}:alibi'))}\"</i>\n"
        f"📉 Believability: <b>{random.randint(1, 40)}%</b>"), "Usage: /alibi @user")


async def execute_cmd(update, context):
    await _generator(update, context, "COURT - EXECUTION", "🦆", lambda m, k: (
        f"{_pick(EXECUTIONS, f'{k}:exec').format(n=m)}\n\n"
        "🎭 <i>Purely fictional comedy. Nobody was harmed, banned or muted.</i>"), "Usage: /execute @user")


async def wanted_cmd(update, context):
    def build(m, k):
        traits = random.sample(WANTED_TRAITS, 3)
        return (f"🚨🚨 <b>WANTED</b> 🚨🚨\n\n👤 {m}\n📜 Wanted for: <b>{_esc(_pick(CHARGES, f'{k}:charge'))}</b>\n"
                f"🔍 Traits: " + "; ".join(_esc(t.lower()) for t in traits) + f".\n"
                f"📍 Last seen: {_esc(_pick(WANTED_SEEN, f'{k}:seen'))}\n\n"
                f"💰 REWARD: <b>🍪 {random.randint(50, 9999):,} imaginary cookies</b>\n"
                "<i>Approach with snacks. Fictional poster.</i>")
    await _generator(update, context, "WANTED", "🚨", build, "Usage: /wanted @user")


async def bail_cmd(update, context):
    """/bail @user: pay imaginary cookies to bail someone out."""
    if not await _group(update) or not await _cool(update):
        return
    case = await _find_case(update, context, statuses=("open", "closed"))
    if not case:
        return
    if case["bail"]:
        await update.effective_message.reply_text("Bail has already been posted for this case.")
        return
    _case_set(case["id"], bail=1)
    amount = random.randint(10, 500)
    await update.effective_message.reply_html(
        f"{_head(context.bot, 'COURT', '⚖️')} - BAIL\n\n{update.effective_user.mention_html()} posts bail of "
        f"<b>🍪 {amount} imaginary cookies</b> for {_mention(case['defendant_id'], case['defendant_name'])}"
        f" (Case #{case['case_no']}).\nIf the verdict is guilty, the sentence will be suspended. 🎭")


async def pardon_cmd(update, context):
    """/pardon @user: admin-only judge's pardon (closes the case, wipes the guilty sentence)."""
    if not await _group(update):
        return
    if not await D.admin_only(update):
        return
    case = await _find_case(update, context, statuses=("open", "closed"))
    if not case:
        return
    _case_set(case["id"], status="pardoned", sentence=None)
    _add_verdict(case_id=case["id"], chat_id=case["chat_id"], defendant_id=case["defendant_id"],
                 verdict="PARDONED")
    await update.effective_message.reply_html(
        f"{_head(context.bot, 'COURT', '⚖️')} - PARDON\n\n🕊️ Case #{case['case_no']}: "
        f"{_mention(case['defendant_id'], case['defendant_name'])} has been officially pardoned by the court. "
        "Confetti everywhere! 🎉\n🎭 <i>Fictional.</i>")


async def appeal_cmd(update, context):
    """/appeal: the defendant reopens their latest case once (admins may appeal for someone)."""
    if not await _group(update) or not await _cool(update):
        return
    msg, chat, user, bot = update.effective_message, update.effective_chat, update.effective_user, context.bot
    info, err = await _resolve(update, context)
    if err:
        await msg.reply_html(err)
        return
    uid = user.id
    if info and info[0] not in (user.id, bot.id):
        if not await D.is_admin(chat, user.id):
            await msg.reply_text("You can only appeal your own case (admins can appeal for others).")
            return
        uid = info[0]
    case = _case({"chat_id": chat.id, "defendant_id": uid, "status": "closed"}, sort=[("id", -1)])
    verdict = _one("court_verdicts", {"case_id": case["id"]}, _VERDICT_COLS, sort=[("id", -1)]) if case else None
    if not case or not verdict or verdict["verdict"] == "INNOCENT":
        await msg.reply_text("There's no verdict to appeal. (Innocent people don't need appeals!)")
        return
    if case["appeals"] >= 1:
        await msg.reply_text("This case has already used its one appeal. The court is tired. 😴")
        return
    now = int(time.time())
    M.col("court_votes").delete_many({"case_id": case["id"]})
    M.col("court_cases").update_one(
        {"id": case["id"]},
        {"$set": {"status": "open", "plea": None, "sentence": None, "closes": now + COURT_OPEN_SECS},
         "$inc": {"appeals": 1}})
    case = _case({"id": case["id"]})
    sent = await msg.reply_html(_case_text(bot, case), reply_markup=_plea_keyboard(case["id"]))
    _case_set(case["id"], message_id=sent.message_id)
    _spawn(_court_timer(bot, chat.id, case["id"], COURT_OPEN_SECS))


# ------------------------------------------------------------ registration
def register(app, deps):
    """deps needs: is_admin, admin_only."""
    global D
    D = deps
    # a restart can't resume timers, so unfinished games are closed instead of left hanging
    M.col("roast_battles").update_many({"status": {"$in": ["pending", "fighting", "voting"]}},
                                       {"$set": {"status": "expired"}})
    M.col("court_cases").update_many({"status": {"$in": ["open", "closing"]}},
                                     {"$set": {"status": "expired"}})
    commands = {
        "roast": roast_cmd, "roastme": roastme_cmd, "cook": cook_cmd, "burn": burn_cmd,
        "finisher": finisher_cmd, "comeback": comeback_cmd, "roastbattle": roastbattle_cmd,
        "roastvote": roastvote_cmd, "roastscore": roastscore_cmd, "roaststats": roaststats_cmd,
        "roastking": roastking_cmd,
        "court": court_cmd, "trial": court_cmd, "guilty": guilty_cmd, "innocent": innocent_cmd,
        "verdict": verdict_cmd, "crime": crime_cmd, "evidence": evidence_cmd, "alibi": alibi_cmd,
        "sentence": sentence_cmd, "bail": bail_cmd, "pardon": pardon_cmd, "appeal": appeal_cmd,
        "execute": execute_cmd, "wanted": wanted_cmd,
    }
    for name, fn in commands.items():
        app.add_handler(CommandHandler(name, fn))
    app.add_handler(CallbackQueryHandler(roast_callback, pattern=r"^rb:"))
    app.add_handler(CallbackQueryHandler(court_callback, pattern=r"^ct:"))
    # group=2: listens for the fighters' roasts without ever blocking the normal handlers
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND, battle_input),
                    group=2)
