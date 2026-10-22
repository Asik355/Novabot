"""
lang/lang.py: the language system, kept apart from the main bot logic.

  t("key", chat_id, name=value)   the text for a key in the group's language (English if the key is missing)
  get_lang(chat_id) / set_lang(chat_id, code)   the group's language (setting "lang": "en" | "hinglish")
  register(app, deps, allowed, guard)           /lang and the 🌐 Language page (button on /help page 2: callback "lang:m")

Languages for now: English and Hinglish, both written below in this one file. To add one: another dict with the same keys
and one line in LANGS. Nothing here knows about the other bot features; group.py (and later other files) only call t().

deps (handed in by group.register, the same object group.py gets): group_only(update), get_setting, set_setting.
allowed(chat, user_id)  async: True for group admins, the bot owner and bot staff (group.py's own check, reused).
guard(q)                async: True when the /help menu belongs to someone else (extra.menu_not_owner, reused).
"""
import logging
import re

from telegram import InlineKeyboardButton, InlineKeyboardMarkup
from telegram.error import TelegramError
from telegram.ext import CallbackQueryHandler, CommandHandler

# ======================================================================================================
# The texts. Key -> text; placeholders look like {name}; HTML is allowed. A key missing in a language falls back to English.
# To add a language: one more dict with the same keys and one line in LANGS.
# ======================================================================================================
EN = {
    # ---- language page
    "lang.title": "<b>🌐 Language</b>",
    "lang.body": "Choose the language the bot uses in this group.\n\nNow: <b>{current}</b>",
    "lang.private": "Language is set for each group. Send /lang inside a group to change it there.",
    "lang.saved": "✅ Language is now <b>{current}</b>.",
    "lang.saved_alert": "Language: {current}",
    "lang.admin_only": "Only group admins can change the language.",
    "lang.unknown": "I don't know that language. Choose: English or Hinglish.",
    "lang.usage": "Usage:\n1. /lang: Show the language page.\n2. /lang en: English.\n3. /lang hinglish: Hinglish.",
    "lang.back": "« Back",

    # ---- time pickers (shared by Auto Close and Night Mode)
    "pick.step1": "<b>Step 1 of 3:</b> pick the hour.",
    "pick.step2": "<b>Step 2 of 3:</b> pick the minute, or send a number from 0 to 59 in this chat (for example <code>7</code> or <code>45</code>).",
    "pick.step3": "<b>Step 3 of 3:</b> pick AM or PM.",
    "pick.hour": "Hour: <b>{hour}</b>",
    "pick.time": "Time: <b>{time}</b>",
    "pick.back": "« Back",
    "pick.am": "☀️ AM",
    "pick.pm": "🌙 PM",

    # ---- Auto Close (the parts shared with the pickers)
    "ac.head_close": "<b>🕒 Auto Close: Close time</b>",
    "ac.head_open": "<b>🕒 Auto Close: Open time</b>",
    "ac.closes_at": "The group closes at <b>{time}</b>.",
    "ac.closes_toast": "Closes at {time}",
    "ac.same_time": "The opening time must be different from the closing time.",
    "ac.db_problem": "The database had a problem. Nothing was changed.",
    "ac.on_toast": "✅ Auto close is ON.",
    "ac.saved": "✅ Saved. Every day I close the group at <b>{close}</b> and open it at <b>{open}</b>.\nGive me the \"Ban users\" admin right so I can do it.",

    # ---- Night Mode
    "night.title": "<b>🌙 Night Mode</b>",
    "night.intro": "At night the group stays open, but members can only send plain text. Photos, videos, voice messages, files, stickers, GIFs and polls are switched off. Admins are not affected.",
    "night.tap": "Tap <b>Set Time</b> to choose when Night Mode starts and when it ends.",
    "night.note": "<b>Note:</b> The bot must be an admin with the \"Ban users\" right. <b>Auto Close comes first:</b> while it has the group closed, Night Mode waits.",
    "night.btn_set": "⏰ Set Time",
    "night.btn_off": "🔴 Turn OFF",
    "night.private": "Open /help inside a group to set up Night Mode for that group.",
    "night.status_off": "Status: <b>OFF ❌</b>",
    "night.status_on": "Status: <b>ON ✅</b> ({tz})\nStarts at <b>{start}</b> and ends at <b>{end}</b>, every day.\nNight Mode is {now} right now.",
    "night.now_active": "active 🌙",
    "night.now_idle": "not active ☀️",
    "night.admin_only": "Only group admins can change Night Mode.",
    "night.head_start": "<b>🌙 Night Mode: Start time</b>",
    "night.head_end": "<b>🌙 Night Mode: End time</b>",
    "night.starts_at": "Night Mode starts at <b>{time}</b>.",
    "night.starts_toast": "Starts at {time}",
    "night.same_time": "The start and end time must be different.",
    "night.on_toast": "✅ Night Mode is ON.",
    "night.saved": "✅ Saved. Every day Night Mode starts at <b>{start}</b> and ends at <b>{end}</b>.\nGive me the \"Ban users\" admin right so I can do it.",
    "night.off_done": "Night Mode is OFF.",
    "night.off_restored": " The group's permissions are back.",
    "night.off_failed": "Night Mode is OFF, but I couldn't give the permissions back. Please make me an admin with the 'Ban users' right, or change the group permissions yourself.",
    "night.start": "🌙 <b>Night Mode</b>\nPlease send text messages only. Photos, videos, voice messages, files, stickers and polls are off until <b>{open_time}</b>.",
    "night.end": "☀️ <b>Night Mode ended</b>\nEveryone can send photos, videos and files again.",
    "night.usage": "Usage:\n1. /night 11pm 6am: Text only every day from 11:00 PM to 6:00 AM.\n2. /night off: Turn Night Mode off.\n3. /night: Show the schedule.",
    "night.cmd_off": "Night Mode is OFF.",
    "night.cmd_on": "🌙 Night Mode is ON ({tz}).\nEvery day from {start} to {end} members can send text only.\nNight Mode is {now} right now.\n\nTurn it off with /night off.",
    "night.cant_read": "I couldn't read those times.",
    "night.cmd_saved": "✅ Night Mode is ON ({tz}).\nEvery day from {start} to {end} members can send text only.\nGive me the 'Ban users' admin right so I can do it.",

    # ---- Appeal
    "apl.title": "<b>📩 Appeal</b>",
    "apl.intro": "A member who was muted or warned can ask the admins to review it. The mute or warning notice gets an <b>Appeal</b> button. The member explains in a private chat with the bot, and the admins decide with one tap.",
    "apl.status_off": "Status: <b>OFF ❌</b>\nAppeals always reach the admins in the bot's private chat, and also go to: <b>{dest}</b>",
    "apl.status_on": "Status: <b>ON ✅</b>\nAppeals always reach the admins in the bot's private chat, and also go to: <b>{dest}</b>",
    "apl.note": "<b>Note:</b> Admins only receive the private copy after they have started the bot once. If the log channel isn't set or can't be used, the card goes to the group. Appeals cover manual mutes and warnings and the bot's own mutes. Bans and automatic spam or flood warnings have no Appeal button. A member whose appeal was rejected can appeal again.",
    "apl.btn_on": "🟢 Turn ON",
    "apl.btn_off": "🔴 Turn OFF",
    "apl.btn_list": "📋 Appeal List",
    "apl.dest_group": "👥 Group",
    "apl.dest_log": "📋 Log channel",
    "apl.toast_on": "✅ Appeal is ON.",
    "apl.toast_off": "Appeal is OFF.",
    "apl.toast_dest": "Appeals also go to: {dest}",
    "apl.admin_only": "Only group admins can change Appeal.",
    "apl.private": "Open /help inside a group to set up Appeal for that group.",
    "apl.usage": "Usage:\n1. /appeal: Show the Appeal page.\n2. /appeal on or /appeal off: Switch it.\n3. /appeal group or /appeal log: Where the extra appeal card goes (the admins always get it in the bot's private chat).",
    "apl.list_title": "<b>📋 Appeals ({count})</b>",
    "apl.list_empty": "There are no appeals yet.",
    "apl.list_line": "{n}. {user}: {kind}, {status}",
    "apl.list_tap": "Tap a pending appeal below to open it.",
    "apl.st_open": "⏳ Pending",
    "apl.st_approved": "✅ Accepted by {admin}",
    "apl.st_rejected": "❌ Rejected by {admin}",
    "apl.btn": "📩 Appeal",
    "apl.kind_mute": "mute",
    "apl.kind_warn": "warning",
    "apl.dm_off": "Appeals are not turned on in that group.",
    "apl.dm_invalid": "I can't open that group any more.",
    "apl.dm_none": "You have no active {kind} in <b>{chat}</b>, so there is nothing to appeal.",
    "apl.dm_open": "You already have a pending appeal for this. Please wait for the admins to decide.",
    "apl.dm_ask": "Appeal for your {kind} in <b>{chat}</b>.\n\nPlease write why you think it should be reviewed (maximum {max} characters), or send /skip to appeal without a reason. Send /cancel to stop.",
    "apl.dm_cancelled": "Cancelled. No appeal was sent.",
    "apl.dm_sent": "✅ Your appeal has been sent to the admins. We will notify you here as soon as they decide. You can check it any time with /myappeals.",
    "apl.dm_fail": "Sorry, I couldn't send your appeal. Please try again later.",
    "apl.card": "📩 <b>Appeal</b> in <b>{chat}</b>\nMember: {user}\nAbout: {kind}\nReason: {reason}",
    "apl.no_reason": "<i>none given</i>",
    "apl.btn_unmute": "✅ Unmute",
    "apl.btn_rmwarn": "✅ Remove warning",
    "apl.btn_reject": "❌ Reject",
    "apl.done_approved": "<i>✅ Accepted by {admin}.</i>",
    "apl.done_rejected": "<i>❌ Rejected by {admin}.</i>",
    "apl.already": "Another admin has already decided this appeal.",
    "apl.card_admin_only": "Only admins of that group can decide appeals.",
    "apl.undo_failed": "I couldn't do it. Please make sure I'm an admin with the 'Ban users' right, then tap again.",
    "apl.approved_dm_mute": "✅ <b>Good news!</b> Your appeal in <b>{chat}</b> has been accepted. Your mute has been lifted, and you can send messages again.",
    "apl.approved_dm_warn": "✅ <b>Good news!</b> Your appeal in <b>{chat}</b> has been accepted. Your warning has been removed.",
    "apl.rejected_dm": "❌ Your appeal in <b>{chat}</b> has been rejected by the admins. If you still believe this was a mistake, you can send a new appeal.",
    "apl.my_title": "<b>📩 Your appeals</b>",
    "apl.my_empty": "You haven't sent any appeals yet.",
    "apl.my_line": "{n}. <b>{chat}</b>: {kind}, {status}",
    "apl.my_st_open": "⏳ waiting for the admins",
    "apl.my_st_approved": "✅ accepted",
    "apl.my_st_rejected": "❌ rejected",
}

HINGLISH = {
    # ---- language page
    "lang.title": "<b>🌐 Language</b>",
    "lang.body": "Is group mein bot kis language mein baat kare, woh chuno.\n\nAbhi: <b>{current}</b>",
    "lang.private": "Language har group ki alag hoti hai. Badalne ke liye kisi group mein /lang bhejo.",
    "lang.saved": "✅ Language ab <b>{current}</b> hai.",
    "lang.saved_alert": "Language: {current}",
    "lang.admin_only": "Sirf group admins language badal sakte hain.",
    "lang.unknown": "Yeh language mujhe nahi pata. Chuno: English ya Hinglish.",
    "lang.usage": "Use kaise karein:\n1. /lang: Language page dikhao.\n2. /lang en: English.\n3. /lang hinglish: Hinglish.",
    "lang.back": "« Back",

    # ---- time pickers (shared by Auto Close and Night Mode)
    "pick.step1": "<b>Step 1 of 3:</b> ghanta (hour) chuno.",
    "pick.step2": "<b>Step 2 of 3:</b> minute chuno, ya is chat mein 0 se 59 ke beech koi number bhejo (jaise <code>7</code> ya <code>45</code>).",
    "pick.step3": "<b>Step 3 of 3:</b> AM ya PM chuno.",
    "pick.hour": "Hour: <b>{hour}</b>",
    "pick.time": "Time: <b>{time}</b>",
    "pick.back": "« Back",
    "pick.am": "☀️ AM",
    "pick.pm": "🌙 PM",

    # ---- Auto Close (the parts shared with the pickers)
    "ac.head_close": "<b>🕒 Auto Close: Band hone ka time</b>",
    "ac.head_open": "<b>🕒 Auto Close: Khulne ka time</b>",
    "ac.closes_at": "Group <b>{time}</b> pe band hoga.",
    "ac.closes_toast": "{time} pe band hoga",
    "ac.same_time": "Khulne ka time band hone ke time se alag hona chahiye.",
    "ac.db_problem": "Database mein problem aayi. Kuch change nahi hua.",
    "ac.on_toast": "✅ Auto close ON ho gaya.",
    "ac.saved": "✅ Save ho gaya. Roz main group <b>{close}</b> pe band karunga aur <b>{open}</b> pe khol dunga.\nMujhe \"Ban users\" admin right do taaki main yeh kar sakun.",

    # ---- Night Mode
    "night.title": "<b>🌙 Night Mode</b>",
    "night.intro": "Raat ko group khula rehta hai, lekin members sirf text bhej sakte hain. Photo, video, voice message, files, stickers, GIF aur poll band ho jaate hain. Admins pe koi asar nahi padta.",
    "night.tap": "<b>Set Time</b> dabao aur chuno ki Night Mode kab shuru ho aur kab khatam.",
    "night.note": "<b>Note:</b> Bot ke paas \"Ban users\" right wala admin hona zaroori hai. <b>Auto Close pehle aata hai:</b> jab woh group band rakhe, tab Night Mode ruka rehta hai.",
    "night.btn_set": "⏰ Set Time",
    "night.btn_off": "🔴 Turn OFF",
    "night.private": "Kisi group ke liye Night Mode set karne ke liye us group mein /help kholo.",
    "night.status_off": "Status: <b>OFF ❌</b>",
    "night.status_on": "Status: <b>ON ✅</b> ({tz})\nRoz <b>{start}</b> pe shuru hota hai aur <b>{end}</b> pe khatam.\nNight Mode abhi {now}.",
    "night.now_active": "chalu hai 🌙",
    "night.now_idle": "chalu nahi hai ☀️",
    "night.admin_only": "Sirf group admins Night Mode badal sakte hain.",
    "night.head_start": "<b>🌙 Night Mode: Shuru hone ka time</b>",
    "night.head_end": "<b>🌙 Night Mode: Khatam hone ka time</b>",
    "night.starts_at": "Night Mode <b>{time}</b> pe shuru hoga.",
    "night.starts_toast": "{time} pe shuru hoga",
    "night.same_time": "Shuru aur khatam hone ka time alag hona chahiye.",
    "night.on_toast": "✅ Night Mode ON ho gaya.",
    "night.saved": "✅ Save ho gaya. Roz Night Mode <b>{start}</b> pe shuru hoga aur <b>{end}</b> pe khatam.\nMujhe \"Ban users\" admin right do taaki main yeh kar sakun.",
    "night.off_done": "Night Mode OFF ho gaya.",
    "night.off_restored": " Group ki permissions wapas aa gayi.",
    "night.off_failed": "Night Mode OFF hai, lekin main permissions wapas nahi de paya. Mujhe \"Ban users\" right wala admin banao, ya group ki permissions khud badlo.",
    "night.start": "🌙 <b>Night Mode</b>\nKripya sirf text message bhejo. Photo, video, voice message, files, stickers aur poll <b>{open_time}</b> tak band hain.",
    "night.end": "☀️ <b>Night Mode khatam</b>\nAb sab photo, video aur files phir se bhej sakte hain.",
    "night.usage": "Use kaise karein:\n1. /night 11pm 6am: Roz raat 11:00 PM se subah 6:00 AM tak sirf text.\n2. /night off: Night Mode band karo.\n3. /night: Schedule dikhao.",
    "night.cmd_off": "Night Mode OFF hai.",
    "night.cmd_on": "🌙 Night Mode ON hai ({tz}).\nRoz {start} se {end} tak members sirf text bhej sakte hain.\nNight Mode abhi {now}.\n\n/night off se band karo.",
    "night.cant_read": "Mujhe woh time samajh nahi aaye.",
    "night.cmd_saved": "✅ Night Mode ON ho gaya ({tz}).\nRoz {start} se {end} tak members sirf text bhej sakte hain.\nMujhe \"Ban users\" admin right do taaki main yeh kar sakun.",

    # ---- Appeal
    "apl.title": "<b>📩 Appeal</b>",
    "apl.intro": "Jis member ko mute ya warn kiya gaya ho, woh admins se dobara review karne ko keh sakta hai. Mute ya warning ke notice mein <b>Appeal</b> button aata hai. Member bot ke private chat mein apni baat likhta hai, aur admins ek tap mein faisla karte hain.",
    "apl.status_off": "Status: <b>OFF ❌</b>\nAppeal hamesha bot ke private chat mein admins tak pahunchti hai, aur yahan bhi jaati hai: <b>{dest}</b>",
    "apl.status_on": "Status: <b>ON ✅</b>\nAppeal hamesha bot ke private chat mein admins tak pahunchti hai, aur yahan bhi jaati hai: <b>{dest}</b>",
    "apl.note": "<b>Note:</b> Admin ko private copy tabhi milti hai jab usne ek baar bot start kiya ho. Agar log channel set nahi hai ya use nahi ho sakta, to card group mein aata hai. Appeal manual mute, warning aur bot ke apne mute par chalti hai. Ban aur automatic spam ya flood warning par Appeal button nahi aata. Jiski appeal reject hui ho, woh dobara appeal kar sakta hai.",
    "apl.btn_on": "🟢 Turn ON",
    "apl.btn_off": "🔴 Turn OFF",
    "apl.btn_list": "📋 Appeal List",
    "apl.dest_group": "👥 Group",
    "apl.dest_log": "📋 Log channel",
    "apl.toast_on": "✅ Appeal ON ho gayi.",
    "apl.toast_off": "Appeal OFF ho gayi.",
    "apl.toast_dest": "Appeal yahan bhi jaayegi: {dest}",
    "apl.admin_only": "Sirf group admins Appeal badal sakte hain.",
    "apl.private": "Kisi group ke liye Appeal set karne ke liye us group mein /help kholo.",
    "apl.usage": "Use kaise karein:\n1. /appeal: Appeal page dikhao.\n2. /appeal on ya /appeal off: Switch karo.\n3. /appeal group ya /appeal log: Extra appeal card kahan jaaye (admins ko bot ke private chat mein woh hamesha milta hai).",
    "apl.list_title": "<b>📋 Appeals ({count})</b>",
    "apl.list_empty": "Abhi tak koi appeal nahi aayi.",
    "apl.list_line": "{n}. {user}: {kind}, {status}",
    "apl.list_tap": "Kholne ke liye neeche pending appeal par tap karo.",
    "apl.st_open": "⏳ Pending",
    "apl.st_approved": "✅ {admin} ne accept kiya",
    "apl.st_rejected": "❌ {admin} ne reject kiya",
    "apl.btn": "📩 Appeal",
    "apl.kind_mute": "mute",
    "apl.kind_warn": "warning",
    "apl.dm_off": "Us group mein Appeal ON nahi hai.",
    "apl.dm_invalid": "Mujhe woh group ab nahi khul raha.",
    "apl.dm_none": "<b>{chat}</b> mein aapka koi active {kind} nahi hai, isliye appeal ki zaroorat nahi.",
    "apl.dm_open": "Iske liye aapki appeal pehle se pending hai. Admins ke faisle ka wait karo.",
    "apl.dm_ask": "<b>{chat}</b> mein aapke {kind} ki appeal.\n\nBataiye ki aapko kyun lagta hai ki ise dobara dekha jaana chahiye (max {max} akshar), ya bina wajah ke appeal karne ke liye /skip bhejo. Rukne ke liye /cancel bhejo.",
    "apl.dm_cancelled": "Cancel ho gaya. Koi appeal nahi bheji.",
    "apl.dm_sent": "✅ Aapki appeal admins ko bhej di gayi hai. Unka faisla aate hi hum aapko yahin bata denge. Aap kabhi bhi /myappeals se status dekh sakte ho.",
    "apl.dm_fail": "Maaf kijiye, main aapki appeal nahi bhej paya. Thodi der baad phir try karo.",
    "apl.card": "📩 <b>Appeal</b> <b>{chat}</b> mein\nMember: {user}\nKis baare mein: {kind}\nWajah: {reason}",
    "apl.no_reason": "<i>kuch nahi likha</i>",
    "apl.btn_unmute": "✅ Unmute",
    "apl.btn_rmwarn": "✅ Remove warning",
    "apl.btn_reject": "❌ Reject",
    "apl.done_approved": "<i>✅ {admin} ne accept kiya.</i>",
    "apl.done_rejected": "<i>❌ {admin} ne reject kiya.</i>",
    "apl.already": "Is appeal ka faisla koi aur admin pehle hi kar chuka hai.",
    "apl.card_admin_only": "Sirf us group ke admins appeal ka faisla kar sakte hain.",
    "apl.undo_failed": "Main yeh nahi kar paya. Mujhe \"Ban users\" right wala admin banao, phir dobara tap karo.",
    "apl.approved_dm_mute": "✅ <b>Khushkhabri!</b> <b>{chat}</b> mein aapki appeal accept ho gayi hai. Aapka mute hat gaya hai, ab aap phir se message bhej sakte ho.",
    "apl.approved_dm_warn": "✅ <b>Khushkhabri!</b> <b>{chat}</b> mein aapki appeal accept ho gayi hai. Aapki warning hata di gayi hai.",
    "apl.rejected_dm": "❌ <b>{chat}</b> mein aapki appeal admins ne reject kar di hai. Agar aapko ab bhi lagta hai ki yeh galti thi, to aap nayi appeal bhej sakte ho.",
    "apl.my_title": "<b>📩 Aapki appeals</b>",
    "apl.my_empty": "Aapne abhi tak koi appeal nahi bheji.",
    "apl.my_line": "{n}. <b>{chat}</b>: {kind}, {status}",
    "apl.my_st_open": "⏳ admins ka wait hai",
    "apl.my_st_approved": "✅ accept hui",
    "apl.my_st_rejected": "❌ reject hui",
}


log = logging.getLogger("lang")
SETTING_KEY = "lang"
DEFAULT = "en"
LANGS = {"en": ("English", EN), "hinglish": ("Hinglish", HINGLISH)}
ALIASES = {"en": "en", "eng": "en", "english": "en", "hinglish": "hinglish", "hing": "hinglish", "hi": "hinglish"}
BACK = "help:more"                                   # the 🌐 Language button lives on /help page 2 (More Features)
_D = None
_allowed = None
_guard = None
_FILL = re.compile(r"\{(\w+)\}")


def _fill(text, values):
    """Replaces {name} with values["name"]; any other brace stays as it is (custom messages contain braces)."""
    if not values:
        return text
    return _FILL.sub(lambda m: str(values[m.group(1)]) if m.group(1) in values else m.group(0), text)


def get_lang(chat_id):
    if _D is None or chat_id is None:
        return DEFAULT
    try:
        code = _D.get_setting(chat_id, SETTING_KEY, DEFAULT) or DEFAULT
    except Exception:
        log.exception("lang: couldn't read the language of %s", chat_id)
        return DEFAULT
    return code if code in LANGS else DEFAULT


def set_lang(chat_id, code):
    if code not in LANGS:
        raise ValueError(code)
    _D.set_setting(chat_id, SETTING_KEY, code)


def t(key, chat_id=None, lang=None, **values):
    """The text for `key` in the group's language (or `lang`). Falls back to English, then to the key itself."""
    code = lang if lang in LANGS else get_lang(chat_id)
    text = LANGS[code][1].get(key)
    if text is None:
        text = EN.get(key, key)
    return _fill(text, values)


def label(code):
    return LANGS[code][0]


# ------------------------------------------------------------------ the page
def page(chat_id):
    """(text, keyboard) of the 🌐 Language page for a group."""
    current = get_lang(chat_id)
    text = t("lang.title", chat_id) + "\n\n" + t("lang.body", chat_id, current=label(current))
    rows = [[InlineKeyboardButton(("✅ " if code == current else "") + name, callback_data=f"lang:s:{code}")
             for code, (name, _) in LANGS.items()],
            [InlineKeyboardButton(t("lang.back", chat_id), callback_data=BACK)]]
    return text, InlineKeyboardMarkup(rows)


async def _edit(q, text, markup):
    try:
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup, disable_web_page_preview=True)
    except TelegramError:
        pass                                          # unchanged (double tap) or too old to edit


async def lang_callback(update, context):
    """"lang:m" opens the page; "lang:s:<code>" sets the language (group admins only, checked on every tap)."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await _guard(q):                              # the /help menu belongs to the person who opened it
        return
    parts = (q.data or "").split(":")
    if chat.type == "private":
        await q.answer(t("lang.private"), show_alert=True)
        return
    if len(parts) == 2 and parts[1] == "m":
        await q.answer()
        await _edit(q, *page(chat.id))
        return
    if len(parts) == 3 and parts[1] == "s" and parts[2] in LANGS:
        if not await _allowed(chat, q.from_user.id):
            await q.answer(t("lang.admin_only", chat.id), show_alert=True)
            return
        try:
            set_lang(chat.id, parts[2])
        except Exception:
            log.exception("lang: saving the language failed in %s", chat.id)
            await q.answer("Database problem. Nothing was changed.", show_alert=True)
            return
        await q.answer(t("lang.saved_alert", chat.id, current=label(parts[2])))
        await _edit(q, *page(chat.id))
        return
    await q.answer("This button is no longer valid.", show_alert=True)


async def lang_cmd(update, context):
    """/lang shows the page; /lang en or /lang hinglish sets it. Group admins only (group_only replies by itself)."""
    if not await _D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    if not context.args:
        text, markup = page(chat.id)
        await msg.reply_html(text, reply_markup=markup)
        return
    code = ALIASES.get(context.args[0].lower())
    if code is None:
        await msg.reply_html(t("lang.unknown", chat.id) + "\n\n" + t("lang.usage", chat.id))
        return
    set_lang(chat.id, code)
    await msg.reply_html(t("lang.saved", chat.id, current=label(code)))


def register(app, deps, allowed, guard):
    """Called once by group.register. Adds /lang and the page's buttons."""
    global _D, _allowed, _guard
    _D, _allowed, _guard = deps, allowed, guard
    app.add_handler(CommandHandler("lang", lang_cmd))
    app.add_handler(CallbackQueryHandler(lang_callback, pattern=r"^lang:"))
