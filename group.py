"""
group.py: all group-management logic in ONE file (merged from autoclose.py, cleaner.py and importexport.py).

  AUTO CLOSE / OPEN   /autoclose 23:00 06:00   /autoclose off   /autoclose
                      (+ the 🕒 Auto Close and ⌨️ Command buttons on /help > Auto Close: hour, minute, AM/PM pickers)
  CLEAN SERVICE       /cleanservice <type>  /keepservice <type>  /nocleanservice <type>  /cleanservicetypes
  CLEAN COMMANDS      /clean <type or /command>  /keep <type or /command>  /cleancommandtypes
                      (the old names /cleancommand and /keepcommand still work; + the ➕ Add Command and ➖ Remove
                      buttons on /help > Clean Commands)
  IMPORT / EXPORT     /export [modules]  /import [modules]  /reset  (+ the Import / Export buttons on /help page 2)
  BROADCAST           📢 button in the Bot Staff panel: send a message to all groups or chosen groups

Sections of this file
  1. Imports, shared state and constants
  2. Auto close / auto open  (schedule, background loop, /autoclose)
  3. Clean service + clean commands
  4. Import / export / reset of a group's settings
  5. Broadcast (Bot Staff panel)
  6. register(app, deps)  <- the single entry point

Wiring in nova.py (replaces the three old register calls and the old module names):

    import group
    group.register(app, SimpleNamespace(
        group_only=..., get_setting=..., set_setting=..., is_paused=..., default_perms=...,
        fun_names=fun_systems._fun_names, is_admin=..., is_bot_owner=...,
        owner_ids=OWNER_IDS, is_super_admin=is_super_admin, groups_source=_stats_refresh))
    # in the Bot Staff keyboard (owner_main_keyboard):  rows.append([group.broadcast_button()])
    # in post_init:
    asyncio.create_task(group.sweeper(app))
    # anywhere you used cleaner.is_service_cleaned(...):
    group.is_service_cleaned(chat_id, "join")

deps needs:
    group_only(update)       async, group + admin check (replies by itself)
    get_setting, set_setting, is_paused(chat_id), default_perms
    fun_names()              async, names of the Fun commands
    is_admin(chat, user_id)  async
    is_bot_owner(user_id)
    owner_ids, is_super_admin(user_id)   who may broadcast (bot owner + bot staff)
    groups_source(bot)       async, [(chat_id, title, link)] of every group the bot is in
"""
import asyncio
import html
import io
import json
import logging
import os
import re
import time
from datetime import datetime, timedelta, timezone

from telegram import ChatPermissions, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.constants import ChatMemberStatus
from telegram.error import BadRequest, ChatMigrated, Forbidden, RetryAfter, TelegramError
from telegram.ext import ApplicationHandlerStop, CallbackQueryHandler, CommandHandler, MessageHandler, filters

import extra
import migrate_to_mongo as store

log = logging.getLogger("group")
D = None            # helpers handed in by nova.py (see register)
_app = None


# ======================================================================================================
# 2. AUTO CLOSE / AUTO OPEN
# ======================================================================================================
# A group is closed every day at a set time (only admins can write) and opened again later.
#   * "Closed" = the group's default member permissions are switched off. Admins/owner/bots with the right are unaffected.
#   * Before closing, the permissions are saved; at opening time exactly those are restored.
#   * A background loop checks every 30 seconds, so a restart never skips an opening/closing time.
#   * The bot needs the "Ban users" (restrict members) admin right.
#   * Nothing happens while a group is paused with /pause.
# Settings per group: autoclose = "HH:MM-HH:MM", autoclose_state = "closed" | "open", autoclose_saved = JSON perms.
# The closed message is PINNED when the group closes and UNPINNED when it opens (autoclose_pin = its message id).
# Custom texts: autoclose_msg_close / autoclose_msg_open (placeholders {open_time} and {close_time}, max 500 characters).
AUTOCLOSE_KEY, STATE_KEY, SAVED_KEY = "autoclose", "autoclose_state", "autoclose_saved"
PIN_KEY, MSG_CLOSE_KEY, MSG_OPEN_KEY = "autoclose_pin", "autoclose_msg_close", "autoclose_msg_open"
MSG_MAX = 500
CHECK_EVERY = 30         # seconds between checks
RETRY_AFTER = 600        # seconds before a failed close/open is tried again
NOTICE_EVERY = 6 * 3600  # at most one "I couldn't do it" notice per group per 6 hours
BOT_TIMEZONE = os.environ.get("BOT_TIMEZONE", "Asia/Kolkata")
_retry_at = {}           # (chat_id, "close"|"open") -> monotonic time of the next try
_notice_at = {}          # chat_id -> monotonic time of the last failure notice

CLOSED_PERMS = ChatPermissions(
    can_send_messages=False, can_send_audios=False, can_send_documents=False, can_send_photos=False,
    can_send_videos=False, can_send_video_notes=False, can_send_voice_notes=False, can_send_polls=False,
    can_send_other_messages=False, can_add_web_page_previews=False, can_invite_users=False,
    can_pin_messages=False, can_change_info=False)


def _tz():
    try:
        from zoneinfo import ZoneInfo
        return ZoneInfo(BOT_TIMEZONE)
    except Exception:
        if BOT_TIMEZONE == "Asia/Kolkata":
            return timezone(timedelta(hours=5, minutes=30), "IST")
        return timezone.utc


# ------------------------------------------------------------------ times
_TIME_RE = re.compile(r"^(\d{1,2})(?::(\d{2}))?\s*(am|pm)?$", re.I)


def parse_time(text):
    """'23:00' | '11pm' | '6:30 am' | '6' -> minutes since midnight, or None."""
    m = _TIME_RE.match((text or "").strip())
    if not m:
        return None
    hour, minute, ampm = int(m.group(1)), int(m.group(2) or 0), (m.group(3) or "").lower()
    if minute > 59:
        return None
    if ampm:
        if not 1 <= hour <= 12:
            return None
        hour = hour % 12 + (12 if ampm == "pm" else 0)
    elif hour > 23:
        return None
    return hour * 60 + minute


def parse_two_times(text):
    """'23:00 06:00' | '11pm 6am' | '11 pm 6 am' | '23:00-06:00' | '11pm to 6am' -> (close, open) in minutes, or (None, None)."""
    text = (text or "").strip().lower()
    parts = [p.strip() for p in re.split(r"\s*-\s*|\s+to\s+", text) if p.strip()]
    if len(parts) != 2:
        tokens = text.split()
        if len(tokens) == 2:
            parts = tokens
        elif len(tokens) == 4 and tokens[1] in ("am", "pm") and tokens[3] in ("am", "pm"):
            parts = [tokens[0] + tokens[1], tokens[2] + tokens[3]]
        else:
            return None, None
    return parse_time(parts[0]), parse_time(parts[1])


def fmt_minutes(mins):
    return f"{mins // 60:02d}:{mins % 60:02d}"


def fmt_12h(mins):
    h, m = divmod(mins, 60)
    return f"{(h % 12) or 12}:{m:02d} {'AM' if h < 12 else 'PM'}"


def load_schedule(raw):
    """'23:00-06:00' -> (1380, 360) or None."""
    try:
        a, _, b = str(raw or "").partition("-")
        close, open_ = parse_time(a), parse_time(b)
    except Exception:
        return None
    return (close, open_) if close is not None and open_ is not None and close != open_ else None


def is_closed_at(now_minutes, close, open_):
    """True when the clock time lies in the closed window. The window may run past midnight (23:00-06:00)."""
    if close < open_:
        return close <= now_minutes < open_
    return now_minutes >= close or now_minutes < open_


def _now_minutes():
    now = datetime.now(_tz())
    return now.hour * 60 + now.minute


# ------------------------------------------------------------------ closing and opening
def _saved_perms(chat):
    perms = getattr(chat, "permissions", None)
    return json.dumps(perms.to_dict()) if perms is not None else ""


def _restore_perms(chat_id):
    raw = D.get_setting(chat_id, SAVED_KEY, "") or ""
    try:
        perms = ChatPermissions(**json.loads(raw)) if raw else None
    except (TypeError, ValueError):
        perms = None
    if perms is None or perms.can_send_messages is False:   # nothing saved, or it was already closed: use defaults
        return D.default_perms
    return perms


async def _fail(bot, chat_id, what, exc):
    _retry_at[(chat_id, what)] = time.monotonic() + RETRY_AFTER
    log.warning("autoclose: couldn't %s %s: %s: %s", what, chat_id, type(exc).__name__, exc)
    last = _notice_at.get(chat_id)
    if last is not None and time.monotonic() - last < NOTICE_EVERY:
        return
    _notice_at[chat_id] = time.monotonic()
    try:
        await bot.send_message(chat_id, f"⚠️ I couldn't {what} the group on schedule. Please make me an admin with the "
                                        "'Ban users' (restrict members) right. I will try again in a few minutes.")
    except TelegramError:
        pass


# ------------------------------------------------------------------ the messages (default or custom)
def default_close_msg(has_open_time):
    text = "🔒 <b>Group Closed</b>\nIt's time for a break! Only admins can send messages right now."
    return text + ("\n🕒 We'll be back at <b>{open_time}</b>. Good night! 🌙" if has_open_time else "")


def default_open_msg(has_close_time):
    text = "🔓 <b>Group Open</b>\nGood morning! The chat is open again, and everyone can send messages. ☀️"
    return text + ("\n🕒 Next close time: <b>{close_time}</b>" if has_close_time else "")


def render_msg(template, open_time, close_time):
    """Fills {open_time} and {close_time}. Plain str.replace, so other braces in a custom text are harmless."""
    return (template.replace("{open_time}", open_time or "later").replace("{close_time}", close_time or "later"))


def build_msg(chat_id, kind, close=None, open_=None):
    """The HTML text to post: the group's custom message when it has one, otherwise the default. `kind` is
    'close' or 'open'; `close` / `open_` are minutes since midnight (or None)."""
    custom = (D.get_setting(chat_id, MSG_CLOSE_KEY if kind == "close" else MSG_OPEN_KEY, "") or "").strip()
    ot = fmt_12h(open_) if open_ is not None else ""
    ct = fmt_12h(close) if close is not None else ""
    if custom:
        template = html.escape(custom[:MSG_MAX])               # a custom text is plain text: never HTML from a user
    elif kind == "close":
        template = default_close_msg(open_ is not None)
    else:
        template = default_open_msg(close is not None)
    return render_msg(template, ot, ct)


async def close_group(bot, chat_id, until_minutes=None):
    """Saves the permissions, switches them off, posts the closed message and PINS it. Returns True when it worked."""
    try:
        chat = await bot.get_chat(chat_id)
        current = _saved_perms(chat)
        if getattr(getattr(chat, "permissions", None), "can_send_messages", True) is not False and current:
            D.set_setting(chat_id, SAVED_KEY, current)             # only save a real "open" state, never a closed one
        await bot.set_chat_permissions(chat_id, CLOSED_PERMS)
    except TelegramError as e:
        await _fail(bot, chat_id, "close", e)
        return False
    D.set_setting(chat_id, STATE_KEY, "closed")
    sched = load_schedule(D.get_setting(chat_id, AUTOCLOSE_KEY, "") or "")
    try:
        sent = await bot.send_message(chat_id, build_msg(chat_id, "close", sched[0] if sched else None, until_minutes),
                                      parse_mode="HTML")
    except TelegramError:
        return True
    try:                                                           # quietly: no notification for the whole group
        await bot.pin_chat_message(chat_id, sent.message_id, disable_notification=True)
        D.set_setting(chat_id, PIN_KEY, str(sent.message_id))
    except TelegramError as e:                                     # no "Pin messages" right: the group is still closed
        log.debug("autoclose: couldn't pin the closed message in %s: %s", chat_id, e)
    return True


async def _unpin_closed_message(bot, chat_id):
    """Unpins the closed message this bot pinned (never any other pinned message)."""
    raw = D.get_setting(chat_id, PIN_KEY, "") or ""
    if not str(raw).isdigit():
        return
    try:
        await bot.unpin_chat_message(chat_id, message_id=int(raw))
    except TelegramError as e:                                     # already unpinned or deleted, or no right
        log.debug("autoclose: couldn't unpin the closed message in %s: %s", chat_id, e)
    store.del_setting(chat_id, PIN_KEY)


async def open_group(bot, chat_id):
    try:
        await bot.set_chat_permissions(chat_id, _restore_perms(chat_id))
    except TelegramError as e:
        await _fail(bot, chat_id, "open", e)
        return False
    D.set_setting(chat_id, STATE_KEY, "open")
    await _unpin_closed_message(bot, chat_id)
    sched = load_schedule(D.get_setting(chat_id, AUTOCLOSE_KEY, "") or "")
    try:
        await bot.send_message(chat_id, build_msg(chat_id, "open", sched[0] if sched else None,
                                                  sched[1] if sched else None), parse_mode="HTML")
    except TelegramError:
        pass
    return True


# ------------------------------------------------------------------ the background loop
def _scheduled_groups():
    """[(chat_id, 'HH:MM-HH:MM')] for every group that has a schedule (one query, no per-group lookups)."""
    rows = store.col("settings").find({"key": AUTOCLOSE_KEY}, {"chat_id": 1, "value": 1})
    return [(int(r["chat_id"]), r.get("value")) for r in rows]


async def run_once(bot):
    now = _now_minutes()
    for chat_id, raw in await asyncio.to_thread(_scheduled_groups):
        sched = load_schedule(raw)
        if not sched or chat_id >= 0 or D.is_paused(chat_id):
            continue
        close, open_ = sched
        want_closed = is_closed_at(now, close, open_)
        is_closed = D.get_setting(chat_id, STATE_KEY, "open") == "closed"
        if want_closed and not is_closed:
            if time.monotonic() >= _retry_at.get((chat_id, "close"), 0):
                await close_group(bot, chat_id, open_)
        elif not want_closed and is_closed:
            if time.monotonic() >= _retry_at.get((chat_id, "open"), 0):
                await open_group(bot, chat_id)


async def sweeper(app):
    """Started once in post_init. Never raises: one bad group or a database hiccup only skips that round."""
    await asyncio.sleep(10)
    while True:
        try:
            await run_once(app.bot)
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("autoclose: round failed")
        await asyncio.sleep(CHECK_EVERY)


# ------------------------------------------------------------------ the command
AUTOCLOSE_USAGE = ("Usage:\n"
                   "1. /autoclose 23:00 06:00: close every day at 11 PM and open at 6 AM (24-hour or 11pm style)\n"
                   "2. /autoclose off: stop the schedule\n"
                   "3. /autoclose: show the schedule\n"
                   "4. /autoclose closemsg <text> and /autoclose openmsg <text>: your own messages "
                   "({open_time} and {close_time} are filled in)")
SAMPLE_CLOSE, SAMPLE_OPEN = 23 * 60, 6 * 60          # 11:00 PM and 6:00 AM, used in message previews


async def turn_off(bot, chat_id):
    """Stops the schedule and opens the group again if it is closed. Shared by /autoclose off and the OFF button.
    Returns (ok, was_closed); ok is False when the group was closed and could not be opened."""
    was_closed = D.get_setting(chat_id, STATE_KEY, "open") == "closed"
    store.del_setting(chat_id, AUTOCLOSE_KEY)
    if was_closed and not await open_group(bot, chat_id):
        return False, was_closed
    store.del_setting(chat_id, STATE_KEY)
    store.del_setting(chat_id, SAVED_KEY)
    return True, was_closed


async def autoclose_cmd(update, context):
    if not await D.group_only(update):                 # group only + admins only
        return
    chat, msg = update.effective_chat, update.effective_message
    args = [a.lower() for a in context.args]
    raw = D.get_setting(chat.id, AUTOCLOSE_KEY, "") or ""
    sched = load_schedule(raw)
    if not args:
        if not sched:
            await msg.reply_text("Auto close is OFF.\n\n" + AUTOCLOSE_USAGE)
            return
        state = "closed" if D.get_setting(chat.id, STATE_KEY, "open") == "closed" else "open"
        await msg.reply_text(f"🕒 Auto close is ON ({BOT_TIMEZONE}).\n"
                             f"Closes at {fmt_12h(sched[0])} and opens at {fmt_12h(sched[1])}, every day.\n"
                             f"The group is {state} right now.\n\nTurn it off with /autoclose off.")
        return
    if args[0] in ("closemsg", "openmsg"):             # /autoclose closemsg <text> | reset
        kind = "close" if args[0] == "closemsg" else "open"
        pieces = (msg.text or "").split(None, 2)        # keep the text exactly as typed (case, new lines)
        text = pieces[2].strip() if len(pieces) > 2 else ""
        if not text:
            await msg.reply_text(f"Usage: /autoclose {args[0]} <your text>\n"
                                 f"Placeholders: {{open_time}} and {{close_time}}. Up to {MSG_MAX} characters.\n"
                                 f"/autoclose {args[0]} reset: go back to the default message.")
            return
        if text.lower() in ("reset", "default"):
            store.del_setting(chat.id, MSG_CLOSE_KEY if kind == "close" else MSG_OPEN_KEY)
            await msg.reply_text(f"✅ The {kind} message is back to the default.")
            return
        if len(text) > MSG_MAX:
            await msg.reply_text(f"❌ That is {len(text)} characters. The most I can use is {MSG_MAX}.")
            return
        D.set_setting(chat.id, MSG_CLOSE_KEY if kind == "close" else MSG_OPEN_KEY, text)
        await msg.reply_html("✅ Saved. Preview:\n\n" + build_msg(chat.id, kind, SAMPLE_CLOSE, SAMPLE_OPEN))
        return
    if args[0] in ("off", "no", "stop", "disable", "0"):
        ok, was_closed = await turn_off(context.bot, chat.id)
        if not ok:
            await msg.reply_text("Auto close is OFF, but I couldn't open the group. Please make me an admin with the "
                                 "'Ban users' right, or change the group permissions yourself.")
            return
        await msg.reply_text("✅ Auto close is OFF." + (" The group is open again." if was_closed else ""))
        return
    close, open_ = parse_two_times(" ".join(args))
    if close is None or open_ is None:
        await msg.reply_text("I couldn't read those times.\n\n" + AUTOCLOSE_USAGE)
        return
    if close == open_:
        await msg.reply_text("The closing and opening time must be different.\n\n" + AUTOCLOSE_USAGE)
        return
    D.set_setting(chat.id, AUTOCLOSE_KEY, f"{fmt_minutes(close)}-{fmt_minutes(open_)}")
    await msg.reply_text(f"✅ Auto close is ON ({BOT_TIMEZONE}).\n"
                         f"Every day I close the group at {fmt_12h(close)} (only admins can write) and open it at "
                         f"{fmt_12h(open_)}.\nGive me the 'Ban users' admin right so I can do it.")
    await run_once(context.bot)                      # apply it right away if the group is inside the closed window now


# ------------------------------------------------------------------ the /help > Auto Close page (buttons)
# nova.py builds /help > Auto Close with only "Usage Guide" and "Back". The handler below runs BEFORE nova's own help
# handler (handler group -20, then ApplicationHandlerStop), so nothing in nova.py has to change. The page gets one row
# with two ways to set up auto close; both work on the same settings as /autoclose:
#   🕒 Auto Close  choose the times with buttons: hour, then minute, then AM/PM (12-hour clock), first for closing,
#                  then for opening. Also shows the status and a Turn OFF button.
#   ⌨️ Command     explains the /autoclose command with examples.
# Button data: "acb:<step>:<args>". Everything the next screen needs travels inside the button, so no state is kept.
#   a            the Auto Close panel            c            the Command page             off          turn it OFF
#   H:<w>:<c>    hour screen                     M:<w>:<c>:<h>             minute screen
#   A:<w>:<c>:<h>:<m>  AM/PM screen              S:<w>:<c>:<h>:<m>:<A|P>   time chosen
#   <w> = "c" (closing time) or "o" (opening time); <c> = the closing time in minutes while choosing the opening time.
# On the minute screen the admin may also TYPE the minute (0 to 59) in the chat instead of tapping a button. The only
# thing kept in memory is who is on that screen: (chat id, user id) -> {which, carry, hour, message id, time}.
AC_HOME = "help:autoclose"
AC_MINUTES = (0, 15, 30, 45)     # the quick-pick buttons; any minute from 0 to 59 is accepted when typed
AC_TYPE_TTL = 300                # seconds a typed minute is still accepted after the minute screen was shown
_ac_pending = {}


def _tz_label():
    return "India time (IST)" if BOT_TIMEZONE == "Asia/Kolkata" else html.escape(BOT_TIMEZONE)


def _ac_status(chat):
    if chat is None or chat.type == "private":
        return "Open /help inside a group to set up auto close for that group."
    sched = load_schedule(D.get_setting(chat.id, AUTOCLOSE_KEY, "") or "")
    if not sched:
        return "Status: <b>OFF ❌</b>"
    state = "closed 🔒" if D.get_setting(chat.id, STATE_KEY, "open") == "closed" else "open 🔓"
    return (f"Status: <b>ON ✅</b> ({html.escape(BOT_TIMEZONE)})\n"
            f"Closes at <b>{fmt_12h(sched[0])}</b> and opens at <b>{fmt_12h(sched[1])}</b>, every day.\n"
            f"The group is {state} right now.")


def _ac_home(chat):
    text = ("<b>🕒 Auto Close</b>\n\n"
            "Close the group automatically at a set time every day and open it again later. While the group is "
            "closed, only admins can write messages.\n\n"
            "Choose how you want to set it up:\n"
            "• <b>🕒 Auto Close</b>: pick the times with buttons\n"
            "• <b>⌨️ Command</b>: set it by typing a command\n\n"
            f"{_ac_status(chat)}\n\n"
            "<b>Note:</b> The bot must be an admin with the \"Ban users\" right. Opening the group brings back the "
            "exact permissions it had before closing.")
    rows = [[InlineKeyboardButton("🕒 Auto Close", callback_data="acb:a"),
             InlineKeyboardButton("⌨️ Command", callback_data="acb:c")],
            [InlineKeyboardButton("📖 Usage Guide", callback_data="help:g_autoclose")],
            [InlineKeyboardButton("« Back", callback_data="help:main")]]
    return text, InlineKeyboardMarkup(rows)


def _ac_panel(chat, note=""):
    sched = load_schedule(D.get_setting(chat.id, AUTOCLOSE_KEY, "") or "")
    text = ("<b>🕒 Auto Close</b>\n\n" + (f"{note}\n\n" if note else "") + f"{_ac_status(chat)}\n\n"
            "Tap <b>Set Time</b> to choose when the group closes and when it opens.")
    rows = [[InlineKeyboardButton("⏰ Set Time", callback_data="acb:H:c:-"),
             InlineKeyboardButton("✏️ Custom Message", callback_data="acb:m")]]
    if sched:
        rows.append([InlineKeyboardButton("🔴 Turn OFF", callback_data="acb:off")])
    rows.append([InlineKeyboardButton("« Back", callback_data=AC_HOME)])
    return text, InlineKeyboardMarkup(rows)


def _ac_command_page():
    text = ("<b>⌨️ Auto Close: Command</b>\n\n"
            "Prefer typing? Use these commands in the group (admins only):\n\n"
            "1. /autoclose 11pm 6am: Close every day at 11:00 PM and open at 6:00 AM.\n"
            "2. /autoclose 11:30pm 6:15am: The same, with minutes: closes at 11:30 PM and opens at 6:15 AM.\n"
            "3. /autoclose off: Stop the schedule. A closed group is opened again.\n"
            "4. /autoclose: Show the schedule and whether the group is closed right now.\n"
            "5. /autoclose closemsg text: Set your own message for when the group closes.\n"
            "6. /autoclose openmsg text: Set your own message for when the group opens.\n\n"
            f"<b>Note:</b> The bot must be an admin with the \"Ban users\" right. Times use {_tz_label()}.")
    return text, InlineKeyboardMarkup([[InlineKeyboardButton("« Back", callback_data=AC_HOME)]])


def _ac_head(which, carry):
    head = f"<b>🕒 Auto Close: {'Close' if which == 'c' else 'Open'} time</b>"
    if which == "o":
        head += f"\nThe group closes at <b>{fmt_12h(int(carry))}</b>."
    return head


def _ac_hour(which, carry):
    text = _ac_head(which, carry) + "\n\n<b>Step 1 of 3:</b> pick the hour."
    rows = [[InlineKeyboardButton(str(h), callback_data=f"acb:M:{which}:{carry}:{h}") for h in range(first, first + 4)]
            for first in (1, 5, 9)]
    rows.append([InlineKeyboardButton("« Back", callback_data="acb:a" if which == "c" else "acb:H:c:-")])
    return text, InlineKeyboardMarkup(rows)


def _ac_minute(which, carry, hour):
    text = (_ac_head(which, carry) + f"\nHour: <b>{hour}</b>\n\n<b>Step 2 of 3:</b> pick the minute, or send a "
            "number from 0 to 59 in this chat (for example <code>7</code> or <code>45</code>).")
    rows = [[InlineKeyboardButton(f"{m:02d}", callback_data=f"acb:A:{which}:{carry}:{hour}:{m}") for m in AC_MINUTES],
            [InlineKeyboardButton("« Back", callback_data=f"acb:H:{which}:{carry}")]]
    return text, InlineKeyboardMarkup(rows)


def _ac_ampm(which, carry, hour, minute):
    text = _ac_head(which, carry) + f"\nTime: <b>{hour}:{minute:02d}</b>\n\n<b>Step 3 of 3:</b> pick AM or PM."
    rows = [[InlineKeyboardButton("☀️ AM", callback_data=f"acb:S:{which}:{carry}:{hour}:{minute}:A"),
             InlineKeyboardButton("🌙 PM", callback_data=f"acb:S:{which}:{carry}:{hour}:{minute}:P")],
            [InlineKeyboardButton("« Back", callback_data=f"acb:M:{which}:{carry}:{hour}")]]
    return text, InlineKeyboardMarkup(rows)


_ac_msg_pending = {}         # (chat id, user id) -> {"kind": "close"|"open", "mid": panel message id, "ts", "warned"}
_AC_KIND = {"c": "close", "o": "open"}


def _ac_msg_menu(chat):
    custom_c = bool((D.get_setting(chat.id, MSG_CLOSE_KEY, "") or "").strip())
    custom_o = bool((D.get_setting(chat.id, MSG_OPEN_KEY, "") or "").strip())
    text = ("<b>✏️ Custom Message</b>\n\n"
            "Write your own message for when the group closes and when it opens.\n"
            f"🔒 Close message: <b>{'custom' if custom_c else 'default'}</b>\n"
            f"🔓 Open message: <b>{'custom' if custom_o else 'default'}</b>\n\n"
            "The closed message is pinned while the group is closed, and unpinned when it opens.")
    rows = [[InlineKeyboardButton("🔒 Close message", callback_data="acb:e:c"),
             InlineKeyboardButton("🔓 Open message", callback_data="acb:e:o")],
            [InlineKeyboardButton("« Back", callback_data="acb:a")]]
    return text, InlineKeyboardMarkup(rows)


def _ac_msg_edit_screen(chat, which, note=""):
    kind = _AC_KIND[which]
    sample = build_msg(chat.id, kind, SAMPLE_CLOSE, SAMPLE_OPEN)
    custom = bool((D.get_setting(chat.id, MSG_CLOSE_KEY if kind == "close" else MSG_OPEN_KEY, "") or "").strip())
    text = (f"<b>{'🔒 Close' if kind == 'close' else '🔓 Open'} message</b>\n\n" + (f"{note}\n\n" if note else "") +
            f"Now using the <b>{'custom' if custom else 'default'}</b> message. Preview (with the times 11:00 PM and "
            f"6:00 AM):\n\n{sample}\n\n"
            "<b>Send your new text in this chat.</b> You can write <code>{open_time}</code> and "
            f"<code>{{close_time}}</code>, and the bot fills in the times. Up to {MSG_MAX} characters, plain text "
            "and emoji.\nI'll wait 5 minutes.")
    rows = []
    if custom:
        rows.append([InlineKeyboardButton("♻️ Reset to default", callback_data=f"acb:rs:{which}")])
    rows.append([InlineKeyboardButton("« Back", callback_data="acb:m")])
    return text, InlineKeyboardMarkup(rows)


async def ac_custom_message(update, context):
    """group=105: an admin on a Custom Message screen sends the new text. It is saved and previewed; text that is too
    long or empty gets one hint and the bot keeps waiting."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg is None or chat is None or user is None or not msg.text:
        return
    pending = _ac_msg_pending.get((chat.id, user.id))
    if pending is None:
        return
    if time.monotonic() - pending["ts"] > AC_TYPE_TTL:
        _ac_msg_pending.pop((chat.id, user.id), None)
        return
    text = msg.text.strip()
    if not text or len(text) > MSG_MAX:
        if not pending["warned"]:
            pending["warned"] = True
            try:
                await msg.reply_text(f"That is {len(text)} characters. Send between 1 and {MSG_MAX}, or tap Back.")
            except TelegramError:
                pass
        return
    _ac_msg_pending.pop((chat.id, user.id), None)
    which = "c" if pending["kind"] == "close" else "o"
    try:
        D.set_setting(chat.id, MSG_CLOSE_KEY if which == "c" else MSG_OPEN_KEY, text)
    except Exception:
        log.exception("autoclose: saving the custom message failed in %s", chat.id)
        try:
            await msg.reply_text("The database had a problem. Nothing was changed.")
        except TelegramError:
            pass
        return
    page, markup = _ac_msg_edit_screen(chat, which, "✅ Saved.")
    try:
        await context.bot.edit_message_text(page, chat_id=chat.id, message_id=pending["mid"], parse_mode="HTML",
                                            reply_markup=markup, disable_web_page_preview=True)
    except TelegramError as e:
        log.warning("autoclose: couldn't update the panel in %s: %s", chat.id, e)


def _ac_num(text, low, high):
    """int(text) when it is a whole number from low to high, else None."""
    return int(text) if text.isascii() and text.isdigit() and low <= int(text) <= high else None


async def _ac_edit(q, text, markup):
    try:
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup, disable_web_page_preview=True)
    except TelegramError:
        pass                                          # unchanged (double tap) or too old to edit


async def _ac_allowed(chat, user_id):
    """Group admins, the bot owner (power ON) and bot staff."""
    if D.is_bot_owner(user_id):
        return True
    try:
        if await asyncio.to_thread(D.is_super_admin, user_id):
            return True
    except Exception:
        log.exception("autoclose: staff check failed")
    return await D.is_admin(chat, user_id)


async def help_autoclose_callback(update, context):
    """group=-20: /help > Auto Close. Replaces nova's plain page and stops nova's handler from answering too."""
    q = update.callback_query
    if q is None:
        return
    if await extra.menu_not_owner(q):                  # help buttons belong to the person who opened /help
        raise ApplicationHandlerStop
    await q.answer()
    await _ac_edit(q, *_ac_home(q.message.chat if q.message else None))
    raise ApplicationHandlerStop


async def ac_minute_message(update, context):
    """group=103: an admin who is on the minute screen sends the minute as a message. A number from 0 to 59 moves the
    panel on to the AM/PM screen; anything else is ordinary chat and is left alone."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg is None or chat is None or user is None or not msg.text:
        return
    pending = _ac_pending.get((chat.id, user.id))
    if pending is None:
        return
    if time.monotonic() - pending["ts"] > AC_TYPE_TTL:
        _ac_pending.pop((chat.id, user.id), None)
        return
    minute = _ac_num(msg.text.strip(), 0, 59)
    if minute is None:
        return
    _ac_pending.pop((chat.id, user.id), None)
    text, markup = _ac_ampm(pending["which"], pending["carry"], pending["hour"], minute)
    try:
        await context.bot.edit_message_text(text, chat_id=chat.id, message_id=pending["mid"], parse_mode="HTML",
                                            reply_markup=markup, disable_web_page_preview=True)
    except TelegramError as e:
        log.warning("autoclose: couldn't show the AM/PM screen in %s: %s", chat.id, e)


async def acb_callback(update, context):
    """The buttons on the Auto Close page. Changing anything needs a group admin (checked on every tap)."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    parts = (q.data or "").split(":")
    act = parts[1] if len(parts) > 1 else ""
    invalid = "This button is no longer valid."
    if act == "c":                                     # the Command page is only information: anyone may read it
        await q.answer()
        await _ac_edit(q, *_ac_command_page())
        return
    if chat.type == "private":
        await q.answer("Open /help inside a group to set up auto close for that group.", show_alert=True)
        return
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer("Only group admins can change auto close.", show_alert=True)
        return
    _ac_pending.pop((chat.id, q.from_user.id), None)   # any tap leaves the "type the minute" state; M sets it again
    _ac_msg_pending.pop((chat.id, q.from_user.id), None)   # ... and the "type the message" state; e sets it again

    if act == "a":
        await q.answer()
        await _ac_edit(q, *_ac_panel(chat))
        return
    if act == "m" and len(parts) == 2:                 # ✏️ Custom Message menu
        await q.answer()
        await _ac_edit(q, *_ac_msg_menu(chat))
        return
    if act in ("e", "rs") and len(parts) == 3 and parts[2] in _AC_KIND:
        which = parts[2]
        if act == "rs":                                # ♻️ back to the default message
            try:
                store.del_setting(chat.id, MSG_CLOSE_KEY if which == "c" else MSG_OPEN_KEY)
            except Exception:
                log.exception("autoclose: resetting the message failed in %s", chat.id)
                await q.answer("The database had a problem. Nothing was changed.", show_alert=True)
                return
            await q.answer("✅ Back to the default message.")
            await _ac_edit(q, *_ac_msg_edit_screen(chat, which, "♻️ Reset to the default message."))
            return
        await q.answer()
        now = time.monotonic()
        for k in [k for k, v in _ac_msg_pending.items() if now - v["ts"] > AC_TYPE_TTL]:
            _ac_msg_pending.pop(k, None)               # forget people who walked away
        _ac_msg_pending[(chat.id, q.from_user.id)] = {"kind": _AC_KIND[which], "mid": q.message.message_id,
                                                      "ts": now, "warned": False}
        await _ac_edit(q, *_ac_msg_edit_screen(chat, which))
        return
    if act == "off":
        try:
            ok, was_closed = await turn_off(context.bot, chat.id)
        except Exception:
            log.exception("autoclose: turning off failed in %s", chat.id)
            await q.answer("The database had a problem. Nothing was changed.", show_alert=True)
            return
        if not ok:
            await q.answer("Auto close is OFF, but I couldn't open the group. Please make me an admin with the "
                           "'Ban users' right.", show_alert=True)
        else:
            await q.answer("Auto close is OFF." + (" The group is open again." if was_closed else ""))
        await _ac_edit(q, *_ac_panel(chat))
        return

    which = parts[2] if len(parts) > 2 else ""
    carry = parts[3] if len(parts) > 3 else ""
    carry_mins = _ac_num(carry, 0, 1439) if which == "o" else None
    if which not in ("c", "o") or (which == "o" and carry_mins is None) or (which == "c" and carry != "-"):
        await q.answer(invalid, show_alert=True)
        return
    hour = _ac_num(parts[4], 1, 12) if len(parts) > 4 else None
    minute = _ac_num(parts[5], 0, 59) if len(parts) > 5 else None

    if act == "H" and len(parts) == 4:
        await q.answer()
        await _ac_edit(q, *_ac_hour(which, carry))
    elif act == "M" and len(parts) == 5 and hour:
        await q.answer()
        now = time.monotonic()
        for key in [k for k, v in _ac_pending.items() if now - v["ts"] > AC_TYPE_TTL]:
            _ac_pending.pop(key, None)                 # forget people who walked away
        _ac_pending[(chat.id, q.from_user.id)] = {"which": which, "carry": carry, "hour": hour,
                                                  "mid": q.message.message_id, "ts": now}
        await _ac_edit(q, *_ac_minute(which, carry, hour))
    elif act == "A" and len(parts) == 6 and hour and minute is not None:
        await q.answer()
        await _ac_edit(q, *_ac_ampm(which, carry, hour, minute))
    elif act == "S" and len(parts) == 7 and hour and minute is not None and parts[6] in ("A", "P"):
        mins = (hour % 12 + (12 if parts[6] == "P" else 0)) * 60 + minute
        if which == "c":                               # closing time chosen: now ask for the opening time
            await q.answer(f"Closes at {fmt_12h(mins)}")
            await _ac_edit(q, *_ac_hour("o", str(mins)))
            return
        if mins == carry_mins:
            await q.answer("The opening time must be different from the closing time.", show_alert=True)
            return
        try:
            D.set_setting(chat.id, AUTOCLOSE_KEY, f"{fmt_minutes(carry_mins)}-{fmt_minutes(mins)}")
        except Exception:
            log.exception("autoclose: saving the schedule failed in %s", chat.id)
            await q.answer("The database had a problem. Nothing was changed.", show_alert=True)
            return
        await q.answer("✅ Auto close is ON.")
        note = (f"✅ Saved. Every day I close the group at <b>{fmt_12h(carry_mins)}</b> and open it at "
                f"<b>{fmt_12h(mins)}</b>.\nGive me the \"Ban users\" admin right so I can do it.")
        await _ac_edit(q, *_ac_panel(chat, note))
        try:
            await run_once(context.bot)                # apply it right away if the group is inside the closed window now
        except Exception:
            log.exception("autoclose: applying the new schedule failed")
    else:
        await q.answer(invalid, show_alert=True)


# ======================================================================================================
# 3. CLEAN SERVICE + CLEAN COMMANDS
# ======================================================================================================
# Keeps a group tidy by deleting Telegram service messages and bot commands. Only admins change the settings.
#   * Commands are deleted AFTER the bot has answered them (late handler group), so the bot can still reply.
#   * Service messages are deleted after the other handlers (welcome, captcha, antiraid ...) have seen them.
#   * Nothing is deleted while a group is paused (/pause) or in private chats.
#   * The bot needs the "Delete messages" admin right.
_registered_cache = None

SERVICE_KEY = "clean_service"
COMMAND_KEY = "clean_command"

SERVICE_TYPES = ("join", "leave", "other", "photo", "pin", "title", "videochat")
COMMAND_TYPES = ("admin", "user", "other")
YES_WORDS = {"yes", "on", "true", "enable", "enabled", "1"}
NO_WORDS = {"no", "off", "false", "disable", "disabled", "0"}

# Telegram message attributes that make a message a service message of each type. Read with getattr(), so an
# attribute that this python-telegram-bot version doesn't know is simply skipped.
SERVICE_ATTRS = {
    "join": ("new_chat_members",),
    "leave": ("left_chat_member",),
    "photo": ("new_chat_photo", "delete_chat_photo", "chat_background_set"),
    "pin": ("pinned_message",),
    "title": ("new_chat_title", "forum_topic_edited"),
    "videochat": ("video_chat_started", "video_chat_ended", "video_chat_scheduled",
                  "video_chat_participants_invited"),
    "other": ("boost_added", "successful_payment", "refunded_payment", "proximity_alert_triggered", "web_app_data",
              "message_auto_delete_timer_changed", "checklist_tasks_done", "checklist_tasks_added",
              "forum_topic_created", "forum_topic_closed", "forum_topic_reopened", "general_forum_topic_hidden",
              "general_forum_topic_unhidden", "group_chat_created", "supergroup_chat_created", "channel_chat_created",
              "write_access_allowed", "users_shared", "chat_shared", "giveaway_created", "giveaway_completed",
              "paid_message_price_changed", "direct_message_price_changed"),
}
# Never touched on purpose: migrate_to_chat_id / migrate_from_chat_id (the bot needs them to follow a group that
# turns into a supergroup).

SERVICE_INFO = (
    ("all", "All service messages."),
    ("join", "When a new user joins, or is added. eg: 'X joined the chat'"),
    ("leave", "When a user leaves, or is removed. eg: 'X left the chat'"),
    ("other", "Miscellaneous items; such as chat boosts, successful telegram payments, proximity alerts, webapp "
              "messages, message auto deletion changes, or checklist updates."),
    ("photo", "When chat photos or chat backgrounds are changed."),
    ("pin", "When a new message is pinned. eg: 'X pinned a message'"),
    ("title", "When chat or topic titles are changed."),
    ("videochat", "When a video chat action occurs - eg starting, ending, scheduling, or adding members to the call."),
)
COMMAND_INFO = (
    ("all", "Delete ALL commands sent to the group."),
    ("admin", "Delete any admin-only commands sent to the group (eg /ban, /mute, or any settings changes)."),
    ("user", "Delete any user commands sent to the group (eg /id, /info, or /get). These commands will also be "
             "cleaned when admins use them."),
    ("other", "Delete any commands which aren't recognised as being valid commands of this bot (or that are meant "
              "for other bots)."),
)

# Commands that members may use. Every OTHER command this bot has registered counts as an admin command; a name the
# bot doesn't know (or a command written for another bot, /cmd@otherbot) counts as "other". The Fun commands made
# in the Fun menu (/hug, /slap ...) are read from the database and count as user commands too.
USER_COMMANDS = frozenset({
    "start", "help", "id", "info", "runs", "donate", "limits", "markdownhelp", "warns", "report", "approval",
    "approved", "get", "notes", "saved", "rules", "filters", "locks", "locktypes", "disableable", "disabled",
    "ask", "imagine", "search", "translate", "joke", "quote", "fact", "roll", "flip", "say", "ai",
    "download", "dl", "da", "rank", "top", "overall", "count", "today", "week", "me",
    "fun", "wish", "birthday",
    "roast", "roastme", "cook", "burn", "finisher", "comeback", "roastbattle", "roastvote", "roastscore",
    "roaststats", "roastking",
    "court", "trial", "guilty", "innocent", "verdict", "crime", "evidence", "alibi", "sentence", "bail", "appeal",
    "execute", "wanted",
    "cleanservicetypes", "cleancommandtypes",
})
_CMD_RE = re.compile(r"^/([A-Za-z0-9_]{1,64})(?:@([A-Za-z0-9_]{1,64}))?")


# ------------------------------------------------------------------ stored settings
def _load(chat_id, key, valid):
    raw = D.get_setting(chat_id, key, "") or ""
    return {t for t in str(raw).replace(" ", "").lower().split(",") if t in valid}


def _save(chat_id, key, chosen, order):
    D.set_setting(chat_id, key, ",".join(t for t in order if t in chosen))


def is_service_cleaned(chat_id, category):
    """True when this group deletes that kind of service message (nova uses it so the welcome message is not sent
    as a reply to an 'X joined' message that is about to be deleted)."""
    try:
        return D is not None and category in _load(chat_id, SERVICE_KEY, SERVICE_TYPES)
    except Exception:
        return False


def _describe(chosen, order):
    if not chosen:
        return "nothing"
    if set(order) <= set(chosen):
        return "all"
    return ", ".join(t for t in order if t in chosen)


def _words(args):
    """['join,leave', 'Pin'] -> ['join', 'leave', 'pin']"""
    return [w for a in args for w in re.split(r"[,\s]+", a.lower()) if w]


def _esc(text):
    return str(text).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def what_cmd(what):
    return "service" if what.startswith("service") else "command"


# ------------------------------------------------------------------ shared command logic
async def _set_cmd(update, context, key, valid, order, what, types_cmd):
    """/cleanservice and /cleancommand: add types (or all / yes / no)."""
    if not await D.group_only(update):          # group only + admin only, with its own reply
        return
    chat, msg = update.effective_chat, update.effective_message
    chosen = _load(chat.id, key, valid)
    words = _words(context.args)
    if not words:
        await msg.reply_html(
            f"Currently deleting <b>{_describe(chosen, order)}</b> {what}.\n\n"
            f"Usage: <code>/clean{what_cmd(what)} &lt;type&gt;</code>. See /{types_cmd} for the types, "
            f"<code>/keep{what_cmd(what)} &lt;type&gt;</code> to stop deleting a type.")
        return
    if words[0] in YES_WORDS:
        new = set(order)
    elif words[0] in NO_WORDS:
        new = set()
    else:
        bad = [w for w in words if w != "all" and w not in valid]
        if bad:
            await msg.reply_html(f"Unknown type: <code>{_esc(', '.join(bad))}</code>\n"
                                 f"Available: all, {', '.join(order)}. See /{types_cmd}.")
            return
        new = chosen | (set(order) if "all" in words else set(words))
    _save(chat.id, key, new, order)
    if new:
        await msg.reply_html(f"✅ I will now delete <b>{_describe(new, order)}</b> {what}.")
    else:
        await msg.reply_html(f"✅ I will no longer delete any {what}.")


async def _keep_cmd(update, context, key, valid, order, what, types_cmd):
    """/keepservice, /nocleanservice and /keepcommand: stop deleting types."""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    words = _words(context.args)
    if not words:
        await msg.reply_html(f"Usage: <code>/keep{what_cmd(what)} &lt;type&gt;</code>. See /{types_cmd} for the types.")
        return
    bad = [w for w in words if w != "all" and w not in valid]
    if bad:
        await msg.reply_html(f"Unknown type: <code>{_esc(', '.join(bad))}</code>\n"
                             f"Available: all, {', '.join(order)}. See /{types_cmd}.")
        return
    chosen = _load(chat.id, key, valid)
    new = set() if "all" in words else chosen - set(words)
    _save(chat.id, key, new, order)
    left = f" Still deleting: <b>{_describe(new, order)}</b>." if new else ""
    await msg.reply_html(f"✅ I will keep {'all' if 'all' in words else ', '.join(words)} {what}.{left}")


# ------------------------------------------------------------------ the commands
async def cleanservice_cmd(update, context):
    await _set_cmd(update, context, SERVICE_KEY, SERVICE_TYPES, SERVICE_TYPES, "service messages", "cleanservicetypes")


async def keepservice_cmd(update, context):
    await _keep_cmd(update, context, SERVICE_KEY, SERVICE_TYPES, SERVICE_TYPES, "service messages", "cleanservicetypes")


async def cleanservicetypes_cmd(update, context):
    lines = ["<b>Service message types</b>", ""] + [f"- <code>{n}</code>: {_esc(d)}" for n, d in SERVICE_INFO]
    await update.effective_message.reply_html("\n".join(lines))


# Besides the three types (admin, user, other) a group can name SPECIFIC commands to delete, whatever their type:
# /clean /roast  deletes every /roast; /keep /roast stops it. Stored as "roast,hug" in the setting clean_command_names.
COMMAND_NAMES_KEY = "clean_command_names"
MAX_COMMAND_NAMES = 50
_NAME_RE = re.compile(r"[a-z0-9_]{1,32}")


def _load_names(chat_id):
    raw = D.get_setting(chat_id, COMMAND_NAMES_KEY, "") or ""
    return sorted({n for n in str(raw).replace(" ", "").lower().split(",") if _NAME_RE.fullmatch(n)})


def _save_names(chat_id, names):
    D.set_setting(chat_id, COMMAND_NAMES_KEY, ",".join(sorted(names)))


def parse_command_names(tokens, bot_username):
    """['/roast', 'hug', '/x@otherbot'] -> (['roast', 'hug'], ['/x@otherbot']). The slash is optional; a command
    written for another bot is refused."""
    good, bad = [], []
    for tok in tokens:
        name, _, tag = tok.lstrip("/").partition("@")
        name = name.lower()
        if _NAME_RE.fullmatch(name) and (not tag or tag.lower() == (bot_username or "").lower()):
            if name not in good:
                good.append(name)
        else:
            bad.append(tok)
    return good, bad


def _describe_clean(chat_id):
    """'user, other + /roast, /hug' | 'all' | 'nothing': what this group deletes now."""
    types = _describe(_load(chat_id, COMMAND_KEY, COMMAND_TYPES), COMMAND_TYPES)
    names = _load_names(chat_id)
    shown = ", ".join("/" + n for n in names[:10]) + (f" and {len(names) - 10} more" if len(names) > 10 else "")
    parts = ([] if types == "nothing" else [types]) + ([shown] if names else [])
    return " + ".join(parts) or "nothing"


async def cleancommand_cmd(update, context):
    """/clean (also /cleancommand): start deleting command types (all, admin, user, other) or specific commands (/roast)."""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    words = _words(context.args)
    if not words:
        await msg.reply_html(
            f"Currently deleting <b>{_esc(_describe_clean(chat.id))}</b> commands.\n\n"
            "Usage:\n"
            "1. /clean user: Delete a type: all, admin, user or other (see /cleancommandtypes).\n"
            "2. /clean /roast: Delete one command by name.\n"
            "3. /keep user: Stop deleting a type (or /keep /roast, /keep all).")
        return
    types = _load(chat.id, COMMAND_KEY, COMMAND_TYPES)
    names = set(_load_names(chat.id))
    if words[0] in YES_WORDS:
        types = set(COMMAND_TYPES)
    elif words[0] in NO_WORDS:
        types, names = set(), set()
    else:
        slash = [w for w in words if w.startswith("/")]
        plain = [w for w in words if not w.startswith("/")]
        bad = [w for w in plain if w != "all" and w not in COMMAND_TYPES]
        new_names, bad_names = parse_command_names(slash, context.bot.username)
        if bad or bad_names:
            shown = _esc(", ".join(bad + bad_names))
            hint = " To delete one command, write it with a slash, for example /clean /roast." if bad else ""
            await msg.reply_html(f"Unknown: <code>{shown}</code>\nTypes: all, {', '.join(COMMAND_TYPES)}. "
                                 f"See /cleancommandtypes.{hint}")
            return
        if len(names | set(new_names)) > MAX_COMMAND_NAMES:
            await msg.reply_html(f"❌ You can delete at most {MAX_COMMAND_NAMES} specific commands.")
            return
        types = types | (set(COMMAND_TYPES) if "all" in plain else set(plain))
        names |= set(new_names)
    _save(chat.id, COMMAND_KEY, types, COMMAND_TYPES)
    _save_names(chat.id, names)
    if types or names:
        await msg.reply_html(f"✅ I will now delete <b>{_esc(_describe_clean(chat.id))}</b> commands.")
    else:
        await msg.reply_html("✅ I will no longer delete any commands.")


async def keepcommand_cmd(update, context):
    """/keep (also /keepcommand): stop deleting command types or specific commands (/keep /roast, /keep all)."""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    words = _words(context.args)
    if not words:
        await msg.reply_html("Usage:\n1. /keep user: Stop deleting a type: all, admin, user or other.\n"
                             "2. /keep /roast: Stop deleting one command.\n"
                             "See /cleancommandtypes for the types.")
        return
    slash = [w for w in words if w.startswith("/")]
    plain = [w for w in words if not w.startswith("/")]
    bad = [w for w in plain if w != "all" and w not in COMMAND_TYPES]
    drop_names, bad_names = parse_command_names(slash, context.bot.username)
    if bad or bad_names:
        shown = _esc(", ".join(bad + bad_names))
        hint = " To stop one command, write it with a slash, for example /keep /roast." if bad else ""
        await msg.reply_html(f"Unknown: <code>{shown}</code>\nTypes: all, {', '.join(COMMAND_TYPES)}. "
                             f"See /cleancommandtypes.{hint}")
        return
    types = _load(chat.id, COMMAND_KEY, COMMAND_TYPES)
    names = set(_load_names(chat.id))
    if "all" in plain:
        types, names = set(), set()
    else:
        types -= set(plain)
        names -= set(drop_names)
    _save(chat.id, COMMAND_KEY, types, COMMAND_TYPES)
    _save_names(chat.id, names)
    kept = "all" if "all" in plain else ", ".join(plain + ["/" + n for n in drop_names])
    left = f" Still deleting: <b>{_esc(_describe_clean(chat.id))}</b>." if (types or names) else ""
    await msg.reply_html(f"✅ I will keep {_esc(kept)} commands.{left}")


async def cleancommandtypes_cmd(update, context):
    lines = ["<b>Command types</b>", ""] + [f"- <code>{n}</code>: {_esc(d)}" for n, d in COMMAND_INFO]
    lines += ["- <code>/name</code>: Delete one specific command whatever its type, eg /clean /roast. "
              "Stop it with /keep /roast."]
    await update.effective_message.reply_html("\n".join(lines))


# ------------------------------------------------------------------ the automatic deleting
def service_category(msg):
    """'join' | 'leave' | ... for a service message, None for an ordinary message."""
    for category, attrs in SERVICE_ATTRS.items():
        for attr in attrs:
            if getattr(msg, attr, None):
                return category
    return None


def _registered_commands():
    """Every command name the bot answers to, read once from the live handler list."""
    global _registered_cache
    if _registered_cache is None:
        names = set()
        try:
            for handlers in _app.handlers.values():
                for h in handlers:
                    if isinstance(h, CommandHandler):
                        cmds = getattr(h, "commands", None)
                        if cmds is None:
                            cmds = getattr(h, "command", ())
                        names.update(str(c).lower() for c in ((cmds,) if isinstance(cmds, str) else cmds))
        except Exception:
            log.exception("cleaner: couldn't read the registered commands")
        _registered_cache = frozenset(names)
    return _registered_cache


async def command_category(context, text):
    """'admin' | 'user' | 'other' for a message that starts with /command, None if it isn't one."""
    m = _CMD_RE.match(text or "")
    if not m:
        return None
    name, tag = m.group(1).lower(), m.group(2)
    if tag and tag.lower() != (context.bot.username or "").lower():
        return "other"                              # written for another bot
    if name in USER_COMMANDS:
        return "user"
    try:
        if name in await D.fun_names():             # /hug, /slap ... made in the Fun menu
            return "user"
    except Exception:
        log.debug("cleaner: couldn't read the Fun command names", exc_info=True)
    return "admin" if name in _registered_commands() else "other"


async def clean_command_handler(update, context):
    """group=100: runs after the command has been answered, then deletes the command message if its type is on."""
    msg, chat = update.effective_message, update.effective_chat
    if msg is None or chat is None or chat.type not in ("group", "supergroup") or D.is_paused(chat.id):
        return
    chosen = _load(chat.id, COMMAND_KEY, COMMAND_TYPES)
    names = _load_names(chat.id)
    if not chosen and not names:
        return
    text = msg.text or ""
    delete = False
    m = _CMD_RE.match(text)
    if names and m and m.group(1).lower() in names:          # a specific command named with /clean /roast
        tag = m.group(2)
        delete = not tag or tag.lower() == (context.bot.username or "").lower()   # never another bot's command
    if not delete and chosen:
        delete = await command_category(context, text) in chosen
    if not delete:
        return
    try:
        await msg.delete()
    except TelegramError as e:
        log.debug("cleaner: couldn't delete a command in %s: %s", chat.id, e)


async def clean_service_handler(update, context):
    """group=101: deletes a service message if its type is on (after welcome, captcha and antiraid saw it)."""
    msg, chat = update.effective_message, update.effective_chat
    if msg is None or chat is None or chat.type not in ("group", "supergroup"):
        return
    category = service_category(msg)
    if category is None or D.is_paused(chat.id):
        return
    if category not in _load(chat.id, SERVICE_KEY, SERVICE_TYPES):
        return
    try:
        await msg.delete()
    except TelegramError as e:
        log.debug("cleaner: couldn't delete a service message in %s: %s", chat.id, e)


# ------------------------------------------------------------------ the /help > Clean Commands page (buttons)
# Same idea as the Auto Close page: nova.py shows /help > Clean Commands with only "Usage Guide" and "Back"; the handler
# below runs before nova's own help handler (handler group -20, then ApplicationHandlerStop), so nova.py stays as it is.
# The page gets one row with two buttons; both change the same settings as /clean and /keep:
#   ➕ Add Command  tap a type (Admin, User, Other, All) to start deleting it, or 🎯 Specific command to name one
#   ➖ Remove       tap a type to stop deleting it (All = everything), or tap a saved specific command to stop it
# Button data: "ccb:<step>:<arg>":  add / rem (the two screens)   t:<type> / r:<type> (start / stop a type)
#                                   sp (ask for a specific command)   rn:<name> (stop one specific command)
CC_HOME = "help:cleancommand"
CC_TYPE_LABELS = (("admin", "Admin"), ("user", "User"), ("other", "Other"))
CC_NAMES_SHOWN = 24          # saved specific commands shown as buttons on the Remove screen
CC_TYPE_TTL = 300            # seconds the bot waits for the specific command to be typed
_cc_pending = {}             # (chat id, user id) -> {"mid": panel message id, "ts": time, "warned": bool}
_CC_TYPES_TEXT = ("• <b>Admin</b>: /ban, /mute, settings changes\n"
                  "• <b>User</b>: /id, /info, /get\n"
                  "• <b>Other</b>: unknown commands, or commands for other bots\n"
                  "• <b>All</b>: every command")


def _cc_status(chat):
    if chat is None or chat.type == "private":
        return "Open /help inside a group to set up clean commands for that group."
    return f"Now deleting: <b>{_esc(_describe_clean(chat.id))}</b>"


def _cc_home(chat):
    text = ("<b>🧽 Clean Commands</b>\n\n"
            "Keep your chat tidy: the bot deletes command messages after it has answered them.\n\n"
            "• <b>➕ Add Command</b>: choose what to delete\n"
            "• <b>➖ Remove</b>: stop deleting something\n\n"
            f"{_cc_status(chat)}\n\n"
            "Prefer typing? Use these commands (admins only):\n"
            "1. /clean user: Delete user commands (or admin, other, all).\n"
            "2. /clean /roast: Delete one specific command.\n"
            "3. /keep user: Stop deleting user commands (or /keep /roast, /keep all).\n"
            "4. /clean: Show what is being deleted now.\n\n"
            "<b>Note:</b> The bot must be an admin with the \"Delete messages\" right.")
    rows = [[InlineKeyboardButton("➕ Add Command", callback_data="ccb:add"),
             InlineKeyboardButton("➖ Remove", callback_data="ccb:rem")],
            [InlineKeyboardButton("📖 Usage Guide", callback_data="help:g_cleancommand")],
            [InlineKeyboardButton("« Back", callback_data="help:main")]]
    return text, InlineKeyboardMarkup(rows)


def _cc_add_screen(chat, note=""):
    types = _load(chat.id, COMMAND_KEY, COMMAND_TYPES)
    text = ("<b>➕ Add Command</b>\n\n" + (f"{note}\n\n" if note else "") + "Tap a type to start deleting it.\n\n"
            f"{_CC_TYPES_TEXT}\n\n{_cc_status(chat)}")
    rows = [[InlineKeyboardButton(("✅ " if t in types else "") + label, callback_data=f"ccb:t:{t}")
             for t, label in CC_TYPE_LABELS],
            [InlineKeyboardButton(("✅ " if set(COMMAND_TYPES) <= types else "") + "All", callback_data="ccb:t:all")],
            [InlineKeyboardButton("🎯 Specific command", callback_data="ccb:sp")],
            [InlineKeyboardButton("« Back", callback_data=CC_HOME)]]
    return text, InlineKeyboardMarkup(rows)


def _cc_remove_screen(chat, note=""):
    names = _load_names(chat.id)
    more = (f"\n…and {len(names) - CC_NAMES_SHOWN} more: remove them with /keep /name."
            if len(names) > CC_NAMES_SHOWN else "")
    text = ("<b>➖ Remove</b>\n\n" + (f"{note}\n\n" if note else "") +
            "Tap a type to stop deleting it. <b>All</b> stops everything." +
            ("\nTap a saved command to stop deleting just that one." if names else "") + f"\n\n{_cc_status(chat)}{more}")
    rows = [[InlineKeyboardButton("🚫 " + label, callback_data=f"ccb:r:{t}") for t, label in CC_TYPE_LABELS],
            [InlineKeyboardButton("🚫 All", callback_data="ccb:r:all")]]
    shown = [InlineKeyboardButton(f"❌ /{n}", callback_data=f"ccb:rn:{n}") for n in names[:CC_NAMES_SHOWN]]
    rows += [shown[i:i + 3] for i in range(0, len(shown), 3)]
    rows.append([InlineKeyboardButton("« Back", callback_data=CC_HOME)])
    return text, InlineKeyboardMarkup(rows)


def _cc_ask_screen():
    text = ("<b>🎯 Specific command</b>\n\n"
            "Send the command you want to delete in this chat, for example <code>roast</code>, or several at once: "
            "<code>roast hug</code>.\nWrite it without the slash so it doesn't run now (a slash works too).\n\n"
            "I'll wait 5 minutes. Tap Back to cancel.")
    return text, InlineKeyboardMarkup([[InlineKeyboardButton("« Back", callback_data="ccb:add")]])


async def help_cleancommand_callback(update, context):
    """group=-20: /help > Clean Commands. Replaces nova's plain page and stops nova's handler from answering too."""
    q = update.callback_query
    if q is None:
        return
    if await extra.menu_not_owner(q):                  # help buttons belong to the person who opened /help
        raise ApplicationHandlerStop
    await q.answer()
    await _ac_edit(q, *_cc_home(q.message.chat if q.message else None))
    raise ApplicationHandlerStop


async def ccb_callback(update, context):
    """The buttons on the Clean Commands page. Changing anything needs a group admin (checked on every tap)."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    parts = (q.data or "").split(":")
    act = parts[1] if len(parts) > 1 else ""
    arg = parts[2] if len(parts) > 2 else ""
    if chat.type == "private":
        await q.answer("Open /help inside a group to set up clean commands for that group.", show_alert=True)
        return
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer("Only group admins can change this.", show_alert=True)
        return
    key = (chat.id, q.from_user.id)
    _cc_pending.pop(key, None)                         # any tap leaves the "type the command" state; sp sets it again
    try:
        if act == "add" and len(parts) == 2:
            await q.answer()
            await _ac_edit(q, *_cc_add_screen(chat))
        elif act == "rem" and len(parts) == 2:
            await q.answer()
            await _ac_edit(q, *_cc_remove_screen(chat))
        elif act == "sp" and len(parts) == 2:
            await q.answer()
            now = time.monotonic()
            for k in [k for k, v in _cc_pending.items() if now - v["ts"] > CC_TYPE_TTL]:
                _cc_pending.pop(k, None)               # forget people who walked away
            _cc_pending[key] = {"mid": q.message.message_id, "ts": now, "warned": False}
            await _ac_edit(q, *_cc_ask_screen())
        elif act == "t" and len(parts) == 3 and arg in COMMAND_TYPES + ("all",):
            types = _load(chat.id, COMMAND_KEY, COMMAND_TYPES)
            new = set(COMMAND_TYPES) if arg == "all" else types | {arg}
            if new == types:
                await q.answer("Already on.")
                return
            _save(chat.id, COMMAND_KEY, new, COMMAND_TYPES)
            await q.answer("✅ Now deleting " + ("all" if arg == "all" else arg) + " commands.")
            await _ac_edit(q, *_cc_add_screen(chat))
        elif act == "r" and len(parts) == 3 and arg in COMMAND_TYPES + ("all",):
            types = _load(chat.id, COMMAND_KEY, COMMAND_TYPES)
            names = set(_load_names(chat.id))
            if arg == "all":
                if not types and not names:
                    await q.answer("Nothing is being deleted.")
                    return
                _save(chat.id, COMMAND_KEY, set(), COMMAND_TYPES)
                _save_names(chat.id, set())
                await q.answer("✅ I will keep all commands.")
            else:
                if arg not in types:
                    await q.answer("That type is not being deleted.")
                    return
                _save(chat.id, COMMAND_KEY, types - {arg}, COMMAND_TYPES)
                await q.answer(f"✅ I will keep {arg} commands.")
            await _ac_edit(q, *_cc_remove_screen(chat))
        elif act == "rn" and len(parts) == 3 and _NAME_RE.fullmatch(arg):
            names = set(_load_names(chat.id))
            if arg not in names:
                await q.answer("That command is no longer on the list.")
            else:
                _save_names(chat.id, names - {arg})
                await q.answer(f"✅ I will keep /{arg}.")
            await _ac_edit(q, *_cc_remove_screen(chat))
        else:
            await q.answer("This button is no longer valid.", show_alert=True)
    except TelegramError:
        raise
    except Exception:
        log.exception("clean commands: button failed in %s", chat.id)
        try:
            await q.answer("The database had a problem. Nothing was changed.", show_alert=True)
        except TelegramError:
            pass


async def cc_message(update, context):
    """group=104: an admin who tapped 🎯 Specific command sends the command name(s). Valid names are saved and the
    panel goes back to the Add Command screen; anything unreadable gets one hint and the bot keeps waiting."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg is None or chat is None or user is None or not msg.text:
        return
    pending = _cc_pending.get((chat.id, user.id))
    if pending is None:
        return
    if time.monotonic() - pending["ts"] > CC_TYPE_TTL:
        _cc_pending.pop((chat.id, user.id), None)
        return
    tokens = [t for t in re.split(r"[,\s]+", msg.text.strip()) if t]
    names, bad = parse_command_names(tokens, context.bot.username)
    current = set(_load_names(chat.id))
    problem = None
    if bad or not names:
        problem = "I couldn't read that. Send a command name like roast, or several like roast hug."
    elif len(current | set(names)) > MAX_COMMAND_NAMES:
        problem = f"You can delete at most {MAX_COMMAND_NAMES} specific commands. Tap Back to cancel."
    if problem:
        if not pending["warned"]:
            pending["warned"] = True
            try:
                await msg.reply_text(problem)
            except TelegramError:
                pass
        return
    _cc_pending.pop((chat.id, user.id), None)
    try:
        _save_names(chat.id, current | set(names))
    except Exception:
        log.exception("clean commands: saving specific commands failed in %s", chat.id)
        try:
            await msg.reply_text("The database had a problem. Nothing was changed.")
        except TelegramError:
            pass
        return
    text, markup = _cc_add_screen(chat, "✅ Added: " + ", ".join("/" + n for n in names))
    try:
        await context.bot.edit_message_text(text, chat_id=chat.id, message_id=pending["mid"], parse_mode="HTML",
                                            reply_markup=markup, disable_web_page_preview=True)
    except TelegramError as e:
        log.warning("clean commands: couldn't update the panel in %s: %s", chat.id, e)


# ======================================================================================================
# 4. IMPORT / EXPORT / RESET
# ======================================================================================================
#   /export [modules]   any admin: sends a JSON file with the group's configuration.
#   /import [modules]   group CREATOR only: reply to an exported file; imports everything (or only listed modules).
#   /reset              group CREATOR only: removes the saved configuration of this group (asks to confirm first).
# Only configuration is moved: never members' data (warnings, approvals, message counts, ranks).
FORMAT = "bot-chat-settings"
VERSION = 1
MAX_FILE_BYTES = 1_000_000
MAX_ITEMS = 1000            # notes / filters / blocklist words accepted from one file
MAX_VALUE_CHARS = 8000
COOLDOWN_SECS = 20          # "heavily rate limited": one import/export per group every 20 seconds
ANON_ADMIN_ID = 1087968824  # Telegram's "Group" anonymous-admin account

# module -> the per-group setting keys it owns (exact names; "prefixes" cover families such as lock_<type>)
MODULES = {
    "admin": {"keys": ("auto_approve", "autoclose", "autoclose_msg_close", "autoclose_msg_open")},
    "antiflood": {"keys": ("flood_limit", "flood_secs", "flood_mode", "repeat_limit", "mention_limit",
                           "antispam", "spam_mode")},
    "blocklists": {"keys": ("blocklist_mode", "block_ads", "block_promo", "block_promo_auth", "block_punish",
                            "block_punish_secs", "bl_notice_secs", "nsfw_word", "nsfw_content", "nsfw_action",
                            "nsfw_secs", "nsfw_allow"),
                   "blocklist": True, "allowlist": True},
    "clean_command": {"keys": ("clean_command", "clean_command_names")},
    "clean_service": {"keys": ("clean_service",)},
    "disabled": {"keys": ("disabled_cmds", "disable_del", "disable_admin")},
    "federations": {"keys": ()},
    "filters": {"keys": (), "filters": True},
    "greetings": {"keys": ("welcome", "welcome_on", "goodbye", "goodbye_on", "clean_welcome", "join_dm",
                           "join_dm_text", "join_delay", "captcha", "captcha_mode", "captcha_time",
                           "captcha_action")},
    "locks": {"keys": ("lock", "lockwarns"), "prefixes": ("lock_",)},
    "notes": {"keys": ("private_notes",), "notes": True},
    "pins": {"keys": ()},
    "raids": {"keys": ("auto_raid", "raid_time", "raid_action_time")},
    "reports": {"keys": ("reports_on",)},
    "rules": {"keys": ("rules", "rules_private", "rules_button")},
    "translations": {"keys": ()},
    "warns": {"keys": ("warn_limit", "warn_time", "warn_mode")},
}
ORDER = tuple(MODULES)
_last_use = {}


# ------------------------------------------------------------------ helpers
def _owns(module, key):
    spec = MODULES[module]
    return key in spec["keys"] or any(key.startswith(p) for p in spec.get("prefixes", ()))


def _module_of(key):
    for m in ORDER:
        if _owns(m, key):
            return m
    return None


def _parse_modules(args):
    """(modules or None, error text or None). None = every module."""
    if not args:
        return None, None
    names = [a.lower().strip(",") for a in args if a.strip(",")]
    bad = [n for n in names if n not in MODULES]
    if bad:
        return None, ("Unknown module: " + ", ".join(bad) + "\nAvailable: " + ", ".join(ORDER))
    return list(dict.fromkeys(names)), None


def _cooldown(chat_id):
    now = time.monotonic()
    if now - _last_use.get(chat_id, 0) < COOLDOWN_SECS:
        return int(COOLDOWN_SECS - (now - _last_use.get(chat_id, 0))) + 1
    if len(_last_use) > 2000:
        _last_use.clear()
    _last_use[chat_id] = now
    return 0


async def _is_creator(chat, user):
    """Only the real group creator (never an anonymous admin: we can't tell who it is)."""
    if user is None or user.id == ANON_ADMIN_ID:
        return False
    if D.is_bot_owner(user.id):
        return True
    try:
        member = await chat.get_member(user.id)
    except TelegramError:
        return False
    return member.status == ChatMemberStatus.OWNER


async def _is_admin(chat, user):
    if user is None:
        return False
    if user.id == ANON_ADMIN_ID or D.is_bot_owner(user.id):
        return True
    return await D.is_admin(chat, user.id)


# ------------------------------------------------------------------ export
def _collect(chat_id, modules):
    """{module: {...}} with only what is actually saved for this group (synchronous: reads the database)."""
    chat_id = int(chat_id)
    settings = store.settings_snapshot(chat_id)
    out = {}
    for m in modules:
        spec, block = MODULES[m], {}
        values = {k: v for k, v in settings.items() if _owns(m, k)}
        if values:
            block["settings"] = values
        if spec.get("notes"):
            names = store.note_names(chat_id)
            if names:
                block["notes"] = [{"name": n, "content": store.note_get(chat_id, n)} for n in names]
        if spec.get("filters"):
            rows = store.filter_rows(chat_id)
            if rows:
                block["filters"] = [{"keyword": k, "reply": r} for k, r in rows]
        if spec.get("blocklist"):
            words = store.block_words(chat_id)
            if words:
                block["blocklist"] = list(words)
        if spec.get("allowlist"):
            allow = [{"kind": kind, "value": v} for kind, vals in store.allow_load(chat_id).items() for v in sorted(vals)]
            if allow:
                block["allowlist"] = allow
        if block:
            out[m] = block
    return out


async def _send_export(chat, msg, bot, modules, reply_to=None):
    data = await asyncio.to_thread(_collect, chat.id, modules or ORDER)
    payload = {"format": FORMAT, "version": VERSION, "exported_at": int(time.time()),
               "chat_title": chat.title or "", "modules": data}
    raw = json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8")
    buf = io.BytesIO(raw)
    safe = "".join(c if c.isalnum() else "_" for c in (chat.title or "chat"))[:30].strip("_") or "chat"
    buf.name = f"{safe}_settings.json"
    chosen = modules or ORDER
    empty = [m for m in chosen if m not in data]
    caption = ("📤 Exported: " + (", ".join(data) or "nothing") + "."
               + (f"\nNothing saved / not used here: {', '.join(empty)}." if empty and not modules else "")
               + "\nImport it in another group: reply to this file with /import (group creator only).")
    await bot.send_document(chat.id, buf, filename=buf.name, caption=caption[:1000],
                            reply_to_message_id=reply_to, allow_sending_without_reply=True)


async def export_cmd(update, context):
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if not msg or chat.type == "private":
        if msg:
            await msg.reply_text("Use /export inside the group you want to export.")
        return
    if not await _is_admin(chat, user):
        await msg.reply_text("Only admins can export the settings.")
        return
    modules, err = _parse_modules(context.args)
    if err:
        await msg.reply_text(err)
        return
    wait = _cooldown(chat.id)
    if wait:
        await msg.reply_text(f"⏳ Slow down: try again in {wait}s.")
        return
    try:
        await _send_export(chat, msg, context.bot, modules, reply_to=msg.message_id)
    except Exception:
        log.exception("export failed")
        await msg.reply_text("⚠️ The export failed. Please try again later.")


# ------------------------------------------------------------------ import
def _apply(chat_id, wanted, payload):
    """Writes the file's data into this group (synchronous). Returns ({module: count}, [skipped text])."""
    chat_id = int(chat_id)
    done, notes = {}, []
    mods = payload.get("modules")
    if not isinstance(mods, dict):
        raise ValueError("The file has no 'modules' section.")
    for m in (wanted or ORDER):
        block = mods.get(m)
        if m not in MODULES or not isinstance(block, dict):
            continue
        n = 0
        settings = block.get("settings")
        if isinstance(settings, dict):
            for k, v in settings.items():
                if not isinstance(k, str) or not _owns(m, k) or not isinstance(v, (str, int, float)):
                    continue                                   # a key this module doesn't own is ignored
                if len(str(v)) > MAX_VALUE_CHARS:
                    notes.append(f"{k}: too long, skipped")
                    continue
                store.set_setting(chat_id, k, v)
                n += 1
        if MODULES[m].get("notes") and isinstance(block.get("notes"), list):
            for item in block["notes"][:MAX_ITEMS]:
                if isinstance(item, dict) and isinstance(item.get("name"), str) and isinstance(item.get("content"), str) \
                        and item["name"] and len(item["content"]) <= MAX_VALUE_CHARS:
                    store.note_set(chat_id, item["name"][:64], item["content"])
                    n += 1
        if MODULES[m].get("filters") and isinstance(block.get("filters"), list):
            for item in block["filters"][:MAX_ITEMS]:
                if isinstance(item, dict) and isinstance(item.get("keyword"), str) and isinstance(item.get("reply"), str) \
                        and item["keyword"] and len(item["reply"]) <= MAX_VALUE_CHARS:
                    store.filter_add(chat_id, item["keyword"][:100], item["reply"])
                    n += 1
        if MODULES[m].get("blocklist") and isinstance(block.get("blocklist"), list):
            for w in block["blocklist"][:MAX_ITEMS]:
                if isinstance(w, str) and w and len(w) <= 200:
                    store.block_add(chat_id, w)
                    n += 1
        if MODULES[m].get("allowlist") and isinstance(block.get("allowlist"), list):
            for item in block["allowlist"][:MAX_ITEMS]:
                if isinstance(item, dict) and isinstance(item.get("kind"), str) and isinstance(item.get("value"), str) \
                        and item["kind"] and item["value"] and len(item["value"]) <= 300:
                    store.allow_add(chat_id, item["kind"], item["value"])
                    n += 1
        done[m] = n
    return done, notes


async def import_cmd(update, context):
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if not msg:
        return
    if chat.type == "private":
        await msg.reply_text("Use /import inside the group you want to import into.")
        return
    if not await _is_creator(chat, user):
        await msg.reply_text("For security, only the group creator can import settings "
                             "(and not while posting anonymously).")
        return
    doc = msg.reply_to_message.document if msg.reply_to_message else None
    if doc is None:
        await msg.reply_text("Reply to an exported settings file with /import.\n"
                             "To import only some modules: /import rules greetings")
        return
    if (doc.file_size or 0) > MAX_FILE_BYTES:
        await msg.reply_text("⚠️ That file is too big to be a settings export.")
        return
    wanted, err = _parse_modules(context.args)
    if err:
        await msg.reply_text(err)
        return
    wait = _cooldown(chat.id)
    if wait:
        await msg.reply_text(f"⏳ Slow down: try again in {wait}s.")
        return
    try:
        raw = bytes(await (await context.bot.get_file(doc.file_id)).download_as_bytearray())
        payload = json.loads(raw.decode("utf-8"))
        if not isinstance(payload, dict) or payload.get("format") != FORMAT:
            raise ValueError("This is not a settings file exported by this bot.")
        done, notes = await asyncio.to_thread(_apply, chat.id, wanted, payload)
    except (ValueError, UnicodeDecodeError) as e:
        await msg.reply_text(f"⚠️ I couldn't read that file: {e}")
        return
    except TelegramError:
        await msg.reply_text("⚠️ I couldn't download that file.")
        return
    except Exception:
        log.exception("import failed")
        await msg.reply_text("⚠️ The import failed. Nothing more was changed.")
        return
    if not done:
        await msg.reply_text("Nothing to import: the file has no data for " + (", ".join(wanted) if wanted else "any module") + ".")
        return
    lines = ["✅ <b>Imported</b>"] + [f"• {html.escape(m)}: {n} item{'s' if n != 1 else ''}" for m, n in done.items()]
    if notes:
        lines.append("\nSkipped: " + html.escape("; ".join(notes[:5])))
    await msg.reply_html("\n".join(lines))


# ------------------------------------------------------------------ reset
def _wipe(chat_id):
    chat_id = int(chat_id)
    settings = store.settings_snapshot(chat_id)
    for k in list(settings):
        if _module_of(k):
            store.del_setting(chat_id, k)
    for n in list(store.note_names(chat_id)):
        store.note_del(chat_id, n)
    for k, _ in list(store.filter_rows(chat_id)):
        store.filter_remove(chat_id, k)
    for w in list(store.block_words(chat_id)):
        store.block_remove(chat_id, w)
    store.allow_clear(chat_id)


async def reset_cmd(update, context):
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if not msg:
        return
    if chat.type == "private":
        await msg.reply_text("Use /reset inside a group.")
        return
    if not await _is_creator(chat, user):
        await msg.reply_text("Only the group creator can reset the settings (and not while posting anonymously).")
        return
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Yes, reset", callback_data=f"ie:rst:y:{user.id}"),
                                InlineKeyboardButton("❌ Cancel", callback_data=f"ie:rst:n:{user.id}")]])
    await msg.reply_html("⚠️ <b>Reset all settings of this group?</b>\n\nThis removes the saved configuration: rules, "
                         "greetings, locks, filters, notes, blocklist, warn settings, antiflood and the other modules "
                         "listed in /help > Import & Export. Members' data (warnings, approvals, message counts) is kept. "
                         "This can't be undone. Tip: /export first.", reply_markup=kb)


# ------------------------------------------------------------------ the buttons on /help page 2
async def ie_callback(update, context):
    q = update.callback_query
    parts = (q.data or "").split(":")
    act = parts[1] if len(parts) > 1 else ""
    chat, user = q.message.chat if q.message else None, q.from_user
    if chat is None:
        await q.answer()
        return
    if act == "rst":                                           # reset confirmation (only the person who asked)
        if len(parts) < 4 or not parts[3].isdigit() or int(parts[3]) != user.id:
            await q.answer("Only the person who started the reset can answer.", show_alert=True)
            return
        if parts[2] != "y":
            await q.answer("Cancelled.")
            await q.edit_message_text("Reset cancelled. Nothing was changed.")
            return
        if not await _is_creator(chat, user):
            await q.answer("Only the group creator can do this.", show_alert=True)
            return
        await q.answer()
        try:
            await asyncio.to_thread(_wipe, chat.id)
            await q.edit_message_text("✅ This group's settings were reset.")
        except Exception:
            log.exception("reset failed")
            await q.edit_message_text("⚠️ The reset failed part-way. Please run /reset again.")
        return
    if await extra.menu_not_owner(q):                           # help buttons belong to who opened /help
        return
    if act == "imp":
        await q.answer("To import: reply to an exported .json file with /import (group creator only). "
                       "To import only some modules: /import rules greetings", show_alert=True)
        return
    if act == "exp":
        if chat.type == "private":
            await q.answer("Open /help inside the group you want to export.", show_alert=True)
            return
        if not await _is_admin(chat, user):
            await q.answer("Only admins can export the settings.", show_alert=True)
            return
        wait = _cooldown(chat.id)
        if wait:
            await q.answer(f"Slow down: try again in {wait}s.", show_alert=True)
            return
        await q.answer("Exporting...")
        try:
            await _send_export(chat, q.message, context.bot, None)
        except Exception:
            log.exception("export (button) failed")
            await context.bot.send_message(chat.id, "⚠️ The export failed. Please try again later.")
        return
    await q.answer()


# ======================================================================================================
# 5. BROADCAST (📢 button in the Bot Staff panel)
# ======================================================================================================
# Send one message to every group the bot is in, or only to the groups you choose.
#   * Only the bot owner and bot staff (never group admins), and only in a private chat with the bot.
#   * Flow: targets (all / chosen groups) -> the message -> pin yes/no -> summary -> Confirm / Edit / Cancel.
#   * The message is COPIED (copy_message), so text, photos, videos and files all work, with their formatting.
#   * Sending runs in the background, slowly (Telegram limits), one broadcast at a time, with a Stop button.
#   * The group list is the bot's own list (the one /stats uses), handed in as deps.groups_source(bot).
BC_PAGE = 8              # groups per page in the picker
BC_DELAY = 0.15          # seconds between two groups (Telegram allows about 30 messages per second in total)
BC_PROGRESS_EVERY = 4    # seconds between two progress updates
BC_LAST_KEY = "broadcast_last"   # settings(0, key): JSON of the last report
_bc_state = {}           # staff user id -> the broadcast that is being prepared
_bc_job = None           # the broadcast that is sending right now (only one at a time)
_bc_task = None


def broadcast_button():
    """The 📢 Broadcast button for the Bot Staff panel in nova.py."""
    return InlineKeyboardButton("📢 Broadcast", callback_data="bc:m")


async def _bc_allowed(user_id):
    if user_id in (getattr(D, "owner_ids", None) or ()):
        return True
    try:
        return bool(await asyncio.to_thread(D.is_super_admin, user_id))
    except Exception:
        log.exception("broadcast: staff check failed")
        return False


def _bc_short(title, n=28):
    title = (title or "?").strip() or "?"
    return title if len(title) <= n else title[:n - 1] + "…"


def _bc_plural(n, word="group"):
    return f"{n} {word}{'' if n == 1 else 's'}"


def _bc_new_state(groups, panel):
    return {"groups": groups, "panel": panel, "mode": None, "sel": set(), "sel_done": False, "page": 0,
            "msg": None, "pin": None, "await_msg": False, "ask_pin": False, "menu": False, "snap": None}


def _bc_step(st):
    if st["mode"] is None:
        return "target"
    if st["mode"] == "pick" and not st["sel_done"]:
        return "pick"
    if st["msg"] is None or st["await_msg"]:
        return "msg"
    if st["pin"] is None or st["ask_pin"]:
        return "pin"
    return "sum"


def _bc_targets_short(st):
    n = len(st["groups"]) if st["mode"] == "all" else len(st["sel"])
    return ("all " if st["mode"] == "all" else "") + _bc_plural(n) + ("" if st["mode"] == "all" else " selected")


def _bc_targets_long(st):
    if st["mode"] == "all":
        return f"All groups ({len(st['groups'])})"
    names = [html.escape(_bc_short(t, 40)) for c, t in st["groups"] if c in st["sel"]]
    lines = "\n".join(f"   • {n}" for n in names[:10])
    more = f"\n   …and {len(names) - 10} more" if len(names) > 10 else ""
    return f"{_bc_plural(len(names))} selected:\n{lines}{more}"


def _bc_screen(st):
    """(text, keyboard) for the step the broadcast is on."""
    step = _bc_step(st)
    n = len(st["groups"])
    cancel = [InlineKeyboardButton("❌ Cancel", callback_data="bc:x")]
    back = [InlineKeyboardButton("🔙 Back to summary", callback_data="bc:sum")] if st.get("snap") else cancel
    if step == "sum" and st.get("menu"):
        rows = [[InlineKeyboardButton("🎯 Targets", callback_data="bc:et")],
                [InlineKeyboardButton("📝 Message", callback_data="bc:em")],
                [InlineKeyboardButton("📌 Pin", callback_data="bc:ep")],
                [InlineKeyboardButton("🔙 Back to summary", callback_data="bc:sum")]]
        return "<b>✏️ What do you want to change?</b>", InlineKeyboardMarkup(rows)
    if step == "target":
        rows = [[InlineKeyboardButton(f"🌐 All groups ({n})", callback_data="bc:ta")],
                [InlineKeyboardButton("🎯 Specific groups", callback_data="bc:tp")], back]
        return (f"<b>📢 Broadcast: who gets it?</b>\n\nThe bot is in <b>{_bc_plural(n)}</b>.\n"
                "Send it to all of them, or pick one or more groups."), InlineKeyboardMarkup(rows)
    if step == "pick":
        pages = max(1, -(-n // BC_PAGE))
        st["page"] = min(max(st["page"], 0), pages - 1)
        start = st["page"] * BC_PAGE
        rows = []
        for i in range(start, min(start + BC_PAGE, n)):
            cid, title = st["groups"][i]
            rows.append([InlineKeyboardButton(("✅ " if cid in st["sel"] else "⬜ ") + _bc_short(title),
                                              callback_data=f"bc:g:{i}")])
        if pages > 1:
            rows.append([InlineKeyboardButton("◀", callback_data=f"bc:pg:{st['page'] - 1}"),
                         InlineKeyboardButton(f"{st['page'] + 1}/{pages}", callback_data="bc:noop"),
                         InlineKeyboardButton("▶", callback_data=f"bc:pg:{st['page'] + 1}")])
        rows.append([InlineKeyboardButton("☑️ Select all", callback_data="bc:sa"),
                     InlineKeyboardButton("🧹 Clear", callback_data="bc:cl")])
        rows.append([InlineKeyboardButton(f"✅ Done ({len(st['sel'])})", callback_data="bc:dn")])
        rows.append([InlineKeyboardButton("🔙 Back", callback_data="bc:bk"), cancel[0]])
        return (f"<b>🎯 Pick the groups</b>\n\nTap a group to select or unselect it. "
                f"Selected: <b>{len(st['sel'])}</b> of {n}."), InlineKeyboardMarkup(rows)
    if step == "msg":
        return (f"<b>📝 Send the message</b>\n\nTargets: <b>{html.escape(_bc_targets_short(st))}</b>\n\n"
                "Now send me the message you want to broadcast, here in this chat. Text, photo, video or a file all "
                "work, and the formatting is kept."), InlineKeyboardMarkup([back])
    if step == "pin":
        rows = [[InlineKeyboardButton("✅ Yes, pin it", callback_data="bc:py"),
                 InlineKeyboardButton("❌ No", callback_data="bc:pn")], back]
        return ("<b>📌 Pin the message?</b>\n\nShould the bot pin it in each group? A group where the bot has no pin "
                "right still gets the message, just not pinned."), InlineKeyboardMarkup(rows)
    info = st["msg"]
    preview = html.escape(info["text"][:120]) + ("…" if len(info["text"]) > 120 else "")
    what = info["kind"] if info["kind"] != "text" else "text"
    text = (f"<b>📋 Broadcast summary</b>\n\n"
            f"🎯 <b>Groups:</b> {_bc_targets_long(st)}\n\n"
            f"📝 <b>Message:</b> {what}" + (f"\n<i>{preview}</i>" if preview else "") + "\n\n"
            f"📌 <b>Pin:</b> {'ON' if st['pin'] else 'OFF'}\n\nCheck everything, then confirm.")
    rows = [[InlineKeyboardButton("✅ Confirm", callback_data="bc:ok")],
            [InlineKeyboardButton("✏️ Edit", callback_data="bc:ed"), cancel[0]]]
    return text, InlineKeyboardMarkup(rows)


async def _bc_render(context, uid, q=None):
    """Shows the current screen: edits the tapped message (q) or sends a new one below the staff's message."""
    st = _bc_state[uid]
    text, markup = _bc_screen(st)
    if q is not None:
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup, disable_web_page_preview=True)
        except TelegramError:
            pass                                          # unchanged (double tap) or too old to edit
        st["panel"] = (q.message.chat.id, q.message.message_id)
        return
    sent = await context.bot.send_message(st["panel"][0], text, parse_mode="HTML", reply_markup=markup,
                                          disable_web_page_preview=True)
    st["panel"] = (sent.chat_id, sent.message_id)


def _bc_panel():
    text = ("<b>📢 Broadcast</b>\n\nSend one message to every group the bot is in, or only to the groups you choose."
            + ("\n\n⏳ A broadcast is sending right now." if _bc_job else ""))
    rows = [[InlineKeyboardButton("✍️ New Broadcast", callback_data="bc:new")],
            [InlineKeyboardButton("📜 Last Report", callback_data="bc:last")],
            [InlineKeyboardButton("🔙 Back", callback_data="own:m")]]
    return text, InlineKeyboardMarkup(rows)


def _bc_report_text(rep):
    when = datetime.fromtimestamp(rep.get("time", 0), _tz()).strftime("%d %b %Y, %I:%M %p")
    head = "⏹ Broadcast stopped" if rep.get("stopped") else "📣 Broadcast finished"
    lines = [f"<b>{head}</b>", f"🕒 {when} ({BOT_TIMEZONE})", "",
             f"✅ Sent: <b>{rep.get('sent', 0)}</b> of {rep.get('total', 0)}",
             f"❌ Failed: <b>{len(rep.get('failed', []))}</b>"]
    if rep.get("pin"):
        lines.append(f"📌 Pinned: <b>{rep.get('pinned', 0)}</b> (pin failed: {rep.get('pin_failed', 0)})")
    failed = rep.get("failed", [])
    if failed:
        lines.append("\n<b>Failed groups:</b>")
        lines += [f"• {html.escape(_bc_short(t, 30))}: {html.escape(r)}" for t, r in failed[:10]]
        if len(failed) > 10:
            lines.append(f"…and {len(failed) - 10} more")
    return "\n".join(lines)


# ------------------------------------------------------------------ sending
def _bc_wait(exc):
    value = getattr(exc, "retry_after", 1)
    value = value.total_seconds() if hasattr(value, "total_seconds") else value
    return min(float(value) + 1, 60)


def _bc_reason(exc):
    text = str(exc).lower()
    if "not found" in text:
        return "group not found"
    if "not enough rights" in text or "have no rights" in text:
        return "no right to write"
    return str(exc)[:40] or type(exc).__name__


async def _bc_send_one(bot, job, cid, title):
    target = cid
    for _ in range(3):
        try:
            sent = await bot.copy_message(target, job["src_chat"], job["src_msg"])
            break
        except RetryAfter as e:
            await asyncio.sleep(_bc_wait(e))
        except ChatMigrated as e:
            target = e.new_chat_id
        except Forbidden:
            job["failed"].append((title, "bot was removed or can't write"))
            return
        except BadRequest as e:
            job["failed"].append((title, _bc_reason(e)))
            return
        except TelegramError as e:
            job["failed"].append((title, type(e).__name__))
            return
    else:
        job["failed"].append((title, "Telegram asked to wait too often"))
        return
    job["sent"] += 1
    if job["pin"]:
        try:
            await bot.pin_chat_message(target, sent.message_id)
            job["pinned"] += 1
        except RetryAfter as e:
            await asyncio.sleep(_bc_wait(e))
            job["pin_failed"] += 1
        except TelegramError:
            job["pin_failed"] += 1


async def _bc_progress(bot, job, force=False):
    now = time.monotonic()
    if not force and now - job["last_edit"] < BC_PROGRESS_EVERY:
        return
    job["last_edit"] = now
    text = (f"<b>📤 Broadcasting…</b>\n\nDone: <b>{job['done']}</b> of {len(job['targets'])}\n"
            f"✅ Sent: {job['sent']}\n❌ Failed: {len(job['failed'])}"
            + (f"\n📌 Pinned: {job['pinned']}" if job["pin"] else ""))
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("⏹ Stop", callback_data="bc:stop")]])
    try:
        await bot.edit_message_text(text, chat_id=job["panel"][0], message_id=job["panel"][1],
                                    parse_mode="HTML", reply_markup=kb)
    except TelegramError:
        pass


async def _bc_run(bot, job):
    global _bc_job
    try:
        await _bc_progress(bot, job, force=True)
        for cid, title in job["targets"]:
            if job["stop"]:
                break
            await _bc_send_one(bot, job, cid, title)
            job["done"] += 1
            await _bc_progress(bot, job)
            await asyncio.sleep(BC_DELAY)
    except asyncio.CancelledError:
        raise
    except Exception:
        log.exception("broadcast: stopped by an error")
    finally:
        rep = {"time": int(time.time()), "total": len(job["targets"]), "sent": job["sent"],
               "failed": [[t, r] for t, r in job["failed"][:30]], "pin": job["pin"], "pinned": job["pinned"],
               "pin_failed": job["pin_failed"], "stopped": job["stop"] or job["done"] < len(job["targets"])}
        _bc_job = None
        try:
            await asyncio.to_thread(D.set_setting, 0, BC_LAST_KEY, json.dumps(rep, ensure_ascii=False))
        except Exception:
            log.exception("broadcast: couldn't save the report")
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="bc:m")]])
        try:
            await bot.edit_message_text(_bc_report_text(rep), chat_id=job["panel"][0], message_id=job["panel"][1],
                                        parse_mode="HTML", reply_markup=kb)
        except TelegramError:
            try:
                await bot.send_message(job["panel"][0], _bc_report_text(rep), parse_mode="HTML", reply_markup=kb)
            except TelegramError:
                pass


async def _bc_start(context, q, uid, st):
    global _bc_job, _bc_task
    if _bc_job:
        await q.answer("A broadcast is already sending. Wait until it finishes.", show_alert=True)
        return
    if st["mode"] == "all":
        try:
            targets = [(int(c), t) for c, t, _ in await D.groups_source(context.bot)]
        except Exception:
            log.exception("broadcast: couldn't refresh the group list, using the saved one")
            targets = list(st["groups"])
    else:
        targets = [(c, t) for c, t in st["groups"] if c in st["sel"]]
    if not targets:
        await q.answer("There are no groups to send to.", show_alert=True)
        return
    _bc_job = {"targets": targets, "src_chat": st["msg"]["chat_id"], "src_msg": st["msg"]["message_id"],
               "pin": bool(st["pin"]), "panel": (q.message.chat.id, q.message.message_id), "stop": False,
               "done": 0, "sent": 0, "failed": [], "pinned": 0, "pin_failed": 0, "last_edit": 0.0}
    _bc_state.pop(uid, None)
    await q.answer("Sending…")
    _bc_task = asyncio.create_task(_bc_run(context.bot, _bc_job))


# ------------------------------------------------------------------ buttons and the message
async def bc_callback(update, context):
    q = update.callback_query
    uid = q.from_user.id
    if not await _bc_allowed(uid):
        await q.answer("This is for the bot owner and bot staff only.", show_alert=True)
        return
    chat = q.message.chat if q.message else None
    if chat is None or chat.type != "private":
        await q.answer("Open me in a private chat to broadcast: send /help there, then Bot Staff > Broadcast.",
                       show_alert=True)
        return
    parts = (q.data or "").split(":")
    act = parts[1] if len(parts) > 1 else "m"
    arg = parts[2] if len(parts) > 2 else ""

    async def show_panel():
        text, markup = _bc_panel()
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup)
        except TelegramError:
            pass

    if act == "noop":
        await q.answer()
        return
    if act == "m":
        await q.answer()
        await show_panel()
        return
    if act == "last":
        raw = await asyncio.to_thread(D.get_setting, 0, BC_LAST_KEY, "")
        try:
            rep = json.loads(raw) if raw else None
        except ValueError:
            rep = None
        await q.answer()
        text = _bc_report_text(rep) if isinstance(rep, dict) else "There is no broadcast report yet."
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("🔙 Back", callback_data="bc:m")]]))
        except TelegramError:
            pass
        return
    if act == "stop":
        if _bc_job:
            _bc_job["stop"] = True
            await q.answer("Stopping…")
        else:
            await q.answer("Nothing is sending right now.")
        return
    if act == "new":
        if _bc_job:
            await q.answer("A broadcast is already sending. Wait until it finishes.", show_alert=True)
            return
        await q.answer("Loading the groups…")
        try:
            found = await D.groups_source(context.bot)
        except Exception:
            log.exception("broadcast: couldn't load the groups")
            await q.edit_message_text("⚠️ I couldn't load the group list. Please try again in a moment.",
                                      reply_markup=InlineKeyboardMarkup(
                                          [[InlineKeyboardButton("🔙 Back", callback_data="bc:m")]]))
            return
        groups = sorted(((int(c), t) for c, t, _ in found), key=lambda g: (g[1] or "").lower())
        if not groups:
            await q.edit_message_text("The bot is not in any group yet.", reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("🔙 Back", callback_data="bc:m")]]))
            return
        _bc_state[uid] = _bc_new_state(groups, (chat.id, q.message.message_id))
        await _bc_render(context, uid, q)
        return

    st = _bc_state.get(uid)
    if st is None:
        await q.answer("This broadcast is no longer active. Please start again.", show_alert=True)
        await show_panel()
        return
    if act == "x":
        _bc_state.pop(uid, None)
        await q.answer("Cancelled.")
        await show_panel()
        return
    st["menu"] = False
    if act == "ta":
        st["mode"] = "all"
    elif act == "tp":
        st["mode"], st["sel_done"], st["page"] = "pick", False, 0
    elif act == "bk":
        st["mode"] = None
    elif act == "g" and arg.isdigit() and int(arg) < len(st["groups"]):
        cid = st["groups"][int(arg)][0]
        st["sel"].symmetric_difference_update({cid})
    elif act == "pg" and arg.lstrip("-").isdigit():
        st["page"] = int(arg)
    elif act == "sa":
        st["sel"] = {c for c, _ in st["groups"]}
    elif act == "cl":
        st["sel"] = set()
    elif act == "dn":
        if not st["sel"]:
            await q.answer("Pick at least one group first.", show_alert=True)
            return
        st["sel_done"] = True
    elif act in ("py", "pn"):
        st["pin"], st["ask_pin"] = act == "py", False
    elif act == "ed":
        st["menu"] = True
    elif act in ("et", "em", "ep"):
        st["snap"] = (st["mode"], set(st["sel"]), st["sel_done"], st["msg"], st["pin"])   # "Back" restores it
        if act == "et":
            st["mode"], st["sel_done"] = None, False
        elif act == "em":
            st["await_msg"] = True
        else:
            st["ask_pin"] = True
    elif act == "sum":
        if st["snap"]:
            st["mode"], st["sel"], st["sel_done"], st["msg"], st["pin"] = st["snap"]
        st["snap"], st["await_msg"], st["ask_pin"] = None, False, False
    elif act == "ok":
        if _bc_step(st) != "sum":
            await q.answer("Please finish the steps first.", show_alert=True)
            return
        await _bc_start(context, q, uid, st)
        return
    else:
        await q.answer()
        return
    if _bc_step(st) == "sum" and not st["menu"]:
        st["snap"] = None                                  # the edit is finished: "Back to summary" is not needed
    await q.answer()
    await _bc_render(context, uid, q)


async def bc_message(update, context):
    """The message the staff member sends after 'Send the message'. Ignored unless a broadcast waits for it."""
    msg, user = update.effective_message, update.effective_user
    if msg is None or user is None:
        return
    st = _bc_state.get(user.id)
    if st is None or _bc_step(st) != "msg":
        return
    if not await _bc_allowed(user.id):
        _bc_state.pop(user.id, None)
        return
    kind = next((k for k in ("photo", "video", "animation", "document", "audio", "voice", "video_note", "sticker",
                             "poll") if getattr(msg, k, None)), "text")
    st["msg"] = {"chat_id": msg.chat_id, "message_id": msg.message_id, "kind": kind,
                 "text": (msg.text or msg.caption or "").strip()}
    st["await_msg"] = False
    if _bc_step(st) == "sum":
        st["snap"] = None
    await _bc_render(context, user.id)


# ======================================================================================================
# 6. REGISTRATION (single entry point)
# ======================================================================================================
def register(app, deps):
    """Registers every handler of this file. See the module docstring for what `deps` needs."""
    global D, _app
    D, _app = deps, app

    # auto close: the command, plus the buttons on /help > Auto Close. The help:autoclose handler sits in group -20 so it
    # runs before nova.py's own help handler and stops it (ApplicationHandlerStop): no change in nova.py is needed.
    app.add_handler(CommandHandler("autoclose", autoclose_cmd))
    app.add_handler(CallbackQueryHandler(help_autoclose_callback, pattern=r"^help:autoclose$"), group=-20)
    app.add_handler(CallbackQueryHandler(acb_callback, pattern=r"^acb:"))
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND, ac_minute_message),
                    group=103)                         # a typed minute on the minute screen
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND, ac_custom_message),
                    group=105)                         # a typed custom close / open message

    # clean service + clean commands
    commands = {
        "cleanservice": cleanservice_cmd, "keepservice": keepservice_cmd, "nocleanservice": keepservice_cmd,
        "cleanservicetypes": cleanservicetypes_cmd,
        "clean": cleancommand_cmd, "keep": keepcommand_cmd,                       # the new names
        "cleancommand": cleancommand_cmd, "keepcommand": keepcommand_cmd,         # the old names keep working
        "cleancommandtypes": cleancommandtypes_cmd,
    }
    for name, fn in commands.items():
        app.add_handler(CommandHandler(name, fn))
    # the buttons on /help > Clean Commands (help:cleancommand sits in group -20, before nova.py's help handler)
    app.add_handler(CallbackQueryHandler(help_cleancommand_callback, pattern=r"^help:cleancommand$"), group=-20)
    app.add_handler(CallbackQueryHandler(ccb_callback, pattern=r"^ccb:"))
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT, cc_message), group=104)  # a typed command name
    # their own late groups: a handler group runs at most one handler, so these never compete with each other or
    # with the bot's other handlers (which all run first)
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.UpdateType.MESSAGE & filters.COMMAND,
                                   clean_command_handler), group=100)
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.UpdateType.MESSAGE & ~filters.COMMAND,
                                   clean_service_handler), group=101)

    # import / export / reset
    app.add_handler(CommandHandler("export", export_cmd))
    app.add_handler(CommandHandler("import", import_cmd))
    app.add_handler(CommandHandler("reset", reset_cmd))
    app.add_handler(CallbackQueryHandler(ie_callback, pattern=r"^ie:"))

    # broadcast (Bot Staff panel): buttons + the message the staff member sends
    app.add_handler(CallbackQueryHandler(bc_callback, pattern=r"^bc:"))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & ~filters.COMMAND & ~filters.StatusUpdate.ALL,
                                   bc_message), group=102)
