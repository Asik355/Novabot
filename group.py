"""
group.py: all group-management logic in ONE file (merged from autoclose.py, cleaner.py and importexport.py).

  AUTO CLOSE / OPEN   /autoclose 23:00 06:00   /autoclose off   /autoclose
                      (+ the 🕒 Auto Close and ⌨️ Command buttons on /help > Auto Close: hour, minute, AM/PM pickers)
  NIGHT MODE          /night 11pm 6am   /night off   /night   (text-only at night; /help > Night Mode page)
  APPEAL              /appeal [on|off|group|log|dm]   (📩 Appeal button on mute / warn notices; OFF by default)
  ANNIVERSARY         /anniv [on|off|9am|text <message>|reset|old on|off|now]   (join anniversaries; birthdays stay in fun_systems.py)
  SHOUT-OUT           /shout [on|off|sun 9pm|top 5|text <message>|reset|mention on|off|now]   (weekly top chatters, written by the admins)
  RULES GATE          /gate [on|off|<time>|kick|mute|ban]   (new members must accept the rules before they can chat)
  GREETINGS           /greet, /wdel <time|off>, /gdel, /wbtn <text> <link>, /gbtn   (extra buttons and delete-after for welcome / goodbye)
  REPORTS             /reportpanel, /reportmute <time>, /reportcooldown <time|off>   (the /report card: Mute / Warn / Delete message / Dismiss)
  PROBATION           /probation [on|off|hours <time>|msgs <n>|start|end|status]   (new members: no links / media for a while)
  RAID SHIELD         /raidmode [ban|restrict|lock], /raidwindow [time]   (extends nova's /antiraid: mute joiners or lock the group)
  MOD LOG             /modlog [@user]   (history page with filters; nova's /modlog calls modlog_command)
  WARN LADDER         /warnladder [on|off|clear|<count> <action> [time]|remove <count>]   (a different action per warning count)
  LANGUAGE            /lang  (English / Hinglish; the texts live in the lang/ folder)
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
    active_warns(chat_id, user_id)   a member's unexpired warnings as (id, reason, time), for Appeal
nova.py also calls group.appeal_markup(chat_id, user_id, "mute"|"warn", kb) where it builds the Unmute / Remove warning button.
nova.py also calls group.gate_start (on_new_members, captcha_callback) and group.gate_cleanup (on_left_member), passes
    restore_permissions, send_welcome, rules_button and announce, and adds group.gate_button(chat) on /help > Rules.
    nova.py also calls group.greet_markup / greet_after_send in send_welcome and on_left_member, passes render, template_markup, safe_html,
    DEFAULT_WELCOME and DEFAULT_GOODBYE, and adds group.greet_button(chat) on /help > Greetings.
    nova.py also calls group.report_submit(bot, chat, msg, reporter) from file_report, passes add_warn and do_action, and adds group.report_button(chat) on /help > Reports.
    nova.py also passes find_violation, load_allow, lock_exempt and is_service_message (its lock engine) for the probation guard, and
    adds group.probation_button(chat) on /help > Locks.
nova.py also calls group.raid_started / raid_stopped (after /antiraid on / off) and delegates raid_new_members to group.raid_new_members;
    raid_left(chat_id) is nova's seconds-left of a raid; group.raid_button(chat) is on /help > Raid & Flood.
nova.py also calls group.record_undo(...) for unmute / unban / removed warnings, and group.modlog_button(chat) on /help > Log Channels.
    get_target(update, context)   async, (user id, mention) of the replied-to or named member (replies by itself on failure)
nova.py also calls group.ladder_warn(...) inside add_warn, group.wl_summary(chat_id) in /limits and group.warn_ladder_button(chat) on /help > Warnings.
"""
import asyncio
import functools
import html
import io
import json
import logging
import os
import re
import time
from datetime import date, datetime, timedelta, timezone

from telegram import ChatPermissions, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.constants import ChatMemberStatus
from telegram.error import BadRequest, ChatMigrated, Forbidden, RetryAfter, TelegramError
from telegram.ext import ApplicationHandlerStop, CallbackQueryHandler, CommandHandler, MessageHandler, filters

import extra
import migrate_to_mongo as store
try:
    import msgcount  # the message counts (nova.py registers it): the weekly shout-out (section 2l) reads them
except ImportError:
    msgcount = None
try:
    from lang import lang as L      # the language system (lang/lang.py): L.t("key", chat_id, name=value)
except ImportError:
    import lang as L                # lang.py uploaded next to group.py instead of inside a lang/ folder

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
# Night Mode (section 2b): night = "HH:MM-HH:MM" (start-end), night_state = "on" while the media permissions are off,
# night_saved = JSON of the real permissions saved when it started.
NIGHT_KEY, NIGHT_STATE_KEY, NIGHT_SAVED_KEY = "night", "night_state", "night_saved"
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
    """`what` keys the retry timer and the words in the notice: "close", "open", "night" or "night-end"."""
    _retry_at[(chat_id, what)] = time.monotonic() + RETRY_AFTER
    log.warning("autoclose: couldn't %s %s: %s: %s", what, chat_id, type(exc).__name__, exc)
    last = _notice_at.get(chat_id)
    if last is not None and time.monotonic() - last < NOTICE_EVERY:
        return
    _notice_at[chat_id] = time.monotonic()
    try:
        await bot.send_message(chat_id, L.t("ac.fail", chat_id, label=L.t("ac.lbl_" + what.replace("-", "_"), chat_id)))
    except TelegramError:
        pass


# ------------------------------------------------------------------ the messages (default or custom)
def default_close_msg(has_open_time, chat_id=None):
    text = L.t("ac.def_close", chat_id)
    return text + (L.t("ac.def_close_back", chat_id) if has_open_time else "")


def default_open_msg(has_close_time, chat_id=None):
    text = L.t("ac.def_open", chat_id)
    return text + (L.t("ac.def_open_next", chat_id) if has_close_time else "")


def render_msg(template, open_time, close_time, chat_id=None):
    """Fills {open_time} and {close_time}. Plain str.replace, so other braces in a custom text are harmless."""
    later = L.t("ac.later", chat_id)
    return template.replace("{open_time}", open_time or later).replace("{close_time}", close_time or later)


def build_msg(chat_id, kind, close=None, open_=None):
    """The HTML text to post: the group's custom message when it has one, otherwise the default. `kind` is
    'close' or 'open'; `close` / `open_` are minutes since midnight (or None)."""
    custom = (D.get_setting(chat_id, MSG_CLOSE_KEY if kind == "close" else MSG_OPEN_KEY, "") or "").strip()
    ot = fmt_12h(open_) if open_ is not None else ""
    ct = fmt_12h(close) if close is not None else ""
    if custom:
        template = html.escape(custom[:MSG_MAX])               # a custom text is plain text: never HTML from a user
    elif kind == "close":
        template = default_close_msg(open_ is not None, chat_id)
    else:
        template = default_open_msg(close is not None, chat_id)
    return render_msg(template, ot, ct, chat_id)


async def close_group(bot, chat_id, until_minutes=None):
    """Saves the permissions, switches them off, posts the closed message and PINS it. Returns True when it worked."""
    try:
        chat = await bot.get_chat(chat_id)
        current = _saved_perms(chat)
        night_saved = D.get_setting(chat_id, NIGHT_STATE_KEY, "") == "on" and D.get_setting(chat_id, NIGHT_SAVED_KEY, "")
        if night_saved == NIGHT_PASSIVE:
            night_saved = ""
        if night_saved:                                            # Night Mode is on: keep the REAL permissions it saved,
            D.set_setting(chat_id, SAVED_KEY, night_saved)         # not the media-off ones the group has right now
        elif getattr(getattr(chat, "permissions", None), "can_send_messages", True) is not False and current:
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
        perms = _restore_perms(chat_id)
        if D.get_setting(chat_id, NIGHT_STATE_KEY, "") == "on":    # opening inside the night window: media stays off
            perms = _night_variant(perms)
        await bot.set_chat_permissions(chat_id, perms)
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
def _scheduled_groups(key=AUTOCLOSE_KEY):
    """[(chat_id, 'HH:MM-HH:MM')] for every group that has a schedule under `key` (Auto Close, or Night Mode's);
    one query, no per-group lookups."""
    rows = store.col("settings").find({"key": key}, {"chat_id": 1, "value": 1})
    return [(int(r["chat_id"]), r.get("value")) for r in rows]


async def run_once(bot):
    """One pass of the 30-second loop. Every job runs on its own: one that fails (a database hiccup, one odd group) is logged and
    never stops the others, so Night Mode keeps working even when something else in the loop is broken."""
    now = _now_minutes()
    for name, job in (("auto close", _auto_close_round(bot, now)),
                      ("night mode", _night_round(bot, now)),       # Night Mode (section 2b) uses the same loop
                      ("raid shield", _raid_round(bot)),            # Raid Shield (section 2f): lifts the lock when the raid is over
                      ("rules gate", _gate_round(bot)),             # Rules gate (section 2j): members who didn't accept in time
                      ("shout-out", _shout_round(bot)),             # Weekly shout-out (section 2l)
                      ("anniversaries", _anniv_round(bot))):        # Join anniversaries (section 2m)
        try:
            await job
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("scheduler: the %s round failed", name)


async def _auto_close_round(bot, now):
    for chat_id, raw in await asyncio.to_thread(_scheduled_groups):
        sched = load_schedule(raw)
        if not sched or chat_id >= 0 or D.is_paused(chat_id) or D.get_setting(chat_id, RAID_LOCK_KEY, "") == "on":
            continue                                     # (a raid lock holds the group: section 2f)
        close, open_ = sched
        want_closed = is_closed_at(now, close, open_)
        is_closed = D.get_setting(chat_id, STATE_KEY, "open") == "closed"
        try:                                             # one group failing never skips the groups after it
            if want_closed and not is_closed:
                if time.monotonic() >= _retry_at.get((chat_id, "close"), 0):
                    await close_group(bot, chat_id, open_)
            elif not want_closed and is_closed:
                if time.monotonic() >= _retry_at.get((chat_id, "open"), 0):
                    await open_group(bot, chat_id)
        except Exception:
            log.exception("autoclose: the round failed for %s", chat_id)


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
def _ac_usage(chat_id):
    return L.t("ac.usage", chat_id)


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
            await msg.reply_text(L.t("ac.cmd_off", chat.id) + "\n\n" + _ac_usage(chat.id))
            return
        state = L.t("ac.state_closed" if D.get_setting(chat.id, STATE_KEY, "open") == "closed" else "ac.state_open", chat.id)
        await msg.reply_text(L.t("ac.cmd_on", chat.id, tz=BOT_TIMEZONE, close=fmt_12h(sched[0]), open=fmt_12h(sched[1]),
                                 state=state))
        return
    if args[0] in ("closemsg", "openmsg"):             # /autoclose closemsg <text> | reset
        kind = "close" if args[0] == "closemsg" else "open"
        pieces = (msg.text or "").split(None, 2)        # keep the text exactly as typed (case, new lines)
        text = pieces[2].strip() if len(pieces) > 2 else ""
        if not text:
            await msg.reply_text(L.t("ac.msg_usage", chat.id, cmd=args[0], max=MSG_MAX))
            return
        if text.lower() in ("reset", "default"):
            store.del_setting(chat.id, MSG_CLOSE_KEY if kind == "close" else MSG_OPEN_KEY)
            await msg.reply_text(L.t("ac.msg_reset", chat.id, kind=kind))
            return
        if len(text) > MSG_MAX:
            await msg.reply_text(L.t("ac.msg_toolong", chat.id, n=len(text), max=MSG_MAX))
            return
        D.set_setting(chat.id, MSG_CLOSE_KEY if kind == "close" else MSG_OPEN_KEY, text)
        await msg.reply_html(L.t("ac.msg_saved", chat.id) + "\n\n" + build_msg(chat.id, kind, SAMPLE_CLOSE, SAMPLE_OPEN))
        return
    if args[0] in ("off", "no", "stop", "disable", "0"):
        ok, was_closed = await turn_off(context.bot, chat.id)
        if not ok:
            await msg.reply_text(L.t("ac.off_fail", chat.id))
            return
        await msg.reply_text(L.t("ac.off_done", chat.id) + (L.t("ac.off_open", chat.id) if was_closed else ""))
        return
    close, open_ = parse_two_times(" ".join(args))
    if close is None or open_ is None:
        await msg.reply_text(L.t("ac.cant_read", chat.id) + "\n\n" + _ac_usage(chat.id))
        return
    if close == open_:
        await msg.reply_text(L.t("ac.cmd_same", chat.id) + "\n\n" + _ac_usage(chat.id))
        return
    D.set_setting(chat.id, AUTOCLOSE_KEY, f"{fmt_minutes(close)}-{fmt_minutes(open_)}")
    await msg.reply_text(L.t("ac.cmd_saved", chat.id, tz=BOT_TIMEZONE, close=fmt_12h(close), open=fmt_12h(open_)))
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


def _tz_label(chat_id=None):
    return L.t("ac.tz_india", chat_id) if BOT_TIMEZONE == "Asia/Kolkata" else html.escape(BOT_TIMEZONE)


def _ac_status(chat):
    cid = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("ac.st_private", cid)
    sched = load_schedule(D.get_setting(chat.id, AUTOCLOSE_KEY, "") or "")
    if not sched:
        return L.t("ac.st_off", cid)
    state = L.t("ac.stt_closed" if D.get_setting(chat.id, STATE_KEY, "open") == "closed" else "ac.stt_open", cid)
    return L.t("ac.st_on", cid, tz=html.escape(BOT_TIMEZONE), close=fmt_12h(sched[0]), open=fmt_12h(sched[1]), state=state)


def _ac_home(chat):
    cid = getattr(chat, "id", None)
    text = (L.t("ac.title", cid) + "\n\n" + L.t("ac.home_intro", cid) + "\n\n" + _ac_status(chat) + "\n\n" +
            L.t("ac.home_note", cid))
    rows = [[InlineKeyboardButton(L.t("ac.btn_auto", cid), callback_data="acb:a"),
             InlineKeyboardButton(L.t("ac.btn_cmd", cid), callback_data="acb:c")],
            [InlineKeyboardButton(L.t("ac.btn_guide", cid), callback_data="help:g_autoclose")],
            [InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]]
    return text, InlineKeyboardMarkup(rows)


def _ac_panel(chat, note=""):
    sched = load_schedule(D.get_setting(chat.id, AUTOCLOSE_KEY, "") or "")
    text = (L.t("ac.title", chat.id) + "\n\n" + (f"{note}\n\n" if note else "") + _ac_status(chat) + "\n\n" +
            L.t("ac.panel_tap", chat.id))
    rows = [[InlineKeyboardButton(L.t("ac.btn_set", chat.id), callback_data="acb:H:c:-"),
             InlineKeyboardButton(L.t("ac.btn_custom", chat.id), callback_data="acb:m")]]
    if sched:
        rows.append([InlineKeyboardButton(L.t("ac.btn_off", chat.id), callback_data="acb:off")])
    rows.append([InlineKeyboardButton(L.t("pick.back", chat.id), callback_data=AC_HOME)])
    return text, InlineKeyboardMarkup(rows)


def _ac_command_page(chat=None):
    cid = getattr(chat, "id", None)
    return (L.t("ac.cmd_page", cid, tz=_tz_label(cid)),
            InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data=AC_HOME)]]))


# The same three pickers serve Auto Close and Night Mode. `which` says which time is being chosen:
#   "c" Auto Close closing time   "o" Auto Close opening time   "nc" Night Mode start   "no" Night Mode end
# (the second time of a pair carries the first one in `carry`). The texts come from lang (keys "pick.*", "ac.*", "night.*").
_AC_FIRST, _AC_SECOND = ("c", "nc"), ("o", "no")


def _ac_head(which, carry, chat_id=None):
    if which in ("nc", "no"):
        head = L.t("night.head_start" if which == "nc" else "night.head_end", chat_id)
        if which == "no":
            head += "\n" + L.t("night.starts_at", chat_id, time=fmt_12h(int(carry)))
        return head
    head = L.t("ac.head_close" if which == "c" else "ac.head_open", chat_id)
    if which == "o":
        head += "\n" + L.t("ac.closes_at", chat_id, time=fmt_12h(int(carry)))
    return head


def _ac_hour(which, carry, chat_id=None):
    text = _ac_head(which, carry, chat_id) + "\n\n" + L.t("pick.step1", chat_id)
    rows = [[InlineKeyboardButton(str(h), callback_data=f"acb:M:{which}:{carry}:{h}") for h in range(first, first + 4)]
            for first in (1, 5, 9)]
    back = {"c": "acb:a", "o": "acb:H:c:-", "nc": "nmb:a", "no": "acb:H:nc:-"}[which]
    rows.append([InlineKeyboardButton(L.t("pick.back", chat_id), callback_data=back)])
    return text, InlineKeyboardMarkup(rows)


def _ac_minute(which, carry, hour, chat_id=None):
    text = (_ac_head(which, carry, chat_id) + "\n" + L.t("pick.hour", chat_id, hour=hour) + "\n\n" +
            L.t("pick.step2", chat_id))
    rows = [[InlineKeyboardButton(f"{m:02d}", callback_data=f"acb:A:{which}:{carry}:{hour}:{m}") for m in AC_MINUTES],
            [InlineKeyboardButton(L.t("pick.back", chat_id), callback_data=f"acb:H:{which}:{carry}")]]
    return text, InlineKeyboardMarkup(rows)


def _ac_ampm(which, carry, hour, minute, chat_id=None):
    text = (_ac_head(which, carry, chat_id) + "\n" + L.t("pick.time", chat_id, time=f"{hour}:{minute:02d}") + "\n\n" +
            L.t("pick.step3", chat_id))
    rows = [[InlineKeyboardButton(L.t("pick.am", chat_id), callback_data=f"acb:S:{which}:{carry}:{hour}:{minute}:A"),
             InlineKeyboardButton(L.t("pick.pm", chat_id), callback_data=f"acb:S:{which}:{carry}:{hour}:{minute}:P")],
            [InlineKeyboardButton(L.t("pick.back", chat_id), callback_data=f"acb:M:{which}:{carry}:{hour}")]]
    return text, InlineKeyboardMarkup(rows)


_ac_msg_pending = {}         # (chat id, user id) -> {"kind": "close"|"open", "mid": panel message id, "ts", "warned"}
_AC_KIND = {"c": "close", "o": "open"}


def _ac_msg_menu(chat):
    custom_c = bool((D.get_setting(chat.id, MSG_CLOSE_KEY, "") or "").strip())
    custom_o = bool((D.get_setting(chat.id, MSG_OPEN_KEY, "") or "").strip())
    word = lambda on: L.t("ac.custom" if on else "ac.default", chat.id)
    text = L.t("ac.cm_menu", chat.id, close=word(custom_c), open=word(custom_o))
    rows = [[InlineKeyboardButton(L.t("ac.btn_close_msg", chat.id), callback_data="acb:e:c"),
             InlineKeyboardButton(L.t("ac.btn_open_msg", chat.id), callback_data="acb:e:o")],
            [InlineKeyboardButton(L.t("pick.back", chat.id), callback_data="acb:a")]]
    return text, InlineKeyboardMarkup(rows)


def _ac_msg_edit_screen(chat, which, note=""):
    kind = _AC_KIND[which]
    sample = build_msg(chat.id, kind, SAMPLE_CLOSE, SAMPLE_OPEN)
    custom = bool((D.get_setting(chat.id, MSG_CLOSE_KEY if kind == "close" else MSG_OPEN_KEY, "") or "").strip())
    text = (L.t("ac.em_head_close" if kind == "close" else "ac.em_head_open", chat.id) + "\n\n" +
            (f"{note}\n\n" if note else "") +
            L.t("ac.em_body", chat.id, state=L.t("ac.custom" if custom else "ac.default", chat.id), sample=sample,
                max=MSG_MAX))
    rows = []
    if custom:
        rows.append([InlineKeyboardButton(L.t("ac.btn_reset", chat.id), callback_data=f"acb:rs:{which}")])
    rows.append([InlineKeyboardButton(L.t("pick.back", chat.id), callback_data="acb:m")])
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
                await msg.reply_text(L.t("ac.cm_toolong", chat.id, n=len(text), max=MSG_MAX))
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
            await msg.reply_text(L.t("ac.db_problem", chat.id))
        except TelegramError:
            pass
        return
    page, markup = _ac_msg_edit_screen(chat, which, L.t("ac.saved_short", chat.id))
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
    text, markup = _ac_ampm(pending["which"], pending["carry"], pending["hour"], minute, chat.id)
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
    invalid = L.t("ac.invalid", chat.id)
    if act == "c":                                     # the Command page is only information: anyone may read it
        await q.answer()
        await _ac_edit(q, *_ac_command_page(chat))
        return
    if chat.type == "private":
        await q.answer(L.t("ac.st_private", chat.id), show_alert=True)
        return
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("ac.admin_only", chat.id), show_alert=True)
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
                await q.answer(L.t("ac.db_problem", chat.id), show_alert=True)
                return
            await q.answer(L.t("ac.toast_reset", chat.id))
            await _ac_edit(q, *_ac_msg_edit_screen(chat, which, L.t("ac.note_reset", chat.id)))
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
            await q.answer(L.t("ac.db_problem", chat.id), show_alert=True)
            return
        if not ok:
            await q.answer(L.t("ac.off_fail_short", chat.id), show_alert=True)
        else:
            await q.answer(L.t("ac.toast_off", chat.id) + (L.t("ac.off_open", chat.id) if was_closed else ""))
        await _ac_edit(q, *_ac_panel(chat))
        return

    which = parts[2] if len(parts) > 2 else ""
    carry = parts[3] if len(parts) > 3 else ""
    carry_mins = _ac_num(carry, 0, 1439) if which in _AC_SECOND else None
    if which not in _AC_FIRST + _AC_SECOND or (which in _AC_SECOND and carry_mins is None) \
            or (which in _AC_FIRST and carry != "-"):
        await q.answer(invalid, show_alert=True)
        return
    night = which in ("nc", "no")
    hour = _ac_num(parts[4], 1, 12) if len(parts) > 4 else None
    minute = _ac_num(parts[5], 0, 59) if len(parts) > 5 else None

    if act == "H" and len(parts) == 4:
        await q.answer()
        await _ac_edit(q, *_ac_hour(which, carry, chat.id))
    elif act == "M" and len(parts) == 5 and hour:
        await q.answer()
        now = time.monotonic()
        for key in [k for k, v in _ac_pending.items() if now - v["ts"] > AC_TYPE_TTL]:
            _ac_pending.pop(key, None)                 # forget people who walked away
        _ac_pending[(chat.id, q.from_user.id)] = {"which": which, "carry": carry, "hour": hour,
                                                  "mid": q.message.message_id, "ts": now}
        await _ac_edit(q, *_ac_minute(which, carry, hour, chat.id))
    elif act == "A" and len(parts) == 6 and hour and minute is not None:
        await q.answer()
        await _ac_edit(q, *_ac_ampm(which, carry, hour, minute, chat.id))
    elif act == "S" and len(parts) == 7 and hour and minute is not None and parts[6] in ("A", "P"):
        mins = (hour % 12 + (12 if parts[6] == "P" else 0)) * 60 + minute
        if which in _AC_FIRST:                         # the first time is chosen: now ask for the second one
            await q.answer(L.t("night.starts_toast" if night else "ac.closes_toast", chat.id, time=fmt_12h(mins)))
            await _ac_edit(q, *_ac_hour("no" if night else "o", str(mins), chat.id))
            return
        if mins == carry_mins:
            await q.answer(L.t("night.same_time" if night else "ac.same_time", chat.id), show_alert=True)
            return
        key = NIGHT_KEY if night else AUTOCLOSE_KEY
        try:
            D.set_setting(chat.id, key, f"{fmt_minutes(carry_mins)}-{fmt_minutes(mins)}")
        except Exception:
            log.exception("autoclose: saving the schedule failed in %s", chat.id)
            await q.answer(L.t("ac.db_problem", chat.id), show_alert=True)
            return
        if night:
            await q.answer(L.t("night.on_toast", chat.id))
            note = L.t("night.saved", chat.id, start=fmt_12h(carry_mins), end=fmt_12h(mins))
            await _ac_edit(q, *_nm_panel(chat, note))
        else:
            await q.answer(L.t("ac.on_toast", chat.id))
            note = L.t("ac.saved", chat.id, close=fmt_12h(carry_mins), open=fmt_12h(mins))
            await _ac_edit(q, *_ac_panel(chat, note))
        try:
            await run_once(context.bot)                # apply it right away if the group is inside the window now
        except Exception:
            log.exception("autoclose: applying the new schedule failed")
    else:
        await q.answer(invalid, show_alert=True)


# ======================================================================================================
# 2b. NIGHT MODE
# ======================================================================================================
# At night the group stays open but members can only send plain text: the media permissions are switched off (photos,
# videos, audio, voice and video messages, files, stickers/GIFs, polls). Telegram has no permission for links, so links
# are not blocked. Admins are never affected. It runs in the same 30-second loop as Auto Close (run_once).
#   * AUTO CLOSE COMES FIRST: while Auto Close has the group closed, Night Mode does nothing; when Auto Close opens the
#     group inside the night window the media stays off (open_group), and when Auto Close closes during Night Mode it
#     saves the REAL permissions that Night Mode saved (close_group), so nothing is ever restored to a media-off state.
#   * Settings per group: night = "HH:MM-HH:MM" (start-end), night_state = "on" while it is active, night_saved = JSON.
#   * The bot needs the "Ban users" (restrict members) admin right.
NIGHT_MEDIA_OFF = ("can_send_audios", "can_send_documents", "can_send_photos", "can_send_videos",
                   "can_send_video_notes", "can_send_voice_notes", "can_send_polls", "can_send_other_messages")


def _night_variant(perms):
    """The given permissions with every media permission switched off; text (and everything else) stays as it was."""
    to_dict = getattr(perms, "to_dict", None)
    d = dict(to_dict()) if to_dict else {}
    d.update({k: False for k in NIGHT_MEDIA_OFF})
    d["can_send_messages"] = True
    try:
        return ChatPermissions(**d)
    except TypeError:                                  # an older python-telegram-bot without some of these fields: drop the unknown ones
        import inspect
        ok = set(inspect.signature(ChatPermissions.__init__).parameters)
        return ChatPermissions(**{k: v for k, v in d.items() if k in ok})


NIGHT_PIN_KEY = "night_pin"   # id of the Night Mode start message this bot pinned


async def _unpin_night_message(bot, chat_id):
    """Unpins the start message this bot pinned (never any other pinned message)."""
    raw = D.get_setting(chat_id, NIGHT_PIN_KEY, "") or ""
    if not str(raw).isdigit():
        return
    try:
        await bot.unpin_chat_message(chat_id, message_id=int(raw))
    except TelegramError as e:
        log.debug("night: couldn't unpin the start message in %s: %s", chat_id, e)
    store.del_setting(chat_id, NIGHT_PIN_KEY)


NIGHT_PASSIVE = "closed"      # night_saved value when the group was ALREADY closed (by an admin) as the window began: nothing to restore


async def _set_perms(bot, chat_id, perms):
    """set_chat_permissions with the permissions treated INDEPENDENTLY. Without that Telegram lets "can send stickers/GIFs" or
    "link previews" imply the photo / video / file / voice permissions, so a Night Mode that switches media off could be
    silently undone. (Older python-telegram-bot versions don't have the option: then the plain call is used.)"""
    try:
        await bot.set_chat_permissions(chat_id, perms, use_independent_chat_permissions=True)
    except TypeError:
        await bot.set_chat_permissions(chat_id, perms)


def _night_saved_perms(chat_id):
    raw = D.get_setting(chat_id, NIGHT_SAVED_KEY, "") or ""
    if raw == NIGHT_PASSIVE:
        raw = ""
    try:
        perms = ChatPermissions(**json.loads(raw)) if raw else None
    except (TypeError, ValueError):
        perms = None
    if perms is None or perms.can_send_messages is False:      # nothing usable saved: the group's defaults
        return D.default_perms
    return perms


async def start_night(bot, chat_id, end_minutes):
    """Saves the permissions, switches the media permissions off, tells the group. Returns True when it worked."""
    try:
        chat = await bot.get_chat(chat_id)
        perms = getattr(chat, "permissions", None)
        if perms is None:                                  # can't read the group's permissions: look again later
            log.warning("night: can't read the permissions of %s", chat_id)
            _retry_at[(chat_id, "night")] = time.monotonic() + RETRY_AFTER
            return False
        if getattr(perms, "can_send_messages", True) is False:
            # Closed by an admin: nobody can send anything anyway. Night Mode counts as active (so the status is right and the
            # window ends cleanly) but touches nothing, says nothing, and never opens the group.
            D.set_setting(chat_id, NIGHT_SAVED_KEY, NIGHT_PASSIVE)
            D.set_setting(chat_id, NIGHT_STATE_KEY, "on")
            return True
        D.set_setting(chat_id, NIGHT_SAVED_KEY, _saved_perms(chat))
        await _set_perms(bot, chat_id, _night_variant(perms))
    except Exception as e:                             # not only TelegramError: any failure is logged and shown, never silent
        log.exception("night: start failed in %s", chat_id)
        store.del_setting(chat_id, NIGHT_SAVED_KEY)
        await _fail(bot, chat_id, "night", e)
        return False
    D.set_setting(chat_id, NIGHT_STATE_KEY, "on")
    try:
        sent = await bot.send_message(chat_id, L.t("night.start", chat_id, open_time=fmt_12h(end_minutes)), parse_mode="HTML")
    except TelegramError:
        return True
    try:                                               # pinned quietly (no notification), unpinned when Night Mode ends
        await bot.pin_chat_message(chat_id, sent.message_id, disable_notification=True)
        D.set_setting(chat_id, NIGHT_PIN_KEY, str(sent.message_id))
    except TelegramError as e:                         # no "Pin messages" right: Night Mode is still on
        log.debug("night: couldn't pin the start message in %s: %s", chat_id, e)
    return True


_NIGHT_MEDIA_ATTRS = ("photo", "video", "animation", "document", "audio", "voice", "video_note", "sticker", "poll")


async def night_enforce(update, context):
    """While Night Mode is ON: text only. A member's photo, video, file, voice, sticker, poll or link is deleted at once
    (the permissions alone are not enough: links and some media types still get through). Admins, the bot owner and
    bot staff are never touched. Runs before the other handlers; after deleting, nothing else handles that message."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg is None or user is None or chat is None or chat.type not in ("group", "supergroup"):
        return
    has_media = any(getattr(msg, a, None) for a in _NIGHT_MEDIA_ATTRS)
    ents = list(msg.entities or []) + list(msg.caption_entities or [])
    has_link = any(e.type in ("url", "text_link") for e in ents)
    if not (has_media or has_link):
        return
    if D.get_setting(chat.id, NIGHT_STATE_KEY, "") != "on" or D.get_setting(chat.id, NIGHT_SAVED_KEY, "") == NIGHT_PASSIVE:
        return
    if D.is_bot_owner(user.id) or await D.is_admin(chat, user.id) or await asyncio.to_thread(D.is_super_admin, user.id):
        return
    try:
        await msg.delete()
    except TelegramError as e:                         # the bot needs the "Delete messages" admin right
        log.warning("night: couldn't delete a message in %s: %s", chat.id, e)
        return
    raise ApplicationHandlerStop


async def end_night(bot, chat_id):
    """Gives the saved permissions back and tells the group. While Auto Close has the group closed only the state is
    cleared (Auto Close keeps the real permissions and restores them when it opens)."""
    closed = D.get_setting(chat_id, STATE_KEY, "open") == "closed"
    passive = D.get_setting(chat_id, NIGHT_SAVED_KEY, "") == NIGHT_PASSIVE      # it began on a group an admin had closed
    if not closed and not passive:
        try:
            await _set_perms(bot, chat_id, _night_saved_perms(chat_id))
        except Exception as e:
            log.exception("night: end failed in %s", chat_id)
            await _fail(bot, chat_id, "night-end", e)
            return False
    store.del_setting(chat_id, NIGHT_STATE_KEY)
    store.del_setting(chat_id, NIGHT_SAVED_KEY)
    await _unpin_night_message(bot, chat_id)
    if not closed and not passive:
        try:
            await bot.send_message(chat_id, L.t("night.end", chat_id), parse_mode="HTML")
        except TelegramError:
            pass
    return True


async def night_off(bot, chat_id):
    """Stops Night Mode and gives the permissions back if it was active. Returns (ok, was_active)."""
    was = D.get_setting(chat_id, NIGHT_STATE_KEY, "") == "on"
    store.del_setting(chat_id, NIGHT_KEY)
    if was and not await end_night(bot, chat_id):
        return False, was
    return True, was


async def _night_round(bot, now):
    for chat_id, raw in await asyncio.to_thread(_scheduled_groups, NIGHT_KEY):
        sched = load_schedule(raw)
        if not sched or chat_id >= 0 or D.is_paused(chat_id) or D.get_setting(chat_id, RAID_LOCK_KEY, "") == "on":
            continue                                     # (a raid lock holds the group: section 2f)
        start, end = sched
        want = is_closed_at(now, start, end)             # "inside the window", same maths as Auto Close
        active = D.get_setting(chat_id, NIGHT_STATE_KEY, "") == "on"
        try:                                             # one group failing never skips the groups after it
            if want and not active:
                if D.get_setting(chat_id, STATE_KEY, "open") == "closed":
                    continue                             # Auto Close comes first
                if time.monotonic() >= _retry_at.get((chat_id, "night"), 0):
                    await start_night(bot, chat_id, end)
            elif not want and active:
                if time.monotonic() >= _retry_at.get((chat_id, "night-end"), 0):
                    await end_night(bot, chat_id)
        except Exception:
            log.exception("night: the round failed for %s", chat_id)


# ------------------------------------------------------------------ the /help > Night Mode page and /night
NIGHT_HOME = "help:night"


def _nm_status(chat):
    chat_id = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("night.private", chat_id)
    sched = load_schedule(D.get_setting(chat.id, NIGHT_KEY, "") or "")
    if not sched:
        return L.t("night.status_off", chat.id)
    return L.t("night.status_on", chat.id, tz=html.escape(BOT_TIMEZONE), start=fmt_12h(sched[0]), end=fmt_12h(sched[1]),
               now=_nm_now(chat.id, sched))


def _nm_now(chat_id, sched):
    """'active' / 'not active' / why it is not active although the clock is inside the window."""
    if D.get_setting(chat_id, NIGHT_STATE_KEY, "") == "on":
        return L.t("night.now_active", chat_id)
    if not is_closed_at(_now_minutes(), sched[0], sched[1]):
        return L.t("night.now_idle", chat_id)
    if D.get_setting(chat_id, STATE_KEY, "open") == "closed":
        return L.t("night.now_wait", chat_id)                 # Auto Close has the group closed: Night Mode waits
    return L.t("night.now_pending", chat_id)                  # inside the window, the loop hasn't applied it (yet)


def _nm_panel(chat, note=""):
    """The whole Night Mode page: what it does, the status, Set Time, Turn OFF (when on) and Back."""
    chat_id = getattr(chat, "id", None)
    sched = load_schedule(D.get_setting(chat.id, NIGHT_KEY, "") or "") if chat is not None and chat.type != "private" else None
    text = (L.t("night.title", chat_id) + "\n\n" + (note + "\n\n" if note else "") + L.t("night.intro", chat_id) +
            "\n\n" + _nm_status(chat) + "\n\n" + L.t("night.tap", chat_id) + "\n\n" + L.t("night.note", chat_id))
    rows = [[InlineKeyboardButton(L.t("night.btn_set", chat_id), callback_data="acb:H:nc:-"),
             InlineKeyboardButton(L.t("night.btn_cmd", chat_id), callback_data="nmb:c")]]       # ⌨️ Command, like Auto Close
    if sched:
        rows.append([InlineKeyboardButton(L.t("night.btn_off", chat_id), callback_data="nmb:off")])
    rows.append([InlineKeyboardButton(L.t("pick.back", chat_id), callback_data="help:main")])
    return text, InlineKeyboardMarkup(rows)


def _nm_command_page(chat=None):
    """⌨️ Command: every Night Mode command (information only)."""
    cid = getattr(chat, "id", None)
    return (L.t("night.cmd_page", cid, tz=_tz_label(cid)),
            InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="nmb:a")]]))


async def help_night_callback(update, context):
    """group=-20: /help > Night Mode (the menu entry comes from nova's help data; this page is built here)."""
    q = update.callback_query
    if q is None:
        return
    if await extra.menu_not_owner(q):
        raise ApplicationHandlerStop
    await q.answer()
    await _ac_edit(q, *_nm_panel(q.message.chat if q.message else None))
    raise ApplicationHandlerStop


async def nmb_callback(update, context):
    """"nmb:a" shows the page, "nmb:off" turns Night Mode off. Group admins only, checked on every tap. (The time
    pickers are the Auto Close ones: "acb:" buttons with which = nc / no.)"""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    act = (q.data or "").split(":")[1:2]
    if act == ["c"]:                                   # the Command page is only information: anyone may read it
        await q.answer()
        await _ac_edit(q, *_nm_command_page(chat))
        return
    if chat.type == "private":
        await q.answer(L.t("night.private"), show_alert=True)
        return
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("night.admin_only", chat.id), show_alert=True)
        return
    _ac_pending.pop((chat.id, q.from_user.id), None)
    if act == ["a"]:
        await q.answer()
        await _ac_edit(q, *_nm_panel(chat))
    elif act == ["off"]:
        try:
            ok, was = await night_off(context.bot, chat.id)
        except Exception:
            log.exception("night: turning off failed in %s", chat.id)
            await q.answer(L.t("ac.db_problem", chat.id), show_alert=True)
            return
        if ok:
            await q.answer(L.t("night.off_done", chat.id) + (L.t("night.off_restored", chat.id) if was else ""))
        else:
            await q.answer(L.t("night.off_failed", chat.id), show_alert=True)
        await _ac_edit(q, *_nm_panel(chat))
    else:
        await q.answer("This button is no longer valid.", show_alert=True)


async def night_cmd(update, context):
    """/night 11pm 6am  |  /night off  |  /night"""
    if not await D.group_only(update):                 # group only + admins only
        return
    chat, msg = update.effective_chat, update.effective_message
    usage = L.t("night.usage", chat.id)
    args = [a.lower() for a in context.args]
    sched = load_schedule(D.get_setting(chat.id, NIGHT_KEY, "") or "")
    if not args:
        if not sched:
            await msg.reply_text(L.t("night.cmd_off", chat.id) + "\n\n" + usage)
        else:
            await msg.reply_text(L.t("night.cmd_on", chat.id, tz=BOT_TIMEZONE, start=fmt_12h(sched[0]), end=fmt_12h(sched[1]),
                                     now=_nm_now(chat.id, sched)))
        return
    if args[0] in ("off", "no", "stop", "disable", "0"):
        ok, was = await night_off(context.bot, chat.id)
        if not ok:
            await msg.reply_text(L.t("night.off_failed", chat.id))
            return
        await msg.reply_text(L.t("night.off_done", chat.id) + (L.t("night.off_restored", chat.id) if was else ""))
        return
    start, end = parse_two_times(" ".join(args))
    if start is None or end is None:
        await msg.reply_text(L.t("night.cant_read", chat.id) + "\n\n" + usage)
        return
    if start == end:
        await msg.reply_text(L.t("night.same_time", chat.id) + "\n\n" + usage)
        return
    D.set_setting(chat.id, NIGHT_KEY, f"{fmt_minutes(start)}-{fmt_minutes(end)}")
    await msg.reply_text(L.t("night.cmd_saved", chat.id, tz=BOT_TIMEZONE, start=fmt_12h(start), end=fmt_12h(end)))
    await run_once(context.bot)                        # apply it right away if the group is inside the window now


# ======================================================================================================
# 2c. APPEAL
# ======================================================================================================
# A muted or warned member can ask the admins to look at it again. OFF by default (setting mod_appeal = "on").
#   * Whoever did it (any admin's /mute /tmute /dmute /warn /dwarn, or the bot's own mutes) the notice gets a
#     "📩 Appeal" button (appeal_markup, called from nova.py). It opens the bot's private chat with a deep link:
#     /start appeal_<chat>_<m|w>. Bans, and automatic spam/flood warnings, are not covered.
#   * In the private chat the bot checks that the person is really muted / warned right now, asks for a reason
#     (max 300 characters, /skip to send none) and posts a card with ✅ Unmute / ✅ Remove warning and ❌ Reject.
#   * The card ALWAYS goes to the bot's private chat with every admin who has started the bot, and also to ONE place
#     the admins choose (mod_appeal_dest): "group" (default) or "log" (the log channel; the group when none is set).
#     Whoever decides first wins; every copy of the card is then updated.
#   * The member gets the answer in the bot's private chat, and /myappeals there lists their appeals. After a
#     rejection the member can appeal again at once (one pending appeal per person and kind).
#   * /help > Appeal > 📋 Appeal List shows the group's appeals (5 per page); a pending one can be opened and decided.
# Appeals are saved in the "appeals" collection: _id, chat_id, chat_title, user_id, user_name, kind ("mute"|"warn"),
# ref (warning id), reason, text (the card), cards [{chat, id}], status ("open"|"approved"|"rejected"), created_at,
# decided_at, decided_by, decided_name.
APPEAL_KEY, APPEAL_DEST_KEY = "mod_appeal", "mod_appeal_dest"
APPEAL_DESTS = ("group", "log")
APPEAL_REASON_MAX = 300
APPEAL_ASK_TTL = 10 * 60             # seconds the bot waits for the reason in the private chat
APPEAL_PAGE = 5                      # appeals per page of the list
APPEAL_ICON = {"open": "⏳", "approved": "✅", "rejected": "❌"}
_apl_pending = {}                    # user_id -> (chat_id, kind, ref, expires at): waiting for the reason


def appeal_on(chat_id):
    return D.get_setting(chat_id, APPEAL_KEY, "off") == "on"


def appeal_dest(chat_id):
    return "log" if D.get_setting(chat_id, APPEAL_DEST_KEY, "group") == "log" else "group"


_apl_dm_sent = {}                    # (chat_id, user_id, kind) -> monotonic time of the last private offer (no duplicates)


async def _apl_dm_offer(chat_id, user_id, kind):
    """Sends the member a private message with an Appeal button right when they are muted / warned.
    Works only if they have started the bot before (Telegram's rule): otherwise it is skipped quietly."""
    try:
        bot = _app.bot
        if not bot.username:
            return
        title = html.escape((await bot.get_chat(chat_id)).title or "the group")
        what = "muted" if kind == "mute" else "warned"
        url = f"https://t.me/{bot.username}?start=appeal_{abs(chat_id)}_{'m' if kind == 'mute' else 'w'}"
        await bot.send_message(user_id, f"You were {what} in <b>{title}</b>.\nIf you think it was a mistake, you can appeal.",
                               parse_mode="HTML",
                               reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(L.t("apl.btn", chat_id), url=url)]]))
    except TelegramError as e:                                   # never started the bot, or blocked it
        log.debug("appeal: couldn't DM %s: %s", user_id, e)
    except Exception:
        log.exception("appeal: private offer failed for %s", user_id)


def appeal_markup(chat_id, user_id, kind, kb=None):
    """`kb` (nova's Unmute / Remove warning markup, or None) with a 📩 Appeal row added when Appeal is ON in this group.
    kind is "mute" or "warn". Returns `kb` unchanged when Appeal is OFF, so it is safe to call everywhere."""
    try:
        if not appeal_on(chat_id):
            return kb
        username = _app.bot.username
        if not username or chat_id >= 0:
            return kb
        url = f"https://t.me/{username}?start=appeal_{abs(chat_id)}_{'m' if kind == 'mute' else 'w'}"
        rows = [list(r) for r in kb.inline_keyboard] if kb else []
        rows.append([InlineKeyboardButton(L.t("apl.btn", chat_id), url=url)])
        key, now = (chat_id, user_id, kind), time.monotonic()
        if now - _apl_dm_sent.get(key, -999) > 60:               # also offer the appeal in the member's private chat
            _apl_dm_sent[key] = now
            try:
                asyncio.get_running_loop().create_task(_apl_dm_offer(chat_id, user_id, kind))
            except RuntimeError:
                pass
        return InlineKeyboardMarkup(rows)
    except Exception:
        log.exception("appeal: couldn't add the Appeal button in %s", chat_id)
        return kb


async def _apl_state(bot, chat_id, user_id, kind):
    """(active, ref, shown reason) for the person's mute or warning right now."""
    if kind == "warn":
        rows = await asyncio.to_thread(D.active_warns, chat_id, user_id)
        return (True, rows[-1][0], rows[-1][1] or "") if rows else (False, None, "")
    member = await bot.get_chat_member(chat_id, user_id)
    muted = member.status == ChatMemberStatus.RESTRICTED and not getattr(member, "can_send_messages", True)
    return muted, None, ""


APPEAL_KEEP = 24 * 3600               # a decided appeal leaves the list this long after the decision


def _apl_purge_find(match, name="appeals", decided=("approved", "rejected"), keep=None):
    """Delete decided appeals older than APPEAL_KEEP (open ones stay), then return the matching rows. The Reports list
    (section 2h) uses it too, with its own collection, statuses and keep time."""
    col = store.col(name)
    try:
        col.delete_many({"status": {"$in": list(decided)}, "decided_at": {"$lt": time.time() - (keep or APPEAL_KEEP)}})
    except Exception:
        log.exception("%s: couldn't clear old decided rows", name)
    return list(col.find(match))


async def _apl_rows(**match):
    """The saved appeals matching `match`, newest first. Decided ones are cleared 24 hours after the decision."""
    rows = await asyncio.to_thread(_apl_purge_find, match)
    return sorted(rows, key=lambda r: r.get("created_at", 0), reverse=True)


# ------------------------------------------------------------------ the /help > Appeal page and /appeal
def _apl_panel(chat, note=""):
    cid = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("apl.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    on, dest = appeal_on(chat.id), appeal_dest(chat.id)
    text = (L.t("apl.title", cid) + "\n\n" + (note + "\n\n" if note else "") + L.t("apl.intro", cid) + "\n\n" +
            L.t("apl.status_on" if on else "apl.status_off", cid, dest=L.t("apl.dest_" + dest, cid)) + "\n\n" +
            L.t("apl.note", cid))
    rows = [[InlineKeyboardButton(L.t("apl.btn_off" if on else "apl.btn_on", cid), callback_data="apb:t")],
            [InlineKeyboardButton(("✅ " if d == dest else "") + L.t("apl.dest_" + d, cid), callback_data=f"apb:d:{d}")
             for d in APPEAL_DESTS],
            [InlineKeyboardButton(L.t("apl.btn_list", cid), callback_data="apb:l:0")],
            [InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]]
    return text, InlineKeyboardMarkup(rows)


def _apl_status(row, cid):
    return L.t("apl.st_" + row["status"], cid, admin=html.escape(row.get("decided_name") or ""))


async def _apl_list_panel(chat, page):
    """The 📋 Appeal List page: 5 appeals, newest first; a pending one can be opened."""
    cid = chat.id
    rows = await _apl_rows(chat_id=cid)
    pages = max(1, -(-len(rows) // APPEAL_PAGE))
    page = min(max(page, 0), pages - 1)
    shown = rows[page * APPEAL_PAGE:(page + 1) * APPEAL_PAGE]
    if not rows:
        text = L.t("apl.list_title", cid, count=0) + "\n\n" + L.t("apl.list_empty", cid)
    else:
        lines = [L.t("apl.list_line", cid, n=page * APPEAL_PAGE + i + 1, user=html.escape(r.get("user_name") or ""),
                     kind=L.t("apl.kind_" + r["kind"], cid), status=_apl_status(r, cid)) for i, r in enumerate(shown)]
        text = L.t("apl.list_title", cid, count=len(rows)) + "\n\n" + "\n".join(lines)
        if any(r["status"] == "open" for r in shown):
            text += "\n\n" + L.t("apl.list_tap", cid)
    kb = [[InlineKeyboardButton(f"⏳ {r.get('user_name') or ''}: {L.t('apl.kind_' + r['kind'], cid)}"[:60],
                                callback_data=f"apb:v:{r['_id']}")] for r in shown if r["status"] == "open"]
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀️", callback_data=f"apb:l:{page - 1}"))
    if page < pages - 1:
        nav.append(InlineKeyboardButton("▶️", callback_data=f"apb:l:{page + 1}"))
    if nav:
        kb.append(nav)
    kb.append([InlineKeyboardButton(L.t("pick.back", cid), callback_data="apb:a")])
    return text, InlineKeyboardMarkup(kb)


def _apl_decide_buttons(row, cid):
    yes = L.t("apl.btn_unmute" if row["kind"] == "mute" else "apl.btn_rmwarn", cid)
    return [InlineKeyboardButton(yes, callback_data=f"apl:a:{row['_id']}"),
            InlineKeyboardButton(L.t("apl.btn_reject", cid), callback_data=f"apl:r:{row['_id']}")]


async def help_appeal_callback(update, context):
    """group=-20: /help > Appeal (the menu entry comes from nova's help data; this page is built here)."""
    q = update.callback_query
    if q is None:
        return
    if await extra.menu_not_owner(q):
        raise ApplicationHandlerStop
    await q.answer()
    await _ac_edit(q, *_apl_panel(q.message.chat if q.message else None))
    raise ApplicationHandlerStop


def _apl_set(chat_id, what, value):
    """what = "t" (switch) or "d" (destination). Returns the note shown on the page."""
    if what == "t":
        D.set_setting(chat_id, APPEAL_KEY, "off" if appeal_on(chat_id) else "on")
        return L.t("apl.toast_on" if appeal_on(chat_id) else "apl.toast_off", chat_id)
    D.set_setting(chat_id, APPEAL_DEST_KEY, value)
    return L.t("apl.toast_dest", chat_id, dest=L.t("apl.dest_" + value, chat_id))


async def apb_callback(update, context):
    """"apb:t" switch ON/OFF, "apb:d:<group|log>" where the extra card goes, "apb:a" the page, "apb:l:<page>" the list,
    "apb:v:<id>" one pending appeal. Admins only, checked on every tap."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    if chat.type == "private":
        await q.answer(L.t("apl.private"), show_alert=True)
        return
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("apl.admin_only", chat.id), show_alert=True)
        return
    parts = (q.data or "").split(":")[1:]
    try:
        if parts == ["a"]:
            await q.answer()
            await _ac_edit(q, *_apl_panel(chat))
        elif parts == ["t"] or (len(parts) == 2 and parts[0] == "d" and parts[1] in APPEAL_DESTS):
            note = _apl_set(chat.id, parts[0], parts[1] if len(parts) == 2 else None)
            await q.answer(note)
            await _ac_edit(q, *_apl_panel(chat))
        elif len(parts) == 2 and parts[0] == "l" and parts[1].isdigit():
            await q.answer()
            await _ac_edit(q, *await _apl_list_panel(chat, int(parts[1])))
        elif len(parts) == 2 and parts[0] == "v":
            rows = await _apl_rows(_id=parts[1], chat_id=chat.id)
            if not rows:
                await q.answer("This button is no longer valid.", show_alert=True)
                return
            row = rows[0]
            kb = ([_apl_decide_buttons(row, chat.id)] if row["status"] == "open" else [])
            kb.append([InlineKeyboardButton(L.t("pick.back", chat.id), callback_data="apb:l:0")])
            await q.answer()
            await _ac_edit(q, (row.get("text") or "") + "\n\n" + _apl_status(row, chat.id), InlineKeyboardMarkup(kb))
        else:
            await q.answer("This button is no longer valid.", show_alert=True)
    except Exception:
        log.exception("appeal: page action failed in %s", chat.id)
        await q.answer(L.t("ac.db_problem", chat.id), show_alert=True)


async def appeal_private(update, context):
    """/appeal in the bot's private chat: lists the groups where this member is muted or has warnings, each with an
    Appeal button (the same deep link as the notice button). Works for a permanent mute whose notice is long gone."""
    msg, user, bot = update.effective_message, update.effective_user, context.bot
    try:
        groups = json.loads(D.get_setting(0, "stats_groups", "{}") or "{}")
    except Exception:
        groups = {}
    rows = []
    for cid_s, title in list(groups.items())[:60]:
        try:
            cid = int(cid_s)
            if cid >= 0 or not appeal_on(cid):
                continue
            member = await bot.get_chat_member(cid, user.id)
            muted = member.status == ChatMemberStatus.RESTRICTED and not getattr(member, "can_send_messages", True)
            warned = bool(await asyncio.to_thread(D.active_warns, cid, user.id))
        except Exception:
            continue
        for kind, on in (("m", muted), ("w", warned)):
            if on and bot.username:
                label = f"{'🔇 Mute' if kind == 'm' else '⚠️ Warning'}: {title or cid_s}"[:60]
                rows.append([InlineKeyboardButton(label, url=f"https://t.me/{bot.username}?start=appeal_{abs(cid)}_{kind}")])
    if not rows:
        await msg.reply_html("You have no mute or warning to appeal in the groups I know (where Appeal is ON).")
        return
    await msg.reply_html("Choose what you want to appeal:", reply_markup=InlineKeyboardMarkup(rows))


async def appeal_cmd(update, context):
    """/appeal  |  /appeal on|off  |  /appeal group|log"""
    if update.effective_chat.type == "private":
        await appeal_private(update, context)
        return
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    arg = context.args[0].lower() if context.args else ""
    if arg in ("on", "off") and appeal_on(chat.id) != (arg == "on"):
        _apl_set(chat.id, "t", None)
    elif arg in APPEAL_DESTS:
        _apl_set(chat.id, "d", arg)
    elif arg and arg not in ("on", "off"):
        await msg.reply_html(L.t("apl.usage", chat.id))
        return
    text, markup = _apl_panel(chat)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


# ------------------------------------------------------------------ the member's side (private chat)
async def appeal_start(update, context):
    """group=-20: /start appeal_<chat>_<m|w>. Any other /start is left alone (nova.py answers it)."""
    msg, user = update.effective_message, update.effective_user
    arg = context.args[0] if context.args else ""
    m = re.fullmatch(r"appeal_(\d+)_([mw])", arg)
    if not m or update.effective_chat.type != "private":
        return
    chat_id, kind = -int(m.group(1)), "mute" if m.group(2) == "m" else "warn"
    try:
        gchat = await context.bot.get_chat(chat_id)
        if not appeal_on(chat_id):
            await msg.reply_html(L.t("apl.dm_off", chat_id))
        else:
            active, ref, _ = await _apl_state(context.bot, chat_id, user.id, kind)
            if not active:
                await msg.reply_html(L.t("apl.dm_none", chat_id, kind=L.t("apl.kind_" + kind, chat_id),
                                         chat=html.escape(gchat.title or "")))
            elif await _apl_rows(chat_id=chat_id, user_id=user.id, kind=kind, status="open"):
                await msg.reply_html(L.t("apl.dm_open", chat_id))
            else:
                _apl_pending[user.id] = (chat_id, kind, ref, time.monotonic() + APPEAL_ASK_TTL)
                await msg.reply_html(L.t("apl.dm_ask", chat_id, chat=html.escape(gchat.title or ""),
                                         kind=L.t("apl.kind_" + kind, chat_id), max=APPEAL_REASON_MAX))
    except TelegramError:
        await msg.reply_html(L.t("apl.dm_invalid", chat_id))
    except Exception:
        log.exception("appeal: start failed for %s in %s", user.id, chat_id)
        await msg.reply_html(L.t("apl.dm_fail", chat_id))
    raise ApplicationHandlerStop


async def appeal_reason(update, context):
    """group=-19, private chat: the reason the member sends (or /skip, /cancel). Does nothing when nothing is pending."""
    msg, user = update.effective_message, update.effective_user
    pend = _apl_pending.get(user.id)
    if pend is None:
        return
    chat_id, kind, ref, until = pend
    text = (msg.text or "").strip()
    if time.monotonic() > until:
        _apl_pending.pop(user.id, None)
        return
    if text.lower().split("@")[0] == "/cancel":
        _apl_pending.pop(user.id, None)
        await msg.reply_html(L.t("apl.dm_cancelled", chat_id))
        raise ApplicationHandlerStop
    if text.startswith("/") and text.lower().split("@")[0] != "/skip":
        return                                             # another command: leave it alone, the wait stays
    reason = "" if text.lower().split("@")[0] == "/skip" else text[:APPEAL_REASON_MAX]
    _apl_pending.pop(user.id, None)
    try:
        ok = await _apl_submit(context.bot, chat_id, user, kind, ref, reason)
    except Exception:
        log.exception("appeal: sending the appeal of %s in %s failed", user.id, chat_id)
        ok = False
    await msg.reply_html(L.t("apl.dm_sent" if ok else "apl.dm_fail", chat_id))
    raise ApplicationHandlerStop


async def myappeals_cmd(update, context):
    """/myappeals in the bot's private chat: the member's own appeals and what became of them."""
    msg, user = update.effective_message, update.effective_user
    rows = (await _apl_rows(user_id=user.id))[:10]
    cid = rows[0]["chat_id"] if rows else None
    if not rows:
        await msg.reply_html(L.t("apl.my_empty"))
        return
    lines = [L.t("apl.my_line", cid, n=i + 1, chat=html.escape(r.get("chat_title") or str(r["chat_id"])),
                 kind=L.t("apl.kind_" + r["kind"], cid), status=L.t("apl.my_st_" + r["status"], cid))
             for i, r in enumerate(rows)]
    await msg.reply_html(L.t("apl.my_title", cid) + "\n\n" + "\n".join(lines))


async def _apl_submit(bot, chat_id, user, kind, ref, reason):
    """Saves the appeal and posts its card: to every admin who started the bot, and to the chosen place. True when
    at least one card went out."""
    active, _, _ = await _apl_state(bot, chat_id, user.id, kind)
    if not active:
        return False
    gchat = await bot.get_chat(chat_id)
    text = L.t("apl.card", chat_id, chat=html.escape(gchat.title or ""), user=user.mention_html(),
               kind=L.t("apl.kind_" + kind, chat_id),
               reason=html.escape(reason) if reason else L.t("apl.no_reason", chat_id))
    row = {"_id": os.urandom(5).hex(), "chat_id": chat_id, "chat_title": gchat.title or "", "user_id": user.id,
           "user_name": getattr(user, "full_name", None) or getattr(user, "first_name", "") or str(user.id),
           "kind": kind, "ref": ref, "reason": reason, "text": text, "cards": [], "status": "open",
           "created_at": time.time()}
    kb = InlineKeyboardMarkup([_apl_decide_buttons(row, chat_id)])

    async def send(to):
        try:
            sent = await bot.send_message(to, text, parse_mode="HTML", reply_markup=kb)
        except TelegramError:
            return False
        row["cards"].append({"chat": to, "id": sent.message_id})
        return True

    try:
        admins = [a.user.id for a in await bot.get_chat_administrators(chat_id) if not a.user.is_bot]
    except TelegramError:
        admins = []
    for admin_id in admins:
        await send(admin_id)                               # always: an admin who never started the bot is skipped
    posted = False
    log_id = D.get_setting(chat_id, "log_channel")
    if appeal_dest(chat_id) == "log" and log_id:
        try:
            posted = await send(int(log_id))
        except ValueError:
            pass
    if not posted:
        await send(chat_id)                                # the group: the default, and the fallback
    if not row["cards"]:
        log.warning("appeal: couldn't post the card in %s", chat_id)
        return False
    await asyncio.to_thread(store.col("appeals").insert_one, row)
    return True


# ------------------------------------------------------------------ the admin's side (the card)
async def apl_callback(update, context):
    """"apl:a:<id>" approves (unmute / remove the warning), "apl:r:<id>" rejects. Admins of the appeal's own group only."""
    q = update.callback_query
    try:
        _, act, appeal_id = (q.data or "").split(":")
        col = store.col("appeals")
        row = await asyncio.to_thread(col.find_one, {"_id": appeal_id})
        chat_id = row["chat_id"] if row else None
        gchat = await context.bot.get_chat(chat_id) if row else None
    except (ValueError, TelegramError):
        row = gchat = None
    if row is None or gchat is None or act not in ("a", "r"):
        await q.answer("This button is no longer valid.", show_alert=True)
        return
    if not await _ac_allowed(gchat, q.from_user.id):
        await q.answer(L.t("apl.card_admin_only", chat_id), show_alert=True)
        return
    new = "approved" if act == "a" else "rejected"
    who = getattr(q.from_user, "full_name", None) or getattr(q.from_user, "first_name", "") or str(q.from_user.id)
    claim = await asyncio.to_thread(col.update_one, {"_id": appeal_id, "status": "open"},
                                    {"$set": {"status": new, "decided_by": q.from_user.id, "decided_name": who,
                                              "decided_at": time.time()}})
    if claim.modified_count != 1:
        await q.answer(L.t("apl.already", chat_id), show_alert=True)
        return
    kind, user_id = row["kind"], row["user_id"]
    if act == "a":
        try:
            if (await _apl_state(context.bot, chat_id, user_id, kind))[0]:
                await _apl_undo(context.bot, row)         # already lifted by someone else: nothing to undo
        except TelegramError as e:
            log.warning("appeal: couldn't undo %s of %s in %s: %s", kind, user_id, chat_id, e)
            await asyncio.to_thread(col.update_one, {"_id": appeal_id}, {"$set": {"status": "open"}})
            await q.answer(L.t("apl.undo_failed", chat_id), show_alert=True)
            return
    await q.answer()
    by = q.from_user.mention_html() if hasattr(q.from_user, "mention_html") else html.escape(who)
    if act == "a":                                         # the mod log: who accepted / rejected the appeal
        await record_undo(chat_id, user_id, row.get("user_name") or str(user_id), "unmute" if kind == "mute" else "unwarn",
                          by, "Appeal accepted")
    else:
        await record_undo(chat_id, user_id, row.get("user_name") or str(user_id), "appeal_no", by,
                          row.get("reason") or None)
    final = (row.get("text") or q.message.text_html) + "\n\n" + L.t("apl.done_" + new, chat_id, admin=html.escape(who))
    here = (q.message.chat.id, q.message.message_id) if q.message else None
    cards = [(c["chat"], c["id"]) for c in row.get("cards", [])]
    for card in cards:                                     # every copy of the card shows the result
        try:
            if card == here:
                await q.edit_message_text(final, parse_mode="HTML", reply_markup=None)
            else:
                await context.bot.edit_message_text(final, chat_id=card[0], message_id=card[1], parse_mode="HTML")
        except TelegramError:
            pass                                           # deleted, or the same text
    if here not in cards:                                  # decided from the Appeal List page
        await _ac_edit(q, final, InlineKeyboardMarkup(
            [[InlineKeyboardButton(L.t("pick.back", chat_id), callback_data="apb:l:0")]]))
    try:
        await context.bot.send_message(user_id, L.t("apl.approved_dm_" + kind if act == "a" else "apl.rejected_dm", chat_id,
                                                    chat=html.escape(gchat.title or "")), parse_mode="HTML")
    except TelegramError:
        pass                                               # the member blocked the bot


async def lift_warn_action(bot, chat_id, user_id):
    """A warning was removed: take the mute / ban it caused back too (unban if banned, unmute if muted). One place for nova's /rmwarn,
    /resetwarns, the Remove warning button and the Appeal."""
    try:
        member = await bot.get_chat_member(chat_id, user_id)
        if member.status == ChatMemberStatus.BANNED:
            await bot.unban_chat_member(chat_id, user_id, only_if_banned=True)
        elif member.status == ChatMemberStatus.RESTRICTED and not getattr(member, "can_send_messages", True):
            await bot.restrict_chat_member(chat_id, user_id, (await bot.get_chat(chat_id)).permissions or D.default_perms)
    except TelegramError as e:
        log.warning("Couldn't lift the action after removing a warning in %s: %s", chat_id, e)


def warn_markup(chat_id, user_id, muted_now, has_warn):
    """The buttons under a /warn notice: Unmute (the warn ladder just muted them) and Remove warning, plus 📩 Appeal when Appeal is ON.
    None when there is nothing to offer."""
    rows = []
    if muted_now:
        rows.append([InlineKeyboardButton(L.t("wn.btn_unmute", chat_id), callback_data=f"unmute:{user_id}")])
    if has_warn:
        rows.append([InlineKeyboardButton(L.t("wn.btn_rmwarn", chat_id), callback_data=f"rmwarn:{user_id}")])
    return appeal_markup(chat_id, user_id, "mute" if muted_now else "warn", InlineKeyboardMarkup(rows)) if rows else None


async def _apl_undo(bot, row):
    """Takes the mute or the warning back, the same way nova's Unmute / Remove warning buttons do."""
    chat_id, user_id = row["chat_id"], row["user_id"]
    if row["kind"] == "mute":
        perms = (await bot.get_chat(chat_id)).permissions or D.default_perms
        await bot.restrict_chat_member(chat_id, user_id, perms)
    elif any(w[0] == row["ref"] for w in await asyncio.to_thread(D.active_warns, chat_id, user_id)):
        await asyncio.to_thread(store.warn_delete, row["ref"])
        await lift_warn_action(bot, chat_id, user_id)      # the warning's mute / ban goes too


# ======================================================================================================
# 2d. WARN LADDER
# ======================================================================================================
# A different action for each warning count, chosen by the admins. NOTHING is set by default.
#   * Saved per group: warn_ladder = "2:tmute:7200,5:kick" (count:action[:seconds], sorted by count) and
#     warn_ladder_on = "on" | "off" (default off).
#   * OFF (or ON with no steps): nova.py's add_warn keeps using /warnlimit + /warnmode, exactly as before.
#   * ON: when a member's active warnings reach a step's count, that step's action is applied. A count without a step
#     gets the plain warning notice. Warnings are KEPT after every step (like Miss Rose): the count keeps growing, and a
#     member who already has more warnings than the last step gets the last step again on every new warning. Warnings go
#     away with /warntime (expiry), /resetwarns or the Remove warning button (which also lifts the mute / ban it caused).
#   * A step is "mute" (permanent), "tmute" (with seconds), "kick" or "ban". Counts 1-50, at most WL_MAX_STEPS steps.
#   * Adding the first step to an empty ladder switches it ON.
#   * Customised from /help > Warnings > 🪜 Warn Ladder, or with /warnladder (see wl_usage in lang.py).
WL_KEY, WL_ON_KEY = "warn_ladder", "warn_ladder_on"
WL_KINDS = ("mute", "tmute", "kick", "ban")
WL_MAX_STEPS = 6
WL_MAX_COUNT = 50
WL_MIN_SECS, WL_MAX_SECS = 60, 365 * 86400      # Telegram treats shorter / longer mutes as permanent
WL_DURATIONS = (900, 1800, 3600, 7200, 21600, 43200, 86400, 259200, 604800, 2592000)   # 15m ... 30d
WL_COUNT_CHOICES = 12                            # warn counts offered as buttons when adding a step


def wl_steps(chat_id):
    """The saved steps as a sorted list of (count, kind, seconds or None). Anything unreadable is ignored."""
    steps = {}
    for part in str(D.get_setting(chat_id, WL_KEY, "") or "").split(","):
        bits = part.strip().split(":")
        try:
            count, kind = int(bits[0]), bits[1]
            secs = int(bits[2]) if len(bits) > 2 else None
        except (ValueError, IndexError):
            continue
        if not 1 <= count <= WL_MAX_COUNT or kind not in WL_KINDS:
            continue
        if kind == "tmute":
            if not secs or not WL_MIN_SECS <= secs <= WL_MAX_SECS:
                continue
        else:
            secs = None
        steps[count] = (count, kind, secs)
    return [steps[c] for c in sorted(steps)][:WL_MAX_STEPS]


def wl_on(chat_id):
    return D.get_setting(chat_id, WL_ON_KEY, "off") == "on"


def wl_active(chat_id):
    """The steps when the ladder is ON, else []. An empty list means: use the normal warn limit and action."""
    return wl_steps(chat_id) if wl_on(chat_id) else []


def _wl_save(chat_id, steps):
    D.set_setting(chat_id, WL_KEY,
                  ",".join(f"{c}:{k}" + (f":{s}" if k == "tmute" else "") for c, k, s in sorted(steps)))


def wl_set_step(chat_id, count, kind, secs=None):
    """Adds the step or changes the action of the step at `count`. Returns None, or \"full\" / \"bad\" when refused."""
    if not 1 <= count <= WL_MAX_COUNT or kind not in WL_KINDS:
        return "bad"
    if kind == "tmute" and not (secs and WL_MIN_SECS <= secs <= WL_MAX_SECS):
        return "bad"
    steps = {s[0]: s for s in wl_steps(chat_id)}
    if count not in steps and len(steps) >= WL_MAX_STEPS:
        return "full"
    was_empty = not steps
    steps[count] = (count, kind, secs if kind == "tmute" else None)
    _wl_save(chat_id, list(steps.values()))
    if was_empty:
        D.set_setting(chat_id, WL_ON_KEY, "on")
    return None


def wl_remove_step(chat_id, count):
    steps = [s for s in wl_steps(chat_id) if s[0] != count]
    _wl_save(chat_id, steps)


def _wl_mode(kind, secs):
    """The mode string nova's do_action understands."""
    return f"tmute:{secs}" if kind == "tmute" else kind


def _wl_mode_en(step):
    """'mute' / 'mute for 2h' / 'kick' / 'ban' as describe_mode() writes them (translated at display time)."""
    _, kind, secs = step
    return f"mute for {extra.fmt_duration(secs)}" if kind == "tmute" else kind


def wl_action_text(kind, secs, chat_id=None, lang=None):
    if kind == "tmute":
        return L.t("wl.d_tmute", chat_id, lang=lang, dur=extra.fmt_duration(secs))
    return L.t("wl.d_" + kind, chat_id, lang=lang)


def wl_summary(chat_id):
    """One line for /limits when the ladder is in use, else None."""
    steps = wl_active(chat_id)
    if not steps:
        return None
    return "Warnings (ladder): " + "; ".join(
        L.t("wl.step_line", lang="en", count=c, action=wl_action_text(k, s, lang="en")) for c, k, s in steps)


def warn_ladder_button(chat):
    """The 🪜 button nova.py adds to /help > Warnings (groups only)."""
    return InlineKeyboardButton(L.t("wl.btn_help", getattr(chat, "id", None)), callback_data="wl:m")


async def ladder_warn(chat, user_id, mention, why, by, count, do_action):
    """Called by nova's add_warn right after a warning is saved (`count` = the member's active warnings now).
    Returns the notice text to announce, or None when the ladder is not in use (add_warn then carries on as before).
    `do_action(chat, user_id, mode)` is nova's own function; `why` is already \"No reason given\" when empty."""
    steps = wl_active(chat.id)
    if not steps:
        return None
    step = next((s for s in steps if s[0] == count), None)
    if step is None and count > steps[-1][0]:
        step = steps[-1]
    if step is None:                                  # between steps: a plain warning
        label = f"Warned (warn {count})"
        nxt = next(s for s in steps if s[0] > count)
        punish = f"Warning {count}: no action yet. At {nxt[0]} warns the action is {_wl_mode_en(nxt)}"
        await extra.record_action(chat.id, user_id, mention, label, why, punish, by, "warn")
        return extra.action_notice(mention, label, why, punish, by, chat_id=chat.id)
    # Warnings are kept after a step (like Miss Rose): the count keeps growing, expires with /warntime, or is cleared by /resetwarns.
    done = await do_action(chat, user_id, _wl_mode(step[1], step[2]))
    if done:
        kind, secs = extra.mode_kind(_wl_mode(step[1], step[2]))
        label = f"{extra.ACTION_LABEL.get(kind, kind.title())} (warn step {step[0]})"
        punish = extra.punishment_text(kind, secs)
        reason = f"Reached {count} warnings. Last warning: {why}"
        await extra.record_action(chat.id, user_id, mention, label, reason, punish, by, "warn")
        return extra.action_notice(mention, label, reason, punish, by, chat_id=chat.id)
    return L.t("wn.step_fail", chat.id, mention=mention, count=count,
               mode=extra._notice_mode(_wl_mode_en(step), chat.id), reason=html.escape(why))


# ------------------------------------------------------------------ the panel
def _wl_back(cid, data="wl:m"):
    return [InlineKeyboardButton(L.t("pick.back", cid), callback_data=data)]


def _wl_panel(chat, note=""):
    cid = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("wl.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    on, steps = wl_on(cid), wl_steps(cid)
    status = L.t("wl.status_off" if not on else ("wl.status_on" if steps else "wl.status_on_empty"), cid)
    lines = [L.t("wl.step_line", cid, count=c, action=wl_action_text(k, s, cid)) for c, k, s in steps]
    text = (L.t("wl.title", cid) + "\n\n" + (note + "\n\n" if note else "") + L.t("wl.intro", cid) + "\n\n" + status + "\n\n" +
            ("\n".join(lines) if lines else L.t("wl.no_steps", cid)) + "\n\n" + L.t("wl.note", cid))
    rows = [[InlineKeyboardButton(L.t("wl.btn_off" if on else "wl.btn_on", cid), callback_data="wl:t")]]
    rows += [[InlineKeyboardButton("✏️ " + line, callback_data=f"wl:s:{c}")] for (c, _, _), line in zip(steps, lines)]
    if len(steps) < WL_MAX_STEPS:
        rows.append([InlineKeyboardButton(L.t("wl.btn_add", cid), callback_data="wl:n")])
    rows.append(_wl_back(cid, "help:warn"))
    return text, InlineKeyboardMarkup(rows)


def _wl_count_panel(cid):
    used = {s[0] for s in wl_steps(cid)}
    free = [c for c in range(1, WL_COUNT_CHOICES + 1) if c not in used]
    text = L.t("wl.new_title", cid) + "\n\n" + L.t("wl.new_hint", cid, max=WL_MAX_COUNT)
    buttons = [InlineKeyboardButton(str(c), callback_data=f"wl:s:{c}") for c in free]
    rows = [buttons[i:i + 4] for i in range(0, len(buttons), 4)] + [_wl_back(cid)]
    return text, InlineKeyboardMarkup(rows)


def _wl_step_panel(cid, count):
    current = next((s for s in wl_steps(cid) if s[0] == count), None)
    now = wl_action_text(current[1], current[2], cid) if current else L.t("wl.step_unset", cid)
    text = L.t("wl.step_title", cid, count=count) + "\n\n" + L.t("wl.step_now", cid, action=now) + "\n\n" + L.t("wl.pick_action", cid)
    mark = lambda kind: "✅ " if current and current[1] == kind else ""
    rows = [[InlineKeyboardButton(mark("mute") + L.t("wl.act_mute", cid), callback_data=f"wl:a:{count}:mute")],
            [InlineKeyboardButton(mark("tmute") + L.t("wl.act_tmute", cid), callback_data=f"wl:d:{count}")],
            [InlineKeyboardButton(mark("kick") + L.t("wl.act_kick", cid), callback_data=f"wl:a:{count}:kick")],
            [InlineKeyboardButton(mark("ban") + L.t("wl.act_ban", cid), callback_data=f"wl:a:{count}:ban")]]
    if current:
        rows.append([InlineKeyboardButton(L.t("wl.btn_remove", cid), callback_data=f"wl:x:{count}")])
    rows.append(_wl_back(cid))
    return text, InlineKeyboardMarkup(rows)


def _wl_dur_panel(cid, count):
    current = next((s for s in wl_steps(cid) if s[0] == count and s[1] == "tmute"), None)
    text = L.t("wl.dur_title", cid, count=count) + "\n\n" + L.t("wl.dur_hint", cid, count=count)
    buttons = [InlineKeyboardButton(("✅ " if current and current[2] == d else "") + extra.fmt_duration(d),
                                    callback_data=f"wl:u:{count}:{d}") for d in WL_DURATIONS]
    rows = [buttons[i:i + 4] for i in range(0, len(buttons), 4)] + [_wl_back(cid, f"wl:s:{count}")]
    return text, InlineKeyboardMarkup(rows)


def _wl_save_note(cid, count, kind, secs):
    """Saves a step and returns the note shown on the panel (or None + error key)."""
    err = wl_set_step(cid, count, kind, secs)
    if err:
        return None, err
    return L.t("wl.t_saved", cid, count=count, action=wl_action_text(kind, secs, cid)), None


async def wl_callback(update, context):
    """\"wl:m\" panel, \"wl:t\" switch, \"wl:n\" pick a count, \"wl:s:<count>\" pick the action, \"wl:a:<count>:<mute|kick|ban>\",
    \"wl:d:<count>\" + \"wl:u:<count>:<seconds>\" timed mute, \"wl:x:<count>\" remove. Admins only, checked on every tap."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    if chat.type == "private":
        await q.answer(L.t("wl.private"), show_alert=True)
        return
    cid = chat.id
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("wl.admin_only", cid), show_alert=True)
        return
    parts = (q.data or "").split(":")[1:]
    act, args = (parts[0] if parts else ""), parts[1:]
    count = _ac_num(args[0], 1, WL_MAX_COUNT) if args else None
    try:
        if act == "m" and not args:
            await q.answer()
            await _ac_edit(q, *_wl_panel(chat))
        elif act == "t" and not args:
            on = not wl_on(cid)
            D.set_setting(cid, WL_ON_KEY, "on" if on else "off")
            await q.answer(L.t("wl.t_on" if on else "wl.t_off", cid))
            await _ac_edit(q, *_wl_panel(chat))
        elif act == "n" and not args:
            if len(wl_steps(cid)) >= WL_MAX_STEPS:
                await q.answer(L.t("wl.t_full", cid, n=WL_MAX_STEPS), show_alert=True)
                return
            await q.answer()
            await _ac_edit(q, *_wl_count_panel(cid))
        elif act in ("s", "d") and count and len(args) == 1:
            if count not in {s[0] for s in wl_steps(cid)} and len(wl_steps(cid)) >= WL_MAX_STEPS:
                await q.answer(L.t("wl.t_full", cid, n=WL_MAX_STEPS), show_alert=True)
                return
            await q.answer()
            await _ac_edit(q, *(_wl_step_panel(cid, count) if act == "s" else _wl_dur_panel(cid, count)))
        elif act == "a" and count and len(args) == 2 and args[1] in ("mute", "kick", "ban"):
            note, err = _wl_save_note(cid, count, args[1], None)
            await q.answer(note if note else L.t("wl.t_full", cid, n=WL_MAX_STEPS), show_alert=bool(err))
            if not err:
                await _ac_edit(q, *_wl_panel(chat))
        elif act == "u" and count and len(args) == 2 and args[1].isascii() and args[1].isdigit() and int(args[1]) in WL_DURATIONS:
            note, err = _wl_save_note(cid, count, "tmute", int(args[1]))
            await q.answer(note if note else L.t("wl.t_full", cid, n=WL_MAX_STEPS), show_alert=bool(err))
            if not err:
                await _ac_edit(q, *_wl_panel(chat))
        elif act == "x" and count and len(args) == 1:
            wl_remove_step(cid, count)
            await q.answer(L.t("wl.t_removed", cid, count=count))
            await _ac_edit(q, *_wl_panel(chat))
        else:
            await q.answer(L.t("wl.invalid", cid), show_alert=True)
    except Exception:
        log.exception("warn ladder: panel action failed in %s", cid)
        await q.answer(L.t("ac.db_problem", cid), show_alert=True)


async def warnladder_cmd(update, context):
    """/warnladder  |  on | off | clear  |  <count> mute|kick|ban  |  <count> tmute <time>  |  remove <count>"""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    cid, args, note = chat.id, [a.lower() for a in (context.args or [])], ""
    try:
        if not args:
            pass
        elif args in (["on"], ["off"]):
            D.set_setting(cid, WL_ON_KEY, args[0])
            note = L.t("wl.t_on" if args[0] == "on" else "wl.t_off", cid)
        elif args == ["clear"]:
            _wl_save(cid, [])
            note = L.t("wl.t_cleared", cid)
        elif len(args) == 2 and args[0] in ("remove", "rm", "del") and _ac_num(args[1], 1, WL_MAX_COUNT):
            count = int(args[1])
            if count not in {s[0] for s in wl_steps(cid)}:
                await msg.reply_html(L.t("wl.err_nostep", cid, count=count))
                return
            wl_remove_step(cid, count)
            note = L.t("wl.t_removed", cid, count=count)
        elif len(args) in (2, 3) and _ac_num(args[0], 1, WL_MAX_COUNT) and args[1] in ("mute", "tmute", "kick", "ban"):
            count, kind, secs = int(args[0]), args[1], None
            if len(args) == 3:
                if kind not in ("mute", "tmute"):
                    raise ValueError("usage")
                secs, kind = extra.parse_duration(args[2]), "tmute"
                if not secs or not WL_MIN_SECS <= secs <= WL_MAX_SECS:
                    await msg.reply_html(L.t("wl.err_dur", cid))
                    return
            elif kind == "tmute":
                await msg.reply_html(L.t("wl.err_dur", cid))
                return
            note, err = _wl_save_note(cid, count, kind, secs)
            if err:
                await msg.reply_html(L.t("wl.t_full", cid, n=WL_MAX_STEPS))
                return
        else:
            raise ValueError("usage")
    except ValueError:
        await msg.reply_html(L.t("wl.usage", cid))
        return
    text, markup = _wl_panel(chat, note)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


# ======================================================================================================
# 2e. MOD LOG
# ======================================================================================================
# The history of what the bot and the admins did in THIS group: bans, kicks, mutes, warnings, unmutes, unbans, removed
# warnings and appeal decisions, each with who did it and why. Rows are written by extra.record_action (nova.py calls
# group.record_undo for the "undo" kinds) and kept 15 days (store.HISTORY_KEEP_DAYS). Rows stay in English; the page
# translates their parts when it shows them (extra.translate_notice), like the action notices.
#   /modlog                the page: filters [All] [Bans] [Kicks] [Mutes] [Warns] [Undone], 6 rows per page
#   /modlog @user | id     the same page for one member (or reply to the member with /modlog)
# Callback data "ml:<filter>:<page>:<member id or 0>"; "ml:s" is the 🔍 Find member help screen.
ML_PAGE = 6
ML_FILTERS = {"a": None, "b": ("ban",), "k": ("kick",), "m": ("mute",), "w": ("warn",),
              "u": ("unmute", "unban", "unwarn")}
ML_ORDER = ("a", "b", "k", "m", "w", "u")
# what: (label, punishment text, category, kind) of the rows record_undo writes. The texts must stay in extra._NOTICE_TEXT.
_ML_UNDO = {"unmute": ("Unmuted", "Mute lifted", "mute", "unmute"),
            "unban": ("Unbanned", "Ban lifted", "ban", "unban"),
            "unwarn": ("Warning removed", "Warning removed", "warn", "unwarn"),
            "reset": ("Warnings reset", "All warnings cleared", "warn", "unwarn"),
            "appeal_no": ("Appeal rejected", "Nothing changed", "appeal", "appeal")}


async def record_undo(chat_id, user_id, name, what, by=None, reason=None):
    """History row for an unmute / unban / removed warning / reset / rejected appeal. `what` is a key of _ML_UNDO,
    `name` and `by` are the same HTML (or plain) text the other history rows use."""
    label, punish, category, kind = _ML_UNDO[what]
    await extra.record_action(chat_id, user_id, name, label, reason or "No reason given", punish, by, category, kind=kind)


def modlog_button(chat):
    """The 📜 Mod Log button nova.py adds to /help > Log Channels (groups only)."""
    return InlineKeyboardButton(L.t("ml.btn_help", getattr(chat, "id", None)), callback_data="ml:a:0:0")


def _ml_text(s, cid, cap):
    """A stored part, translated for the group, cut to `cap` characters and made safe for HTML."""
    s = extra.translate_notice(str(s or ""), cid)
    return html.escape(s[:cap] + ("…" if len(s) > cap else ""))


def _ml_row(row, n, cid):
    when = datetime.fromtimestamp(row.get("ts") or 0, extra.NOTICE_IST).strftime("%d %b %I:%M %p")
    meta = row.get("meta") or {}
    if not meta:                                       # a row saved before the mod log page existed: shown as it was saved
        return L.t("ml.row_old", cid, n=n, when=when, text=html.escape(str(row.get("text") or "")[:300]))
    uid, name = row.get("user_id"), html.escape(meta.get("name") or "")
    user = f"{name} ({uid})" if name and uid and name != str(uid) else (name or str(uid or "?"))
    by = html.escape(meta.get("by") or "") or L.t("ml.by_bot", cid)
    return L.t("ml.row", cid, n=n, when=when, label=_ml_text(meta.get("label"), cid, 80), user=user, by=by,
               reason=_ml_text(meta.get("reason") or "No reason given", cid, 150), punish=_ml_text(meta.get("punish"), cid, 120))


async def _ml_panel(chat, f, page, uid, name=None):
    """(text, keyboard) of the page. `uid` 0 = every member."""
    cid = chat.id
    kinds = ML_FILTERS[f]
    back = [InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:log")]
    try:
        total = await asyncio.to_thread(store.modlog_count, cid, uid or None, kinds)
        pages = max(1, -(-total // ML_PAGE))
        page = min(max(page, 0), pages - 1)
        rows = await asyncio.to_thread(store.modlog_recent, cid, ML_PAGE, user_id=uid or None, kinds=kinds, skip=page * ML_PAGE)
    except Exception:
        log.exception("modlog: couldn't read the history of %s", cid)
        return L.t("ml.err", cid), InlineKeyboardMarkup([back])
    head = L.t("ml.title", cid)
    if uid:
        who = name or next((html.escape((r.get("meta") or {}).get("name") or "") for r in rows if (r.get("meta") or {}).get("name")), "") or str(uid)
        head += "\n" + L.t("ml.member", cid, user=who, id=uid)
    head += "\n" + L.t("ml.showing", cid, what=L.t("ml.f_" + f, cid), page=page + 1, pages=pages, total=total)
    foot = L.t("ml.foot", cid, days=store.HISTORY_KEEP_DAYS)
    lines = [_ml_row(r, page * ML_PAGE + i + 1, cid) for i, r in enumerate(rows)]
    while lines and len(head) + len(foot) + sum(len(x) + 2 for x in lines) > 3900:
        lines.pop()                                    # never let one page go over Telegram's size limit
    body = "\n\n".join(lines) if lines else L.t("ml.empty_user" if uid else "ml.empty", cid)
    text = head + "\n\n" + body + "\n\n" + foot
    kb = [[InlineKeyboardButton(("✅ " if k == f else "") + L.t("ml.f_" + k, cid), callback_data=f"ml:{k}:0:{uid}")
           for k in ML_ORDER[i:i + 3]] for i in (0, 3)]
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀️", callback_data=f"ml:{f}:{page - 1}:{uid}"))
    if page < pages - 1:
        nav.append(InlineKeyboardButton("▶️", callback_data=f"ml:{f}:{page + 1}:{uid}"))
    if nav:
        kb.append(nav)
    kb.append([InlineKeyboardButton(L.t("ml.btn_clear" if uid else "ml.btn_find", cid), callback_data="ml:a:0:0" if uid else "ml:s")])
    kb.append(back)
    return text, InlineKeyboardMarkup(kb)


async def ml_callback(update, context):
    """\"ml:<filter>:<page>:<member id or 0>\" shows a page, \"ml:s\" the Find member screen. Admins only, checked on every tap."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    if chat.type == "private":
        await q.answer(L.t("ml.private"), show_alert=True)
        return
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("ml.admin_only", chat.id), show_alert=True)
        return
    parts = (q.data or "").split(":")[1:]
    try:
        if parts == ["s"]:
            await q.answer()
            await _ac_edit(q, L.t("ml.find", chat.id), InlineKeyboardMarkup(
                [[InlineKeyboardButton(L.t("pick.back", chat.id), callback_data="ml:a:0:0")]]))
        elif (len(parts) == 3 and parts[0] in ML_FILTERS and _ac_num(parts[1], 0, 100000) is not None
              and _ac_num(parts[2], 0, 10 ** 15) is not None):
            await q.answer()
            await _ac_edit(q, *await _ml_panel(chat, parts[0], int(parts[1]), int(parts[2])))
        else:
            await q.answer(L.t("ml.invalid", chat.id), show_alert=True)
    except Exception:
        log.exception("modlog: page action failed in %s", chat.id)
        await q.answer(L.t("ac.db_problem", chat.id), show_alert=True)


async def modlog_command(update, context):
    """/modlog  |  /modlog @user  |  /modlog <id>  |  reply to a member with /modlog   (admins only)"""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    uid, name = 0, None
    if msg.reply_to_message or context.args:
        uid, name = await D.get_target(update, context)   # replies by itself when it can't find the member
        if not uid:
            return
    text, markup = await _ml_panel(chat, "a", 0, uid or 0, name)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


# ======================================================================================================
# 2f. RAID SHIELD  (extends nova.py's AntiRaid: /antiraid, /raidtime, /raidactiontime, /autoantiraid)
# ======================================================================================================
# A raid is on while the group's `raid_until` time is in the future (set by /antiraid or by the join counter). New here:
#   * raid_mode   "ban" (default: every joiner is banned for raid_action_time, exactly as before) | "restrict" (every
#                 joiner is muted until the raid ends) | "lock" (the whole group is closed for everyone until the raid ends)
#   * raid_window seconds the join counter looks back (default 60): /autoantiraid N starts a raid when more than N
#                 people join within it
#   * raid_time   how long a raid lasts. Not set: 6h in ban mode (as before), 30 minutes in restrict / lock mode.
#   * the lift is automatic: "restrict" uses Telegram's own until_date, "lock" is lifted by the 30-second loop
#     (run_once -> _raid_round) or at once by /antiraid off.
#   * NIGHT MODE + AUTO CLOSE: while the lock is on (raid_lock_state = "on") both are put on hold for that group (their
#     rounds skip it) so nothing re-opens it. raid_lock_saved remembers what to give back: a permissions JSON (group was
#     open), "default", "night" (Night Mode was on: its media-off state comes back) or "" (Auto Close or an admin had
#     it closed already: nothing to restore). After the lift the normal rounds catch up on their own.
#   * panel: /help > Raid & Flood > 🛡 Raid Shield (callbacks "rd:..."), or /raidmode, /raidwindow.
RAID_MODE_KEY, RAID_WINDOW_KEY = "raid_mode", "raid_window"
RAID_LOCK_KEY, RAID_LOCK_SAVED_KEY, RAID_MUTED_KEY = "raid_lock_state", "raid_lock_saved", "raid_muted"
RAID_MODES = ("ban", "restrict", "lock")
RAID_TIME_BAN_DEFAULT = 6 * 3600       # the same default nova.py always had
RAID_TIME_SOFT_DEFAULT = 30 * 60       # restrict / lock: a shorter default
RAID_ACTION_DEFAULT = 3600
RAID_MAX_SECS = 30 * 86400
RAID_JOINS = (5, 10, 15, 25)           # auto-start buttons (0 = off)
RAID_WINDOWS = (30, 60, 120, 300)
RAID_DURATIONS = (900, 1800, 3600, 10800, 21600)
RAID_MUTED_MAX = 300                   # joiners remembered per raid, so /antiraid off can free them
_raid_joins = {}                       # chat_id -> recent join times
_raid_notice_at = {}                   # chat_id -> monotonic time of the last "couldn't lock" notice


def _int_setting(chat_id, key, default):
    try:
        return int(D.get_setting(chat_id, key, default) or default)
    except (TypeError, ValueError):
        return default


def raid_mode(chat_id):
    mode = D.get_setting(chat_id, RAID_MODE_KEY, "ban")
    return mode if mode in RAID_MODES else "ban"


def raid_window(chat_id):
    secs = _int_setting(chat_id, RAID_WINDOW_KEY, 60)
    return secs if 10 <= secs <= 3600 else 60


def raid_default_secs(chat_id):
    return RAID_TIME_BAN_DEFAULT if raid_mode(chat_id) == "ban" else RAID_TIME_SOFT_DEFAULT


def raid_secs(chat_id):
    """How long a raid lasts: the saved /raidtime, else the default of the current mode."""
    default = raid_default_secs(chat_id)
    secs = _int_setting(chat_id, "raid_time", default)
    return secs if 60 <= secs <= RAID_MAX_SECS else default


def _window_text(secs, chat_id=None):
    if secs == 60:
        return L.t("rd.w_min1", chat_id)
    return L.t("rd.w_mins", chat_id, n=secs // 60) if secs % 60 == 0 else L.t("rd.w_secs", chat_id, n=secs)


def _parse_secs(text, low, high):
    """'30s', '5m', '2h' ... in seconds, or None when it is not a time between `low` and `high` seconds."""
    m = re.fullmatch(r"(\d{1,6})\s*s", str(text).strip().lower())
    secs = int(m.group(1)) if m else extra.parse_duration(str(text).lower())
    return secs if secs and low <= secs <= high else None


def _parse_window(text):
    return _parse_secs(text, 10, 3600)


def raid_button(chat):
    """The 🛡 button nova.py adds to /help > Raid & Flood (groups only)."""
    return InlineKeyboardButton(L.t("rd.btn_help", getattr(chat, "id", None)), callback_data="rd:m")


async def _raid_fail(bot, chat_id, what, exc):
    _retry_at[(chat_id, what)] = time.monotonic() + RETRY_AFTER
    log.warning("raid shield: couldn't %s %s: %s: %s", what, chat_id, type(exc).__name__, exc)
    last = _raid_notice_at.get(chat_id)
    if last is not None and time.monotonic() - last < NOTICE_EVERY:
        return
    _raid_notice_at[chat_id] = time.monotonic()
    try:
        await bot.send_message(chat_id, L.t("rd.fail", chat_id, label=L.t("rd.lbl_" + what.replace("-", "_"), chat_id)))
    except TelegramError:
        pass


# ------------------------------------------------------------------ lock / unlock the group
async def raid_lock(bot, chat_id):
    """Closes the group for the raid. Returns True when it is locked (or already closed by Auto Close / an admin)."""
    if D.get_setting(chat_id, RAID_LOCK_KEY, "") == "on":
        return True
    saved = ""
    try:
        if D.get_setting(chat_id, STATE_KEY, "open") != "closed":          # Auto Close has it closed: nothing to do
            chat = await bot.get_chat(chat_id)
            perms = getattr(chat, "permissions", None)
            if perms is None or getattr(perms, "can_send_messages", True) is not False:   # not closed by hand either
                night_on = D.get_setting(chat_id, NIGHT_STATE_KEY, "") == "on"
                saved = "night" if night_on else (_saved_perms(chat) or "default")
                await bot.set_chat_permissions(chat_id, CLOSED_PERMS)
    except TelegramError as e:
        await _raid_fail(bot, chat_id, "lock", e)
        return False
    D.set_setting(chat_id, RAID_LOCK_SAVED_KEY, saved)
    D.set_setting(chat_id, RAID_LOCK_KEY, "on")
    return True


async def raid_unlock(bot, chat_id):
    """Gives the group back as it was, tells the group. Returns True when it is done (or was not locked)."""
    if D.get_setting(chat_id, RAID_LOCK_KEY, "") != "on":
        return True
    saved = D.get_setting(chat_id, RAID_LOCK_SAVED_KEY, "") or ""
    perms = None
    if saved == "night":                                                  # Night Mode was on: media stays off
        perms = None if D.get_setting(chat_id, NIGHT_SAVED_KEY, "") == NIGHT_PASSIVE else _night_variant(_night_saved_perms(chat_id))
    elif saved == "default":
        perms = D.default_perms
    elif saved:
        try:
            perms = ChatPermissions(**json.loads(saved))
        except (TypeError, ValueError):
            perms = D.default_perms
        if perms.can_send_messages is False:                              # never give back a closed state
            perms = D.default_perms
    if perms is not None:
        try:
            await _set_perms(bot, chat_id, perms)
        except TelegramError as e:
            await _raid_fail(bot, chat_id, "raid-end", e)
            return False                                                  # the state stays on: the loop tries again
    store.del_setting(chat_id, RAID_LOCK_KEY)
    store.del_setting(chat_id, RAID_LOCK_SAVED_KEY)
    try:
        await bot.send_message(chat_id, L.t("rd.lock_end", chat_id), parse_mode="HTML")
    except TelegramError:
        pass
    return True


def _raid_muted_ids(chat_id):
    return [int(x) for x in str(D.get_setting(chat_id, RAID_MUTED_KEY, "") or "").split(",") if x.strip().isdigit()]


def _raid_muted_add(chat_id, user_id):
    ids = [i for i in _raid_muted_ids(chat_id) if i != user_id] + [user_id]
    D.set_setting(chat_id, RAID_MUTED_KEY, ",".join(str(i) for i in ids[-RAID_MUTED_MAX:]))


async def _raid_lift_muted(bot, chat_id):
    """Frees the joiners muted by the raid (when it is stopped early; otherwise Telegram lifts them by itself)."""
    for uid in _raid_muted_ids(chat_id):
        try:
            await bot.restrict_chat_member(chat_id, uid, D.default_perms)
        except TelegramError as e:
            log.debug("raid shield: couldn't free %s in %s: %s", uid, chat_id, e)
        await asyncio.sleep(0.05)
    store.del_setting(chat_id, RAID_MUTED_KEY)


async def raid_started(bot, chat):
    """nova.py calls this right after it switched a raid ON (/antiraid, or the join counter). Lock mode closes the group."""
    return await raid_lock(bot, chat.id) if raid_mode(chat.id) == "lock" else True


async def raid_stopped(bot, chat):
    """nova.py calls this after /antiraid off: lifts the lock and frees the muted joiners."""
    await raid_unlock(bot, chat.id)
    await _raid_lift_muted(bot, chat.id)


async def _raid_round(bot):
    """Part of run_once (every 30 seconds): lifts the lock of every group whose raid is over."""
    for chat_id, value in await asyncio.to_thread(_scheduled_groups, RAID_LOCK_KEY):
        try:
            if value == "on" and not D.raid_left(chat_id) and time.monotonic() >= _retry_at.get((chat_id, "raid-end"), 0):
                await raid_unlock(bot, chat_id)
        except Exception:
            log.exception("raid shield: lifting the lock failed in %s", chat_id)
    for chat_id, value in await asyncio.to_thread(_scheduled_groups, RAID_MUTED_KEY):
        if value and not D.raid_left(chat_id):                           # Telegram already lifted them: forget the list
            store.del_setting(chat_id, RAID_MUTED_KEY)


# ------------------------------------------------------------------ the joins
async def _raid_record(chat, user, mode):
    ban = mode == "ban"
    await extra.record_action(chat.id, user.id, user.mention_html() if hasattr(user, "mention_html") else str(user.id),
                              "Banned (raid)" if ban else "Muted (raid)", "Joined during a raid",
                              "Temporary ban" if ban else "Muted until the raid ends", None, "ban" if ban else "mute",
                              kind="ban" if ban else "mute")


async def raid_new_members(update, context):
    """group=-9 (nova registers it), before the captcha / welcome handler: counts the joins, starts the raid by itself
    and, while it lasts, bans (default) or mutes the joiners; in lock mode the group is closed instead. Never touches
    bots, admins, the bot owner or members an admin added."""
    chat, msg = update.effective_chat, update.effective_message
    people = [u for u in (msg.new_chat_members or []) if not u.is_bot]
    if not people:
        return
    now = time.time()
    limit = _int_setting(chat.id, "auto_raid", 0)
    if limit:
        window = raid_window(chat.id)
        recent = [t for t in _raid_joins.get(chat.id, []) if now - t < window] + [now] * len(people)
        _raid_joins[chat.id] = recent
        if len(recent) > limit and not D.raid_left(chat.id):
            secs, mode = raid_secs(chat.id), raid_mode(chat.id)
            D.set_setting(chat.id, "raid_until", int(now) + secs)
            await raid_started(context.bot, chat)
            try:
                await chat.send_message(L.t("rd.detected_" + mode, chat.id, limit=limit, window=_window_text(window, chat.id),
                                            dur=extra.fmt_duration(secs)))
            except TelegramError:
                pass
    if not D.raid_left(chat.id):
        return
    mode = raid_mode(chat.id)
    if mode == "lock":
        return                                    # nobody is banned or muted: the group is closed for everyone
    until = _int_setting(chat.id, "raid_until", 0)
    act = _int_setting(chat.id, "raid_action_time", RAID_ACTION_DEFAULT)
    done = 0
    for user in people:
        if D.is_bot_owner(user.id) or await D.is_admin(chat, user.id):
            continue
        if msg.from_user and msg.from_user.id != user.id and await D.is_admin(chat, msg.from_user.id):
            continue                              # an admin added them on purpose
        try:
            if mode == "ban":
                await chat.ban_member(user.id, until_date=int(now) + max(act, 60))
            else:
                await chat.restrict_member(user.id, CLOSED_PERMS, until_date=max(until, int(now) + 60))
                _raid_muted_add(chat.id, user.id)
        except TelegramError as e:
            log.warning("antiraid: couldn't %s %s in %s: %s", "ban" if mode == "ban" else "mute", user.id, chat.id, e)
            continue
        done += 1
        await _raid_record(chat, user, mode)
    if done:
        try:
            await msg.delete()
        except TelegramError:
            pass
        if done == len(people):
            raise ApplicationHandlerStop          # nobody left to welcome or verify


# ------------------------------------------------------------------ the panel
def _rd_panel(chat, note=""):
    cid = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("rd.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    mode, left = raid_mode(cid), D.raid_left(cid)
    limit, window = _int_setting(cid, "auto_raid", 0), raid_window(cid)
    act = _int_setting(cid, "raid_action_time", RAID_ACTION_DEFAULT)
    text = (L.t("rd.title", cid) + "\n\n" + (note + "\n\n" if note else "") + L.t("rd.intro", cid) + "\n\n" +
            (L.t("rd.status_on", cid, dur=extra.fmt_duration(left)) if left else L.t("rd.status_off", cid)) + "\n" +
            (L.t("rd.auto_on", cid, n=limit, window=_window_text(window, cid)) if limit else L.t("rd.auto_off", cid)) + "\n" +
            L.t("rd.mode_line", cid, mode=L.t("rd.mode_" + mode, cid, act=extra.fmt_duration(act))) + "\n" +
            L.t("rd.dur_line", cid, dur=extra.fmt_duration(raid_secs(cid))) + "\n\n" + L.t("rd.legend", cid) + "\n\n" + L.t("rd.note", cid))
    mark = lambda cond: "✅ " if cond else ""
    rows = [[InlineKeyboardButton(L.t("rd.btn_stop" if left else "rd.btn_start", cid), callback_data="rd:g")],
            [InlineKeyboardButton(mark(mode == m) + L.t("rd.btn_" + m, cid), callback_data=f"rd:o:{m}") for m in RAID_MODES],
            [InlineKeyboardButton(mark(limit == n) + "👥 " + (str(n) if n else L.t("rd.off", cid)), callback_data=f"rd:j:{n}")
             for n in (0,) + RAID_JOINS],
            [InlineKeyboardButton(mark(window == w) + "⏱ " + extra.fmt_duration(w), callback_data=f"rd:w:{w}") for w in RAID_WINDOWS],
            [InlineKeyboardButton(mark(raid_secs(cid) == d) + "⌛ " + extra.fmt_duration(d), callback_data=f"rd:t:{d}")
             for d in RAID_DURATIONS],
            [InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:flood")]]
    return text, InlineKeyboardMarkup(rows)


async def _rd_set_mode(bot, chat, mode):
    old = raid_mode(chat.id)
    D.set_setting(chat.id, RAID_MODE_KEY, mode)
    if D.raid_left(chat.id) and old != mode:                  # a raid is on right now: follow the new mode
        if mode == "lock":
            await raid_lock(bot, chat.id)
        elif old == "lock":
            await raid_unlock(bot, chat.id)


async def rd_callback(update, context):
    """\"rd:m\" panel, \"rd:g\" start / stop now, \"rd:o:<mode>\", \"rd:j:<joins or 0>\", \"rd:w:<seconds>\", \"rd:t:<seconds>\".
    Admins only, checked on every tap."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    if chat.type == "private":
        await q.answer(L.t("rd.private"), show_alert=True)
        return
    cid = chat.id
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("rd.admin_only", cid), show_alert=True)
        return
    parts = (q.data or "").split(":")[1:]
    act, arg = (parts[0] if parts else ""), (parts[1] if len(parts) == 2 else None)
    num = _ac_num(arg, 0, 100000) if arg is not None else None
    toast = None
    try:
        if act == "m" and arg is None and len(parts) == 1:
            pass
        elif act == "g" and arg is None and len(parts) == 1:
            if D.raid_left(cid):
                D.set_setting(cid, "raid_until", 0)
                await raid_stopped(context.bot, chat)
                toast = L.t("rd.t_stopped", cid)
            else:
                secs = raid_secs(cid)
                D.set_setting(cid, "raid_until", int(time.time()) + secs)
                await raid_started(context.bot, chat)
                toast = L.t("rd.t_started", cid, dur=extra.fmt_duration(secs))
        elif act == "o" and arg in RAID_MODES:
            await _rd_set_mode(context.bot, chat, arg)
            toast = L.t("rd.t_mode", cid, mode=L.t("rd.btn_" + arg, cid))
        elif act == "j" and num is not None and (num == 0 or num in RAID_JOINS):
            D.set_setting(cid, "auto_raid", num)
            toast = L.t("rd.t_joins", cid, n=num) if num else L.t("rd.t_joins_off", cid)
        elif act == "w" and num in RAID_WINDOWS:
            D.set_setting(cid, RAID_WINDOW_KEY, num)
            toast = L.t("rd.t_window", cid, window=_window_text(num, cid))
        elif act == "t" and num in RAID_DURATIONS:
            D.set_setting(cid, "raid_time", num)
            toast = L.t("rd.t_dur", cid, dur=extra.fmt_duration(num))
        else:
            await q.answer(L.t("rd.invalid", cid), show_alert=True)
            return
        await q.answer(toast)
        await _ac_edit(q, *_rd_panel(chat))
    except Exception:
        log.exception("raid shield: panel action failed in %s", cid)
        await q.answer(L.t("ac.db_problem", cid), show_alert=True)


async def raidmode_cmd(update, context):
    """/raidmode  |  /raidmode ban|restrict|lock"""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    note = ""
    if context.args:
        mode = context.args[0].lower()
        if mode not in RAID_MODES or len(context.args) != 1:
            await msg.reply_html(L.t("rd.err_mode", chat.id))
            return
        await _rd_set_mode(context.bot, chat, mode)
        note = L.t("rd.t_mode", chat.id, mode=L.t("rd.btn_" + mode, chat.id))
    text, markup = _rd_panel(chat, note)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


async def raidwindow_cmd(update, context):
    """/raidwindow  |  /raidwindow 30s | 2m   (how far back the join counter looks)"""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    note = ""
    if context.args:
        secs = _parse_window(" ".join(context.args))
        if secs is None:
            await msg.reply_html(L.t("rd.err_window", chat.id))
            return
        D.set_setting(chat.id, RAID_WINDOW_KEY, secs)
        note = L.t("rd.t_window", chat.id, window=_window_text(secs, chat.id))
    text, markup = _rd_panel(chat, note)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


# ======================================================================================================
# 2g. NEW-MEMBER PROBATION
# ======================================================================================================
# New members can't send links / media / stickers / forwards for their first hours or their first messages. It reuses
# nova's lock engine (find_violation + the allowlist + lock_exempt), so allowlisted links stay allowed and admins,
# approved members and the bot owner are never touched.
#   * settings: prob "on"|"off" (default off), prob_hours (seconds, 0 = not used, default 24h), prob_msgs (0 = not used),
#     prob_block (which of links, media, stickers, forwards; default "links,media"), prob_notice "on"|"off" (default on).
#   * it ends at whichever limit comes FIRST (time or messages). Only messages that are allowed count.
#   * a record {joined, count} per member lives in the "probation" collection (store.probation_*). It is created when
#     the member joins (handler group -8) or when an admin runs `/probation start`; it is removed when probation ends.
#     Members who were already in the group when probation was switched on are not affected.
#   * the guard (handler group -10) runs before the locks, flood and spam handlers: a blocked message is deleted, the
#     member gets a short notice (deleted by itself after 15 seconds) and no other handler sees the message.
#   * panel: /help > Locks > 🆕 New Member Probation (callbacks "pb:..."), or /probation.
PB_KEY, PB_HOURS_KEY, PB_MSGS_KEY, PB_BLOCK_KEY, PB_NOTICE_KEY = "prob", "prob_hours", "prob_msgs", "prob_block", "prob_notice"
PB_BLOCKS = {"links": ("links", "invitelinks", "stickerpack"), "media": ("media",), "stickers": ("stickers",),
             "forwards": ("forwards",)}               # block name -> nova lock names
PB_BLOCK_ORDER = tuple(PB_BLOCKS)
PB_BLOCK_DEFAULT = ("links", "media")
PB_HOURS_DEFAULT = 86400
PB_HOURS = (3600, 21600, 43200, 86400, 259200, 604800)    # panel presets (the command takes any time up to 30 days)
PB_MSGS = (3, 5, 10, 20)
PB_MAX_SECS, PB_MAX_MSGS = 30 * 86400, 1000
PB_NOTICE_SECS = 15
_pb_cache = {}          # (chat_id, user_id) -> (record or None, monotonic time loaded)
_pb_notice_at = {}      # (chat_id, user_id) -> monotonic time of the last notice to that member
_pb_nodelete_at = {}    # chat_id -> monotonic time of the last "I can't delete" notice
PB_NONE_TTL, PB_CACHE_MAX, PB_NOTICE_EVERY = 600, 20000, 30


class _Args:
    """Stand-in `context` for nova's get_target: it only reads .args and .bot."""
    def __init__(self, args, bot):
        self.args, self.bot = list(args), bot


def _num_setting(chat_id, key, default):
    raw = D.get_setting(chat_id, key, None)
    if raw is None or raw == "":
        return default
    try:
        return int(raw)
    except (TypeError, ValueError):
        return default


def pb_on(chat_id):
    return D.get_setting(chat_id, PB_KEY, "off") == "on"


def pb_hours(chat_id):
    secs = _num_setting(chat_id, PB_HOURS_KEY, PB_HOURS_DEFAULT)
    return secs if 0 <= secs <= PB_MAX_SECS else PB_HOURS_DEFAULT


def pb_msgs(chat_id):
    n = _num_setting(chat_id, PB_MSGS_KEY, 0)
    return n if 0 <= n <= PB_MAX_MSGS else 0


def pb_blocks(chat_id):
    raw = D.get_setting(chat_id, PB_BLOCK_KEY, None)
    if raw is None:
        return PB_BLOCK_DEFAULT
    return tuple(b for b in PB_BLOCK_ORDER if b in str(raw).split(","))


def pb_locks(chat_id):
    """The nova lock names probation applies to in this group."""
    return {lock for b in pb_blocks(chat_id) for lock in PB_BLOCKS[b]}


def probation_button(chat):
    """The 🆕 button nova.py adds to /help > Locks (groups only)."""
    return InlineKeyboardButton(L.t("pb.btn_help", getattr(chat, "id", None)), callback_data="pb:p")


def _pb_state(chat_id, rec, now):
    """(still on probation, seconds left or None, messages left or None) for a record."""
    hours, msgs = pb_hours(chat_id), pb_msgs(chat_id)
    if not hours and not msgs:
        return False, None, None
    left_t = hours - (now - rec["joined"]) if hours else None
    left_m = msgs - rec["count"] if msgs else None
    over = (left_t is not None and left_t <= 0) or (left_m is not None and left_m <= 0)
    return (not over), left_t, left_m


async def _pb_record(chat_id, user_id):
    key, now = (chat_id, user_id), time.monotonic()
    hit = _pb_cache.get(key)
    if hit and (hit[0] is not None or now - hit[1] < PB_NONE_TTL):
        return hit[0]
    rec = await asyncio.to_thread(store.probation_get, chat_id, user_id)
    if len(_pb_cache) > PB_CACHE_MAX:
        _pb_cache.clear()
    _pb_cache[key] = (rec, now)
    return rec


async def _pb_begin(chat_id, user_id):
    now = int(time.time())
    await asyncio.to_thread(store.probation_start, chat_id, user_id, now)
    _pb_cache[(chat_id, user_id)] = ({"joined": now, "count": 0}, time.monotonic())


async def _pb_finish(chat_id, user_id):
    """Probation is over (or an admin ended it). Returns True when the member was on probation."""
    _pb_cache[(chat_id, user_id)] = (None, time.monotonic())
    return await asyncio.to_thread(store.probation_end, chat_id, user_id)


def _pb_when(chat_id, left_t, left_m):
    dur = extra.fmt_duration(max(60, -(-int(left_t) // 60) * 60)) if left_t is not None else None   # rounded up to whole minutes
    if dur and left_m is not None:
        return L.t("pb.when_both", chat_id, dur=dur, n=left_m)
    return L.t("pb.when_time", chat_id, dur=dur) if dur else L.t("pb.when_msgs", chat_id, n=left_m)


async def probation_new_members(update, context):
    """group=-8 (a service message: nobody else uses this group for one): a new member starts probation."""
    chat, msg = update.effective_chat, update.effective_message
    if not pb_on(chat.id):
        return
    for user in msg.new_chat_members or []:
        if not user.is_bot:
            await _pb_begin(chat.id, user.id)


async def probation_guard(update, context):
    """group=-10, before the locks, flood and spam handlers: deletes what a member on probation may not send yet."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or chat.type == "private" or not pb_on(chat.id):
        return                                          # (settings are cached in memory: no Telegram or database call)
    if D.is_service_message(msg) or D.is_paused(chat.id):
        return
    rec = await _pb_record(chat.id, user.id)
    if rec is None:
        return
    on, left_t, left_m = _pb_state(chat.id, rec, time.time())
    if not on:
        await _pb_finish(chat.id, user.id)
        return
    if await D.lock_exempt(chat, msg, user, context.bot.id):   # admins, approved members, the bot owner: trusted
        await _pb_finish(chat.id, user.id)
        return
    name = D.find_violation(msg, pb_locks(chat.id), D.load_allow(chat.id)) if pb_locks(chat.id) else None
    if not name:                                        # an allowed message counts towards the message limit
        rec["count"] += 1
        await asyncio.to_thread(store.probation_add_message, chat.id, user.id)
        if pb_msgs(chat.id) and rec["count"] >= pb_msgs(chat.id):
            await _pb_finish(chat.id, user.id)
        return
    try:
        await msg.delete()
    except TelegramError as e:
        log.warning("probation: couldn't delete in chat %s: %s: %s", chat.id, type(e).__name__, e)
        if time.monotonic() - _pb_nodelete_at.get(chat.id, -1e9) > 600:
            _pb_nodelete_at[chat.id] = time.monotonic()
            try:
                await chat.send_message(L.t("pb.no_delete", chat.id))
            except TelegramError:
                pass
        return
    key = (chat.id, user.id)
    if D.get_setting(chat.id, PB_NOTICE_KEY, "on") == "on" and time.monotonic() - _pb_notice_at.get(key, -1e9) > PB_NOTICE_EVERY:
        _pb_notice_at[key] = time.monotonic()
        kind = next((b for b, locks in PB_BLOCKS.items() if name in locks), "links")
        try:
            sent = await chat.send_message(L.t("pb.notice", chat.id, user=user.mention_html(), what=L.t("pb.w_" + kind, chat.id),
                                               when=_pb_when(chat.id, left_t, left_m)), parse_mode="HTML")
            await extra.track_notice(sent, PB_NOTICE_SECS)
        except TelegramError:
            pass
    raise ApplicationHandlerStop                        # nothing else acts on a deleted message


# ------------------------------------------------------------------ the panel
async def _pb_panel(chat, note=""):
    cid = chat.id
    if chat.type == "private":
        return L.t("pb.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    on, hours, msgs, blocks = pb_on(cid), pb_hours(cid), pb_msgs(cid), pb_blocks(cid)
    try:
        total = await asyncio.to_thread(store.probation_total, cid)
    except Exception:
        total = 0
    if hours and msgs:
        rule = L.t("pb.rule_both", cid, dur=extra.fmt_duration(hours), n=msgs)
    elif hours:
        rule = L.t("pb.rule_time", cid, dur=extra.fmt_duration(hours))
    elif msgs:
        rule = L.t("pb.rule_msgs", cid, n=msgs)
    else:
        rule = L.t("pb.rule_none", cid)
    text = (L.t("pb.title", cid) + "\n\n" + (note + "\n\n" if note else "") + L.t("pb.intro", cid) + "\n\n" +
            L.t("pb.status_on" if on else "pb.status_off", cid) + "\n" + rule + "\n" +
            L.t("pb.blocked", cid, what=", ".join(L.t("pb.b_" + b, cid) for b in blocks) or L.t("pb.nothing", cid)) + "\n" +
            L.t("pb.notice_on" if D.get_setting(cid, PB_NOTICE_KEY, "on") == "on" else "pb.notice_off", cid) + "\n" +
            L.t("pb.total", cid, n=total) + "\n\n" + L.t("pb.legend", cid) + "\n\n" + L.t("pb.note", cid))
    mark = lambda cond: "✅ " if cond else ""
    hour_btns = [InlineKeyboardButton(mark(hours == h) + "⌛ " + (extra.fmt_duration(h) if h else L.t("pb.off", cid)), callback_data=f"pb:h:{h}")
                 for h in (0,) + PB_HOURS]
    msg_btns = [InlineKeyboardButton(mark(msgs == n) + "✉️ " + (str(n) if n else L.t("pb.off", cid)), callback_data=f"pb:c:{n}")
                for n in (0,) + PB_MSGS]
    rows = [[InlineKeyboardButton(L.t("pb.btn_off" if on else "pb.btn_on", cid), callback_data="pb:t")],
            hour_btns[:4], hour_btns[4:], msg_btns,
            [InlineKeyboardButton(mark(b in blocks) + L.t("pb.b_" + b, cid), callback_data=f"pb:b:{b}") for b in PB_BLOCK_ORDER],
            [InlineKeyboardButton(L.t("pb.btn_notice_off" if D.get_setting(cid, PB_NOTICE_KEY, "on") == "on" else "pb.btn_notice_on", cid),
                                  callback_data="pb:n")],
            [InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:locks")]]
    return text, InlineKeyboardMarkup(rows)


async def pb_callback(update, context):
    """\"pb:p\" panel, \"pb:t\" on/off, \"pb:h:<seconds or 0>\", \"pb:c:<messages or 0>\", \"pb:b:<links|media|stickers|forwards>\",
    \"pb:n\" notice on/off. Admins only, checked on every tap."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    if chat.type == "private":
        await q.answer(L.t("pb.private"), show_alert=True)
        return
    cid = chat.id
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("pb.admin_only", cid), show_alert=True)
        return
    parts = (q.data or "").split(":")[1:]
    act, arg = (parts[0] if parts else ""), (parts[1] if len(parts) == 2 else None)
    num = _ac_num(arg, 0, 10 ** 7) if arg is not None else None
    toast = None
    try:
        if act == "p" and len(parts) == 1:
            pass
        elif act == "t" and len(parts) == 1:
            if pb_on(cid):
                D.set_setting(cid, PB_KEY, "off")
                toast = L.t("pb.t_off", cid)
            else:
                if not pb_hours(cid) and not pb_msgs(cid):
                    D.set_setting(cid, PB_HOURS_KEY, PB_HOURS_DEFAULT)
                D.set_setting(cid, PB_KEY, "on")
                toast = L.t("pb.t_on", cid)
        elif act == "h" and num is not None and (num == 0 or num in PB_HOURS):
            if num == 0 and not pb_msgs(cid):
                await q.answer(L.t("pb.t_keep_one", cid), show_alert=True)
                return
            D.set_setting(cid, PB_HOURS_KEY, num)
            toast = L.t("pb.t_hours", cid, dur=extra.fmt_duration(num)) if num else L.t("pb.t_hours_off", cid)
        elif act == "c" and num is not None and (num == 0 or num in PB_MSGS):
            if num == 0 and not pb_hours(cid):
                await q.answer(L.t("pb.t_keep_one", cid), show_alert=True)
                return
            D.set_setting(cid, PB_MSGS_KEY, num)
            toast = L.t("pb.t_msgs", cid, n=num) if num else L.t("pb.t_msgs_off", cid)
        elif act == "b" and arg in PB_BLOCKS:
            blocks = set(pb_blocks(cid)) ^ {arg}
            if not blocks:
                await q.answer(L.t("pb.t_keep_block", cid), show_alert=True)
                return
            D.set_setting(cid, PB_BLOCK_KEY, ",".join(b for b in PB_BLOCK_ORDER if b in blocks))
            toast = L.t("pb.t_block", cid)
        elif act == "n" and len(parts) == 1:
            now_on = D.get_setting(cid, PB_NOTICE_KEY, "on") == "on"
            D.set_setting(cid, PB_NOTICE_KEY, "off" if now_on else "on")
            toast = L.t("pb.t_notice_off" if now_on else "pb.t_notice_on", cid)
        else:
            await q.answer(L.t("pb.invalid", cid), show_alert=True)
            return
        await q.answer(toast)
        await _ac_edit(q, *await _pb_panel(chat))
    except Exception:
        log.exception("probation: panel action failed in %s", cid)
        await q.answer(L.t("ac.db_problem", cid), show_alert=True)


async def probation_cmd(update, context):
    """/probation  |  on | off  |  hours <time|off>  |  msgs <number|off>  |  start | end | status (reply to a member, @user or id)"""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    cid, args, note = chat.id, [a.lower() for a in (context.args or [])], ""
    if not args:
        pass
    elif args in (["on"], ["off"]):
        if args[0] == "on" and not pb_hours(cid) and not pb_msgs(cid):
            D.set_setting(cid, PB_HOURS_KEY, PB_HOURS_DEFAULT)
        D.set_setting(cid, PB_KEY, args[0])
        note = L.t("pb.t_on" if args[0] == "on" else "pb.t_off", cid)
    elif args[0] == "hours" and len(args) == 2:
        secs = 0 if args[1] == "off" else extra.parse_duration(args[1])
        if secs is None or not 0 <= secs <= PB_MAX_SECS or (secs and secs < 60):
            await msg.reply_html(L.t("pb.err_hours", cid))
            return
        if not secs and not pb_msgs(cid):
            await msg.reply_html(L.t("pb.t_keep_one", cid))
            return
        D.set_setting(cid, PB_HOURS_KEY, secs)
        note = L.t("pb.t_hours", cid, dur=extra.fmt_duration(secs)) if secs else L.t("pb.t_hours_off", cid)
    elif args[0] in ("msgs", "messages") and len(args) == 2:
        n = 0 if args[1] == "off" else (_ac_num(args[1], 1, PB_MAX_MSGS) or None)
        if n is None:
            await msg.reply_html(L.t("pb.err_msgs", cid, max=PB_MAX_MSGS))
            return
        if not n and not pb_hours(cid):
            await msg.reply_html(L.t("pb.t_keep_one", cid))
            return
        D.set_setting(cid, PB_MSGS_KEY, n)
        note = L.t("pb.t_msgs", cid, n=n) if n else L.t("pb.t_msgs_off", cid)
    elif args[0] in ("start", "end", "status"):
        sub = _Args(args=context.args[1:], bot=context.bot)         # get_target reads the member from the arguments after the word
        uid, name = await D.get_target(update, sub)
        if not uid:
            return
        if args[0] == "start":
            if D.is_bot_owner(uid) or await D.is_admin(chat, uid):
                await msg.reply_html(L.t("pb.err_admin", cid))
                return
            await _pb_begin(cid, uid)
            await msg.reply_html(L.t("pb.m_started", cid, user=name))
        elif args[0] == "end":
            await msg.reply_html(L.t("pb.m_ended" if await _pb_finish(cid, uid) else "pb.m_not_on", cid, user=name))
        else:
            rec = await _pb_record(cid, uid)
            on, left_t, left_m = _pb_state(cid, rec, time.time()) if rec else (False, None, None)
            await msg.reply_html(L.t("pb.m_status_on", cid, user=name, when=_pb_when(cid, left_t, left_m)) if on
                                 else L.t("pb.m_not_on", cid, user=name))
        return
    else:
        await msg.reply_html(L.t("pb.usage", cid))
        return
    text, markup = await _pb_panel(chat, note)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


# ======================================================================================================
# 2h. REPORTS  (extends nova.py's /report and "@admin": the reply that mentioned every admin is now a card)
# ======================================================================================================
# A member replies /report (or @admin) to a message. Admins get a card, in the same style as an Appeal card:
#   [🔇 Mute 1h] [⚠️ Warn]  /  [🗑 Delete message] [✅ Dismiss]      (two buttons in a line)
#   * the card goes to the private chat of every admin who started the bot, plus the chosen place (report_dest:
#     "log" channel (default) | "group" | "none" = private chats only). When no card could be delivered at all, to the group.
#   * one open report per message: a second member reporting the same message only adds to the card (+N more).
#   * the first admin to tap decides; every copy of the card then shows who did what; the reporters get a short message
#     in the bot's private chat. Decided reports leave the list 24 hours later (REPORT_KEEP). Open ones never do.
#   * Mute = a timed mute (report_mute, default 1h); Warn = nova's add_warn (so the Warn Ladder applies); Delete message;
#     Dismiss. Mute and Delete are written to the mod log (Warn writes its own row).
#   * settings: reports_on (nova's /reports), report_dest, report_mute (seconds), report_cooldown (seconds a member waits
#     between reports, default 60, 0 = none).
#   * panel: /help > Reports > 🚨 Report Settings (callbacks "rp:..."), or /reportpanel, /reportmute, /reportcooldown.
#   * data: collection "reports" {_id, chat_id, chat_title, msg_id, reported_id, reported_name, reported_mention,
#     reporter_ids, reporter_mentions, pkind, preview, link, mute_secs, cards [{chat, id}], status
#     (open|muted|warned|deleted|dismissed), created_at, decided_at, decided_by, decided_name}.
REPORT_KEEP = 24 * 3600
RP_DECIDED = ("muted", "warned", "deleted", "dismissed")
RP_ACTS = {"m": "muted", "w": "warned", "x": "deleted", "d": "dismissed"}
RP_DESTS = ("log", "group", "none")
RP_PAGE = 6
RP_MUTES = (900, 3600, 21600, 86400)
RP_COOLDOWNS = (0, 30, 60, 120, 300)
RP_KINDS = (("photo", "photo"), ("video", "video"), ("video_note", "video"), ("voice", "voice"), ("audio", "audio"),
            ("document", "file"), ("animation", "gif"), ("sticker", "sticker"), ("poll", "poll"))
_rp_last = {}           # (chat_id, reporter id) -> monotonic time of that member's last report


def reports_on(chat_id):
    return D.get_setting(chat_id, "reports_on", "True") == "True"


def report_dest(chat_id):
    dest = D.get_setting(chat_id, "report_dest", "log")
    return dest if dest in RP_DESTS else "log"


def report_mute_secs(chat_id):
    secs = _num_setting(chat_id, "report_mute", 3600)
    return secs if 60 <= secs <= RAID_MAX_SECS else 3600


def report_cooldown(chat_id):
    secs = _num_setting(chat_id, "report_cooldown", 60)
    return secs if 0 <= secs <= 3600 else 60


def report_button(chat):
    """The 🚨 button nova.py adds to /help > Reports (groups only)."""
    return InlineKeyboardButton(L.t("rp.btn_help", getattr(chat, "id", None)), callback_data="rp:p")


def _pairs(buttons):
    """Two buttons in a line."""
    return [buttons[i:i + 2] for i in range(0, len(buttons), 2)]


def _rp_preview(msg):
    """(kind, text): the reported text (cut), or what kind of message it is."""
    text = (getattr(msg, "text", None) or getattr(msg, "caption", None) or "").strip()
    if text:
        return "text", text[:150] + ("…" if len(text) > 150 else "")
    for attr, kind in RP_KINDS:
        if getattr(msg, attr, None):
            return kind, ""
    return "other", ""


def _rp_link(chat, msg_id):
    if getattr(chat, "username", None):
        return f"https://t.me/{chat.username}/{msg_id}"
    sid = str(chat.id)
    return f"https://t.me/c/{sid[4:]}/{msg_id}" if sid.startswith("-100") else None


def _rp_card_text(row, cid):
    kind = row.get("pkind") or "other"
    preview = html.escape(row.get("preview") or "") if kind == "text" else L.t("rp.p_" + kind, cid)
    n = len(row.get("reporter_ids") or [])
    reporter = (row.get("reporter_mentions") or ["?"])[0] + (L.t("rp.more", cid, n=n - 1) if n > 1 else "")
    text = L.t("rp.card", cid, chat=html.escape(row.get("chat_title") or ""), user=row.get("reported_mention") or "?",
               reporter=reporter, preview=preview)
    return text + ("\n" + L.t("rp.link", cid, url=row["link"]) if row.get("link") else "")


def _rp_buttons(row, cid):
    i = row["_id"]
    return _pairs([InlineKeyboardButton(L.t("rp.btn_mute", cid, dur=extra.fmt_duration(row.get("mute_secs") or 3600)), callback_data=f"rp:m:{i}"),
                   InlineKeyboardButton(L.t("rp.btn_warn", cid), callback_data=f"rp:w:{i}"),
                   InlineKeyboardButton(L.t("rp.btn_delete", cid), callback_data=f"rp:x:{i}"),
                   InlineKeyboardButton(L.t("rp.btn_dismiss", cid), callback_data=f"rp:d:{i}")])


def _rp_done_text(row, cid):
    return L.t("rp.done_" + row["status"], cid, admin=html.escape(row.get("decided_name") or ""),
               dur=extra.fmt_duration(row.get("mute_secs") or 3600))


async def _rp_edit_cards(bot, row, text, markup=None, skip=None):
    """Shows `text` on every copy of the card (except the one at `skip`, which the caller edits itself)."""
    for card in row.get("cards", []):
        if (card["chat"], card["id"]) == skip:
            continue
        try:
            await bot.edit_message_text(text, chat_id=card["chat"], message_id=card["id"], parse_mode="HTML", reply_markup=markup)
        except TelegramError:
            pass                                           # deleted, or the same text


async def _rp_note(msg, key, secs, **values):
    """A short reply in the group that deletes itself."""
    try:
        sent = await msg.reply_html(L.t(key, msg.chat.id, **values))
        await extra.track_notice(sent, secs)
    except TelegramError:
        pass


async def report_submit(bot, chat, msg, reporter):
    """nova's file_report calls this with the /report message (`msg`, a reply to the reported one). Returns True when the
    report was filed (a new card, or the reporter added to an open one)."""
    cid, target = chat.id, msg.reply_to_message
    cd, key, now = report_cooldown(cid), (chat.id, reporter.id), time.monotonic()
    if cd and key in _rp_last and now - _rp_last[key] < cd:
        await _rp_note(msg, "rp.cooldown", 10, n=max(1, int(cd - (now - _rp_last[key]))))
        return False
    col = store.col("reports")
    open_row = await asyncio.to_thread(col.find_one, {"chat_id": cid, "msg_id": target.message_id, "status": "open"})
    if open_row:                                           # the same message again: one card, a counter
        if reporter.id in open_row.get("reporter_ids", []):
            await _rp_note(msg, "rp.dup", 10)
            return False
        open_row["reporter_ids"] = open_row.get("reporter_ids", []) + [reporter.id]
        open_row["reporter_mentions"] = open_row.get("reporter_mentions", []) + [reporter.mention_html()]
        await asyncio.to_thread(col.update_one, {"_id": open_row["_id"]},
                                {"$set": {"reporter_ids": open_row["reporter_ids"], "reporter_mentions": open_row["reporter_mentions"]}})
        await _rp_edit_cards(bot, open_row, _rp_card_text(open_row, cid), InlineKeyboardMarkup(_rp_buttons(open_row, cid)))
        _rp_last[key] = now
        await _rp_note(msg, "rp.sent", 60, reporter=reporter.mention_html())
        return True
    reported = target.from_user
    pkind, preview = _rp_preview(target)
    row = {"_id": os.urandom(5).hex(), "chat_id": cid, "chat_title": chat.title or "", "msg_id": target.message_id,
           "reported_id": reported.id, "reported_name": getattr(reported, "full_name", None) or str(reported.id),
           "reported_mention": reported.mention_html(), "reporter_ids": [reporter.id], "reporter_mentions": [reporter.mention_html()],
           "pkind": pkind, "preview": preview, "link": _rp_link(chat, target.message_id), "mute_secs": report_mute_secs(cid),
           "cards": [], "status": "open", "created_at": time.time()}
    text, kb = _rp_card_text(row, cid), InlineKeyboardMarkup(_rp_buttons(row, cid))

    async def send(to):
        try:
            sent = await bot.send_message(to, text, parse_mode="HTML", reply_markup=kb, disable_web_page_preview=True)
        except TelegramError:
            return False
        row["cards"].append({"chat": to, "id": sent.message_id})
        return True

    try:
        admins = [a.user.id for a in await bot.get_chat_administrators(cid) if not a.user.is_bot]
    except TelegramError:
        admins = []
    for admin_id in admins:
        await send(admin_id)                               # an admin who never started the bot is skipped
    dest = report_dest(cid)
    if dest == "log" and D.get_setting(cid, "log_channel"):
        try:
            await send(int(D.get_setting(cid, "log_channel")))
        except ValueError:
            pass
    elif dest == "group":
        await send(cid)
    if not row["cards"]:
        await send(cid)                                    # nobody could be reached any other way
    if not row["cards"]:
        log.warning("report: couldn't post the card in %s", cid)
        return False
    await asyncio.to_thread(col.insert_one, row)
    _rp_last[key] = now
    await _rp_note(msg, "rp.sent", 60, reporter=reporter.mention_html())
    return True


# ------------------------------------------------------------------ deciding (the card)
async def _rp_apply(bot, gchat, row, act, admin_mention):
    """Does what the button says. Returns True when it worked."""
    cid, uid, mode_secs = row["chat_id"], row["reported_id"], row.get("mute_secs") or 3600
    if act == "muted":
        mode = f"tmute:{mode_secs}"
        if not await D.do_action(gchat, uid, mode):
            return False
        kind, secs = extra.mode_kind(mode)
        await extra.record_action(cid, uid, row.get("reported_mention") or str(uid), "Muted (report)", "Reported by a member",
                                  extra.punishment_text(kind, secs), admin_mention, "mute", kind="mute")
    elif act == "warned":
        notice = await D.add_warn(gchat, uid, row.get("reported_mention") or str(uid), "Reported by a member", admin_mention)
        try:
            await bot.send_message(cid, notice, parse_mode="HTML")
        except TelegramError:
            pass
    elif act == "deleted":
        try:
            await bot.delete_message(cid, row["msg_id"])
        except TelegramError as e:
            if "not found" not in str(e).lower():          # already gone is fine
                return False
        await extra.record_action(cid, uid, row.get("reported_mention") or str(uid), "Message deleted (report)", "Reported by a member",
                                  "Message deleted only (no mute or ban)", admin_mention, "mod", kind="delete")
    return True


async def rp_decide(update, context, act_key, report_id):
    q, bot = update.callback_query, context.bot
    col = store.col("reports")
    try:
        row = await asyncio.to_thread(col.find_one, {"_id": report_id})
        gchat = await bot.get_chat(row["chat_id"]) if row else None
    except TelegramError:
        row = gchat = None
    if row is None or gchat is None:
        await q.answer(L.t("rp.invalid"), show_alert=True)
        return
    cid, new = row["chat_id"], RP_ACTS[act_key]
    if not await _ac_allowed(gchat, q.from_user.id):
        await q.answer(L.t("rp.card_admin_only", cid), show_alert=True)
        return
    who = getattr(q.from_user, "full_name", None) or getattr(q.from_user, "first_name", "") or str(q.from_user.id)
    claim = await asyncio.to_thread(col.update_one, {"_id": report_id, "status": "open"},
                                    {"$set": {"status": new, "decided_by": q.from_user.id, "decided_name": who, "decided_at": time.time()}})
    if claim.modified_count != 1:
        await q.answer(L.t("rp.already", cid), show_alert=True)
        return
    by = q.from_user.mention_html() if hasattr(q.from_user, "mention_html") else html.escape(who)
    try:
        worked = await _rp_apply(bot, gchat, row, new, by)
    except TelegramError as e:
        log.warning("report: couldn't %s in %s: %s", new, cid, e)
        worked = False
    if not worked:
        await asyncio.to_thread(col.update_one, {"_id": report_id}, {"$set": {"status": "open"}})      # still open: try again
        await q.answer(L.t("rp.act_failed", cid), show_alert=True)
        return
    await q.answer()
    row["status"], row["decided_name"] = new, who
    final = _rp_card_text(row, cid) + "\n\n" + _rp_done_text(row, cid)
    here = (q.message.chat.id, q.message.message_id) if q.message else None
    cards = [(c["chat"], c["id"]) for c in row.get("cards", [])]
    await _rp_edit_cards(bot, row, final, None, skip=here)
    if here is not None and here in cards:
        try:
            await q.edit_message_text(final, parse_mode="HTML", reply_markup=None, disable_web_page_preview=True)
        except TelegramError:
            pass
    elif here is not None:                                 # decided from the Report List page
        await _ac_edit(q, final, InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="rp:l:0")]]))
    for reporter_id in row.get("reporter_ids", []):        # the reporters get a plain status message
        try:
            await bot.send_message(reporter_id, L.t("rp.dm_dismissed" if new == "dismissed" else "rp.dm_acted", cid,
                                                    chat=html.escape(gchat.title or "")), parse_mode="HTML")
        except TelegramError:
            pass                                           # they never started the bot


# ------------------------------------------------------------------ the settings panel and the list
def _rp_panel(chat, note=""):
    cid = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("rp.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    on, dest, mute, cd = reports_on(cid), report_dest(cid), report_mute_secs(cid), report_cooldown(cid)
    text = (L.t("rp.title", cid) + "\n\n" + (note + "\n\n" if note else "") + L.t("rp.intro", cid) + "\n\n" +
            L.t("rp.status_on" if on else "rp.status_off", cid) + "\n" + L.t("rp.dest_line", cid, dest=L.t("rp.dest_" + dest, cid)) + "\n" +
            L.t("rp.mute_line", cid, dur=extra.fmt_duration(mute)) + "\n" +
            L.t("rp.cd_line", cid, dur=extra.fmt_duration(cd) if cd else L.t("rp.off", cid)) + "\n\n" + L.t("rp.note", cid))
    mark = lambda cond: "✅ " if cond else ""
    rows = [[InlineKeyboardButton(L.t("rp.btn_off" if on else "rp.btn_on", cid), callback_data="rp:t")]]
    rows += _pairs([InlineKeyboardButton(mark(d == dest) + L.t("rp.d_" + d, cid), callback_data=f"rp:e:{d}") for d in RP_DESTS])
    rows += _pairs([InlineKeyboardButton(mark(s == mute) + "🔇 " + extra.fmt_duration(s), callback_data=f"rp:u:{s}") for s in RP_MUTES])
    rows += _pairs([InlineKeyboardButton(mark(s == cd) + "⏱ " + (extra.fmt_duration(s) if s else L.t("rp.off", cid)), callback_data=f"rp:c:{s}")
                    for s in RP_COOLDOWNS])
    rows.append([InlineKeyboardButton(L.t("rp.btn_list", cid), callback_data="rp:l:0")])
    rows.append([InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:reports")])
    return text, InlineKeyboardMarkup(rows)


async def _rp_list_panel(chat, page):
    cid = chat.id
    rows = await asyncio.to_thread(_apl_purge_find, {"chat_id": cid}, "reports", RP_DECIDED, REPORT_KEEP)
    rows.sort(key=lambda r: r.get("created_at", 0), reverse=True)
    pages = max(1, -(-len(rows) // RP_PAGE))
    page = min(max(page, 0), pages - 1)
    shown = rows[page * RP_PAGE:(page + 1) * RP_PAGE]
    if not rows:
        text = L.t("rp.list_title", cid, count=0) + "\n\n" + L.t("rp.list_empty", cid)
    else:
        lines = [L.t("rp.list_line", cid, n=page * RP_PAGE + i + 1, user=html.escape(r.get("reported_name") or ""),
                     status=L.t("rp.st_" + r["status"], cid, admin=html.escape(r.get("decided_name") or "")))
                 for i, r in enumerate(shown)]
        text = L.t("rp.list_title", cid, count=len(rows)) + "\n\n" + "\n".join(lines)
        if any(r["status"] == "open" for r in shown):
            text += "\n\n" + L.t("rp.list_tap", cid)
    kb = [[InlineKeyboardButton(f"🔴 {r.get('reported_name') or ''}"[:60], callback_data=f"rp:o:{r['_id']}")] for r in shown if r["status"] == "open"]
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀️", callback_data=f"rp:l:{page - 1}"))
    if page < pages - 1:
        nav.append(InlineKeyboardButton("▶️", callback_data=f"rp:l:{page + 1}"))
    if nav:
        kb.append(nav)
    kb.append([InlineKeyboardButton(L.t("pick.back", cid), callback_data="rp:p")])
    return text, InlineKeyboardMarkup(kb)


async def rp_callback(update, context):
    """\"rp:<m|w|x|d>:<id>\" the card buttons (Mute, Warn, Delete message, Dismiss: admins of the report's group, in any chat),
    and for the panel in a group: \"rp:p\", \"rp:t\", \"rp:e:<dest>\", \"rp:u:<secs>\", \"rp:c:<secs>\", \"rp:l:<page>\", \"rp:o:<id>\"."""
    q = update.callback_query
    parts = (q.data or "").split(":")[1:]
    act, arg = (parts[0] if parts else ""), (parts[1] if len(parts) == 2 else None)
    if act in RP_ACTS and arg and len(parts) == 2:
        await rp_decide(update, context, act, arg)
        return
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    if chat.type == "private":
        await q.answer(L.t("rp.private"), show_alert=True)
        return
    cid = chat.id
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("rp.admin_only", cid), show_alert=True)
        return
    num = _ac_num(arg, 0, 10 ** 7) if arg is not None else None
    toast = None
    try:
        if act == "p" and len(parts) == 1:
            await q.answer()
            await _ac_edit(q, *_rp_panel(chat))
            return
        if act == "l" and num is not None:
            await q.answer()
            await _ac_edit(q, *await _rp_list_panel(chat, num))
            return
        if act == "o" and arg and len(parts) == 2:
            row = await asyncio.to_thread(store.col("reports").find_one, {"_id": arg, "chat_id": cid})
            if not row:
                await q.answer(L.t("rp.invalid", cid), show_alert=True)
                return
            await q.answer()
            back = [[InlineKeyboardButton(L.t("pick.back", cid), callback_data="rp:l:0")]]
            if row["status"] == "open":
                await _ac_edit(q, _rp_card_text(row, cid), InlineKeyboardMarkup(_rp_buttons(row, cid) + back))
            else:
                await _ac_edit(q, _rp_card_text(row, cid) + "\n\n" + _rp_done_text(row, cid), InlineKeyboardMarkup(back))
            return
        if act == "t" and len(parts) == 1:
            on = not reports_on(cid)
            D.set_setting(cid, "reports_on", "True" if on else "False")      # the same text nova's /reports saves
            toast = L.t("rp.t_on" if on else "rp.t_off", cid)
        elif act == "e" and arg in RP_DESTS:
            D.set_setting(cid, "report_dest", arg)
            toast = L.t("rp.t_dest", cid, dest=L.t("rp.dest_" + arg, cid))
        elif act == "u" and num in RP_MUTES:
            D.set_setting(cid, "report_mute", num)
            toast = L.t("rp.t_mute", cid, dur=extra.fmt_duration(num))
        elif act == "c" and num in RP_COOLDOWNS:
            D.set_setting(cid, "report_cooldown", num)
            toast = L.t("rp.t_cd", cid, dur=extra.fmt_duration(num) if num else L.t("rp.off", cid))
        else:
            await q.answer(L.t("rp.invalid", cid), show_alert=True)
            return
        await q.answer(toast)
        await _ac_edit(q, *_rp_panel(chat))
    except Exception:
        log.exception("reports: panel action failed in %s", cid)
        await q.answer(L.t("ac.db_problem", cid), show_alert=True)


async def _rp_setting_cmd(update, context, key, low, high, err, toast, allow_off=False):
    """Shared by /reportmute and /reportcooldown."""
    if not await D.group_only(update):
        return
    chat, msg, note = update.effective_chat, update.effective_message, ""
    if context.args:
        text = " ".join(context.args).lower()
        secs = 0 if (allow_off and text == "off") else _parse_secs(text, low, high)
        if secs is None:
            await msg.reply_html(L.t(err, chat.id))
            return
        D.set_setting(chat.id, key, secs)
        note = L.t(toast, chat.id, dur=extra.fmt_duration(secs) if secs else L.t("rp.off", chat.id))
    text, markup = _rp_panel(chat, note)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


async def reportpanel_cmd(update, context):
    """/reportpanel: the settings panel (admins)."""
    if not await D.group_only(update):
        return
    text, markup = _rp_panel(update.effective_chat)
    await update.effective_message.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


async def reportmute_cmd(update, context):
    """/reportmute 2h: how long the card's Mute button mutes."""
    await _rp_setting_cmd(update, context, "report_mute", 60, RAID_MAX_SECS, "rp.err_mute", "rp.t_mute")


async def reportcooldown_cmd(update, context):
    """/reportcooldown 60s | off: how long a member waits between reports."""
    await _rp_setting_cmd(update, context, "report_cooldown", 10, 3600, "rp.err_cd", "rp.t_cd", allow_off=True)


# ======================================================================================================
# 2i. GREETINGS PANEL  (extends nova.py's welcome / goodbye: extra buttons + delete-after)
# ======================================================================================================
# nova.py keeps the texts (/setwelcome, /setgoodbye ...) and the old [Text](buttonurl://link) buttons. New here, per message
# kind "w" (welcome) and "g" (goodbye):
#   * extra link buttons, two in a line (max GR_MAX_BTNS): welcome_btns / goodbye_btns = JSON [[text, url], ...]
#   * delete-after: welcome_del / goodbye_del = seconds (0 = the message stays). It uses the notice sweeper (extra.track_notice),
#     which runs every minute and keeps its schedule in MongoDB, so a restart loses nothing: the message goes within about a
#     minute of the chosen time (minimum 1 minute).
#   * nova's send_welcome / on_left_member call greet_markup(chat_id, kind, markup) and greet_after_send(chat_id, kind, sent).
#   * panel: /greet or /help > Greetings > 👋 Greetings Panel (callbacks "gr:..."). Short commands:
#       /wdel 5m | off, /gdel 5m | off     (delete-after)
#       /wbtn Join channel https://t.me/abc, /gbtn ...   (add a button: the last word is the link)
#       /wbtn 2 removes button 2, /wbtn alone opens that screen
#   * "➕ Add button" in the panel waits for the admin's next message (5 minutes) in that chat: "Text link".
GR_KINDS = {"w": ("welcome", "welcome_on", "True", "welcome_btns", "welcome_del"),
            "g": ("goodbye", "goodbye_on", "False", "goodbye_btns", "goodbye_del")}   # kind -> (template key, on key, on default, buttons key, delete key)
GR_MAX_BTNS = 6
GR_DELS = (0, 60, 300, 900, 3600)
GR_DEL_MIN, GR_DEL_MAX = 60, 86400
GR_TEXT_MAX, GR_URL_MAX = 40, 300
GR_PENDING_SECS = 300
GR_PREVIEW_SECS = 60
_gr_pending = {}        # (chat_id, admin id) -> {"kind", "panel": (chat id, message id), "until": monotonic time}


def gr_buttons(chat_id, kind):
    """The saved extra buttons of a message kind as a list of (text, url). Anything unreadable is ignored."""
    try:
        raw = json.loads(D.get_setting(chat_id, GR_KINDS[kind][3], "") or "[]")
    except (TypeError, ValueError):
        return []
    out = []
    for item in raw if isinstance(raw, list) else []:
        if isinstance(item, (list, tuple)) and len(item) == 2 and all(isinstance(x, str) for x in item) and item[0] and item[1]:
            out.append((item[0][:GR_TEXT_MAX], item[1]))
    return out[:GR_MAX_BTNS]


def _gr_save_buttons(chat_id, kind, buttons):
    D.set_setting(chat_id, GR_KINDS[kind][3], json.dumps([list(b) for b in buttons], ensure_ascii=False))


def gr_delete_secs(chat_id, kind):
    secs = _num_setting(chat_id, GR_KINDS[kind][4], 0)
    return secs if secs == 0 or GR_DEL_MIN <= secs <= GR_DEL_MAX else 0


def gr_on(chat_id, kind):
    _, on_key, default, _, _ = GR_KINDS[kind]
    return D.get_setting(chat_id, on_key, default) == "True"


def greet_button(chat):
    """The 👋 button nova.py adds to /help > Greetings (groups only)."""
    return InlineKeyboardButton(L.t("gr.btn_help", getattr(chat, "id", None)), callback_data="gr:m")


def greet_markup(chat_id, kind, markup):
    """nova's markup (its [..](buttonurl://..) buttons and {rules}) plus the panel's extra buttons, two in a line."""
    extras = gr_buttons(chat_id, kind)
    if not extras:
        return markup
    rows = [list(r) for r in (markup.inline_keyboard if markup else [])]
    rows += _pairs([InlineKeyboardButton(text, url=url) for text, url in extras])
    return InlineKeyboardMarkup(rows)


async def greet_after_send(chat_id, kind, sent):
    """Schedules the message's deletion when the group chose a delete-after time."""
    secs = gr_delete_secs(chat_id, kind)
    if secs and sent is not None:
        await extra.track_notice(sent, secs)


def _gr_url(token):
    """A safe link from what an admin typed: https://..., http://..., tg://..., t.me/x or @channel. None when it is not one."""
    token = token.strip()
    if re.fullmatch(r"@[A-Za-z][A-Za-z0-9_]{3,31}", token):
        return "https://t.me/" + token[1:]
    if re.match(r"(?i)(t\.me|telegram\.me)/\S+$", token):
        token = "https://" + token
    return token if re.fullmatch(r"(?i)(https?|tg)://\S+", token) and len(token) <= GR_URL_MAX else None


def _gr_parse_button(text):
    """'Join channel https://t.me/abc' -> ('Join channel', 'https://t.me/abc'), or None."""
    bits = str(text).strip().rsplit(None, 1)
    if len(bits) != 2:
        return None
    label, url = bits[0].strip(), _gr_url(bits[1])
    return (label, url) if url and 1 <= len(label) <= GR_TEXT_MAX else None


def _gr_add_button(chat_id, kind, text):
    """Returns (note, error key). Same text as an existing button replaces its link."""
    parsed = _gr_parse_button(text)
    if parsed is None:
        return None, "gr.err_btn"
    buttons = [b for b in gr_buttons(chat_id, kind) if b[0] != parsed[0]]
    if len(buttons) >= GR_MAX_BTNS:
        return None, "gr.err_full"
    _gr_save_buttons(chat_id, kind, buttons + [parsed])
    return L.t("gr.t_added", chat_id, text=html.escape(parsed[0])), None


def _gr_state(chat_id, kind):
    on = L.t("gr.on" if gr_on(chat_id, kind) else "gr.off", chat_id)
    secs = gr_delete_secs(chat_id, kind)
    return on, (L.t("gr.del_after", chat_id, dur=extra.fmt_duration(secs)) if secs else L.t("gr.del_never", chat_id))


def _gr_main(chat, note=""):
    cid = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("gr.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    lines = []
    for kind in ("w", "g"):
        on, dele = _gr_state(cid, kind)
        lines.append(L.t("gr.line_" + kind, cid, state=on, dele=dele, n=len(gr_buttons(cid, kind))))
    clean = D.get_setting(cid, "clean_welcome", "False") == "True"
    text = (L.t("gr.title", cid) + "\n\n" + (note + "\n\n" if note else "") + L.t("gr.intro", cid) + "\n\n" + "\n".join(lines) + "\n" +
            L.t("gr.clean_on" if clean else "gr.clean_off", cid) + "\n\n" + L.t("gr.note", cid))
    rows = _pairs([InlineKeyboardButton(L.t("gr.b_w", cid), callback_data="gr:w:s"), InlineKeyboardButton(L.t("gr.b_g", cid), callback_data="gr:g:s"),
                   InlineKeyboardButton(L.t("gr.b_clean", cid, state=L.t("gr.on" if clean else "gr.off", cid)), callback_data="gr:c")])
    rows.append([InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:greet")])
    return text, InlineKeyboardMarkup(rows)


def _gr_screen(chat, kind, note=""):
    cid = chat.id
    if chat.type == "private":
        return L.t("gr.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    on = gr_on(cid, kind)
    _, dele = _gr_state(cid, kind)
    buttons, secs = gr_buttons(cid, kind), gr_delete_secs(cid, kind)
    lines = [f"{i}. {html.escape(t)} → {html.escape(u)}" for i, (t, u) in enumerate(buttons, 1)]
    text = (L.t("gr.s_title_" + kind, cid) + "\n\n" + (note + "\n\n" if note else "") +
            L.t("gr.s_state", cid, state=L.t("gr.on" if on else "gr.off", cid)) + "\n" + L.t("gr.s_del", cid, dele=dele) + "\n\n" +
            L.t("gr.s_btns", cid, n=len(buttons), max=GR_MAX_BTNS) + "\n" + ("\n".join(lines) if lines else L.t("gr.s_none", cid)) + "\n\n" +
            L.t("gr.s_hint_" + kind, cid))
    mark = lambda cond: "✅ " if cond else ""
    rows = _pairs([InlineKeyboardButton(L.t("gr.b_off" if on else "gr.b_on", cid), callback_data=f"gr:{kind}:t"),
                   InlineKeyboardButton(L.t("gr.b_preview", cid), callback_data=f"gr:{kind}:p")])
    rows += _pairs([InlineKeyboardButton(mark(s == secs) + "⏱ " + (extra.fmt_duration(s) if s else L.t("gr.never", cid)), callback_data=f"gr:{kind}:d:{s}")
                    for s in GR_DELS])
    rows += _pairs([InlineKeyboardButton(f"🗑 {i}. {t[:18]}", callback_data=f"gr:{kind}:x:{i}") for i, (t, _) in enumerate(buttons, 1)])
    if len(buttons) < GR_MAX_BTNS:
        rows.append([InlineKeyboardButton(L.t("gr.b_add", cid), callback_data=f"gr:{kind}:a")])
    rows.append([InlineKeyboardButton(L.t("pick.back", cid), callback_data="gr:m")])
    return text, InlineKeyboardMarkup(rows)


async def _gr_preview(bot, chat, kind, user):
    """Posts the message as a new member would see it (deletes itself soon)."""
    tmpl_key, _, _, _, _ = GR_KINDS[kind]
    template = D.get_setting(chat.id, tmpl_key, D.DEFAULT_WELCOME if kind == "w" else D.DEFAULT_GOODBYE)
    count = await chat.get_member_count()
    body, markup = await D.template_markup(template, _Args((), bot), chat.id)
    markup = greet_markup(chat.id, kind, markup)
    send = functools.partial(chat.send_message, reply_markup=markup) if markup else chat.send_message
    sent = await D.safe_html(send, D.render(body, user, chat, count))
    if sent is not None:
        await extra.track_notice(sent, GR_PREVIEW_SECS)
    return sent


async def gr_callback(update, context):
    """\"gr:m\" main, \"gr:c\" clean welcome on/off, \"gr:<w|g>:s\" a message's screen, \":t\" on/off, \":p\" preview,
    \":d:<secs>\" delete after, \":x:<n>\" remove a button, \":a\" add a button. Admins only, checked on every tap."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    if chat.type == "private":
        await q.answer(L.t("gr.private"), show_alert=True)
        return
    cid = chat.id
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("gr.admin_only", cid), show_alert=True)
        return
    parts = (q.data or "").split(":")[1:]
    toast, screen = None, None                               # screen: the kind whose screen to show again (None = main)
    try:
        if parts == ["m"]:
            pass
        elif parts == ["c"]:
            now_on = D.get_setting(cid, "clean_welcome", "False") == "True"
            D.set_setting(cid, "clean_welcome", "False" if now_on else "True")
            toast = L.t("gr.t_clean_off" if now_on else "gr.t_clean_on", cid)
        elif len(parts) >= 2 and parts[0] in GR_KINDS and parts[1] in ("s", "t", "p", "a", "d", "x"):
            kind, act, arg = parts[0], parts[1], (parts[2] if len(parts) == 3 else None)
            screen = kind
            if act in ("s", "t", "p", "a") and len(parts) != 2 or act in ("d", "x") and len(parts) != 3:
                raise ValueError
            if act == "t":
                D.set_setting(cid, GR_KINDS[kind][1], "False" if gr_on(cid, kind) else "True")
                toast = L.t("gr.t_on" if gr_on(cid, kind) else "gr.t_off", cid)
            elif act == "p":
                if await _gr_preview(context.bot, chat, kind, q.from_user) is None:
                    await q.answer(L.t("gr.err_preview", cid), show_alert=True)
                    return
                toast = L.t("gr.t_preview", cid)
            elif act == "d":
                secs = _ac_num(arg, 0, GR_DEL_MAX)
                if secs not in GR_DELS:
                    raise ValueError
                D.set_setting(cid, GR_KINDS[kind][4], secs)
                toast = L.t("gr.t_del", cid, dur=extra.fmt_duration(secs)) if secs else L.t("gr.t_del_off", cid)
            elif act == "x":
                n, buttons = _ac_num(arg, 1, GR_MAX_BTNS), gr_buttons(cid, kind)
                if n is None or n > len(buttons):
                    raise ValueError
                _gr_save_buttons(cid, kind, buttons[:n - 1] + buttons[n:])
                toast = L.t("gr.t_removed", cid)
            elif act == "a":
                if len(gr_buttons(cid, kind)) >= GR_MAX_BTNS:
                    await q.answer(L.t("gr.err_full", cid, n=GR_MAX_BTNS), show_alert=True)
                    return
                _gr_pending[(cid, q.from_user.id)] = {"kind": kind, "panel": (cid, q.message.message_id), "until": time.monotonic() + GR_PENDING_SECS}
                await q.answer(L.t("gr.t_ask", cid))
                await chat.send_message(L.t("gr.ask", cid, user=q.from_user.mention_html()), parse_mode="HTML")
                return
        else:
            raise ValueError
    except ValueError:
        await q.answer(L.t("gr.invalid", cid), show_alert=True)
        return
    except Exception:
        log.exception("greetings: panel action failed in %s", cid)
        await q.answer(L.t("ac.db_problem", cid), show_alert=True)
        return
    await q.answer(toast)
    await _ac_edit(q, *(_gr_screen(chat, screen) if screen else _gr_main(chat)))


async def gr_input(update, context):
    """group=-11, cheap: only acts when the admin tapped ➕ Add button and now sends "Text link" (or "cancel")."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or not _gr_pending:
        return
    key = (chat.id, user.id)
    pending = _gr_pending.get(key)
    if pending is None:
        return
    if time.monotonic() > pending["until"]:
        _gr_pending.pop(key, None)
        return
    if not await D.is_admin(chat, user.id):
        _gr_pending.pop(key, None)
        return
    kind, text = pending["kind"], (msg.text or "").strip()
    if text.lower() in ("cancel", "stop"):
        _gr_pending.pop(key, None)
        await _rp_note(msg, "gr.t_cancel", 10)
        raise ApplicationHandlerStop
    note, err = _gr_add_button(chat.id, kind, text)
    if err:
        await _rp_note(msg, err, 15, n=GR_MAX_BTNS)
        raise ApplicationHandlerStop
    _gr_pending.pop(key, None)
    try:
        await msg.delete()
    except TelegramError:
        pass
    try:
        panel_chat, panel_id = pending["panel"]
        screen, kb = _gr_screen(chat, kind, note)
        await context.bot.edit_message_text(screen, chat_id=panel_chat, message_id=panel_id, parse_mode="HTML", reply_markup=kb,
                                            disable_web_page_preview=True)
    except TelegramError:
        await _rp_note(msg, "gr.t_added", 10, text=html.escape(text))
    raise ApplicationHandlerStop


async def greet_cmd(update, context):
    """/greet: the panel (admins)."""
    if not await D.group_only(update):
        return
    text, markup = _gr_main(update.effective_chat)
    await update.effective_message.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


async def _gr_del_cmd(update, context, kind):
    if not await D.group_only(update):
        return
    chat, msg, note = update.effective_chat, update.effective_message, ""
    if context.args:
        text = " ".join(context.args).lower()
        secs = 0 if text in ("off", "no", "0") else _parse_secs(text, GR_DEL_MIN, GR_DEL_MAX)
        if secs is None:
            await msg.reply_html(L.t("gr.err_del", chat.id, cmd="wdel" if kind == "w" else "gdel"))
            return
        D.set_setting(chat.id, GR_KINDS[kind][4], secs)
        note = L.t("gr.t_del", chat.id, dur=extra.fmt_duration(secs)) if secs else L.t("gr.t_del_off", chat.id)
    text, markup = _gr_screen(chat, kind, note)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


async def _gr_btn_cmd(update, context, kind):
    if not await D.group_only(update):
        return
    chat, msg, note = update.effective_chat, update.effective_message, ""
    if context.args:
        buttons = gr_buttons(chat.id, kind)
        if len(context.args) == 1 and context.args[0].isdigit():
            n = int(context.args[0])
            if not 1 <= n <= len(buttons):
                await msg.reply_html(L.t("gr.err_nobtn", chat.id, n=n))
                return
            _gr_save_buttons(chat.id, kind, buttons[:n - 1] + buttons[n:])
            note = L.t("gr.t_removed", chat.id)
        else:
            note, err = _gr_add_button(chat.id, kind, " ".join(context.args))
            if err:
                await msg.reply_html(L.t(err, chat.id, n=GR_MAX_BTNS))
                return
    text, markup = _gr_screen(chat, kind, note)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


async def wdel_cmd(update, context):
    """/wdel 5m | off: delete the welcome message after a while."""
    await _gr_del_cmd(update, context, "w")


async def gdel_cmd(update, context):
    """/gdel 5m | off: the same for the goodbye message."""
    await _gr_del_cmd(update, context, "g")


async def wbtn_cmd(update, context):
    """/wbtn Join channel https://t.me/abc: add a welcome button. /wbtn 2 removes button 2. /wbtn alone opens the screen."""
    await _gr_btn_cmd(update, context, "w")


async def gbtn_cmd(update, context):
    """/gbtn ...: the same for the goodbye message."""
    await _gr_btn_cmd(update, context, "g")


# ======================================================================================================
# 2j. RULES GATE
# ======================================================================================================
# New members must read the rules and tap ✅ I accept before they can chat. Until then they are muted and a short message
# with [📜 Read the rules] (nova's rules button) and [✅ I accept] waits for them. It uses the group's saved rules (/setrules).
#   * settings: rules_gate "on"|"off" (default off), gate_time (seconds to accept, default 5 minutes),
#     gate_action ("kick" default | "mute" = stay muted | "ban") when the time runs out.
#   * nova.py: on_new_members calls gate_start (not for admins, the bot owner or members an admin added); with the CAPTCHA on,
#     captcha_callback calls gate_start after the member verified (so: verify first, then accept the rules);
#     on_left_member calls gate_cleanup.
#   * waiting members live in the "rules_gate" collection (store.gate_*): a restart loses nothing. The 30-second loop
#     (run_once -> _gate_round) applies the action to members whose time ran out.
#   * accepting: the member's own tap (callback "rg:a:<user id>") gives back the group's permissions, removes the message and
#     sends the normal welcome. Turning the gate OFF lets everyone waiting in.
#   * panel: /help > Rules > 📜 Rules Gate, or /gate  |  /gate on|off  |  /gate 10m  |  /gate kick|mute|ban  (callbacks "rg:...").
RG_KEY, RG_TIME_KEY, RG_ACTION_KEY = "rules_gate", "gate_time", "gate_action"
RG_ACTIONS = ("kick", "mute", "ban")
RG_TIMES = (120, 300, 600, 1800, 3600)
RG_TIME_DEFAULT, RG_TIME_MIN, RG_TIME_MAX = 300, 60, 86400


def gate_on(chat_id):
    return D.get_setting(chat_id, RG_KEY, "off") == "on"


def gate_secs(chat_id):
    secs = _num_setting(chat_id, RG_TIME_KEY, RG_TIME_DEFAULT)
    return secs if RG_TIME_MIN <= secs <= RG_TIME_MAX else RG_TIME_DEFAULT


def gate_action(chat_id):
    action = D.get_setting(chat_id, RG_ACTION_KEY, "kick")
    return action if action in RG_ACTIONS else "kick"


def gate_needed(chat_id):
    """The gate is ON and the group has rules to accept."""
    return gate_on(chat_id) and bool(D.get_setting(chat_id, "rules"))


_rg_origin = {}         # (chat_id, panel message id) -> True when the panel was opened from /help page 2 (Back goes there)


def gate_button(chat, from_more=False):
    """The 📜 button nova.py adds to /help > Rules and to /help page 2 "More Features" (groups only; `from_more` makes the
    panel's Back button return to page 2)."""
    return InlineKeyboardButton(L.t("rg.btn_help", getattr(chat, "id", None)), callback_data="rg:q" if from_more else "rg:p")


async def gate_start(context, chat, user, after_captcha=False):
    """Mutes the member and posts the "read the rules, tap I accept" message. Returns True when the gate is up (the caller then
    does not send the welcome yet); False when there is no gate for this member (or Telegram refused)."""
    if not gate_needed(chat.id):
        return False
    secs = gate_secs(chat.id)
    pending = await asyncio.to_thread(store.gate_get, chat.id, user.id)
    if pending:                                       # they rejoined while waiting: one message only
        try:
            await context.bot.delete_message(chat.id, pending[0])
        except TelegramError:
            pass
    elif not after_captcha:
        try:
            member = await chat.get_member(user.id)
            if member.status == "restricted" and not getattr(member, "can_send_messages", True):
                return False                          # already muted by an admin: don't override that
        except TelegramError:
            pass
    try:
        await chat.restrict_member(user.id, CLOSED_PERMS)
    except TelegramError as e:
        log.warning("rules gate: can't restrict in chat %s: %s", chat.id, e)
        return False
    kb = InlineKeyboardMarkup([[await D.rules_button(context, chat.id)],
                               [InlineKeyboardButton(L.t("rg.btn_accept", chat.id), callback_data=f"rg:a:{user.id}")]])
    try:
        sent = await chat.send_message(L.t("rg.ask", chat.id, user=user.mention_html(), dur=extra.fmt_duration(secs)), parse_mode="HTML", reply_markup=kb)
    except TelegramError as e:
        log.warning("rules gate: couldn't post the message in chat %s: %s", chat.id, e)
        await D.restore_permissions(_Args((), context.bot), chat, user.id)
        return False
    await asyncio.to_thread(store.gate_put, chat.id, user.id, sent.message_id, time.time() + secs, user.mention_html())
    return True


async def gate_cleanup(bot, chat_id, user_id):
    """A member left while waiting: drop the message and the record."""
    msg_id = await asyncio.to_thread(store.gate_pop, chat_id, user_id)
    if msg_id:
        try:
            await bot.delete_message(chat_id, msg_id)
        except TelegramError:
            pass


async def gate_release_all(bot, chat):
    """The gate was turned OFF: everyone still waiting is let in."""
    for user_id, msg_id in await asyncio.to_thread(store.gate_pop_chat, chat.id):
        try:
            await bot.delete_message(chat.id, msg_id)
        except TelegramError:
            pass
        await D.restore_permissions(_Args((), bot), chat, user_id)


async def _gate_round(bot):
    """Part of run_once (every 30 seconds): applies the chosen action to members who didn't accept in time."""
    for chat_id, user_id, msg_id, mention in await asyncio.to_thread(store.gate_take_expired, int(time.time())):
        try:
            await bot.delete_message(chat_id, msg_id)
        except TelegramError:
            pass
        try:
            chat = await bot.get_chat(chat_id)
            mode = gate_action(chat_id)
            if not await D.do_action(chat, user_id, mode):
                continue
            kind, secs = extra.mode_kind(mode)
            label, punish, reason = extra.ACTION_LABEL.get(kind, kind.title()), extra.punishment_text(kind, secs), "Didn't accept the rules in time"
            await D.announce(chat, extra.action_notice(mention, label, reason, punish, chat_id=chat_id), user_id)
            await extra.record_action(chat_id, user_id, mention, label, reason, punish, None, "mod", kind=kind)
        except Exception:
            log.exception("rules gate: applying the action failed in %s", chat_id)


async def _rg_accept(update, context, user_id):
    q, chat = update.callback_query, update.callback_query.message.chat
    if q.from_user.id != user_id:
        await q.answer(L.t("rg.not_you", chat.id), show_alert=True)
        return
    if not await asyncio.to_thread(store.gate_delete, chat.id, user_id):
        await q.answer(L.t("rg.expired", chat.id))
        return
    if not await D.restore_permissions(context, chat, user_id):
        await asyncio.to_thread(store.gate_put, chat.id, user_id, q.message.message_id, time.time() + gate_secs(chat.id), q.from_user.mention_html())
        await q.answer(L.t("rg.unmute_failed", chat.id), show_alert=True)       # still waiting: they can tap again
        return
    await q.answer(L.t("rg.accepted", chat.id))
    try:
        await q.message.delete()
    except TelegramError:
        pass
    await D.send_welcome(context, chat, q.from_user)


# ------------------------------------------------------------------ the panel
async def _rg_panel(chat, note="", back="help:rules"):
    cid = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("rg.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    on, secs, action = gate_on(cid), gate_secs(cid), gate_action(cid)
    try:
        waiting = await asyncio.to_thread(store.gate_count, cid)
    except Exception:
        waiting = 0
    text = (L.t("rg.title", cid) + "\n\n" + (note + "\n\n" if note else "") + L.t("rg.intro", cid) + "\n\n" +
            L.t("rg.status_on" if on else "rg.status_off", cid) + "\n" +
            ((L.t("rg.no_rules", cid) + "\n") if on and not D.get_setting(cid, "rules") else "") +
            L.t("rg.time_line", cid, dur=extra.fmt_duration(secs)) + "\n" + L.t("rg.action_line", cid, action=L.t("rg.a_" + action, cid)) + "\n" +
            L.t("rg.waiting", cid, n=waiting) + "\n\n" + L.t("rg.note", cid))
    mark = lambda cond: "✅ " if cond else ""
    rows = [[InlineKeyboardButton(L.t("rg.btn_off" if on else "rg.btn_on", cid), callback_data="rg:t")]]
    rows += _pairs([InlineKeyboardButton(mark(s == secs) + "⏱ " + extra.fmt_duration(s), callback_data=f"rg:m:{s}") for s in RG_TIMES])
    rows += _pairs([InlineKeyboardButton(mark(a == action) + L.t("rg.act_" + a, cid), callback_data=f"rg:x:{a}") for a in RG_ACTIONS])
    rows.append([InlineKeyboardButton(L.t("pick.back", cid), callback_data=back)])
    return text, InlineKeyboardMarkup(rows)


async def _rg_set_on(bot, chat, on):
    D.set_setting(chat.id, RG_KEY, "on" if on else "off")
    if not on:
        await gate_release_all(bot, chat)


async def rg_callback(update, context):
    """\"rg:a:<user id>\" the member's own ✅ I accept (anyone else is told it isn't theirs); for admins in a group: \"rg:p\" panel
    (\"rg:q\": the same, opened from /help page 2),
    \"rg:t\" on/off, \"rg:m:<seconds>\" time, \"rg:x:<kick|mute|ban>\" action."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    parts = (q.data or "").split(":")[1:]
    if len(parts) == 2 and parts[0] == "a":
        uid = _ac_num(parts[1], 1, 10 ** 15)
        if uid is None:
            await q.answer(L.t("rg.invalid", chat.id), show_alert=True)
            return
        await _rg_accept(update, context, uid)
        return
    if await extra.menu_not_owner(q):
        return
    if chat.type == "private":
        await q.answer(L.t("rg.private"), show_alert=True)
        return
    cid = chat.id
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("rg.admin_only", cid), show_alert=True)
        return
    act, arg = (parts[0] if parts else ""), (parts[1] if len(parts) == 2 else None)
    num = _ac_num(arg, 0, 10 ** 7) if arg is not None else None
    toast = None
    if act in ("p", "q") and len(parts) == 1:               # "q" = opened from /help page 2: Back returns there
        _rg_origin[(cid, q.message.message_id)] = act == "q"
    back = "help:more" if _rg_origin.get((cid, q.message.message_id)) else "help:rules"
    try:
        if act in ("p", "q") and len(parts) == 1:
            pass
        elif act == "t" and len(parts) == 1:
            on = not gate_on(cid)
            await _rg_set_on(context.bot, chat, on)
            toast = L.t("rg.t_on" if on else "rg.t_off", cid)
        elif act == "m" and num in RG_TIMES:
            D.set_setting(cid, RG_TIME_KEY, num)
            toast = L.t("rg.t_time", cid, dur=extra.fmt_duration(num))
        elif act == "x" and arg in RG_ACTIONS:
            D.set_setting(cid, RG_ACTION_KEY, arg)
            toast = L.t("rg.t_action", cid, action=L.t("rg.a_" + arg, cid))
        else:
            await q.answer(L.t("rg.invalid", cid), show_alert=True)
            return
        await q.answer(toast)
        await _ac_edit(q, *await _rg_panel(chat, back=back))
    except Exception:
        log.exception("rules gate: panel action failed in %s", cid)
        await q.answer(L.t("ac.db_problem", cid), show_alert=True)


async def gate_cmd(update, context):
    """/gate  |  on | off  |  10m  |  kick | mute | ban   (any of them together, like /gate on 10m kick)"""
    if not await D.group_only(update):
        return
    chat, msg, notes = update.effective_chat, update.effective_message, []
    for arg in (a.lower() for a in (context.args or [])):
        if arg in ("on", "off"):
            await _rg_set_on(context.bot, chat, arg == "on")
            notes.append(L.t("rg.t_on" if arg == "on" else "rg.t_off", chat.id))
        elif arg in RG_ACTIONS:
            D.set_setting(chat.id, RG_ACTION_KEY, arg)
            notes.append(L.t("rg.t_action", chat.id, action=L.t("rg.a_" + arg, chat.id)))
        elif _parse_secs(arg, RG_TIME_MIN, RG_TIME_MAX):
            secs = _parse_secs(arg, RG_TIME_MIN, RG_TIME_MAX)
            D.set_setting(chat.id, RG_TIME_KEY, secs)
            notes.append(L.t("rg.t_time", chat.id, dur=extra.fmt_duration(secs)))
        else:
            await msg.reply_html(L.t("rg.usage", chat.id))
            return
    text, markup = await _rg_panel(chat, "\n".join(notes))
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


# ======================================================================================================
# 2l. WEEKLY SHOUT-OUT  (reads the message counts of msgcount.py)
# ======================================================================================================
# A weekly "top chatters" post that the admins write themselves. Settings (per group):
#   shout_on "on"|"off" (default off) · shout_day 0-6 (Monday = 0, default Sunday) · shout_time minutes after midnight (default 9 PM,
#   in BOT_TIMEZONE) · shout_top 1-10 members (default 3) · shout_mention "on"|"off" (default on: names are links that notify)
#   · shout_text = the admins' own message (empty = the built-in one) · shout_last = Monday of the week already posted.
# The week is the one /week shows (Monday to Sunday, IST): posted on a Sunday it is this week, on any other day the week that just
# ended. One post per week; a week nobody chatted in posts nothing. The 30-second loop (run_once -> _shout_round) posts it.
# Placeholders in the text: {group} {week} {list} {winner} {count} {total} {people} {top} and, per rank 1-10, {name1} {count1}
# {mention1}. Unknown ones stay as typed; ranks nobody reached are empty. Admin HTML (<b>...</b>) works; broken markup falls back to plain.
# Panel: 📊 Count > 🏆 Weekly Shout-out, or /help page 2 (callbacks "so:..."), or /shout:
#   /shout  |  on | off  |  sun 9pm  |  top 5  |  text <message>  |  reset  |  mention on|off  |  now
SO_KEY, SO_DAY_KEY, SO_TIME_KEY, SO_TOP_KEY = "shout_on", "shout_day", "shout_time", "shout_top"
SO_TEXT_KEY, SO_MENTION_KEY, SO_LAST_KEY = "shout_text", "shout_mention", "shout_last"
SO_DAY_DEFAULT, SO_TIME_DEFAULT, SO_TOP_DEFAULT = 6, 21 * 60, 3
SO_TIMES = (540, 720, 1080, 1260, 1320)
SO_TOPS = (1, 3, 5, 10)
SO_MAX_TOP, SO_MAX_TEXT, SO_PREVIEW_SECS, SO_PENDING_SECS = 10, 1500, 60, 300
SO_DAY_WORDS = {"mon": 0, "monday": 0, "tue": 1, "tues": 1, "tuesday": 1, "wed": 2, "wednesday": 2, "thu": 3, "thur": 3, "thurs": 3,
                "thursday": 3, "fri": 4, "friday": 4, "sat": 5, "saturday": 5, "sun": 6, "sunday": 6}
_SO_MEDALS = {1: "🥇", 2: "🥈", 3: "🥉"}
_SO_TOKEN = re.compile(r"\{(group|week|list|winner|count|total|people|top|(?:name|count|mention)(?:10|[1-9]))\}")
_so_pending = {}        # (chat_id, admin id) -> {"panel": (chat id, message id), "until": monotonic time}
_so_origin = {}         # (chat_id, panel message id) -> True when the panel was opened from /help page 2 (Back goes there)


def _now_weekday():
    return datetime.now(_tz()).weekday()


def so_on(chat_id):
    return D.get_setting(chat_id, SO_KEY, "off") == "on"


def so_day(chat_id):
    day = _num_setting(chat_id, SO_DAY_KEY, SO_DAY_DEFAULT)
    return day if 0 <= day <= 6 else SO_DAY_DEFAULT


def so_time(chat_id):
    mins = _num_setting(chat_id, SO_TIME_KEY, SO_TIME_DEFAULT)
    return mins if 0 <= mins < 1440 else SO_TIME_DEFAULT


def so_top(chat_id):
    top = _num_setting(chat_id, SO_TOP_KEY, SO_TOP_DEFAULT)
    return top if 1 <= top <= SO_MAX_TOP else SO_TOP_DEFAULT


def so_mention(chat_id):
    return D.get_setting(chat_id, SO_MENTION_KEY, "on") == "on"


def so_text(chat_id):
    return str(D.get_setting(chat_id, SO_TEXT_KEY, "") or "")[:SO_MAX_TEXT]


def shout_week(day=SO_DAY_DEFAULT, now=None):
    """(first day, last day) of the week the shout-out reports, as the IST day strings the message counts use."""
    _, wk0, wk1 = msgcount.periods(now)
    if day == 6:
        return wk0, wk1
    start = date.fromisoformat(wk0) - timedelta(days=7)
    return start.isoformat(), (start + timedelta(days=6)).isoformat()


def _so_week_text(lo, hi):
    a, b = date.fromisoformat(lo), date.fromisoformat(hi)
    return f"{a.day} {a.strftime('%b')} - {b.day} {b.strftime('%b')}"


def so_render(chat_id, title, rows, people, total, lo, hi):
    """The message: the admins' text (or the built-in one) with the placeholders filled in."""
    link = so_mention(chat_id)

    def name_of(uid, name):
        return html.escape((name or "").strip()[:32] or L.t("mc.user_n", chat_id, uid=uid))

    def who(uid, name, force=False):
        return f'<a href="tg://user?id={uid}">{name_of(uid, name)}</a>' if (link or force) else name_of(uid, name)

    vals = {"group": html.escape(title or ""), "week": _so_week_text(lo, hi), "total": f"{total:,}", "people": f"{people:,}",
            "top": str(len(rows)), "winner": who(*rows[0][:2]) if rows else "", "count": f"{rows[0][2]:,}" if rows else ""}
    lines = []
    for i, (uid, name, n) in enumerate(rows, 1):
        lines.append(f"{_SO_MEDALS.get(i, f'{i}.')} {who(uid, name)} - {L.t('so.messages', chat_id, n=f'{n:,}')}")
        vals[f"name{i}"], vals[f"count{i}"], vals[f"mention{i}"] = name_of(uid, name), f"{n:,}", who(uid, name, force=True)
    vals["list"] = "\n".join(lines)
    return _SO_TOKEN.sub(lambda m: vals.get(m.group(1), ""), so_text(chat_id) or L.t("so.default", chat_id))


async def shout_post(bot, chat_id, delete_after=None):
    """Builds and posts this group's shout-out. Returns "sent", "empty" (nobody chatted that week) or "error"."""
    if msgcount is None:
        return "error"
    lo, hi = shout_week(so_day(chat_id))
    try:
        rows, people, total = await msgcount.top_between(chat_id, lo, hi, so_top(chat_id))
    except Exception:
        log.exception("shout-out: couldn't read the message counts of %s", chat_id)
        return "error"
    if not rows:
        return "empty"
    try:
        title = (await bot.get_chat(chat_id)).title
    except TelegramError:
        title = ""
    try:
        sent = await D.safe_html(functools.partial(bot.send_message, chat_id, disable_web_page_preview=True),
                                 so_render(chat_id, title, rows, people, total, lo, hi))
    except TelegramError as e:
        log.warning("shout-out: couldn't post in %s: %s", chat_id, e)
        return "error"
    if delete_after and sent is not None:
        await extra.track_notice(sent, delete_after)
    return "sent"


async def _shout_round(bot):
    """Part of run_once (every 30 seconds): posts the week's shout-out once, on the chosen day after the chosen time."""
    for chat_id, value in await asyncio.to_thread(_scheduled_groups, SO_KEY):
        try:
            if value != "on" or chat_id >= 0 or D.is_paused(chat_id):
                continue
            day = so_day(chat_id)
            if _now_weekday() != day or _now_minutes() < so_time(chat_id):
                continue
            lo, _ = shout_week(day)
            if D.get_setting(chat_id, SO_LAST_KEY, "") == lo or time.monotonic() < _retry_at.get((chat_id, "shout"), 0):
                continue
            if await shout_post(bot, chat_id) == "error":
                _retry_at[(chat_id, "shout")] = time.monotonic() + RETRY_AFTER      # try again in a few minutes
            else:
                D.set_setting(chat_id, SO_LAST_KEY, lo)                             # "sent" or "empty": this week is done
        except Exception:
            log.exception("shout-out: the round failed for %s", chat_id)


# ------------------------------------------------------------------ the panel
def shout_button(chat):
    return InlineKeyboardButton(L.t("mo.b_so", getattr(chat, "id", None)), callback_data="so:q")


def _so_when(chat_id):
    return L.t("so.when", chat_id, day=L.t(f"so.d_{so_day(chat_id)}", chat_id), time=fmt_12h(so_time(chat_id)), tz=_tz_label(chat_id))


def _so_panel(chat, note="", back="mc:d"):
    cid = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("so.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    on, day, when, top, link = so_on(cid), so_day(cid), so_time(cid), so_top(cid), so_mention(cid)
    custom = so_text(cid)
    text = (L.t("so.title", cid) + "\n\n" + (note + "\n\n" if note else "") + L.t("so.intro", cid) + "\n\n" +
            L.t("so.status_on" if on else "so.status_off", cid) + "\n" + _so_when(cid) + "\n" + L.t("so.top_line", cid, n=top) + "\n" +
            L.t("so.mention_on" if link else "so.mention_off", cid) + "\n" +
            (L.t("so.text_custom", cid, n=len(custom)) if custom else L.t("so.text_default", cid)) + "\n\n" + L.t("so.note", cid))
    mark = lambda cond: "✅ " if cond else ""
    rows = _pairs([InlineKeyboardButton(L.t("so.btn_off" if on else "so.btn_on", cid), callback_data="so:t"),
                   InlineKeyboardButton(L.t("so.btn_preview", cid), callback_data="so:v")])
    rows += _pairs([InlineKeyboardButton(mark(d == day) + L.t(f"so.ds_{d}", cid), callback_data=f"so:d:{d}") for d in range(7)])
    rows += _pairs([InlineKeyboardButton(mark(m == when) + "🕘 " + fmt_12h(m), callback_data=f"so:h:{m}") for m in SO_TIMES])
    rows += _pairs([InlineKeyboardButton(mark(n == top) + L.t("so.b_top", cid, n=n), callback_data=f"so:n:{n}") for n in SO_TOPS])
    rows += _pairs([InlineKeyboardButton(L.t("so.btn_mention_off" if link else "so.btn_mention_on", cid), callback_data="so:m"),
                    InlineKeyboardButton(L.t("so.btn_text", cid), callback_data="so:x"),
                    InlineKeyboardButton(L.t("so.btn_default", cid), callback_data="so:r"),
                    InlineKeyboardButton(L.t("so.btn_now", cid), callback_data="so:g")])
    rows.append([InlineKeyboardButton(L.t("so.btn_cmd", cid), callback_data="so:c")])
    rows.append([InlineKeyboardButton(L.t("pick.back", cid), callback_data=back)])
    return text, InlineKeyboardMarkup(rows)


def _so_command_page(chat=None):
    cid = getattr(chat, "id", None)
    return (L.t("so.cmd_page", cid, tz=_tz_label(cid)), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="so:p")]]))


def _so_result_note(chat_id, result):
    return L.t({"sent": "so.t_sent", "empty": "so.t_empty"}.get(result, "so.t_error"), chat_id)


async def so_callback(update, context):
    """\"so:p\" panel (\"so:q\": opened from /help page 2), \"so:t\" on/off, \"so:d:<0-6>\" day, \"so:h:<minutes>\" time, \"so:n:<members>\", \"so:m\" mentions,
    \"so:v\" preview, \"so:g\" post now, \"so:x\" write the text, \"so:r\" built-in text, \"so:c\" commands. Admins only (\"so:c\" is just information)."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    parts = (q.data or "").split(":")[1:]
    act, arg = (parts[0] if parts else ""), (parts[1] if len(parts) == 2 else None)
    if parts == ["c"]:
        await q.answer()
        await _ac_edit(q, *_so_command_page(chat))
        return
    if chat.type == "private":
        await q.answer(L.t("so.private"), show_alert=True)
        return
    cid = chat.id
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("so.admin_only", cid), show_alert=True)
        return
    if parts in (["p"], ["q"]):
        _so_origin[(cid, q.message.message_id)] = parts == ["q"]
    back = "help:more" if _so_origin.get((cid, q.message.message_id)) else "mc:d"
    num = _ac_num(arg, 0, 10 ** 7) if arg is not None else None
    toast = None
    try:
        if parts in (["p"], ["q"]):
            pass
        elif parts == ["t"]:
            on = not so_on(cid)
            D.set_setting(cid, SO_KEY, "on" if on else "off")
            toast = L.t("so.t_on" if on else "so.t_off", cid)
        elif act == "d" and num is not None and 0 <= num <= 6 and arg is not None:
            D.set_setting(cid, SO_DAY_KEY, num)
            toast = L.t("so.t_when", cid, when=_so_when_text(num, so_time(cid), cid))
        elif act == "h" and num in SO_TIMES:
            D.set_setting(cid, SO_TIME_KEY, num)
            toast = L.t("so.t_when", cid, when=_so_when_text(so_day(cid), num, cid))
        elif act == "n" and num in SO_TOPS:
            D.set_setting(cid, SO_TOP_KEY, num)
            toast = L.t("so.t_top", cid, n=num)
        elif parts == ["m"]:
            link = not so_mention(cid)
            D.set_setting(cid, SO_MENTION_KEY, "on" if link else "off")
            toast = L.t("so.t_mention_on" if link else "so.t_mention_off", cid)
        elif parts == ["r"]:
            D.set_setting(cid, SO_TEXT_KEY, "")
            toast = L.t("so.t_reset", cid)
        elif parts == ["v"] or parts == ["g"]:
            result = await shout_post(context.bot, cid, delete_after=SO_PREVIEW_SECS if parts == ["v"] else None)
            await q.answer(_so_result_note(cid, result), show_alert=result != "sent")
            return
        elif parts == ["x"]:
            _so_pending[(cid, q.from_user.id)] = {"panel": (cid, q.message.message_id), "until": time.monotonic() + SO_PENDING_SECS}
            await q.answer(L.t("so.t_ask", cid))
            await chat.send_message(L.t("so.ask", cid, user=q.from_user.mention_html(), max=SO_MAX_TEXT), parse_mode="HTML")
            return
        else:
            await q.answer(L.t("so.invalid", cid), show_alert=True)
            return
        await q.answer(toast)
        await _ac_edit(q, *_so_panel(chat, back=back))
    except Exception:
        log.exception("shout-out: panel action failed in %s", cid)
        await q.answer(L.t("ac.db_problem", cid), show_alert=True)


def _so_when_text(day, mins, chat_id):
    return L.t("so.when_short", chat_id, day=L.t(f"so.d_{day}", chat_id), time=fmt_12h(mins))


async def so_input(update, context):
    """group=-12, cheap: only acts when the admin tapped ✏️ Text and now sends the message (or "cancel" / "default")."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or not _so_pending:
        return
    key = (chat.id, user.id)
    pending = _so_pending.get(key)
    if pending is None:
        return
    if time.monotonic() > pending["until"] or not await D.is_admin(chat, user.id):
        _so_pending.pop(key, None)
        return
    text = (msg.text or "").strip()
    if text.lower() in ("cancel", "stop"):
        _so_pending.pop(key, None)
        await _rp_note(msg, "so.t_cancel", 10)
        raise ApplicationHandlerStop
    if len(text) > SO_MAX_TEXT:
        await _rp_note(msg, "so.err_long", 15, max=SO_MAX_TEXT)
        raise ApplicationHandlerStop
    _so_pending.pop(key, None)
    D.set_setting(chat.id, SO_TEXT_KEY, "" if text.lower() == "default" else text)
    try:
        await msg.delete()
    except TelegramError:
        pass
    try:
        panel_chat, panel_id = pending["panel"]
        screen, kb = _so_panel(chat, L.t("so.t_saved", chat.id), back="help:more" if _so_origin.get(pending["panel"]) else "mc:d")
        await context.bot.edit_message_text(screen, chat_id=panel_chat, message_id=panel_id, parse_mode="HTML", reply_markup=kb,
                                            disable_web_page_preview=True)
    except TelegramError:
        await _rp_note(msg, "so.t_saved", 10)
    raise ApplicationHandlerStop


def _so_parse_when(tokens):
    """Day names and a time in any order ('sun 9pm', '9 pm monday', '21:00') -> (day or None, minutes or None, ok)."""
    day = mins = None
    tokens = [t.lower() for t in tokens]
    i = 0
    while i < len(tokens):
        t = tokens[i]
        if t in SO_DAY_WORDS and day is None:
            day = SO_DAY_WORDS[t]
        else:
            if i + 1 < len(tokens) and tokens[i + 1] in ("am", "pm"):
                t, i = t + tokens[i + 1], i + 1
            parsed = parse_time(t)
            if parsed is None or mins is not None:
                return None, None, False
            mins = parsed
        i += 1
    return day, mins, True


async def shout_cmd(update, context):
    """/shout  |  on | off  |  sun 9pm  |  top 5  |  text <message>  |  reset  |  mention on|off  |  now"""
    if not await D.group_only(update):
        return
    chat, msg, args, note = update.effective_chat, update.effective_message, list(context.args or []), ""
    cid, first = chat.id, (args[0].lower() if args else "")
    if not args:
        pass
    elif first in ("on", "off") and len(args) == 1:
        D.set_setting(cid, SO_KEY, first)
        note = L.t("so.t_on" if first == "on" else "so.t_off", cid)
    elif first == "reset" and len(args) == 1:
        D.set_setting(cid, SO_TEXT_KEY, "")
        note = L.t("so.t_reset", cid)
    elif first == "now" and len(args) == 1:
        note = _so_result_note(cid, await shout_post(context.bot, cid))
    elif first == "top" and len(args) == 2:
        n = _ac_num(args[1], 1, SO_MAX_TOP)
        if n is None:
            await msg.reply_html(L.t("so.usage", cid))
            return
        D.set_setting(cid, SO_TOP_KEY, n)
        note = L.t("so.t_top", cid, n=n)
    elif first == "mention" and len(args) == 2 and args[1].lower() in ("on", "off"):
        D.set_setting(cid, SO_MENTION_KEY, args[1].lower())
        note = L.t("so.t_mention_on" if args[1].lower() == "on" else "so.t_mention_off", cid)
    elif first == "text":
        raw = (msg.text or "").split(None, 2)                 # keeps the admin's line breaks
        value = raw[2].strip() if len(raw) == 3 else ""
        if not value:
            await msg.reply_html(L.t("so.usage", cid))
            return
        if len(value) > SO_MAX_TEXT:
            await msg.reply_html(L.t("so.err_long", cid, max=SO_MAX_TEXT))
            return
        D.set_setting(cid, SO_TEXT_KEY, value)
        note = L.t("so.t_saved", cid)
    else:
        day, mins, ok = _so_parse_when(args)
        if not ok or (day is None and mins is None):
            await msg.reply_html(L.t("so.usage", cid))
            return
        if day is not None:
            D.set_setting(cid, SO_DAY_KEY, day)
        if mins is not None:
            D.set_setting(cid, SO_TIME_KEY, mins)
        note = L.t("so.t_when", cid, when=_so_when_text(so_day(cid), so_time(cid), cid))
    text, markup = _so_panel(chat, note)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


# ======================================================================================================
# 2m. JOIN ANNIVERSARIES  (birthdays already have their own system in fun_systems.py: 🎂 Birthday)
# ======================================================================================================
# On the day a member joined (every year after the first) the bot posts ONE short thank-you for everybody who has an anniversary
# that day, in the admins' own words. Where the date comes from (collection "member_since", store.since_*):
#   * every join the bot sees (handler group 106) sets the date (leaving deletes it, a rejoin starts again);
#   * people who were already here have no join date: with `anniv_seen` ON (default) the first message the bot sees from them
#     (handler group 107, checked once per member per run) counts as their date. A join date is never replaced by a seen date.
# Settings: anniv_on "on"|"off" (default off) · anniv_time minutes after midnight in BOT_TIMEZONE (default 9 AM) · anniv_text (own text,
# empty = built-in) · anniv_seen "on"|"off" · anniv_last = the day already posted. The 30-second loop (run_once -> _anniv_round) posts it.
# Text placeholders: {group} {date} {count} {list} (one line per member: mention and years). A 29 Feb join is celebrated on 28 Feb
# in years that have no 29 Feb. Panel: /help page 2 > 🎖 Anniversary (callbacks "an:..."), or /anniv:
#   /anniv  |  on | off  |  9am  |  text <message>  |  reset  |  old on|off  |  now
AN_KEY, AN_TIME_KEY, AN_TEXT_KEY, AN_SEEN_KEY, AN_LAST_KEY = "anniv_on", "anniv_time", "anniv_text", "anniv_seen", "anniv_last"
AN_TIME_DEFAULT = 9 * 60
AN_TIMES = (540, 720, 1080, 1260)
AN_MAX_TEXT, AN_MAX_LINES, AN_PREVIEW_SECS, AN_PENDING_SECS, AN_KNOWN_MAX = 1500, 20, 60, 300, 50000
_AN_TOKEN = re.compile(r"\{(group|date|count|list)\}")
_an_known = set()       # (chat_id, user_id) whose join / first-seen date was already written during this run
_an_pending = {}        # (chat_id, admin id) -> {"panel": (chat id, message id), "until": monotonic time}
_an_origin = {}         # (chat_id, panel message id) -> True: opened from /help page 2 (the only way in, so Back goes there)


def _local_today():
    return datetime.now(_tz()).date()


def an_on(chat_id):
    return D.get_setting(chat_id, AN_KEY, "off") == "on"


def an_time(chat_id):
    mins = _num_setting(chat_id, AN_TIME_KEY, AN_TIME_DEFAULT)
    return mins if 0 <= mins < 1440 else AN_TIME_DEFAULT


def an_seen_on(chat_id):
    return D.get_setting(chat_id, AN_SEEN_KEY, "on") == "on"


def an_text(chat_id):
    return str(D.get_setting(chat_id, AN_TEXT_KEY, "") or "")[:AN_MAX_TEXT]


def _an_md_y(ts):
    d = datetime.fromtimestamp(ts, _tz())
    return f"{d.month:02d}-{d.day:02d}", d.year


def _an_mds(today):
    """The 'MM-DD' join days celebrated on `today` (29 Feb joiners on 28 Feb in years without a 29 Feb)."""
    leap = today.year % 4 == 0 and (today.year % 100 != 0 or today.year % 400 == 0)
    return ["02-28", "02-29"] if (today.month, today.day) == (2, 28) and not leap else [f"{today.month:02d}-{today.day:02d}"]


def _an_name(user):
    return (getattr(user, "full_name", None) or getattr(user, "first_name", None) or "")[:60]


# ------------------------------------------------------------------ recording the dates
async def anniv_members(update, context):
    """group=106: a member joined (their date is set) or left (their date is deleted)."""
    msg, chat = update.effective_message, update.effective_chat
    if not msg or chat.type == "private":
        return
    now = int(time.time())
    for user in msg.new_chat_members or []:
        if not user.is_bot:
            md, year = _an_md_y(now)
            await asyncio.to_thread(store.since_put_join, chat.id, user.id, now, _an_name(user), md, year)
            _an_known.add((chat.id, user.id))
    left = getattr(msg, "left_chat_member", None)
    if left is not None and not left.is_bot:
        await asyncio.to_thread(store.since_delete, chat.id, left.id)
        _an_known.discard((chat.id, left.id))


async def anniv_seen(update, context):
    """group=107, cheap: the first message of a member the bot has no date for gives them one (only where Anniversary is ON)."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or user.is_bot or chat.type == "private" or not an_on(chat.id) or not an_seen_on(chat.id):
        return
    key = (chat.id, user.id)
    if key in _an_known:
        return
    if len(_an_known) > AN_KNOWN_MAX:
        _an_known.clear()
    _an_known.add(key)
    now = int(time.time())
    md, year = _an_md_y(now)
    await asyncio.to_thread(store.since_put_seen, chat.id, user.id, now, _an_name(user), md, year)


# ------------------------------------------------------------------ the post
def an_render(chat_id, title, people, today):
    """people: [(user_id, name, years)], longest members first."""
    def years_text(n):
        return L.t("an.year_1" if n == 1 else "an.year_n", chat_id, n=n)

    lines = [f'🎖 <a href="tg://user?id={uid}">{html.escape((name or "").strip()[:32] or L.t("mc.user_n", chat_id, uid=uid))}</a> - {years_text(years)}'
             for uid, name, years in people[:AN_MAX_LINES]]
    if len(people) > AN_MAX_LINES:
        lines.append(L.t("an.more", chat_id, n=len(people) - AN_MAX_LINES))
    vals = {"group": html.escape(title or ""), "date": f"{today.day} {today.strftime('%b')}", "count": str(len(people)), "list": "\n".join(lines)}
    return _AN_TOKEN.sub(lambda m: vals[m.group(1)], an_text(chat_id) or L.t("an.default", chat_id))


async def anniv_post(bot, chat_id, today=None, sample_user=None, delete_after=None):
    """Posts today's anniversaries. Returns "sent", "empty" (none today), "sample" (none today, an example was posted for `sample_user`) or "error"."""
    today = today or _local_today()
    try:
        rows = await asyncio.to_thread(store.since_on_day, chat_id, _an_mds(today), today.year, AN_MAX_LINES + 10)
    except Exception:
        log.exception("anniversary: couldn't read the dates of %s", chat_id)
        return "error"
    people = []
    for uid, name, year in rows:
        try:
            member = await bot.get_chat_member(chat_id, uid)
            if member.status in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED):
                await asyncio.to_thread(store.since_delete, chat_id, uid)          # not in the group any more
                continue
            name = _an_name(getattr(member, "user", None)) or name
        except TelegramError:
            pass                                                                    # can't check: keep them
        people.append((uid, name, today.year - year))
    sample = False
    if not people:
        if sample_user is None:
            return "empty"
        people, sample = [(sample_user.id, _an_name(sample_user), 2)], True
    try:
        title = (await bot.get_chat(chat_id)).title
    except TelegramError:
        title = ""
    try:
        sent = await D.safe_html(functools.partial(bot.send_message, chat_id, disable_web_page_preview=True), an_render(chat_id, title, people, today))
    except TelegramError as e:
        log.warning("anniversary: couldn't post in %s: %s", chat_id, e)
        return "error"
    if delete_after and sent is not None:
        await extra.track_notice(sent, delete_after)
    return "sample" if sample else "sent"


async def _anniv_round(bot):
    """Part of run_once (every 30 seconds): posts today's anniversaries once, after the chosen time."""
    for chat_id, value in await asyncio.to_thread(_scheduled_groups, AN_KEY):
        try:
            if value != "on" or chat_id >= 0 or D.is_paused(chat_id):
                continue
            today = _local_today()
            if _now_minutes() < an_time(chat_id) or D.get_setting(chat_id, AN_LAST_KEY, "") == today.isoformat():
                continue
            if time.monotonic() < _retry_at.get((chat_id, "anniv"), 0):
                continue
            if await anniv_post(bot, chat_id, today) == "error":
                _retry_at[(chat_id, "anniv")] = time.monotonic() + RETRY_AFTER      # try again in a few minutes
            else:
                D.set_setting(chat_id, AN_LAST_KEY, today.isoformat())              # "sent" or "empty": today is done
        except Exception:
            log.exception("anniversary: the round failed for %s", chat_id)


# ------------------------------------------------------------------ the panel
def anniv_button(chat):
    return InlineKeyboardButton(L.t("mo.b_an", getattr(chat, "id", None)), callback_data="an:q")


def _an_panel(chat, note=""):
    cid = getattr(chat, "id", None)
    if chat is None or chat.type == "private":
        return L.t("an.private", cid), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]])
    on, when, seen, custom = an_on(cid), an_time(cid), an_seen_on(cid), an_text(cid)
    try:
        known = store.since_count(cid)
    except Exception:
        known = 0
    text = (L.t("an.title", cid) + "\n\n" + (note + "\n\n" if note else "") + L.t("an.intro", cid) + "\n\n" +
            L.t("an.status_on" if on else "an.status_off", cid) + "\n" + L.t("an.when", cid, time=fmt_12h(when), tz=_tz_label(cid)) + "\n" +
            L.t("an.known", cid, n=known) + "\n" + L.t("an.seen_on" if seen else "an.seen_off", cid) + "\n" +
            (L.t("an.text_custom", cid, n=len(custom)) if custom else L.t("an.text_default", cid)) + "\n\n" + L.t("an.note", cid))
    mark = lambda cond: "✅ " if cond else ""
    rows = _pairs([InlineKeyboardButton(L.t("an.btn_off" if on else "an.btn_on", cid), callback_data="an:t"),
                   InlineKeyboardButton(L.t("an.btn_preview", cid), callback_data="an:v")])
    rows += _pairs([InlineKeyboardButton(mark(m == when) + "🕘 " + fmt_12h(m), callback_data=f"an:h:{m}") for m in AN_TIMES])
    rows += _pairs([InlineKeyboardButton(L.t("an.btn_text", cid), callback_data="an:x"), InlineKeyboardButton(L.t("an.btn_default", cid), callback_data="an:r"),
                    InlineKeyboardButton(L.t("an.btn_seen_off" if seen else "an.btn_seen_on", cid), callback_data="an:s"),
                    InlineKeyboardButton(L.t("an.btn_now", cid), callback_data="an:g")])
    rows.append([InlineKeyboardButton(L.t("an.btn_cmd", cid), callback_data="an:c")])
    rows.append([InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:more")])
    return text, InlineKeyboardMarkup(rows)


def _an_command_page(chat=None):
    cid = getattr(chat, "id", None)
    return (L.t("an.cmd_page", cid, tz=_tz_label(cid)), InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="an:q")]]))


def _an_result_note(chat_id, result):
    return L.t({"sent": "an.t_sent", "sample": "an.t_sample", "empty": "an.t_empty"}.get(result, "an.t_error"), chat_id)


async def an_callback(update, context):
    """\"an:q\" panel, \"an:t\" on/off, \"an:h:<minutes>\" time, \"an:s\" count people who were here before, \"an:v\" preview, \"an:g\" post today's now,
    \"an:x\" write the text, \"an:r\" built-in text, \"an:c\" commands. Admins only (\"an:c\" is just information)."""
    q = update.callback_query
    chat = q.message.chat if q.message else None
    if chat is None:
        await q.answer()
        return
    if await extra.menu_not_owner(q):
        return
    parts = (q.data or "").split(":")[1:]
    act, arg = (parts[0] if parts else ""), (parts[1] if len(parts) == 2 else None)
    if parts == ["c"]:
        await q.answer()
        await _ac_edit(q, *_an_command_page(chat))
        return
    if chat.type == "private":
        await q.answer(L.t("an.private"), show_alert=True)
        return
    cid = chat.id
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("an.admin_only", cid), show_alert=True)
        return
    num = _ac_num(arg, 0, 10 ** 7) if arg is not None else None
    toast = None
    try:
        if parts in (["p"], ["q"]):
            pass
        elif parts == ["t"]:
            on = not an_on(cid)
            D.set_setting(cid, AN_KEY, "on" if on else "off")
            toast = L.t("an.t_on" if on else "an.t_off", cid)
        elif act == "h" and num in AN_TIMES:
            D.set_setting(cid, AN_TIME_KEY, num)
            toast = L.t("an.t_time", cid, time=fmt_12h(num))
        elif parts == ["s"]:
            seen = not an_seen_on(cid)
            D.set_setting(cid, AN_SEEN_KEY, "on" if seen else "off")
            toast = L.t("an.t_seen_on" if seen else "an.t_seen_off", cid)
        elif parts == ["r"]:
            D.set_setting(cid, AN_TEXT_KEY, "")
            toast = L.t("an.t_reset", cid)
        elif parts in (["v"], ["g"]):
            preview = parts == ["v"]
            result = await anniv_post(context.bot, cid, sample_user=q.from_user if preview else None, delete_after=AN_PREVIEW_SECS if preview else None)
            await q.answer(_an_result_note(cid, result), show_alert=result in ("empty", "error", "sample"))
            return
        elif parts == ["x"]:
            _an_pending[(cid, q.from_user.id)] = {"panel": (cid, q.message.message_id), "until": time.monotonic() + AN_PENDING_SECS}
            await q.answer(L.t("an.t_ask", cid))
            await chat.send_message(L.t("an.ask", cid, user=q.from_user.mention_html(), max=AN_MAX_TEXT), parse_mode="HTML")
            return
        else:
            await q.answer(L.t("an.invalid", cid), show_alert=True)
            return
        await q.answer(toast)
        await _ac_edit(q, *_an_panel(chat))
    except Exception:
        log.exception("anniversary: panel action failed in %s", cid)
        await q.answer(L.t("ac.db_problem", cid), show_alert=True)


async def an_input(update, context):
    """group=-13, cheap: only acts when the admin tapped ✏️ Text and now sends the message (or "cancel" / "default")."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or not _an_pending:
        return
    key = (chat.id, user.id)
    pending = _an_pending.get(key)
    if pending is None:
        return
    if time.monotonic() > pending["until"] or not await D.is_admin(chat, user.id):
        _an_pending.pop(key, None)
        return
    text = (msg.text or "").strip()
    if text.lower() in ("cancel", "stop"):
        _an_pending.pop(key, None)
        await _rp_note(msg, "an.t_cancel", 10)
        raise ApplicationHandlerStop
    if len(text) > AN_MAX_TEXT:
        await _rp_note(msg, "an.err_long", 15, max=AN_MAX_TEXT)
        raise ApplicationHandlerStop
    _an_pending.pop(key, None)
    D.set_setting(chat.id, AN_TEXT_KEY, "" if text.lower() == "default" else text)
    try:
        await msg.delete()
    except TelegramError:
        pass
    try:
        panel_chat, panel_id = pending["panel"]
        screen, kb = _an_panel(chat, L.t("an.t_saved", chat.id))
        await context.bot.edit_message_text(screen, chat_id=panel_chat, message_id=panel_id, parse_mode="HTML", reply_markup=kb, disable_web_page_preview=True)
    except TelegramError:
        await _rp_note(msg, "an.t_saved", 10)
    raise ApplicationHandlerStop


async def anniv_cmd(update, context):
    """/anniv  |  on | off  |  9am  |  text <message>  |  reset  |  old on|off  |  now"""
    if not await D.group_only(update):
        return
    chat, msg, args, note = update.effective_chat, update.effective_message, list(context.args or []), ""
    cid, first = chat.id, (args[0].lower() if args else "")
    if not args:
        pass
    elif first in ("on", "off") and len(args) == 1:
        D.set_setting(cid, AN_KEY, first)
        note = L.t("an.t_on" if first == "on" else "an.t_off", cid)
    elif first == "reset" and len(args) == 1:
        D.set_setting(cid, AN_TEXT_KEY, "")
        note = L.t("an.t_reset", cid)
    elif first == "now" and len(args) == 1:
        note = _an_result_note(cid, await anniv_post(context.bot, cid))
    elif first == "old" and len(args) == 2 and args[1].lower() in ("on", "off"):
        D.set_setting(cid, AN_SEEN_KEY, args[1].lower())
        note = L.t("an.t_seen_on" if args[1].lower() == "on" else "an.t_seen_off", cid)
    elif first == "text":
        raw = (msg.text or "").split(None, 2)                 # keeps the admin's line breaks
        value = raw[2].strip() if len(raw) == 3 else ""
        if not value:
            await msg.reply_html(L.t("an.usage", cid))
            return
        if len(value) > AN_MAX_TEXT:
            await msg.reply_html(L.t("an.err_long", cid, max=AN_MAX_TEXT))
            return
        D.set_setting(cid, AN_TEXT_KEY, value)
        note = L.t("an.t_saved", cid)
    else:
        day, mins, ok = _so_parse_when(args)
        if not ok or day is not None or mins is None:
            await msg.reply_html(L.t("an.usage", cid))
            return
        D.set_setting(cid, AN_TIME_KEY, mins)
        note = L.t("an.t_time", cid, time=fmt_12h(mins))
    text, markup = _an_panel(chat, note)
    await msg.reply_html(text, reply_markup=markup, disable_web_page_preview=True)


# ======================================================================================================
# 2k. /help PAGE 2 ("More Features")
# ======================================================================================================
# Page 2 is a grid like page 1 (three buttons in a line, from the top): one short button for every panel built in sections
# 2d-2j, then nova's own 🌐 Language, 🗑 Delete and ✨ Extras. Groups only for these panels (they need a group). Each button
# opens the panel through the same callback its own help page uses, so there is one panel per feature, not a copy.
MORE_PANELS = (("wl", "wl:m"), ("ml", "ml:a:0:0"), ("rd", "rd:m"), ("pb", "pb:p"), ("rp", "rp:p"), ("gr", "gr:m"), ("rg", "rg:q"), ("so", "so:q"), ("an", "an:q"))


_HELP_PAGE_BUTTONS = {"warn": warn_ladder_button, "flood": raid_button, "locks": probation_button, "reports": report_button,
                      "greet": greet_button, "rules": gate_button, "log": modlog_button}   # /help page -> the panel button on it


def help_buttons(key, chat):
    """Rows of the newer features' panel buttons that belong on /help page `key` (groups only). nova's help_section_keyboard calls this once."""
    make = _HELP_PAGE_BUTTONS.get(key)
    return [[make(chat)]] if make and chat is not None and getattr(chat, "type", "private") != "private" else []


def more_buttons(chat):
    """The panel buttons for /help page 2, in order (empty in private chats)."""
    if chat is None or getattr(chat, "type", "private") == "private":
        return []
    cid = getattr(chat, "id", None)
    return [InlineKeyboardButton(L.t("mo.b_" + key, cid), callback_data=data) for key, data in MORE_PANELS]


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

SERVICE_INFO = ("all",) + SERVICE_TYPES          # their descriptions are the lang keys "cl.si_<name>"
COMMAND_INFO = ("all",) + COMMAND_TYPES          # ... and "cl.ci_<name>"

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


def _describe(chosen, order, chat_id=None):
    if not chosen:
        return L.t("cl.nothing", chat_id)
    if set(order) <= set(chosen):
        return L.t("cl.all", chat_id)
    return ", ".join(t for t in order if t in chosen)


def _words(args):
    """['join,leave', 'Pin'] -> ['join', 'leave', 'pin']"""
    return [w for a in args for w in re.split(r"[,\s]+", a.lower()) if w]


def _esc(text):
    return str(text).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def what_cmd(what):
    return "service" if what.startswith("service") else "command"


def _what(what, chat_id=None):
    """The words for "service messages" / "commands" in the group's language."""
    return L.t("cl.w_service" if what.startswith("service") else "cl.w_cmd", chat_id)


# ------------------------------------------------------------------ shared command logic
async def _set_cmd(update, context, key, valid, order, what, types_cmd):
    """/cleanservice and /cleancommand: add types (or all / yes / no)."""
    if not await D.group_only(update):          # group only + admin only, with its own reply
        return
    chat, msg = update.effective_chat, update.effective_message
    chosen = _load(chat.id, key, valid)
    words = _words(context.args)
    if not words:
        await msg.reply_html(L.t("cl.set_help", chat.id, desc=_describe(chosen, order, chat.id), what=_what(what, chat.id),
                                 cmd=what_cmd(what), types=types_cmd))
        return
    if words[0] in YES_WORDS:
        new = set(order)
    elif words[0] in NO_WORDS:
        new = set()
    else:
        bad = [w for w in words if w != "all" and w not in valid]
        if bad:
            await msg.reply_html(L.t("cl.unknown_type", chat.id, bad=_esc(", ".join(bad)), order=", ".join(order),
                                     types=types_cmd))
            return
        new = chosen | (set(order) if "all" in words else set(words))
    _save(chat.id, key, new, order)
    if new:
        await msg.reply_html(L.t("cl.set_ok", chat.id, desc=_describe(new, order, chat.id), what=_what(what, chat.id)))
    else:
        await msg.reply_html(L.t("cl.set_none", chat.id, what=_what(what, chat.id)))


async def _keep_cmd(update, context, key, valid, order, what, types_cmd):
    """/keepservice, /nocleanservice and /keepcommand: stop deleting types."""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    words = _words(context.args)
    if not words:
        await msg.reply_html(L.t("cl.keep_usage", chat.id, cmd=what_cmd(what), types=types_cmd))
        return
    bad = [w for w in words if w != "all" and w not in valid]
    if bad:
        await msg.reply_html(L.t("cl.unknown_type", chat.id, bad=_esc(", ".join(bad)), order=", ".join(order),
                                 types=types_cmd))
        return
    chosen = _load(chat.id, key, valid)
    new = set() if "all" in words else chosen - set(words)
    _save(chat.id, key, new, order)
    left = L.t("cl.still", chat.id, desc=_describe(new, order, chat.id)) if new else ""
    kept = L.t("cl.all", chat.id) if "all" in words else ", ".join(words)
    await msg.reply_html(L.t("cl.keep_ok", chat.id, kept=kept, what=_what(what, chat.id), left=left))


# ------------------------------------------------------------------ the commands
async def cleanservice_cmd(update, context):
    await _set_cmd(update, context, SERVICE_KEY, SERVICE_TYPES, SERVICE_TYPES, "service messages", "cleanservicetypes")


async def keepservice_cmd(update, context):
    await _keep_cmd(update, context, SERVICE_KEY, SERVICE_TYPES, SERVICE_TYPES, "service messages", "cleanservicetypes")


async def cleanservicetypes_cmd(update, context):
    cid = update.effective_chat.id
    lines = [L.t("cl.svc_title", cid), ""] + [f"- <code>{n}</code>: {_esc(L.t('cl.si_' + n, cid))}" for n in SERVICE_INFO]
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
    chosen = _load(chat_id, COMMAND_KEY, COMMAND_TYPES)
    names = _load_names(chat_id)
    shown = ", ".join("/" + n for n in names[:10]) + (L.t("cl.and_more", chat_id, n=len(names) - 10) if len(names) > 10 else "")
    parts = ([_describe(chosen, COMMAND_TYPES, chat_id)] if chosen else []) + ([shown] if names else [])
    return " + ".join(parts) or L.t("cl.nothing", chat_id)


async def cleancommand_cmd(update, context):
    """/clean (also /cleancommand): start deleting command types (all, admin, user, other) or specific commands (/roast)."""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    words = _words(context.args)
    if not words:
        await msg.reply_html(L.t("cl.cmd_help", chat.id, desc=_esc(_describe_clean(chat.id))))
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
            hint = L.t("cl.hint_clean", chat.id) if bad else ""
            await msg.reply_html(L.t("cl.cmd_unknown", chat.id, shown=shown, types=", ".join(COMMAND_TYPES), hint=hint))
            return
        if len(names | set(new_names)) > MAX_COMMAND_NAMES:
            await msg.reply_html(L.t("cl.max", chat.id, max=MAX_COMMAND_NAMES))
            return
        types = types | (set(COMMAND_TYPES) if "all" in plain else set(plain))
        names |= set(new_names)
    _save(chat.id, COMMAND_KEY, types, COMMAND_TYPES)
    _save_names(chat.id, names)
    if types or names:
        await msg.reply_html(L.t("cl.cmd_ok", chat.id, desc=_esc(_describe_clean(chat.id))))
    else:
        await msg.reply_html(L.t("cl.cmd_none", chat.id))


async def keepcommand_cmd(update, context):
    """/keep (also /keepcommand): stop deleting command types or specific commands (/keep /roast, /keep all)."""
    if not await D.group_only(update):
        return
    chat, msg = update.effective_chat, update.effective_message
    words = _words(context.args)
    if not words:
        await msg.reply_html(L.t("cl.keepcmd_usage", chat.id))
        return
    slash = [w for w in words if w.startswith("/")]
    plain = [w for w in words if not w.startswith("/")]
    bad = [w for w in plain if w != "all" and w not in COMMAND_TYPES]
    drop_names, bad_names = parse_command_names(slash, context.bot.username)
    if bad or bad_names:
        shown = _esc(", ".join(bad + bad_names))
        hint = L.t("cl.hint_keep", chat.id) if bad else ""
        await msg.reply_html(L.t("cl.cmd_unknown", chat.id, shown=shown, types=", ".join(COMMAND_TYPES), hint=hint))
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
    kept = L.t("cl.all", chat.id) if "all" in plain else ", ".join(plain + ["/" + n for n in drop_names])
    left = L.t("cl.still", chat.id, desc=_esc(_describe_clean(chat.id))) if (types or names) else ""
    await msg.reply_html(L.t("cl.keepcmd_ok", chat.id, kept=_esc(kept), left=left))


async def cleancommandtypes_cmd(update, context):
    cid = update.effective_chat.id
    lines = [L.t("cl.cmd_types_title", cid), ""] + [f"- <code>{n}</code>: {_esc(L.t('cl.ci_' + n, cid))}" for n in COMMAND_INFO]
    lines += [L.t("cl.ci_name", cid)]
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
CC_TYPE_LABELS = ("admin", "user", "other")   # the button words are the lang keys "cl.t_<type>"
CC_NAMES_SHOWN = 24          # saved specific commands shown as buttons on the Remove screen
CC_TYPE_TTL = 300            # seconds the bot waits for the specific command to be typed
_cc_pending = {}             # (chat id, user id) -> {"mid": panel message id, "ts": time, "warned": bool}


def _cc_status(chat):
    if chat is None or chat.type == "private":
        return L.t("cl.st_private", getattr(chat, "id", None))
    return L.t("cl.st_now", chat.id, desc=_esc(_describe_clean(chat.id)))


def _cc_home(chat):
    cid = getattr(chat, "id", None)
    text = (L.t("cl.title", cid) + "\n\n" + L.t("cl.home_intro", cid) + "\n\n" + _cc_status(chat) + "\n\n" +
            L.t("cl.home_type", cid))
    rows = [[InlineKeyboardButton(L.t("cl.btn_add", cid), callback_data="ccb:add"),
             InlineKeyboardButton(L.t("cl.btn_remove", cid), callback_data="ccb:rem")],
            [InlineKeyboardButton(L.t("ac.btn_guide", cid), callback_data="help:g_cleancommand")],
            [InlineKeyboardButton(L.t("pick.back", cid), callback_data="help:main")]]
    return text, InlineKeyboardMarkup(rows)


def _cc_add_screen(chat, note=""):
    types = _load(chat.id, COMMAND_KEY, COMMAND_TYPES)
    text = (L.t("cl.add_title", chat.id) + "\n\n" + (f"{note}\n\n" if note else "") + L.t("cl.add_tap", chat.id) + "\n\n" +
            L.t("cl.types_text", chat.id) + "\n\n" + _cc_status(chat))
    rows = [[InlineKeyboardButton(("✅ " if t in types else "") + L.t("cl.t_" + t, chat.id), callback_data=f"ccb:t:{t}")
             for t in CC_TYPE_LABELS],
            [InlineKeyboardButton(("✅ " if set(COMMAND_TYPES) <= types else "") + L.t("cl.t_all", chat.id),
                                  callback_data="ccb:t:all")],
            [InlineKeyboardButton(L.t("cl.btn_specific", chat.id), callback_data="ccb:sp")],
            [InlineKeyboardButton(L.t("pick.back", chat.id), callback_data=CC_HOME)]]
    return text, InlineKeyboardMarkup(rows)


def _cc_remove_screen(chat, note=""):
    names = _load_names(chat.id)
    more = L.t("cl.rm_more", chat.id, n=len(names) - CC_NAMES_SHOWN) if len(names) > CC_NAMES_SHOWN else ""
    text = (L.t("cl.rm_title", chat.id) + "\n\n" + (f"{note}\n\n" if note else "") + L.t("cl.rm_tap", chat.id) +
            (L.t("cl.rm_tap_saved", chat.id) if names else "") + f"\n\n{_cc_status(chat)}{more}")
    rows = [[InlineKeyboardButton("🚫 " + L.t("cl.t_" + t, chat.id), callback_data=f"ccb:r:{t}") for t in CC_TYPE_LABELS],
            [InlineKeyboardButton("🚫 " + L.t("cl.t_all", chat.id), callback_data="ccb:r:all")]]
    shown = [InlineKeyboardButton(f"❌ /{n}", callback_data=f"ccb:rn:{n}") for n in names[:CC_NAMES_SHOWN]]
    rows += [shown[i:i + 3] for i in range(0, len(shown), 3)]
    rows.append([InlineKeyboardButton(L.t("pick.back", chat.id), callback_data=CC_HOME)])
    return text, InlineKeyboardMarkup(rows)


def _cc_ask_screen(chat=None):
    cid = getattr(chat, "id", None)
    return (L.t("cl.ask_text", cid),
            InlineKeyboardMarkup([[InlineKeyboardButton(L.t("pick.back", cid), callback_data="ccb:add")]]))


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
        await q.answer(L.t("cl.st_private", chat.id), show_alert=True)
        return
    if not await _ac_allowed(chat, q.from_user.id):
        await q.answer(L.t("cl.admin_only", chat.id), show_alert=True)
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
            await _ac_edit(q, *_cc_ask_screen(chat))
        elif act == "t" and len(parts) == 3 and arg in COMMAND_TYPES + ("all",):
            types = _load(chat.id, COMMAND_KEY, COMMAND_TYPES)
            new = set(COMMAND_TYPES) if arg == "all" else types | {arg}
            if new == types:
                await q.answer(L.t("cl.t_already", chat.id))
                return
            _save(chat.id, COMMAND_KEY, new, COMMAND_TYPES)
            await q.answer(L.t("cl.t_done", chat.id, what=L.t("cl.all", chat.id) if arg == "all" else arg))
            await _ac_edit(q, *_cc_add_screen(chat))
        elif act == "r" and len(parts) == 3 and arg in COMMAND_TYPES + ("all",):
            types = _load(chat.id, COMMAND_KEY, COMMAND_TYPES)
            names = set(_load_names(chat.id))
            if arg == "all":
                if not types and not names:
                    await q.answer(L.t("cl.r_nothing", chat.id))
                    return
                _save(chat.id, COMMAND_KEY, set(), COMMAND_TYPES)
                _save_names(chat.id, set())
                await q.answer(L.t("cl.r_all", chat.id))
            else:
                if arg not in types:
                    await q.answer(L.t("cl.r_not", chat.id))
                    return
                _save(chat.id, COMMAND_KEY, types - {arg}, COMMAND_TYPES)
                await q.answer(L.t("cl.r_type", chat.id, arg=arg))
            await _ac_edit(q, *_cc_remove_screen(chat))
        elif act == "rn" and len(parts) == 3 and _NAME_RE.fullmatch(arg):
            names = set(_load_names(chat.id))
            if arg not in names:
                await q.answer(L.t("cl.rn_gone", chat.id))
            else:
                _save_names(chat.id, names - {arg})
                await q.answer(L.t("cl.rn_ok", chat.id, arg=arg))
            await _ac_edit(q, *_cc_remove_screen(chat))
        else:
            await q.answer(L.t("ac.invalid", chat.id), show_alert=True)
    except TelegramError:
        raise
    except Exception:
        log.exception("clean commands: button failed in %s", chat.id)
        try:
            await q.answer(L.t("ac.db_problem", chat.id), show_alert=True)
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
        problem = L.t("cl.msg_bad", chat.id)
    elif len(current | set(names)) > MAX_COMMAND_NAMES:
        problem = L.t("cl.msg_max", chat.id, max=MAX_COMMAND_NAMES)
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
            await msg.reply_text(L.t("ac.db_problem", chat.id))
        except TelegramError:
            pass
        return
    text, markup = _cc_add_screen(chat, L.t("cl.added", chat.id, names=", ".join("/" + n for n in names)))
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
                           "welcome_btns", "goodbye_btns", "welcome_del", "goodbye_del",
                           "join_dm_text", "join_delay", "captcha", "captcha_mode", "captcha_time",
                           "captcha_action")},
    "locks": {"keys": ("lock", "lockwarns", "prob", "prob_hours", "prob_msgs", "prob_block", "prob_notice"), "prefixes": ("lock_",)},
    "notes": {"keys": ("private_notes",), "notes": True},
    "pins": {"keys": ()},
    "raids": {"keys": ("auto_raid", "raid_time", "raid_action_time", "raid_mode", "raid_window")},
    "reports": {"keys": ("reports_on", "report_dest", "report_mute", "report_cooldown")},
    "rules": {"keys": ("rules", "rules_private", "rules_button", "rules_gate", "gate_time", "gate_action")},
    "shoutout": {"keys": ("shout_on", "shout_day", "shout_time", "shout_top", "shout_text", "shout_mention")},
    "anniversary": {"keys": ("anniv_on", "anniv_time", "anniv_text", "anniv_seen")},
    "translations": {"keys": ()},
    "warns": {"keys": ("warn_limit", "warn_time", "warn_mode", "warn_ladder", "warn_ladder_on")},
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


def _parse_modules(args, chat_id=None):
    """(modules or None, error text or None). None = every module."""
    if not args:
        return None, None
    names = [a.lower().strip(",") for a in args if a.strip(",")]
    bad = [n for n in names if n not in MODULES]
    if bad:
        return None, L.t("ie.unknown_module", chat_id, bad=", ".join(bad), order=", ".join(ORDER))
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
    caption = (L.t("ie.cap_exported", chat.id, done=", ".join(data) or L.t("cl.nothing", chat.id))
               + (L.t("ie.cap_empty", chat.id, empty=", ".join(empty)) if empty and not modules else "")
               + L.t("ie.cap_import", chat.id))
    await bot.send_document(chat.id, buf, filename=buf.name, caption=caption[:1000],
                            reply_to_message_id=reply_to, allow_sending_without_reply=True)


async def export_cmd(update, context):
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if not msg or chat.type == "private":
        if msg:
            await msg.reply_text(L.t("ie.use_export"))
        return
    if not await _is_admin(chat, user):
        await msg.reply_text(L.t("ie.admin_export", chat.id))
        return
    modules, err = _parse_modules(context.args, chat.id)
    if err:
        await msg.reply_text(err)
        return
    wait = _cooldown(chat.id)
    if wait:
        await msg.reply_text(L.t("ie.slow", chat.id, wait=wait))
        return
    try:
        await _send_export(chat, msg, context.bot, modules, reply_to=msg.message_id)
    except Exception:
        log.exception("export failed")
        await msg.reply_text(L.t("ie.export_fail", chat.id))


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
        await msg.reply_text(L.t("ie.use_import"))
        return
    if not await _is_creator(chat, user):
        await msg.reply_text(L.t("ie.creator_import", chat.id))
        return
    doc = msg.reply_to_message.document if msg.reply_to_message else None
    if doc is None:
        await msg.reply_text(L.t("ie.reply_import", chat.id))
        return
    if (doc.file_size or 0) > MAX_FILE_BYTES:
        await msg.reply_text(L.t("ie.too_big", chat.id))
        return
    wanted, err = _parse_modules(context.args, chat.id)
    if err:
        await msg.reply_text(err)
        return
    wait = _cooldown(chat.id)
    if wait:
        await msg.reply_text(L.t("ie.slow", chat.id, wait=wait))
        return
    try:
        raw = bytes(await (await context.bot.get_file(doc.file_id)).download_as_bytearray())
        payload = json.loads(raw.decode("utf-8"))
        if not isinstance(payload, dict) or payload.get("format") != FORMAT:
            raise ValueError(L.t("ie.not_file", chat.id))
        done, notes = await asyncio.to_thread(_apply, chat.id, wanted, payload)
    except (ValueError, UnicodeDecodeError) as e:
        await msg.reply_text(L.t("ie.read_fail", chat.id, e=e))
        return
    except TelegramError:
        await msg.reply_text(L.t("ie.dl_fail", chat.id))
        return
    except Exception:
        log.exception("import failed")
        await msg.reply_text(L.t("ie.import_fail", chat.id))
        return
    if not done:
        await msg.reply_text(L.t("ie.nothing", chat.id, what=", ".join(wanted) if wanted else L.t("ie.any_module", chat.id)))
        return
    lines = [L.t("ie.imported", chat.id)] + [L.t("ie.item_one" if n == 1 else "ie.item_many", chat.id, m=html.escape(m), n=n)
                                             for m, n in done.items()]
    if notes:
        lines.append(L.t("ie.skipped", chat.id, notes=html.escape("; ".join(notes[:5]))))
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
        await msg.reply_text(L.t("ie.use_reset"))
        return
    if not await _is_creator(chat, user):
        await msg.reply_text(L.t("ie.creator_reset", chat.id))
        return
    kb = InlineKeyboardMarkup([[InlineKeyboardButton(L.t("ie.yes_reset", chat.id), callback_data=f"ie:rst:y:{user.id}"),
                                InlineKeyboardButton(L.t("ie.cancel", chat.id), callback_data=f"ie:rst:n:{user.id}")]])
    await msg.reply_html(L.t("ie.reset_ask", chat.id), reply_markup=kb)


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
            await q.answer(L.t("ie.reset_only_asker", chat.id), show_alert=True)
            return
        if parts[2] != "y":
            await q.answer(L.t("ie.cancelled", chat.id))
            await q.edit_message_text(L.t("ie.reset_cancelled", chat.id))
            return
        if not await _is_creator(chat, user):
            await q.answer(L.t("ie.creator_only", chat.id), show_alert=True)
            return
        await q.answer()
        try:
            await asyncio.to_thread(_wipe, chat.id)
            await q.edit_message_text(L.t("ie.reset_done", chat.id))
        except Exception:
            log.exception("reset failed")
            await q.edit_message_text(L.t("ie.reset_fail", chat.id))
        return
    if await extra.menu_not_owner(q):                           # help buttons belong to who opened /help
        return
    if act == "imp":
        await q.answer(L.t("ie.imp_help", chat.id), show_alert=True)
        return
    if act == "exp":
        if chat.type == "private":
            await q.answer(L.t("ie.open_help_export"), show_alert=True)
            return
        if not await _is_admin(chat, user):
            await q.answer(L.t("ie.admin_export", chat.id), show_alert=True)
            return
        wait = _cooldown(chat.id)
        if wait:
            await q.answer(L.t("ie.slow_short", chat.id, wait=wait), show_alert=True)
            return
        await q.answer(L.t("ie.exporting", chat.id))
        try:
            await _send_export(chat, q.message, context.bot, None)
        except Exception:
            log.exception("export (button) failed")
            await context.bot.send_message(chat.id, L.t("ie.export_fail", chat.id))
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
    # night mode: /night, the /help > Night Mode page (same -20 trick as Auto Close) and its Turn OFF button;
    # its time pickers are the Auto Close ones above (acb: buttons with which = nc / no)
    app.add_handler(CommandHandler("night", night_cmd))
    app.add_handler(CallbackQueryHandler(help_night_callback, pattern=r"^help:night$"), group=-20)
    app.add_handler(CallbackQueryHandler(nmb_callback, pattern=r"^nmb:"))
    # appeal: /appeal, the /help > Appeal page, the Appeal deep link (/start appeal_...) and the reason in the private chat
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & ~filters.COMMAND & ~filters.StatusUpdate.ALL,
                                   night_enforce), group=-26)       # Night Mode: text only (deletes media and links)
    app.add_handler(CommandHandler("appeal", appeal_cmd))
    app.add_handler(CallbackQueryHandler(help_appeal_callback, pattern=r"^help:appeal$"), group=-20)
    app.add_handler(CallbackQueryHandler(apb_callback, pattern=r"^apb:"))
    app.add_handler(CallbackQueryHandler(apl_callback, pattern=r"^apl:"))
    app.add_handler(CommandHandler("start", appeal_start, filters=filters.ChatType.PRIVATE), group=-20)
    app.add_handler(CommandHandler("myappeals", myappeals_cmd, filters=filters.ChatType.PRIVATE))
    app.add_handler(CommandHandler("warnladder", warnladder_cmd))      # custom action for each warning count
    app.add_handler(CallbackQueryHandler(wl_callback, pattern=r"^wl:"))
    app.add_handler(CallbackQueryHandler(ml_callback, pattern=r"^ml:"))        # /modlog page buttons (the command itself is nova's /modlog)
    app.add_handler(CommandHandler("raidmode", raidmode_cmd))          # Raid Shield: ban / mute joiners / lock the group
    app.add_handler(CommandHandler("raidwindow", raidwindow_cmd))
    app.add_handler(CallbackQueryHandler(rd_callback, pattern=r"^rd:"))
    app.add_handler(CommandHandler("anniv", anniv_cmd))                # Join anniversaries
    app.add_handler(CallbackQueryHandler(an_callback, pattern=r"^an:"))
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND, an_input), group=-13)    # ✏️ Text: the next message
    app.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS | filters.StatusUpdate.LEFT_CHAT_MEMBER, anniv_members), group=106)   # join date
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & ~filters.StatusUpdate.ALL, anniv_seen), group=107)        # first message of people already here
    app.add_handler(CommandHandler("shout", shout_cmd))                # Weekly shout-out (top chatters of the week)
    app.add_handler(CallbackQueryHandler(so_callback, pattern=r"^so:"))
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND, so_input), group=-12)   # ✏️ Text: the next message
    app.add_handler(CommandHandler("gate", gate_cmd))                  # Rules gate: accept the rules before chatting
    app.add_handler(CallbackQueryHandler(rg_callback, pattern=r"^rg:"))
    app.add_handler(CommandHandler("greet", greet_cmd))                # Greetings: extra buttons, delete-after
    app.add_handler(CommandHandler("wdel", wdel_cmd))
    app.add_handler(CommandHandler("gdel", gdel_cmd))
    app.add_handler(CommandHandler("wbtn", wbtn_cmd))
    app.add_handler(CommandHandler("gbtn", gbtn_cmd))
    app.add_handler(CallbackQueryHandler(gr_callback, pattern=r"^gr:"))
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND, gr_input), group=-11)   # ➕ Add button: the next message
    app.add_handler(CommandHandler("reportpanel", reportpanel_cmd))    # Reports: card settings
    app.add_handler(CommandHandler("reportmute", reportmute_cmd))
    app.add_handler(CommandHandler("reportcooldown", reportcooldown_cmd))
    app.add_handler(CallbackQueryHandler(rp_callback, pattern=r"^rp:"))
    app.add_handler(CommandHandler("probation", probation_cmd))        # new members: no links / media for a while
    app.add_handler(CallbackQueryHandler(pb_callback, pattern=r"^pb:"))
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & ~filters.StatusUpdate.ALL, probation_guard), group=-10)   # before the locks (-2)
    app.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, probation_new_members), group=-8)           # after the raid shield (-9)
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.TEXT, appeal_reason), group=-19)
    L.register(app, deps, _ac_allowed, extra.menu_not_owner)   # /lang and the 🌐 Language page (lang/ folder)
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
