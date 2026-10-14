"""
Message Count / group leaderboard / group-wide milestones.

Kept in its own file so none of the existing code had to be rewritten. Wired up from nova.py with:
    msgcount.menu_button()      -> the "📊 Message Count" button of the /help menu (left of 🤖 AI Commands)
    msgcount.register(app)      -> commands, callbacks and the message counter
    msgcount.outbox_sweeper(app)-> background retry loop for milestone notifications (started in post_init)

    COMMANDS   /rank /top /overall /today /week /me /radmin /resetrank

DATA (MongoDB, the same connection/database as the rest of the bot; every record carries chat_id)
    mc_groups      one doc per group: chat_id (unique), name, total, enabled, initial, interval,
                   last_milestone, last_reset_at, created_at, updated_at
    mc_counts      one doc per (chat_id, user_id, p) (unique): p = "all" (all-time, scope "all", has the
                   display name) or p = "YYYY-MM-DD" (scope "day", IST calendar day, expires after 45 days)
    mc_milestones  durable notification outbox: (chat_id, milestone) unique, status pending/sending/sent/failed
Nothing is ever stored globally: every query, update and reset is filtered by the chat_id of the group
where the command/button was used.

TIME: timestamps are stored in UTC; day and week boundaries are IST (Asia/Kolkata, UTC+05:30, no DST);
weeks run Monday-Sunday.
"""
import asyncio
import hashlib
import hmac
import html
import logging
import os
import re
import time
from collections import OrderedDict
from datetime import datetime, timedelta, timezone

from pymongo import ReturnDocument, UpdateOne
from pymongo.errors import BulkWriteError, DuplicateKeyError, PyMongoError
from telegram import InlineKeyboardButton as B, InlineKeyboardMarkup as KB, Update
from telegram.error import BadRequest, Forbidden, RetryAfter, TelegramError
from telegram.ext import (
    ApplicationHandlerStop,  # noqa: F401  (kept for parity with the other modules; never raised here)
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

import extra  # reused: menu ownership lock (remember_menu_owner / menu_not_owner)
import migrate_to_mongo as M  # the one MongoDB connection of the bot

log = logging.getLogger("msgcount")

GROUPS, COUNTS, MILESTONES = "mc_groups", "mc_counts", "mc_milestones"
GROUP_TYPES = ("group", "supergroup")
ANON_ADMIN_ID = 1087968824          # "Group Anonymous Bot"
TELEGRAM_SERVICE_ID = 777000        # automatic channel forwards
IST = timezone(timedelta(hours=5, minutes=30))

DEFAULT_INITIAL = 100
DEFAULT_INTERVAL = 500
MIN_INTERVAL, MAX_INTERVAL = 100, 100000
PAGE_SIZE, FULL_PAGE_SIZE = 10, 25
DAILY_KEEP_DAYS = 45                # daily rows are only needed for /today and /week
CONFIRM_SECS = 120                  # /resetrank confirmation lifetime
INPUT_SECS = 120                    # custom-interval input lifetime
MAX_DELIVERY_ATTEMPTS = 10
NO_DB = "⚠️ Message count data is temporarily unavailable. Please try again in a moment."
GROUP_ONLY = "This command only works in groups."
ADMIN_ONLY = "Only this group's owner or administrators can do this."


# ------------------------------------------------------------------ pure helpers
def next_milestone(last, initial=DEFAULT_INITIAL, interval=DEFAULT_INTERVAL):
    """The first milestone after `last`: `initial` first, then every multiple of `interval`.
    interval 500 -> 100, 500, 1000...   interval 200 -> 100, 200, 400...   interval 1000 -> 100, 1000, 2000..."""
    if last < initial:
        return initial
    return (last // interval + 1) * interval


def prev_milestone(total, initial=DEFAULT_INITIAL, interval=DEFAULT_INTERVAL):
    """The last milestone of the sequence that is <= total (0 when none was reached yet)."""
    if total < initial:
        return 0
    return max(initial, (total // interval) * interval)


def _utcnow():
    return datetime.now(timezone.utc)


def _ist(dt):
    return dt.astimezone(IST)


def periods(now=None):
    """(today, week_start, week_end) as IST calendar-day strings; the week is Monday-Sunday."""
    d = _ist(now or _utcnow()).date()
    monday = d - timedelta(days=d.weekday())
    return d.isoformat(), monday.isoformat(), (monday + timedelta(days=6)).isoformat()


def _expire_at(now):
    d = _ist(now).date()
    end = datetime(d.year, d.month, d.day, tzinfo=IST) + timedelta(days=1)
    return end.astimezone(timezone.utc) + timedelta(days=DAILY_KEEP_DAYS)


def _esc(text, limit=32):
    text = (text or "").strip() or "Unknown"
    return html.escape(text[:limit])


def _step(v, up=True):
    v = v if up else max(v - 1, MIN_INTERVAL)
    return 100 if v < 1000 else 500 if v < 5000 else 1000 if v < 20000 else 5000


def _sign(chat_id, req, ts):
    key = (os.getenv("BOT_TOKEN") or "").strip().encode() or b"msgcount"
    return hmac.new(key, f"rr:{chat_id}:{req}:{ts}".encode(), hashlib.sha256).hexdigest()[:10]


def menu_button():
    """The '📊 Message Count' button for the main /help menu."""
    return B("📊 Count", callback_data="mc:d")


# ------------------------------------------------------------------ database (synchronous, run in threads)
def ensure_indexes():
    try:
        M.col(GROUPS).create_index([("chat_id", 1)], unique=True)
        c = M.col(COUNTS)
        c.create_index([("chat_id", 1), ("user_id", 1), ("p", 1)], unique=True)
        c.create_index([("chat_id", 1), ("scope", 1), ("p", 1)])
        c.create_index([("chat_id", 1), ("scope", 1), ("count", -1), ("user_id", 1)])
        c.create_index("expire_at", expireAfterSeconds=0)  # only daily rows carry expire_at
        m = M.col(MILESTONES)
        m.create_index([("chat_id", 1), ("milestone", 1)], unique=True)
        m.create_index([("status", 1), ("next_try", 1)])
    except PyMongoError:
        log.exception("msgcount: couldn't create the indexes")


def _group_defaults(now):
    return {"total": 0, "enabled": True, "initial": DEFAULT_INITIAL, "interval": DEFAULT_INTERVAL,
            "last_milestone": 0, "created_at": now}


def _group_sync(chat_id):
    g = M.col(GROUPS).find_one({"chat_id": chat_id})
    return g or {"chat_id": chat_id, "total": 0, "enabled": True, "initial": DEFAULT_INITIAL,
                 "interval": DEFAULT_INTERVAL, "last_milestone": 0}


def _bulk_retry(coll, ops):
    """Unordered bulk upserts; re-sends only the operations that lost a duplicate-key race."""
    try:
        coll.bulk_write(ops, ordered=False)
    except BulkWriteError as e:
        failed = [w["index"] for w in e.details.get("writeErrors", [])]
        if not failed or any(w.get("code") != 11000 for w in e.details.get("writeErrors", [])):
            raise
        coll.bulk_write([ops[i] for i in failed], ordered=False)


def _count_sync(chat_id, user_id, name, title, now):
    """Counts ONE message. Returns None when counting is OFF for this group, else (group_doc, [new milestones])."""
    g = M.col(GROUPS)
    doc = None
    for _ in range(2):
        try:
            doc = g.find_one_and_update(
                {"chat_id": chat_id, "enabled": {"$ne": False}},
                {"$inc": {"total": 1}, "$set": {"name": title, "updated_at": now},
                 "$setOnInsert": {"enabled": True, "initial": DEFAULT_INITIAL, "interval": DEFAULT_INTERVAL,
                                  "last_milestone": 0, "created_at": now}},
                upsert=True, return_document=ReturnDocument.AFTER)
            break
        except DuplicateKeyError:
            cur = g.find_one({"chat_id": chat_id}, {"enabled": 1})
            if cur is not None and cur.get("enabled") is False:
                return None            # the row exists and counting is OFF
            # otherwise two first messages raced to create the row: try once more
    if doc is None:
        return None
    _bulk_retry(M.col(COUNTS), [
        UpdateOne({"chat_id": chat_id, "user_id": user_id, "p": "all"},
                  {"$inc": {"count": 1}, "$set": {"name": name, "updated_at": now}, "$setOnInsert": {"scope": "all"}},
                  upsert=True),
        UpdateOne({"chat_id": chat_id, "user_id": user_id, "p": periods(now)[0]},
                  {"$inc": {"count": 1}, "$setOnInsert": {"scope": "day", "expire_at": _expire_at(now)}},
                  upsert=True),
    ])
    created = []
    for _ in range(3):
        last, initial, interval = int(doc.get("last_milestone", 0)), int(doc.get("initial", DEFAULT_INITIAL)), int(doc.get("interval", DEFAULT_INTERVAL))
        nm = next_milestone(last, initial, interval)
        if int(doc["total"]) < nm:
            break
        # 1) the durable outbox row first (unique per group+milestone), 2) then advance the pointer.
        #    A crash between the two is repaired by the next message (the insert is a harmless duplicate).
        try:
            M.col(MILESTONES).insert_one({
                "chat_id": chat_id, "milestone": nm, "total": int(doc["total"]), "group_name": doc.get("name") or title,
                "reached_at": now, "status": "pending", "attempts": 0, "next_try": now, "lock_until": None})
            created.append(nm)
        except DuplicateKeyError:
            pass
        upd = g.find_one_and_update({"chat_id": chat_id, "last_milestone": last}, {"$set": {"last_milestone": nm}},
                                    return_document=ReturnDocument.AFTER)
        if upd is None:
            break                      # a concurrent message already advanced it
        doc = upd
    return doc, created


def _board_page_sync(chat_id, kind, page):
    size = FULL_PAGE_SIZE if kind == "full" else PAGE_SIZE
    c = M.col(COUNTS)
    today, wk0, wk1 = periods()
    if kind in ("all", "full"):
        total = c.count_documents({"chat_id": chat_id, "scope": "all", "count": {"$gt": 0}})
        pages = max(1, -(-total // size))
        page = min(max(page, 0), pages - 1)
        rows = [(d["user_id"], d.get("name"), d["count"]) for d in
                c.find({"chat_id": chat_id, "scope": "all", "count": {"$gt": 0}})
                .sort([("count", -1), ("user_id", 1)]).skip(page * size).limit(size)]
        return {"rows": rows, "total": total, "pages": pages, "page": page, "size": size}
    lo, hi = (today, today) if kind == "today" else (wk0, wk1)
    # page is clamped after the count is known
    res = list(c.aggregate([
        {"$match": {"chat_id": chat_id, "scope": "day", "p": {"$gte": lo, "$lte": hi}}},
        {"$group": {"_id": "$user_id", "n": {"$sum": "$count"}}},
        {"$sort": {"n": -1, "_id": 1}},
        {"$facet": {"rows": [{"$skip": max(page, 0) * size}, {"$limit": size}], "meta": [{"$count": "c"}]}},
    ]))
    total = res[0]["meta"][0]["c"] if res and res[0]["meta"] else 0
    pages = max(1, -(-total // size))
    if page > pages - 1:
        return _board_page_sync(chat_id, kind, pages - 1)
    rows = [(r["_id"], None, r["n"]) for r in (res[0]["rows"] if res else [])]
    names = {d["user_id"]: d.get("name") for d in
             c.find({"chat_id": chat_id, "scope": "all", "user_id": {"$in": [r[0] for r in rows]}}, {"user_id": 1, "name": 1})}
    rows = [(u, names.get(u), n) for u, _, n in rows]
    return {"rows": rows, "total": total, "pages": pages, "page": max(page, 0), "size": size}


def _board_sync(chat_id, kind, page):
    """One leaderboard page plus this group's summary (shown above every leaderboard)."""
    data = _board_page_sync(chat_id, kind, page)
    data["group"] = _group_sync(chat_id)
    return data


def _me_sync(chat_id, user_id):
    c = M.col(COUNTS)
    today, wk0, wk1 = periods()
    me = c.find_one({"chat_id": chat_id, "user_id": user_id, "p": "all"})
    total = int(me["count"]) if me else 0
    rank = None
    if total > 0:
        rank = (c.count_documents({"chat_id": chat_id, "scope": "all", "count": {"$gt": total}})
                + c.count_documents({"chat_id": chat_id, "scope": "all", "count": total, "user_id": {"$lt": user_id}}) + 1)
    d = c.find_one({"chat_id": chat_id, "user_id": user_id, "p": today})
    wk = list(c.aggregate([{"$match": {"chat_id": chat_id, "user_id": user_id, "scope": "day", "p": {"$gte": wk0, "$lte": wk1}}},
                           {"$group": {"_id": None, "n": {"$sum": "$count"}}}]))
    return {"total": total, "rank": rank, "today": int(d["count"]) if d else 0, "week": int(wk[0]["n"]) if wk else 0,
            "members": c.count_documents({"chat_id": chat_id, "scope": "all", "count": {"$gt": 0}}), "group": _group_sync(chat_id)}


def _admins_today_sync(chat_id, ids):
    today = periods()[0]
    return {d["user_id"]: int(d["count"]) for d in
            M.col(COUNTS).find({"chat_id": chat_id, "scope": "day", "p": today, "user_id": {"$in": list(ids)}})}


def _toggle_sync(chat_id, flag, now):
    M.col(GROUPS).update_one(
        {"chat_id": chat_id},
        {"$set": {"enabled": bool(flag), "updated_at": now},
         "$setOnInsert": {"total": 0, "initial": DEFAULT_INITIAL, "interval": DEFAULT_INTERVAL, "last_milestone": 0, "created_at": now}},
        upsert=True)
    return _group_sync(chat_id)


def _save_interval_sync(chat_id, value, now):
    """Deterministic interval-change rule: the pointer moves to the last milestone of the NEW sequence that is
    <= the current total, so nothing already passed is announced and the next milestone is the first one of the
    new sequence above the current total. Totals, rankings and history are untouched."""
    cur = M.col(GROUPS).find_one({"chat_id": chat_id}) or {}
    last = prev_milestone(int(cur.get("total", 0)), int(cur.get("initial", DEFAULT_INITIAL)), value)
    return M.col(GROUPS).find_one_and_update(
        {"chat_id": chat_id},
        {"$set": {"interval": value, "last_milestone": last, "updated_at": now},
         "$setOnInsert": {"total": 0, "enabled": True, "initial": DEFAULT_INITIAL, "created_at": now}},
        upsert=True, return_document=ReturnDocument.AFTER)


def _reset_sync(chat_id, ts, now):
    """Resets ONE group. Returns False when this confirmation was already used (replay)."""
    g = M.col(GROUPS)
    g.update_one({"chat_id": chat_id}, {"$setOnInsert": _group_defaults(now)}, upsert=True)
    claimed = g.find_one_and_update(
        {"chat_id": chat_id, "$or": [{"last_reset_at": {"$exists": False}},
                                     {"last_reset_at": {"$lt": datetime.fromtimestamp(ts, timezone.utc)}}]},
        {"$set": {"last_reset_at": now}})
    if claimed is None:
        return False
    M.col(COUNTS).delete_many({"chat_id": chat_id})
    M.col(MILESTONES).delete_many({"chat_id": chat_id})
    g.update_one({"chat_id": chat_id}, {"$set": {"total": 0, "last_milestone": 0, "updated_at": now}})
    return True


# ------------------------------------------------------------------ milestone outbox (durable delivery)
def _claim_sync(chat_id, milestone, now):
    return M.col(MILESTONES).find_one_and_update(
        {"chat_id": chat_id, "milestone": milestone, "next_try": {"$lte": now},
         "$or": [{"status": "pending"}, {"status": "sending", "lock_until": {"$lt": now}}]},
        {"$set": {"status": "sending", "lock_until": now + timedelta(seconds=60)}, "$inc": {"attempts": 1}},
        return_document=ReturnDocument.AFTER)


def _due_sync(now, limit=20):
    return [(d["chat_id"], d["milestone"]) for d in
            M.col(MILESTONES).find({"next_try": {"$lte": now}, "status": {"$in": ["pending", "sending"]}}).limit(limit)]


def _finish_sync(chat_id, milestone, ok, now, delay=None, error=None, permanent=False):
    m = M.col(MILESTONES)
    if ok:
        m.update_one({"chat_id": chat_id, "milestone": milestone}, {"$set": {"status": "sent", "sent_at": now, "lock_until": None}})
        return
    doc = m.find_one({"chat_id": chat_id, "milestone": milestone}) or {}
    dead = permanent or int(doc.get("attempts", 0)) >= MAX_DELIVERY_ATTEMPTS
    delay = delay if delay is not None else min(30 * 2 ** int(doc.get("attempts", 1)), 3600)
    m.update_one({"chat_id": chat_id, "milestone": milestone},
                 {"$set": {"status": "failed" if dead else "pending", "next_try": now + timedelta(seconds=delay),
                           "lock_until": None, "last_error": (error or "")[:200]}})


def _milestone_text(d):
    when = _ist(d["reached_at"].replace(tzinfo=timezone.utc) if d["reached_at"].tzinfo is None else d["reached_at"])
    return ("🎉 <b>GROUP MESSAGE MILESTONE!</b>\n\n"
            f"👥 <b>Group:</b> {_esc(d.get('group_name'), 64)}\n\n"
            f"💬 <b>Total Group Messages:</b> {int(d['total']):,}\n\n"
            f"🏆 <b>Milestone:</b> {int(d['milestone']):,} Messages Reached!\n\n"
            f"📅 <b>Date:</b> {when.strftime('%d %B %Y')}\n\n"
            f"🕒 <b>Time:</b> {when.strftime('%I:%M %p')} IST\n\n"
            "Congratulations! 🎊\nKeep chatting! 💬")


async def _deliver(bot, chat_id, milestone):
    """Sends one pending milestone message. Marked 'sent' only AFTER Telegram accepted it."""
    try:
        doc = await asyncio.to_thread(_claim_sync, chat_id, milestone, _utcnow())
    except PyMongoError:
        log.exception("msgcount: couldn't claim milestone %s of %s", milestone, chat_id)
        return
    if not doc:
        return
    try:
        await bot.send_message(chat_id, _milestone_text(doc), parse_mode="HTML")
    except RetryAfter as e:
        ra = e.retry_after.total_seconds() if hasattr(e.retry_after, "total_seconds") else float(e.retry_after)
        await _finish(chat_id, milestone, False, delay=ra + 1, error="rate limited")
    except Forbidden as e:
        await _finish(chat_id, milestone, False, error=str(e), permanent=True)      # bot was removed / blocked
    except BadRequest as e:
        await _finish(chat_id, milestone, False, error=str(e), permanent="chat not found" in str(e).lower())
    except TelegramError as e:
        await _finish(chat_id, milestone, False, error=f"{type(e).__name__}: {e}")
    else:
        await _finish(chat_id, milestone, True)


async def _finish(chat_id, milestone, ok, **kw):
    try:
        await asyncio.to_thread(_finish_sync, chat_id, milestone, ok, _utcnow(), **kw)
    except PyMongoError:
        log.exception("msgcount: couldn't update the state of milestone %s of %s", milestone, chat_id)
    if not ok:
        log.warning("msgcount: milestone %s for %s not delivered (%s); will retry", milestone, chat_id, kw.get("error"))


async def outbox_sweeper(app):
    """Background loop (survives restarts because the outbox is in MongoDB): re-sends pending milestones."""
    await asyncio.sleep(5)
    while True:
        try:
            for chat_id, milestone in await asyncio.to_thread(_due_sync, _utcnow()):
                await _deliver(app.bot, chat_id, milestone)
        except Exception:
            log.exception("msgcount: outbox sweeper error")
        await asyncio.sleep(30)


# ------------------------------------------------------------------ the counter
_CONTENT_ATTRS = ("text", "caption", "photo", "video", "audio", "voice", "document", "sticker", "animation",
                  "video_note", "contact", "location", "venue", "poll", "dice", "game", "story", "invoice",
                  "paid_media", "checklist")
_seen = OrderedDict()          # (chat_id, message_id) of recently counted messages (bounded)
_off_until = {}                # chat_id -> monotonic time until which "counting is OFF" is trusted (bounded)


def _paused(chat_id):
    """/pause state of this group (same setting nova.py writes: 0 = running, -1 = until /resume, else end time)."""
    try:
        until = int(M.get_setting(chat_id, "paused_until", 0) or 0)
    except Exception:
        return False
    return until == -1 or (until > 0 and until > time.time())


async def count_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """group=5: counts each eligible human message once. Never blocks other handlers."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg is None or chat is None or user is None or chat.type not in GROUP_TYPES:
        return
    if user.is_bot or user.id in (ANON_ADMIN_ID, TELEGRAM_SERVICE_ID):
        return
    if msg.sender_chat is not None or getattr(msg, "is_automatic_forward", None):
        return                                  # channel posts / anonymous-admin posts: no human to credit
    if not any(getattr(msg, attr, None) for attr in _CONTENT_ATTRS):
        return                                  # service message (tag/setting changes...): not a message
    if _paused(chat.id):
        return                                  # /pause is on for this group: nothing is counted
    until = _off_until.get(chat.id)
    if until and until > time.monotonic():
        return
    key = (chat.id, msg.message_id)
    if key in _seen:
        return
    _seen[key] = True
    if len(_seen) > 5000:
        for _ in range(1000):
            _seen.popitem(last=False)
    title = (chat.title or "").strip()
    try:
        res = await asyncio.to_thread(_count_sync, chat.id, user.id, (user.full_name or "")[:64], title, _utcnow())
    except PyMongoError:
        _seen.pop(key, None)
        log.exception("msgcount: couldn't count a message in %s", chat.id)
        return
    if res is None:
        if len(_off_until) > 2000:
            _off_until.clear()
        _off_until[chat.id] = time.monotonic() + 30
        return
    _, created = res
    for milestone in created:
        await _deliver(context.bot, chat.id, milestone)


# ------------------------------------------------------------------ permissions
async def _is_group_admin(bot, chat_id, user_id):
    """True/False from Telegram's own member info for THIS chat; None when Telegram can't be asked."""
    fn = getattr(getattr(extra, "_BD", None), "is_bot_owner", None)
    try:
        if fn and fn(user_id):
            return True                         # bot owner with /power ON counts as an admin everywhere
    except Exception:
        log.exception("msgcount: owner power check failed")
    try:
        m = await bot.get_chat_member(chat_id, user_id)
    except TelegramError:
        log.exception("msgcount: get_chat_member failed chat=%s user=%s", chat_id, user_id)
        return None
    return m.status in ("creator", "administrator")


# ------------------------------------------------------------------ texts and keyboards
def _dash_text(title, g, commands=True):
    total, initial, interval = int(g.get("total", 0)), int(g.get("initial", DEFAULT_INITIAL)), int(g.get("interval", DEFAULT_INTERVAL))
    last = int(g.get("last_milestone", 0))
    nxt = next_milestone(last, initial, interval)
    on = g.get("enabled", True) is not False
    return ("📊 <b>GROUP MESSAGE COUNT</b>\n\n"
            f"👥 <b>Group:</b> {_esc(title, 64)}\n\n"
            f"💬 <b>Total Group Messages:</b> {total:,}\n\n"
            f"⚙️ <b>Milestone Interval:</b> Every {interval:,} messages\n\n"
            f"🏆 <b>Last Milestone:</b> {f'{last:,}' if last else 'None yet'}\n\n"
            f"🎯 <b>Next Milestone:</b> {nxt:,}\n\n"
            f"📨 <b>Messages Until Next Milestone:</b> {max(nxt - total, 0):,}\n\n"
            f"🔔 <b>Message Counting:</b> {'ON' if on else 'OFF'}"
            + ("\n\n📖 <b>Commands</b>\n"
               "/rank (or /top) — leaderboard\n"
               "/today — today's leaderboard\n"
               "/week — this week's leaderboard\n"
               "/overall — all-time leaderboard\n"
               "/me — your messages and rank\n"
               "/radmin — admins' message count today\n"
               "/resetrank — reset this group's counts (admins only)" if commands else ""))


def _dash_kb(g):
    on = g.get("enabled", True) is not False
    return KB([
        [B("🏆 Overall Leaderboard", callback_data="mc:b:all:0")],
        [B("✅ Today", callback_data="mc:b:today:0"), B("📅 Week", callback_data="mc:b:week:0")],
        [B("📊 View Complete Leaderboard", callback_data="mc:b:full:0")],
        [B("⚙️ Milestone Settings", callback_data="mc:s")],
        [B("✅ Message Count: ON" if on else "❌ Message Count: OFF", callback_data=f"mc:t:{0 if on else 1}")],
        [B("🔙 Back", callback_data="help:main")],
    ])


def _settings_text(title, g, draft):
    saved = int(g.get("interval", DEFAULT_INTERVAL))
    note = "" if draft == saved else "\n\n<i>Not saved yet. Tap 💾 Save Settings to apply it.</i>"
    return ("⚙️ <b>GROUP MILESTONE SETTINGS</b>\n\n"
            f"👥 <b>Group:</b> {_esc(title, 64)}\n\n"
            f"📊 <b>Initial Milestone:</b> {int(g.get('initial', DEFAULT_INITIAL)):,} messages\n\n"
            f"🔔 <b>Current Interval:</b> {draft:,} messages{note}\n\n"
            "📖 These settings are changed with the buttons below (group admins only). "
            "/resetrank resets this group's counts.")


def _settings_kb(draft):
    return KB([
        [B("➖ Decrease Interval", callback_data=f"mc:si:{max(draft - _step(draft, False), MIN_INTERVAL)}"),
         B("➕ Increase Interval", callback_data=f"mc:si:{min(draft + _step(draft), MAX_INTERVAL)}")],
        [B("✏️ Set Custom Interval", callback_data="mc:sc")],
        [B("💾 Save Settings", callback_data=f"mc:ss:{draft}")],
        [B("🔙 Back", callback_data="mc:d")],
    ])


_MEDALS = {1: "🥇", 2: "🥈", 3: "🥉"}
_KIND_TITLE = {"all": "🏆 Overall", "full": "📊 Complete Leaderboard", "today": "✅ Today", "week": "📅 This Week"}


def _chat_title_of(title, data):
    return title or data["group"].get("name") or "this group"


def _board_text(title, kind, data):
    today, wk0, wk1 = periods()
    sub = _KIND_TITLE[kind]
    if kind == "today":
        sub += f" ({today} IST)"
    elif kind == "week":
        sub += f" ({wk0} to {wk1}, IST)"
    lines = [_dash_text(_chat_title_of(title, data), data["group"], commands=False), "", "📈 <b>LEADERBOARD</b>", "", sub, ""]
    if not data["rows"]:
        lines.append("No messages recorded yet for this period.")
    base = data["page"] * data["size"]
    for i, (uid, name, n) in enumerate(data["rows"], start=base + 1):
        lines.append(f"{_MEDALS.get(i, f'{i}.')} {_esc(name or f'User {uid}')} — {n:,}")
    if data["pages"] > 1:
        lines += ["", f"Page {data['page'] + 1}/{data['pages']}"]
    lines += ["", "📖 <b>Commands</b>", "/rank (or /top): all-time leaderboard", "/today: today's leaderboard",
              "/week: this week's leaderboard", "/me: your messages and rank"]
    return "\n".join(lines)


def _board_kb(kind, data):
    rows = []
    if data["pages"] > 1:
        nav = []
        if data["page"] > 0:
            nav.append(B("⬅️ Prev", callback_data=f"mc:b:{kind}:{data['page'] - 1}"))
        if data["page"] < data["pages"] - 1:
            nav.append(B("Next ➡️", callback_data=f"mc:b:{kind}:{data['page'] + 1}"))
        rows.append(nav)
    rows += [[B("🏆 Overall", callback_data="mc:b:all:0")],
             [B("✅ Today", callback_data="mc:b:today:0"), B("📅 Week", callback_data="mc:b:week:0")],
             [B("📊 View Complete Leaderboard", callback_data="mc:b:full:0")],
             [B("🔙 Back", callback_data="mc:d")]]
    return KB(rows)


def _chat_title(chat, g=None):
    return (chat.title or (g or {}).get("name") or "this group")


async def _edit(q, text, markup):
    try:
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=markup, disable_web_page_preview=True)
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            log.warning("msgcount: couldn't edit a message: %s", e)
    except TelegramError as e:
        log.warning("msgcount: couldn't edit a message: %s: %s", type(e).__name__, e)


# ------------------------------------------------------------------ commands
async def _group_chat_or_reject(update):
    chat, msg = update.effective_chat, update.effective_message
    if chat is None or msg is None:
        return None
    if chat.type not in GROUP_TYPES:
        await msg.reply_text(GROUP_ONLY)
        return None
    return chat


async def rank_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/rank  /top  /overall: this group's all-time leaderboard."""
    await _send_board(update, "all")


async def today_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _send_board(update, "today")


async def week_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _send_board(update, "week")


async def _send_board(update, kind):
    chat = await _group_chat_or_reject(update)
    if chat is None:
        return
    msg = update.effective_message
    try:
        data = await asyncio.to_thread(_board_sync, chat.id, kind, 0)
    except PyMongoError:
        log.exception("msgcount: leaderboard failed in %s", chat.id)
        await msg.reply_text(NO_DB)
        return
    sent = await msg.reply_html(_board_text(_chat_title(chat), kind, data), reply_markup=_board_kb(kind, data),
                                disable_web_page_preview=True)
    extra.remember_menu_owner(sent, update.effective_user.id if update.effective_user else None)


async def me_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = await _group_chat_or_reject(update)
    if chat is None:
        return
    msg, user = update.effective_message, update.effective_user
    if user is None or user.id == ANON_ADMIN_ID or msg.sender_chat is not None:
        await msg.reply_text("I can't tell who you are while you post anonymously. Please post as yourself.")
        return
    try:
        d = await asyncio.to_thread(_me_sync, chat.id, user.id)
    except PyMongoError:
        log.exception("msgcount: /me failed in %s", chat.id)
        await msg.reply_text(NO_DB)
        return
    lines = ["👤 <b>YOUR MESSAGE STATISTICS</b>", "",
             f"👥 <b>Group:</b> {_esc(_chat_title(chat, d['group']), 64)}", "",
             f"💬 <b>All-Time Messages:</b> {d['total']:,}", "",
             f"✅ <b>Today's Messages:</b> {d['today']:,}", "",
             f"📅 <b>This Week:</b> {d['week']:,}", "",
             f"🏆 <b>Current Group Rank:</b> {('#%d of %d' % (d['rank'], d['members'])) if d['rank'] else 'Not ranked yet'}"]
    if not d["total"]:
        lines += ["", "You haven't sent any counted messages in this group yet, so you are not ranked yet."]
    if d["group"].get("enabled") is False:
        lines += ["", "<i>Message counting is currently OFF in this group.</i>"]
    await msg.reply_html("\n".join(lines))


async def radmin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = await _group_chat_or_reject(update)
    if chat is None:
        return
    msg = update.effective_message
    try:
        admins = [a for a in await context.bot.get_chat_administrators(chat.id) if not a.user.is_bot]
    except TelegramError:
        log.exception("msgcount: get_chat_administrators failed in %s", chat.id)
        await msg.reply_text("I couldn't read this group's administrator list right now. Please try again.")
        return
    try:
        counts = await asyncio.to_thread(_admins_today_sync, chat.id, [a.user.id for a in admins])
    except PyMongoError:
        log.exception("msgcount: /radmin failed in %s", chat.id)
        await msg.reply_text(NO_DB)
        return
    today = periods()[0]
    rows = sorted(((counts.get(a.user.id, 0), a.user.full_name or f"User {a.user.id}") for a in admins), key=lambda r: (-r[0], r[1].lower()))
    if not any(n for n, _ in rows):
        await msg.reply_html(f"👮 <b>ADMIN MESSAGES TODAY</b> ({today} IST)\n\nNo admin has sent a counted message in this group today yet.")
        return
    lines = [f"👮 <b>ADMIN MESSAGES TODAY</b> ({today} IST)", f"👥 {_esc(_chat_title(chat), 64)}", ""]
    for i, (n, name) in enumerate(rows[:40], start=1):
        lines.append(f"{_MEDALS.get(i, f'{i}.')} {_esc(name)} — {n:,}")
    if len(rows) > 40:
        lines.append(f"…and {len(rows) - 40} more admins")
    await msg.reply_html("\n".join(lines))


async def resetrank_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = await _group_chat_or_reject(update)
    if chat is None:
        return
    msg, user = update.effective_message, update.effective_user
    anonymous = user is None or user.id == ANON_ADMIN_ID or (msg.sender_chat is not None and msg.sender_chat.id == chat.id)
    if anonymous:
        if not (msg.sender_chat is not None and msg.sender_chat.id == chat.id):
            await msg.reply_text(ADMIN_ONLY)
            return
        req = 0                       # Telegram only sends sender_chat == this chat for its real admins
    else:
        ok = await _is_group_admin(context.bot, chat.id, user.id)
        if ok is not True:
            await msg.reply_text(ADMIN_ONLY if ok is False else "I couldn't verify your permissions right now. Please try again.")
            return
        req = user.id
    ts = int(time.time())
    kb = KB([[B("✅ Confirm Reset", callback_data=f"mc:rr:y:{req}:{ts}:{_sign(chat.id, req, ts)}"),
              B("❌ Cancel", callback_data=f"mc:rr:n:{req}:{ts}:{_sign(chat.id, req, ts)}")]])
    sent = await msg.reply_html(
        "⚠️ <b>RESET GROUP MESSAGE STATISTICS?</b>\n\n"
        f"👥 <b>Group:</b> {_esc(_chat_title(chat), 64)}\n\n"
        "This will reset the current group's message totals and leaderboard statistics.\n\n"
        "Other groups will not be affected.", reply_markup=kb)
    extra.remember_menu_owner(sent, user.id if user else None)


# ------------------------------------------------------------------ custom interval input (per user + group, expires)
_pending = {}   # (chat_id, user_id) -> expiry (monotonic). Transient UI state only; no statistics live here.


def _pending_put(chat_id, user_id):
    now = time.monotonic()
    for k in [k for k, v in _pending.items() if v <= now]:
        _pending.pop(k, None)
    if len(_pending) > 500:
        _pending.clear()
    _pending[(chat_id, user_id)] = now + INPUT_SECS


def _pending_live(chat_id, user_id):
    exp = _pending.get((chat_id, user_id))
    if exp is None:
        return False
    if exp <= time.monotonic():
        _pending.pop((chat_id, user_id), None)
        return False
    return True


async def pending_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """group=-29: only reacts to the user who tapped 'Set Custom Interval' in THIS group; never stops other handlers."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg is None or chat is None or user is None or not _pending:
        return
    if not _pending_live(chat.id, user.id):
        return
    text = (msg.text or "").strip()
    if not re.fullmatch(r"[0-9]{1,7}", text) or not (MIN_INTERVAL <= int(text) <= MAX_INTERVAL):
        await msg.reply_text(f"Please send a whole number from {MIN_INTERVAL:,} to {MAX_INTERVAL:,} (or tap Cancel on the prompt).")
        return
    _pending.pop((chat.id, user.id), None)
    ok = await _is_group_admin(context.bot, chat.id, user.id)
    if ok is not True:
        await msg.reply_text(ADMIN_ONLY if ok is False else "I couldn't verify your permissions right now. Nothing was changed.")
        return
    await _apply_interval(msg.reply_html, chat, int(text))


async def _apply_interval(reply, chat, value):
    try:
        g = await asyncio.to_thread(_save_interval_sync, chat.id, value, _utcnow())
    except PyMongoError:
        log.exception("msgcount: saving the interval failed in %s", chat.id)
        await reply(NO_DB)
        return None
    nxt = next_milestone(int(g.get("last_milestone", 0)), int(g.get("initial", DEFAULT_INITIAL)), value)
    await reply(f"✅ <b>Settings saved.</b>\nMilestone interval: every {value:,} messages.\nNext milestone: {nxt:,}.")
    return g


# ------------------------------------------------------------------ buttons
async def mc_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    parts = (q.data or "").split(":")
    try:
        if len(parts) >= 2 and parts[1] == "rr":
            await _reset_callback(update, context, parts)
            return
        if await extra.menu_not_owner(q):
            return
        msg = q.message
        chat = getattr(msg, "chat", None)
        if chat is None:
            await q.answer()
            return
        if chat.type not in GROUP_TYPES:
            await q.answer()
            await _edit(q, "📊 <b>Message Count</b>\n\nMessage statistics are tracked separately for every group, so they "
                           "can only be viewed inside a group. Open /help in a group and tap 📊 Message Count there.",
                        KB([[B("🔙 Back", callback_data="help:main")]]))
            return
        action = parts[1] if len(parts) > 1 else ""
        if action == "d":
            await q.answer()
            await _show_dashboard(q, chat)
        elif action == "b" and len(parts) == 4 and parts[2] in _KIND_TITLE and parts[3].isdigit() and len(parts[3]) <= 6:
            await q.answer()
            data = await asyncio.to_thread(_board_sync, chat.id, parts[2], int(parts[3]))
            await _edit(q, _board_text(_chat_title(chat), parts[2], data), _board_kb(parts[2], data))
        elif action in ("s", "si", "ss", "sc", "sx", "t"):
            await _admin_action(q, context, chat, parts)
        else:
            await q.answer("This button is no longer valid.", show_alert=True)
    except PyMongoError:
        log.exception("msgcount: database error in callback %r", q.data)
        try:
            await q.answer(NO_DB, show_alert=True)
        except TelegramError:
            pass
    except TelegramError as e:
        log.warning("msgcount: Telegram error in callback %r: %s", q.data, e)
    except Exception:
        log.exception("msgcount: callback %r failed", q.data)
        try:
            await q.answer("Something went wrong. Please try again.", show_alert=True)
        except TelegramError:
            pass


async def _show_dashboard(q, chat):
    g = await asyncio.to_thread(_group_sync, chat.id)
    await _edit(q, _dash_text(_chat_title(chat, g), g), _dash_kb(g))


async def _admin_action(q, context, chat, parts):
    """Settings / toggle: permissions are re-checked against Telegram on EVERY click."""
    ok = await _is_group_admin(context.bot, chat.id, q.from_user.id)
    if ok is not True:
        await q.answer(ADMIN_ONLY if ok is False else "I couldn't verify your permissions right now. Nothing was changed.", show_alert=True)
        return
    action = parts[1]
    g = await asyncio.to_thread(_group_sync, chat.id)
    if action == "s":
        await q.answer()
        draft = int(g.get("interval", DEFAULT_INTERVAL))
        await _edit(q, _settings_text(_chat_title(chat, g), g, draft), _settings_kb(draft))
    elif action == "si":
        if len(parts) != 3 or not parts[2].isdigit() or not (MIN_INTERVAL <= int(parts[2]) <= MAX_INTERVAL):
            await q.answer("Invalid interval.", show_alert=True)
            return
        await q.answer()
        draft = int(parts[2])
        await _edit(q, _settings_text(_chat_title(chat, g), g, draft), _settings_kb(draft))
    elif action == "ss":
        if len(parts) != 3 or not parts[2].isdigit() or not (MIN_INTERVAL <= int(parts[2]) <= MAX_INTERVAL):
            await q.answer("Invalid interval.", show_alert=True)
            return
        g2 = await asyncio.to_thread(_save_interval_sync, chat.id, int(parts[2]), _utcnow())
        await q.answer("Settings saved.")
        await _edit(q, _dash_text(_chat_title(chat, g2), g2), _dash_kb(g2))
    elif action == "sc":
        await q.answer()
        _pending_put(chat.id, q.from_user.id)
        await q.message.reply_html(
            f"✏️ <b>Custom interval</b>\n\n{html.escape(q.from_user.first_name or 'Admin')}, send a whole number from "
            f"{MIN_INTERVAL:,} to {MAX_INTERVAL:,} within {INPUT_SECS // 60} minutes.\nOnly your next message in this group is used.",
            reply_markup=KB([[B("❌ Cancel", callback_data="mc:sx")]]))
    elif action == "sx":
        _pending.pop((chat.id, q.from_user.id), None)
        await q.answer("Cancelled.")
        await _edit(q, "Custom interval cancelled. Nothing was changed.", None)
    elif action == "t":
        if len(parts) != 3 or parts[2] not in ("0", "1"):
            await q.answer("This button is no longer valid.", show_alert=True)
            return
        flag = parts[2] == "1"
        g2 = await asyncio.to_thread(_toggle_sync, chat.id, flag, _utcnow())
        if flag:
            _off_until.pop(chat.id, None)
        else:
            _off_until[chat.id] = time.monotonic() + 30
        await q.answer("Message counting is now ON." if flag else "Message counting is now OFF.")
        await _edit(q, _dash_text(_chat_title(chat, g2), g2), _dash_kb(g2))


async def _reset_callback(update, context, parts):
    q = update.callback_query
    msg = q.message
    chat = getattr(msg, "chat", None)
    try:
        if chat is None or chat.type not in GROUP_TYPES or len(parts) != 6 or parts[2] not in ("y", "n"):
            await q.answer("This button is no longer valid.", show_alert=True)
            return
        req, ts = int(parts[3]), int(parts[4])
    except ValueError:
        await q.answer("This button is no longer valid.", show_alert=True)
        return
    if not hmac.compare_digest(parts[5], _sign(chat.id, req, ts)):     # forged, or taken from another group
        await q.answer("This button is not valid for this group.", show_alert=True)
        return
    if time.time() - ts > CONFIRM_SECS or ts > time.time() + 5:
        await q.answer("This confirmation has expired. Send /resetrank again.", show_alert=True)
        await _edit(q, "⌛ This reset request expired. Nothing was changed.", None)
        return
    if req != 0 and q.from_user.id != req:
        await q.answer("Only the admin who sent /resetrank can answer this.", show_alert=True)
        return
    ok = await _is_group_admin(context.bot, chat.id, q.from_user.id)   # permissions may have changed since
    if ok is not True:
        await q.answer(ADMIN_ONLY if ok is False else "I couldn't verify your permissions right now. Nothing was changed.", show_alert=True)
        return
    if parts[2] == "n":
        await q.answer("Cancelled.")
        await _edit(q, "❌ Reset cancelled. Nothing was changed.", None)
        return
    await q.answer("Resetting…")
    try:
        done = await asyncio.to_thread(_reset_sync, chat.id, ts, _utcnow())
    except PyMongoError:
        log.exception("msgcount: reset failed in %s", chat.id)
        await _edit(q, "⚠️ The reset could not be completed because the database had a problem. "
                       "Some statistics may be unchanged. Please send /resetrank again.", None)
        return
    if not done:
        await _edit(q, "This reset request was already used. Nothing more was changed.", None)
        return
    _off_until.pop(chat.id, None)
    await _edit(q, f"✅ <b>Message statistics reset</b> for {_esc(_chat_title(chat), 64)}.\n\n"
                   "Only this group's statistics were reset. Other groups were not affected. The counting ON/OFF "
                   "setting and the milestone interval were kept; milestones start again from 100.", None)


# ------------------------------------------------------------------ group -> supergroup migration
def _migrate_sync(old, new):
    for name in (GROUPS, COUNTS, MILESTONES):
        c = M.col(name)
        for doc in list(c.find({"chat_id": old})):
            try:
                c.update_one({"_id": doc["_id"]}, {"$set": {"chat_id": new}})
            except DuplicateKeyError:
                if name == COUNTS:
                    c.update_one({"chat_id": new, "user_id": doc["user_id"], "p": doc["p"]}, {"$inc": {"count": doc.get("count", 0)}})
                elif name == GROUPS:
                    c.update_one({"chat_id": new}, {"$inc": {"total": doc.get("total", 0)}})
                c.delete_one({"_id": doc["_id"]})


async def on_migrate(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """group=42: a basic group became a supergroup (new chat id): move its statistics across."""
    msg = update.effective_message
    new = msg.migrate_to_chat_id if msg else None
    if not new:
        return
    try:
        await asyncio.to_thread(_migrate_sync, msg.chat.id, new)
    except PyMongoError:
        log.exception("msgcount: couldn't move the statistics of %s to %s", msg.chat.id, new)


# ------------------------------------------------------------------ registration
_registered = set()


def register(app):
    """Commands, button handler and the counter. Call once, after the database is connected."""
    if id(app) in _registered:
        log.warning("msgcount.register called twice; ignoring the second call.")
        return
    _registered.add(id(app))
    ensure_indexes()
    app.add_handler(CommandHandler(["rank", "top", "overall"], rank_cmd))
    app.add_handler(CommandHandler("today", today_cmd))
    app.add_handler(CommandHandler("week", week_cmd))
    app.add_handler(CommandHandler("me", me_cmd))
    app.add_handler(CommandHandler("radmin", radmin_cmd))
    app.add_handler(CommandHandler("resetrank", resetrank_cmd))
    app.add_handler(CallbackQueryHandler(mc_callback, pattern=r"^mc:"))
    # own handler groups (nova.py uses -30..-1 and 0..5, 40, 41): none of them ever stops an update
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND, pending_input), group=-29)
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.UpdateType.MESSAGE & ~filters.StatusUpdate.ALL,
                                   count_message), group=60)
    app.add_handler(MessageHandler(filters.StatusUpdate.MIGRATE, on_migrate), group=42)
