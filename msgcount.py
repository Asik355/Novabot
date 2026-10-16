"""
Message Count / group leaderboard / group-wide milestones.

Kept in its own file so none of the existing code had to be rewritten. Wired up from nova.py with:
    msgcount.menu_button()      -> the "📊 Message Count" button of the /help menu (left of 🤖 AI Commands)
    msgcount.register(app)      -> commands, callbacks and the message counter
    msgcount.outbox_sweeper(app)-> background retry loop for milestone notifications (started in post_init)

    COMMANDS   /rank /top /overall /today /week /me /radmin /resetrank

DATA (MongoDB, the same connection/database as the rest of the bot; every record carries chat_id)
    mc_groups      one doc per group: chat_id (unique), name, total, enabled, initial, interval,
                   last_milestone, last_reset_at, created_at, updated_at, plus (all optional, old docs work without them):
                   last_msg_id  highest Telegram message number seen (supergroups): the "all messages sent" total
                   msg_base     start point subtracted from it (/resetrank moves it up), so Normal Count = last_msg_id - msg_base
                   custom_total / custom_enabled   the Bot Owner's custom count and whether it is ON (private chat only)
                   resync       set when counting is switched back ON: the next message does not count the gap
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
MAX_CUSTOM = 9_999_999_999          # largest custom count the Bot Owner can set
CC_PAGE = 8                         # groups per page in the owner's group list
_OWNERS = frozenset()               # Bot Owner IDs (OWNER_IDS of nova.py), set by register(); empty = nobody
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


def normal_count(g):
    """The real count: in supergroups the highest message number seen minus the start point (so it includes every
    message ever sent there: people, other bots, service messages), elsewhere the count of people's messages."""
    if g.get("last_msg_id") is not None:
        return max(int(g["last_msg_id"]) - int(g.get("msg_base", 0)), 0)
    return int(g.get("total", 0))


def active_count(g):
    """What the group sees: the custom count while Custom Mode is ON, otherwise the normal count. Never their sum."""
    if g.get("custom_enabled") is True:
        return int(g.get("custom_total", 0))
    return normal_count(g)


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


def _count_sync(chat_id, user_id, name, title, now, msg_id=None, supergroup=False, gap=False):
    """Counts ONE message. Returns None when counting is OFF for this group, else (group_doc, [new milestones]).
    Supergroups: the group total follows Telegram's message number (it catches up after downtime and includes messages
    this bot never receives); `gap` / the resync flag mean counting was OFF or paused, so that gap is NOT counted."""
    g = M.col(GROUPS)
    use_id = bool(supergroup and isinstance(msg_id, int) and msg_id > 0)
    before = None
    ran = False
    for _ in range(2):
        try:
            upd = {"$inc": {"total": 1}, "$set": {"name": title, "updated_at": now},
                   "$setOnInsert": {"enabled": True, "initial": DEFAULT_INITIAL, "interval": DEFAULT_INTERVAL,
                                    "last_milestone": 0, "created_at": now}}
            if use_id:
                upd["$max"] = {"last_msg_id": msg_id}
            before = g.find_one_and_update({"chat_id": chat_id, "enabled": {"$ne": False}}, upd,
                                           upsert=True, return_document=ReturnDocument.BEFORE) or {}
            ran = True
            break
        except DuplicateKeyError:
            cur = g.find_one({"chat_id": chat_id}, {"enabled": 1})
            if cur is not None and cur.get("enabled") is False:
                return None            # the row exists and counting is OFF
            # otherwise two first messages raced to create the row: try once more
    if not ran:
        return None
    # the state right after THIS message (the update above is atomic, so this is exact)
    doc = dict(before)
    doc.setdefault("chat_id", chat_id)
    doc.setdefault("enabled", True)
    doc.setdefault("initial", DEFAULT_INITIAL)
    doc.setdefault("interval", DEFAULT_INTERVAL)
    doc.setdefault("last_milestone", 0)
    doc["name"] = title
    doc["total"] = int(before.get("total", 0)) + 1
    delta, fix_pointer = 1, False
    if use_id:
        old = before.get("last_msg_id")
        doc["last_msg_id"] = max(int(old or 0), msg_id)
        if old is None:                                    # first message since message-number counting exists
            human = doc["total"]
            base = 0 if msg_id >= human else msg_id - human    # never let the count go backwards
            g.update_one({"chat_id": chat_id}, {"$set": {"msg_base": base}, "$unset": {"resync": ""}})
            doc["msg_base"] = base
            fix_pointer = True
        elif gap or before.get("resync"):                  # counting was OFF/paused: skip those messages
            skipped = msg_id - 1 - int(old)
            upd2 = {"$unset": {"resync": ""}}
            if skipped > 0:
                upd2["$inc"] = {"msg_base": skipped}
                doc["msg_base"] = int(before.get("msg_base", 0)) + skipped
            g.update_one({"chat_id": chat_id}, upd2)
        else:
            delta = max(msg_id - int(old), 0)              # also covers messages sent while the bot was offline
    if before.get("custom_enabled") is True:
        if delta > 0:
            cd = g.find_one_and_update({"chat_id": chat_id, "custom_enabled": True}, {"$inc": {"custom_total": delta}},
                                       return_document=ReturnDocument.AFTER)
            if cd is not None:
                doc["custom_total"] = int(cd.get("custom_total", 0))
            else:                                          # switched OFF in the meantime
                doc["custom_enabled"] = False
    _bulk_retry(M.col(COUNTS), [
        UpdateOne({"chat_id": chat_id, "user_id": user_id, "p": "all"},
                  {"$inc": {"count": 1}, "$set": {"name": name, "updated_at": now}, "$setOnInsert": {"scope": "all"}},
                  upsert=True),
        UpdateOne({"chat_id": chat_id, "user_id": user_id, "p": periods(now)[0]},
                  {"$inc": {"count": 1}, "$setOnInsert": {"scope": "day", "expire_at": _expire_at(now)}},
                  upsert=True),
    ])
    if fix_pointer:                                        # the total just jumped to the real number: don't announce old milestones
        doc["last_milestone"] = prev_milestone(active_count(doc), int(doc["initial"]), int(doc["interval"]))
        g.update_one({"chat_id": chat_id}, {"$set": {"last_milestone": doc["last_milestone"]}})
    created = []
    for _ in range(3):
        last, initial, interval = int(doc.get("last_milestone", 0)), int(doc.get("initial", DEFAULT_INITIAL)), int(doc.get("interval", DEFAULT_INTERVAL))
        nm = next_milestone(last, initial, interval)
        active = active_count(doc)
        if active < nm:
            break
        # 1) the durable outbox row first (unique per group+milestone), 2) then advance the pointer.
        #    A crash between the two is repaired by the next message (the insert is a harmless duplicate).
        try:
            M.col(MILESTONES).insert_one({
                "chat_id": chat_id, "milestone": nm, "total": active, "group_name": doc.get("name") or title,
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
    sets = {"enabled": bool(flag), "updated_at": now}
    if flag:
        sets["resync"] = True          # whatever was sent while counting was OFF is not counted
    M.col(GROUPS).update_one(
        {"chat_id": chat_id},
        {"$set": sets,
         "$setOnInsert": {"total": 0, "initial": DEFAULT_INITIAL, "interval": DEFAULT_INTERVAL, "last_milestone": 0, "created_at": now}},
        upsert=True)
    return _group_sync(chat_id)


def _save_interval_sync(chat_id, value, now):
    """Deterministic interval-change rule: the pointer moves to the last milestone of the NEW sequence that is
    <= the current total, so nothing already passed is announced and the next milestone is the first one of the
    new sequence above the current total. Totals, rankings and history are untouched."""
    cur = M.col(GROUPS).find_one({"chat_id": chat_id}) or {}
    last = prev_milestone(active_count(cur), int(cur.get("initial", DEFAULT_INITIAL)), value)
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
    claimed = claimed or {}
    upd = {"total": 0, "last_milestone": 0, "updated_at": now}
    if claimed.get("last_msg_id") is not None:
        upd["msg_base"] = int(claimed["last_msg_id"])      # the normal count starts again from 0
    if claimed.get("custom_enabled") is True:              # the custom count is untouched: keep its milestone pointer
        upd["last_milestone"] = prev_milestone(int(claimed.get("custom_total", 0)),
                                               int(claimed.get("initial", DEFAULT_INITIAL)),
                                               int(claimed.get("interval", DEFAULT_INTERVAL)))
    g.update_one({"chat_id": chat_id}, {"$set": upd})
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


_gap = set()   # chats where a message was skipped because of /pause (the gap is not counted afterwards)


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
        if len(_gap) > 2000:
            _gap.clear()
        _gap.add(chat.id)                       # remember it: that gap must not be counted when the pause ends
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
        res = await asyncio.to_thread(_count_sync, chat.id, user.id, (user.full_name or "")[:64], title, _utcnow(),
                                      msg.message_id, chat.type == "supergroup", chat.id in _gap)
    except PyMongoError:
        _seen.pop(key, None)
        log.exception("msgcount: couldn't count a message in %s", chat.id)
        return
    _gap.discard(chat.id)
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
    total, initial, interval = active_count(g), int(g.get("initial", DEFAULT_INITIAL)), int(g.get("interval", DEFAULT_INTERVAL))
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
        shown = (data.get("marks") or {}).get(uid) or _esc(name or f"User {uid}")
        lines.append(f"{_MEDALS.get(i, f'{i}.')} {shown} — {n:,}")
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


async def count_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/count: opens the Message Count menu (same screen as the 📊 Count button). In a private chat it shows the same
    note the button shows there, because counts are kept per group."""
    chat, msg = update.effective_chat, update.effective_message
    if chat is None or msg is None:
        return
    if chat.type == "private" and _cc_is_owner(update.effective_user.id if update.effective_user else None):
        text, kb = await _cc_list(msg.get_bot(), 0)
        await msg.reply_html(text, reply_markup=kb)
        return
    if chat.type not in GROUP_TYPES:
        await msg.reply_html("📊 <b>Message Count</b>\n\nMessage statistics are tracked separately for every group, so they "
                             "can only be viewed inside a group. Send /count in a group to see its message count.")
        return
    try:
        g = await asyncio.to_thread(_group_sync, chat.id)
    except PyMongoError:
        log.exception("msgcount: /count failed in %s", chat.id)
        await msg.reply_text(NO_DB)
        return
    sent = await msg.reply_html(_dash_text(_chat_title(chat, g), g), reply_markup=_dash_kb(g),
                                disable_web_page_preview=True)
    extra.remember_menu_owner(sent, update.effective_user.id if update.effective_user else None)


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
    await _decorate(msg.get_bot(), chat.id, data)
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
        if chat.type == "private" and _cc_is_owner(q.from_user.id):
            await q.answer()
            await _edit(q, *await _cc_list(context.bot, 0))
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
            await _decorate(context.bot, chat.id, data)
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


# ------------------------------------------------------------------ Delete: deleted accounts and inactive members
# Telegram gives a bot no member list, so everything here works on the people this bot has already counted (mc_counts).
# A deleted account is recognised by the name Telegram returns for it ("Deleted Account"). Only group admins can use any
# of it, and every kick needs the Ban Users right (checked on each tap). Nothing here is stored in the database.
DEAD_NAME = "Deleted Account"
DEAD_TTL = 24 * 3600                # how long a "checked" answer from Telegram is trusted
SCAN_CAP = 600                      # most members checked in one scan (the ones with the most messages first)
INACTIVE_DEFAULT, INACTIVE_MAX = 30, 365
INACTIVE_PAGE = 10
DELALL_SECS = 120                   # how long the Delete All lock stays open
LIST_SHOW = 40                      # serials shown in one message
_dead = {}        # chat_id -> {user_id: (checked_at, still_in_group)}   deleted accounts only
_clean = {}       # (chat_id, user_id) -> checked_at                      checked and NOT deleted
_dlist = {}       # chat_id -> (taken_at, [entries], capped)   the last scan: the serial numbers refer to this list
_delall = {}      # chat_id -> monotonic time the Delete All unlock ends (absent = locked)
_dpend = {}       # (chat_id, user_id) -> monotonic expiry: waiting for a serial number
_delall_running = set()
_scanning = set()
_last_force = {}
_bg = set()       # strong references to background tasks
DEL_DENIED = "Only group admins can use this. Kicking also needs the Ban Users right."
DEL_NEED_BAN = "You need the Ban Users right to kick members."


def _naive(dt):
    return dt.replace(tzinfo=None) if getattr(dt, "tzinfo", None) else dt


def _ago(dt):
    if dt is None:
        return "unknown"
    s = max(int((_naive(_utcnow()) - _naive(dt)).total_seconds()), 0)
    d = s // 86400
    if d >= 1:
        return f"{d} day{'s' if d != 1 else ''} ago"
    if s >= 3600:
        return f"{s // 3600} hour{'s' if s // 3600 != 1 else ''} ago"
    return "just now" if s < 120 else f"{s // 60} min ago"


def _retry_secs(e):
    ra = getattr(e, "retry_after", 1)
    ra = ra.total_seconds() if hasattr(ra, "total_seconds") else ra
    try:
        return min(max(float(ra), 0.5), 5.0)
    except (TypeError, ValueError):
        return 1.0


def _lock_on(chat_id):
    exp = _delall.get(chat_id)
    if exp is None:
        return False
    if exp <= time.monotonic():
        _delall.pop(chat_id, None)
        return False
    return True


def _countable(uid):
    return isinstance(uid, int) and uid > 0 and uid not in (ANON_ADMIN_ID, TELEGRAM_SERVICE_ID)


async def _check_users(bot, chat_id, ids, force=False):
    """Asks Telegram about each user in THIS chat (answers are cached for 24 h unless force).
    Returns {user_id: (deleted, still_in_group)}; a user Telegram can't answer for is simply left out (never guessed)."""
    now = time.monotonic()
    out, todo = {}, []
    dead = _dead.setdefault(chat_id, {})
    for uid in ids:
        if not force:
            d = dead.get(uid)
            if d is not None and now - d[0] < DEAD_TTL:
                out[uid] = (True, d[1])
                continue
            c = _clean.get((chat_id, uid))
            if c is not None and now - c < DEAD_TTL:
                out[uid] = (False, True)
                continue
        todo.append(uid)
    if not todo:
        return out
    sem = asyncio.Semaphore(8)

    async def one(uid):
        async with sem:
            for _ in range(2):
                try:
                    m = await bot.get_chat_member(chat_id, uid)
                except RetryAfter as e:
                    await asyncio.sleep(_retry_secs(e))
                    continue
                except TelegramError:
                    return None
                u = getattr(m, "user", None)
                deleted = (getattr(u, "first_name", None) or "").strip() == DEAD_NAME
                present = m.status in ("member", "administrator", "creator") or \
                    (m.status == "restricted" and getattr(m, "is_member", True) is not False)
                return uid, deleted, present
            return None

    stamp = time.monotonic()
    if len(_clean) > 50000:
        _clean.clear()
    for r in await asyncio.gather(*[one(u) for u in todo]):
        if r is None:
            continue
        uid, deleted, present = r
        out[uid] = (deleted, present)
        if deleted:
            dead[uid] = (stamp, present)
            _clean.pop((chat_id, uid), None)
        else:
            dead.pop(uid, None)
            _clean[(chat_id, uid)] = stamp
    return out


def _scan_rows_sync(chat_id):
    rows = list(M.col(COUNTS).find({"chat_id": chat_id, "scope": "all", "count": {"$gt": 0}},
                                   {"user_id": 1, "name": 1, "count": 1, "updated_at": 1},
                                   sort=[("count", -1), ("user_id", 1)], limit=SCAN_CAP + 1))
    capped = len(rows) > SCAN_CAP
    return [r for r in rows[:SCAN_CAP] if _countable(r.get("user_id"))], capped


def _serials_sync(chat_id):
    """Serial numbers of the deleted accounts already confirmed in this group (most messages first). Same order as the list."""
    ids = [u for u, (_, present) in (_dead.get(chat_id) or {}).items() if present]
    if not ids:
        return {}
    rows = list(M.col(COUNTS).find({"chat_id": chat_id, "scope": "all", "user_id": {"$in": ids}},
                                   {"user_id": 1, "count": 1}))
    rows.sort(key=lambda r: (-int(r.get("count", 0)), r["user_id"]))
    return {r["user_id"]: i for i, r in enumerate(rows, 1)}


def _lastseen_sync(chat_id, ids):
    return {d["user_id"]: d.get("updated_at") for d in
            M.col(COUNTS).find({"chat_id": chat_id, "scope": "all", "user_id": {"$in": list(ids)}},
                               {"user_id": 1, "updated_at": 1})}


async def _scan_deleted(bot, chat_id, force=False):
    """Checks the counted members of this group and returns (entries, capped); entries are the deleted accounts that are
    still in the group, numbered 1.. (most messages first). The result is kept as the list the serial numbers refer to."""
    if chat_id in _scanning:
        snap = _dlist.get(chat_id)
        return (snap[1], snap[2]) if snap else ([], False)
    _scanning.add(chat_id)
    try:
        rows, capped = await asyncio.to_thread(_scan_rows_sync, chat_id)
        res = await _check_users(bot, chat_id, [r["user_id"] for r in rows], force=force)
        ents = []
        for r in rows:
            st = res.get(r["user_id"])
            if st and st[0] and st[1]:
                ents.append({"uid": r["user_id"], "count": int(r.get("count", 0)), "last": r.get("updated_at"),
                             "n": len(ents) + 1})
        if len(_dlist) > 500:
            _dlist.clear()
        _dlist[chat_id] = (time.monotonic(), ents, capped)
        return ents, capped
    finally:
        _scanning.discard(chat_id)


async def _decorate(bot, chat_id, data):
    """Adds data['marks'] to a leaderboard page: 👻 for deleted accounts (with their serial) and 💤 for members quiet for
    INACTIVE_DEFAULT days. Never raises: on any problem the board simply shows without marks."""
    data["marks"] = {}
    try:
        rows = data.get("rows") or []
        ids = [u for u, _, _ in rows if _countable(u)]
        if not ids:
            return
        res = await asyncio.wait_for(_check_users(bot, chat_id, ids), timeout=8)
        serial = await asyncio.to_thread(_serials_sync, chat_id)
        seen = await asyncio.to_thread(_lastseen_sync, chat_id, ids)
        cutoff = _naive(_utcnow()) - timedelta(days=INACTIVE_DEFAULT)
        names = {u: n for u, n, _ in rows}
        for u in ids:
            st = res.get(u)
            if st and st[0]:
                n = serial.get(u) if st[1] else None
                data["marks"][u] = "👻 Deleted Account" + (f" #{n}" if n else "")
            elif seen.get(u) is not None and _naive(seen[u]) < cutoff:
                data["marks"][u] = "💤 " + _esc(names.get(u) or f"User {u}")
    except Exception:
        log.warning("msgcount: leaderboard marks skipped", exc_info=True)
        data["marks"] = {}


async def _owner_power(user_id):
    fn = getattr(getattr(extra, "_BD", None), "is_bot_owner", None)
    try:
        return bool(fn and fn(user_id))
    except Exception:
        log.exception("msgcount: owner power check failed")
        return False


async def _rights(bot, chat_id, user_id):
    """2 = may kick (owner / admin with Ban Users), 1 = admin without it, 0 = not an admin, None = Telegram can't be asked."""
    if await _owner_power(user_id):
        return 2
    try:
        m = await bot.get_chat_member(chat_id, user_id)
    except TelegramError:
        log.exception("msgcount: get_chat_member failed chat=%s user=%s", chat_id, user_id)
        return None
    if m.status == "creator":
        return 2
    if m.status == "administrator":
        return 2 if getattr(m, "can_restrict_members", False) else 1
    return 0


async def _bot_can_kick(bot, chat_id):
    try:
        me = await bot.get_chat_member(chat_id, bot.id)
    except TelegramError:
        return None
    return me.status == "administrator" and bool(getattr(me, "can_restrict_members", False))


async def _kick_dead(bot, chat_id, uid):
    """Removes ONE deleted account (ban + unban = kick, no ban stays). Checks it again first. Returns (kind, text):
    kind is 'ok', 'skip' or 'fail'."""
    res = await _check_users(bot, chat_id, [uid], force=True)
    st = res.get(uid)
    if st is None:
        return "skip", "Telegram could not confirm this account"
    if not st[0]:
        return "skip", "it is not a deleted account"
    if not st[1]:
        return "skip", "it already left the group"
    for attempt in range(2):
        try:
            await bot.ban_chat_member(chat_id, uid)
            break
        except RetryAfter as e:
            await asyncio.sleep(_retry_secs(e))
        except TelegramError as e:
            return "fail", str(e)[:80]
    else:
        return "fail", "Telegram is busy, try again"
    note = ""
    for attempt in range(3):
        try:
            await bot.unban_chat_member(chat_id, uid, only_if_banned=True)
            break
        except RetryAfter as e:
            await asyncio.sleep(_retry_secs(e))
        except TelegramError:
            await asyncio.sleep(0.5)
    else:
        note = " (kicked, but the unban failed: unban it manually)"
    _dead.setdefault(chat_id, {})[uid] = (time.monotonic(), False)
    snap = _dlist.get(chat_id)
    if snap:
        _dlist[chat_id] = (snap[0], [e for e in snap[1] if e["uid"] != uid], snap[2])
    return "ok", note


def _entry(chat_id, uid=None, n=None):
    snap = _dlist.get(chat_id)
    if not snap:
        return None
    for e in snap[1]:
        if (uid is not None and e["uid"] == uid) or (n is not None and e["n"] == n):
            return e
    return None


# ----- screens
def _del_card_view():
    text = ("🗑 <b>DELETE</b>\n\n"
            "👻 <b>Deleted Accounts</b>\nFind deleted accounts and kick them one by one.\n\n"
            "💤 <b>Inactive Members</b>\nSee members with no message for N days.")
    return text, KB([[B("👻 Deleted List", callback_data="mcd:l"), B(f"💤 Inactive {INACTIVE_DEFAULT}", callback_data=f"mcd:i:{INACTIVE_DEFAULT}:0")],
                     [B("ℹ️ How it works", callback_data="mcd:h")],
                     [B("« Back", callback_data="help:main")]])


_DEL_HELP = ("ℹ️ <b>HOW IT WORKS</b>\n\n"
             "👻 <b>Deleted accounts</b>\nTelegram does not give bots the member list, so the bot checks the members it has "
             "already counted (the most active first). Members who never wrote a message can't be found.\n\n"
             "🔢 <b>Serial numbers</b>\nThe list is numbered #1, #2, … by messages. The numbers can change when the list "
             "changes, so always check the latest list.\n\n"
             "🗑 <b>Kick one</b>\nSend its number (or <code>/deleted 3</code>), then confirm. The account is checked again, "
             "then kicked (no ban is left).\n\n"
             "🔒 <b>Delete All</b>\nLocked by default. Turn it on, it stays open for 2 minutes, then confirm.\n\n"
             "💤 <b>Inactive</b>\n<code>/inactive 30</code> lists members with no message for 30 days. Members who left "
             "may still appear.\n\n"
             "🔐 Only group admins can use this; kicking needs the Ban Users right.")


def _dlist_view(chat_id, ents, capped, note=""):
    on = _lock_on(chat_id)
    lines = [f"{note}👻 <b>DELETED ACCOUNTS ({len(ents)})</b>", ""]
    if not ents:
        lines.append("No deleted accounts found among the members counted so far.")
    for e in ents[:LIST_SHOW]:
        lines.append(f"<b>#{e['n']}</b> · {e['count']:,} msgs · last seen {_ago(e['last'])}")
    if len(ents) > LIST_SHOW:
        lines.append(f"… and {len(ents) - LIST_SHOW} more (kick some, then refresh)")
    if ents:
        lines += ["", "Send a serial number to kick that account."]
        if on:
            lines.append("🔓 Delete All is ON for 2 minutes.")
    if capped:
        lines += ["", f"<i>Only the {SCAN_CAP} members with the most messages were checked.</i>"]
    kb = []
    if ents:
        kb.append([B("🗑 Delete #", callback_data="mcd:s")])
        kb.append([B("🔓 Delete All: ON" if on else "🔒 Delete All: OFF", callback_data="mcd:t")])
        if on:
            kb.append([B(f"🗑 Delete All ({len(ents)})", callback_data="mcd:da")])
    kb.append([B("🔄 Refresh", callback_data="mcd:lr"), B("« Back", callback_data="mcd:m")])
    return "\n".join(lines), KB(kb)


async def _inactive_view(bot, chat_id, days, page):
    def q():
        cutoff = _utcnow() - timedelta(days=days)
        flt = {"chat_id": chat_id, "scope": "all", "count": {"$gt": 0}, "updated_at": {"$lt": cutoff}}
        c = M.col(COUNTS)
        total = c.count_documents(flt)
        pages = max(1, -(-total // INACTIVE_PAGE))
        pg = min(max(page, 0), pages - 1)
        rows = list(c.find(flt, {"user_id": 1, "name": 1, "count": 1, "updated_at": 1},
                           sort=[("updated_at", 1), ("user_id", 1)], skip=pg * INACTIVE_PAGE, limit=INACTIVE_PAGE))
        return total, pages, pg, rows
    total, pages, pg, rows = await asyncio.to_thread(q)
    marks = {}
    try:
        res = await asyncio.wait_for(_check_users(bot, chat_id, [r["user_id"] for r in rows if _countable(r["user_id"])]), timeout=8)
        serial = await asyncio.to_thread(_serials_sync, chat_id)
        for u, (dele, present) in res.items():
            if dele:
                n = serial.get(u) if present else None
                marks[u] = "👻 Deleted Account" + (f" #{n}" if n else "")
    except Exception:
        log.warning("msgcount: inactive list marks skipped", exc_info=True)
    lines = [f"💤 <b>INACTIVE {days}+ DAYS ({total})</b>", ""]
    if not rows:
        lines.append("Nobody has been quiet that long among the members counted so far.")
    base = pg * INACTIVE_PAGE
    for i, r in enumerate(rows, base + 1):
        who = marks.get(r["user_id"]) or _esc(r.get("name") or f"User {r['user_id']}")
        lines.append(f"{i}. {who} — {int(r['count']):,} msgs · {_ago(r.get('updated_at'))}")
    if pages > 1:
        lines += ["", f"Page {pg + 1}/{pages}"]
    lines += ["", "<i>Only members who wrote at least one counted message appear. Members who left may still be listed.</i>"]
    kb = []
    nav = []
    if pg > 0:
        nav.append(B("⬅️ Prev", callback_data=f"mcd:i:{days}:{pg - 1}"))
    if pg < pages - 1:
        nav.append(B("Next ➡️", callback_data=f"mcd:i:{days}:{pg + 1}"))
    if nav:
        kb.append(nav)
    kb.append([B(f"{d} days", callback_data=f"mcd:i:{d}:0") for d in (7, 30, 90)])
    kb.append([B("« Back", callback_data="mcd:m")])
    return "\n".join(lines), KB(kb)


def _kick_confirm_view(e):
    return (f"🗑 <b>KICK DELETED ACCOUNT #{e['n']}?</b>\n\n{e['count']:,} msgs · last seen {_ago(e['last'])}\n"
            "It is checked again before it is kicked.",
            KB([[B("✅ Confirm", callback_data=f"mcd:ky:{e['uid']}"), B("❌ Cancel", callback_data="mcd:l")]]))


def _delall_confirm_view(n):
    return (f"⚠️ <b>KICK ALL {n} DELETED ACCOUNTS?</b>\n\nEach account is checked again before it is kicked.\nThis cannot be undone.",
            KB([[B("✅ Confirm", callback_data="mcd:day"), B("❌ Cancel", callback_data="mcd:l")]]))


async def _run_delall(bot, q, chat_id):
    """Background: kicks the deleted accounts of the last list one by one, then reports. The lock is already OFF."""
    try:
        ents = list((_dlist.get(chat_id) or (0, [], False))[1])
        kicked = skipped = failed = 0
        notes = []
        for i, e in enumerate(ents, 1):
            kind, note = await _kick_dead(bot, chat_id, e["uid"])
            if kind == "ok":
                kicked += 1
                if note:
                    notes.append(f"#{e['n']}{note}")
            elif kind == "skip":
                skipped += 1
            else:
                failed += 1
                notes.append(f"#{e['n']}: {note}")
            if i % 10 == 0 and i < len(ents):
                await _edit(q, f"⏳ <b>Kicking deleted accounts…</b> {i}/{len(ents)}", None)
            await asyncio.sleep(0.3)
        text = f"✅ <b>DELETE ALL DONE</b>\n\nKicked: {kicked}\nSkipped: {skipped}"
        if failed:
            text += f"\nFailed: {failed}"
        if notes:
            text += "\n\n" + "\n".join(_esc(n, 90) for n in notes[:10])
        text += "\n\n🔒 Delete All is OFF again."
        await _edit(q, text, KB([[B("👻 Deleted List", callback_data="mcd:l"), B("« Back", callback_data="mcd:m")]]))
    except Exception:
        log.exception("msgcount: Delete All failed in %s", chat_id)
        await _edit(q, "⚠️ Delete All stopped because of an error. Some accounts may already be kicked. Open the list to see what is left.",
                    KB([[B("👻 Deleted List", callback_data="mcd:l")]]))
    finally:
        _delall_running.discard(chat_id)
        _delall.pop(chat_id, None)


async def _guard(q, bot, chat_id, need):
    """Strict permission check on every tap. need: 1 = admin, 2 = may kick. True when allowed (else the user was told)."""
    r = await _rights(bot, chat_id, q.from_user.id)
    if r is None:
        await q.answer("I couldn't verify your permissions right now. Nothing was changed.", show_alert=True)
        return False
    if r < need:
        await q.answer(DEL_DENIED if r == 0 else DEL_NEED_BAN, show_alert=True)
        return False
    return True


async def del_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    parts = (q.data or "").split(":")
    try:
        if await extra.menu_not_owner(q):
            return
        chat = getattr(q.message, "chat", None)
        act = parts[1] if len(parts) > 1 else ""
        if chat is None or chat.type not in GROUP_TYPES:
            await q.answer("Open /help inside a group to use this.", show_alert=True)
            return
        bot = context.bot
        cid = chat.id
        need = 2 if act in ("s", "k", "ky", "t", "da", "day") else 1
        if not await _guard(q, bot, cid, need):
            return
        if act == "m":
            _dpend.pop((cid, q.from_user.id), None)
            await q.answer()
            await _edit(q, *_del_card_view())
        elif act == "h":
            await q.answer()
            await _edit(q, _DEL_HELP, KB([[B("« Back", callback_data="mcd:m")]]))
        elif act in ("l", "lr"):
            _dpend.pop((cid, q.from_user.id), None)
            force = act == "lr"
            if force:
                if time.monotonic() - _last_force.get(cid, -1e9) < 60:
                    await q.answer("Please wait a minute before refreshing again.", show_alert=True)
                    return
                if len(_last_force) > 500:
                    _last_force.clear()
                _last_force[cid] = time.monotonic()
            await q.answer()
            snap = _dlist.get(cid)
            if act == "l" and snap and time.monotonic() - snap[0] < 600:
                ents, capped = snap[1], snap[2]
            else:
                await _edit(q, "👻 <b>Checking members…</b>\n\nThis can take a little while.", None)
                ents, capped = await _scan_deleted(bot, cid, force=force)
            await _edit(q, *_dlist_view(cid, ents, capped))
        elif act == "s":
            if not _entry(cid, n=1) and not (_dlist.get(cid) and _dlist[cid][1]):
                await q.answer("Open the list first.", show_alert=True)
                return
            if len(_dpend) > 500:
                _dpend.clear()
            _dpend[(cid, q.from_user.id)] = time.monotonic() + INPUT_SECS
            await q.answer()
            await _edit(q, "🗑 <b>KICK A DELETED ACCOUNT</b>\n\nSend the serial number from the list (for example <code>3</code>) "
                           f"within {INPUT_SECS // 60} minutes.", KB([[B("❌ Cancel", callback_data="mcd:l")]]))
        elif act == "t":
            ents = (_dlist.get(cid) or (0, [], False))[1]
            if not ents:
                await q.answer("There is nothing to delete. Open the list first.", show_alert=True)
                return
            if _lock_on(cid):
                _delall.pop(cid, None)
                await q.answer("Delete All is locked again.")
            else:
                if len(_delall) > 500:
                    _delall.clear()
                _delall[cid] = time.monotonic() + DELALL_SECS
                await q.answer("Delete All is ON for 2 minutes.")
            snap = _dlist[cid]
            await _edit(q, *_dlist_view(cid, snap[1], snap[2]))
        elif act == "da":
            snap = _dlist.get(cid)
            if not _lock_on(cid):
                await q.answer("Delete All is locked. Turn it on first.", show_alert=True)
                return
            if not snap or not snap[1]:
                await q.answer("There is nothing to delete.", show_alert=True)
                return
            await q.answer()
            await _edit(q, *_delall_confirm_view(len(snap[1])))
        elif act == "day":
            if not _lock_on(cid):
                await q.answer("Delete All was locked again. Turn it on first.", show_alert=True)
                return
            if cid in _delall_running:
                await q.answer("Delete All is already running.", show_alert=True)
                return
            snap = _dlist.get(cid)
            if not snap or not snap[1]:
                await q.answer("There is nothing to delete.", show_alert=True)
                return
            ok = await _bot_can_kick(bot, cid)
            if ok is not True:
                await q.answer("I need the Ban Users admin right to kick members." if ok is False else "I couldn't check my own rights. Nothing was changed.", show_alert=True)
                return
            _delall.pop(cid, None)             # the lock closes the moment it is used
            _delall_running.add(cid)
            await q.answer("Started.")
            await _edit(q, f"⏳ <b>Kicking deleted accounts…</b> 0/{len(snap[1])}", None)
            task = asyncio.get_running_loop().create_task(_run_delall(bot, q, cid))
            _bg.add(task)
            task.add_done_callback(_bg.discard)
        elif act == "k" and len(parts) == 3 and parts[2].isdigit():
            e = _entry(cid, uid=int(parts[2]))
            if e is None:
                await q.answer("That list is out of date. Open the list again.", show_alert=True)
                return
            await q.answer()
            await _edit(q, *_kick_confirm_view(e))
        elif act == "ky" and len(parts) == 3 and parts[2].isdigit():
            uid = int(parts[2])
            e = _entry(cid, uid=uid)
            ok = await _bot_can_kick(bot, cid)
            if ok is not True:
                await q.answer("I need the Ban Users admin right to kick members." if ok is False else "I couldn't check my own rights. Nothing was changed.", show_alert=True)
                return
            kind, note = await _kick_dead(bot, cid, uid)
            await q.answer()
            snap = _dlist.get(cid) or (0, [], False)
            if kind == "ok":
                text = f"✅ <b>Deleted Account{(' #%d' % e['n']) if e else ''} was removed.</b>{_esc(note, 90)}\n\n{len(snap[1])} deleted account(s) remain in the last list."
            else:
                text = f"⚠️ <b>Nothing was kicked.</b> {_esc(note, 90)}"
            await _edit(q, text, KB([[B("👻 Deleted List", callback_data="mcd:l"), B("« Back", callback_data="mcd:m")]]))
        elif act == "i" and len(parts) == 4 and parts[2].isdigit() and parts[3].isdigit() and len(parts[3]) <= 6:
            days = int(parts[2])
            if not 1 <= days <= INACTIVE_MAX:
                await q.answer("This button is no longer valid.", show_alert=True)
                return
            await q.answer()
            await _edit(q, *await _inactive_view(bot, cid, days, int(parts[3])))
        else:
            await q.answer("This button is no longer valid.", show_alert=True)
    except PyMongoError:
        log.exception("msgcount: database error in delete callback %r", q.data)
        try:
            await q.answer(NO_DB, show_alert=True)
        except TelegramError:
            pass
    except TelegramError as e:
        log.warning("msgcount: Telegram error in delete callback %r: %s", q.data, e)
    except Exception:
        log.exception("msgcount: delete callback %r failed", q.data)
        try:
            await q.answer("Something went wrong. Please try again.", show_alert=True)
        except TelegramError:
            pass


async def _confirm_serial(msg, bot, chat, user, n):
    """Shared by the typed serial number and /deleted <n>: shows the confirmation for ONE account."""
    if not await _bot_can_kick(bot, chat.id) is True:
        await msg.reply_text("I need the Ban Users admin right to kick members, so nothing was changed.")
        return
    e = _entry(chat.id, n=n)
    if e is None:
        await msg.reply_text("There is no deleted account with that number in the latest list. Open /deleted and check the numbers.")
        return
    text, kb = _kick_confirm_view(e)
    sent = await msg.reply_html(text, reply_markup=kb)
    extra.remember_menu_owner(sent, user.id)


async def del_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """group=-27: the serial number typed after 🗑 Delete #. Only the admin who tapped it, only digits, only in time.
    Never stops other handlers."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg is None or chat is None or user is None or not _dpend:
        return
    exp = _dpend.get((chat.id, user.id))
    if exp is None:
        return
    if exp <= time.monotonic():
        _dpend.pop((chat.id, user.id), None)
        return
    text = (msg.text or "").strip()
    if not re.fullmatch(r"[0-9]{1,5}", text):
        return                                   # ordinary chat while waiting: ignore it
    _dpend.pop((chat.id, user.id), None)
    r = await _rights(context.bot, chat.id, user.id)
    if r != 2:
        await msg.reply_text(DEL_DENIED if r == 0 else DEL_NEED_BAN if r == 1 else "I couldn't verify your permissions right now. Nothing was changed.")
        return
    await _confirm_serial(msg, context.bot, chat, user, int(text))


async def deleted_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = await _group_chat_or_reject(update)
    if chat is None:
        return
    msg, user = update.effective_message, update.effective_user
    if user is None or user.id == ANON_ADMIN_ID or msg.sender_chat is not None:
        await msg.reply_text("I can't tell who you are while you post anonymously. Please post as yourself.")
        return
    arg = (context.args[0].lower() if getattr(context, "args", None) else "")
    r = await _rights(context.bot, chat.id, user.id)
    if r is None:
        await msg.reply_text("I couldn't verify your permissions right now. Nothing was changed.")
        return
    if r < (2 if arg else 1):
        await msg.reply_text(DEL_DENIED if r == 0 else DEL_NEED_BAN)
        return
    try:
        if arg == "all":
            if not _lock_on(chat.id):
                await msg.reply_html("🔒 <b>Delete All is locked.</b>\nTurn it on in 🗑 Delete → Deleted List.")
                return
            snap = _dlist.get(chat.id)
            if not snap or not snap[1]:
                await msg.reply_text("There is nothing to delete. Open /deleted first.")
                return
            text, kb = _delall_confirm_view(len(snap[1]))
            sent = await msg.reply_html(text, reply_markup=kb)
            extra.remember_menu_owner(sent, user.id)
        elif arg:
            if not re.fullmatch(r"[0-9]{1,5}", arg):
                await msg.reply_text("Use /deleted to see the list, /deleted 3 to kick #3, or /deleted all.")
                return
            await _confirm_serial(msg, context.bot, chat, user, int(arg))
        else:
            wait = await msg.reply_html("👻 <b>Checking members…</b>\n\nThis can take a little while.")
            ents, capped = await _scan_deleted(context.bot, chat.id)
            text, kb = _dlist_view(chat.id, ents, capped)
            try:
                await wait.edit_text(text, parse_mode="HTML", reply_markup=kb)
            except TelegramError:
                await msg.reply_html(text, reply_markup=kb)
            extra.remember_menu_owner(wait, user.id)
    except PyMongoError:
        log.exception("msgcount: /deleted failed in %s", chat.id)
        await msg.reply_text(NO_DB)


async def inactive_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = await _group_chat_or_reject(update)
    if chat is None:
        return
    msg, user = update.effective_message, update.effective_user
    if user is None or user.id == ANON_ADMIN_ID or msg.sender_chat is not None:
        await msg.reply_text("I can't tell who you are while you post anonymously. Please post as yourself.")
        return
    days = INACTIVE_DEFAULT
    args = getattr(context, "args", None) or []
    if args:
        if not re.fullmatch(r"[0-9]{1,4}", args[0]) or not 1 <= int(args[0]) <= INACTIVE_MAX:
            await msg.reply_text(f"Use /inactive or /inactive <days>, with days from 1 to {INACTIVE_MAX}. Example: /inactive 30")
            return
        days = int(args[0])
    r = await _rights(context.bot, chat.id, user.id)
    if r is None:
        await msg.reply_text("I couldn't verify your permissions right now. Nothing was changed.")
        return
    if r < 1:
        await msg.reply_text(DEL_DENIED)
        return
    try:
        text, kb = await _inactive_view(context.bot, chat.id, days, 0)
    except PyMongoError:
        log.exception("msgcount: /inactive failed in %s", chat.id)
        await msg.reply_text(NO_DB)
        return
    sent = await msg.reply_html(text, reply_markup=kb)
    extra.remember_menu_owner(sent, user.id)


# ------------------------------------------------------------------ Bot Owner: custom count (private chat only)
# Nothing here is ever reachable from a group: every handler requires a PRIVATE chat and the sender's ID in OWNER_IDS,
# checked again on every tap and on every typed number. The group dashboard has no such buttons.
_cc_pending = {}   # owner id -> (group chat_id, expiry on the monotonic clock, "count" | "interval"). Transient UI state only.


def _cc_is_owner(user_id):
    return user_id is not None and user_id in _OWNERS


def _cc_groups_sync(page, ids=None):
    c = M.col(GROUPS)
    flt = {"chat_id": {"$lt": 0}} if ids is None else {"chat_id": {"$in": list(ids)}}
    total = c.count_documents(flt)
    pages = max(1, -(-total // CC_PAGE))
    page = min(max(page, 0), pages - 1)
    rows = list(c.find(flt, sort=[("name", 1), ("chat_id", 1)], skip=page * CC_PAGE, limit=CC_PAGE))
    return rows, page, pages


_GROUPS_SOURCE = None          # async callable(bot) -> [(chat_id, title, link)]: the groups the bot is in RIGHT NOW (set by register)
_cc_ids_cache = (0.0, None)    # (monotonic time, set of chat ids) kept for 60 seconds


async def _cc_current_ids(bot):
    """The chat ids of the groups the bot is currently in (checked with Telegram by the bot's own group list), or None when
    that can't be known right now (then the list simply isn't filtered: never hide a group on a guess)."""
    global _cc_ids_cache
    if _GROUPS_SOURCE is None:
        return None
    t, ids = _cc_ids_cache
    if ids is not None and time.monotonic() - t < 60:
        return ids
    try:
        rows = await asyncio.wait_for(_GROUPS_SOURCE(bot), timeout=25)
        ids = {int(r[0]) for r in rows}
    except Exception:
        log.warning("msgcount: couldn't get the bot's current groups; using the last known list", exc_info=True)
        return ids                                         # the last good answer, or None
    _cc_ids_cache = (time.monotonic(), ids)
    return ids


async def _cc_list(bot, page):
    ids = await _cc_current_ids(bot)
    return await asyncio.to_thread(_cc_list_view, page, ids)


def _cc_list_view(page, ids=None):
    rows, page, pages = _cc_groups_sync(page, ids)
    if not rows:
        return "📊 <b>SELECT A GROUP</b>\n\nNo group the bot is in has been counted yet.", KB([[B("🔙 Back", callback_data="help:main")]])
    kb = [[B("👥 " + (r.get("name") or str(r["chat_id"]))[:40], callback_data=f"mcc:g:{r['chat_id']}")] for r in rows]
    nav = []
    if page > 0:
        nav.append(B("⬅️ Prev", callback_data=f"mcc:l:{page - 1}"))
    if page < pages - 1:
        nav.append(B("Next ➡️", callback_data=f"mcc:l:{page + 1}"))
    if nav:
        kb.append(nav)
    kb.append([B("🔙 Back", callback_data="help:main")])
    return "📊 <b>SELECT A GROUP</b>" + (f"\n\nPage {page + 1}/{pages}" if pages > 1 else ""), KB(kb)


def _cc_dash_view(chat_id, note=""):
    g = M.col(GROUPS).find_one({"chat_id": chat_id})
    if g is None:
        return "⚠️ This group is no longer in the list.", KB([[B("🔙 Select Group", callback_data="mcc:l:0")]])
    on = g.get("custom_enabled") is True
    text = (f"{note}📊 <b>CUSTOM COUNT</b>\n\n"
            f"👥 <b>Group:</b> {_esc(g.get('name') or chat_id, 64)}\n\n"
            f"💬 <b>Active Count:</b> {active_count(g):,}\n"
            f"📊 <b>Normal Count:</b> {normal_count(g):,}\n"
            f"🔧 <b>Custom Mode:</b> {'ON' if on else 'OFF'}\n"
            f"💾 <b>Saved Custom Count:</b> {int(g.get('custom_total', 0)):,}\n"
            f"🎯 <b>Milestone:</b> every {int(g.get('interval', DEFAULT_INTERVAL)):,} messages")
    return text, KB([
        [B("⚙️ Set Custom Count", callback_data=f"mcc:s:{chat_id}")],
        [B("🎯 Milestone", callback_data=f"mcc:m:{chat_id}")],
        [B("♻️ Reset to Default", callback_data=f"mcc:r:{chat_id}")],
        [B("📖 Help Me", callback_data=f"mcc:h:{chat_id}")],
        [B("🔙 Select Group", callback_data="mcc:l:0")],
    ])


def _cc_set_sync(chat_id, value, now):
    """Save the custom count and switch Custom Mode ON. The normal count is not touched. Returns False if the group is gone."""
    c = M.col(GROUPS)
    g = c.find_one({"chat_id": chat_id})
    if g is None:
        return False
    # the group is told about no old milestones just because a number was set: the pointer moves to the new count
    last = prev_milestone(value, int(g.get("initial", DEFAULT_INITIAL)), int(g.get("interval", DEFAULT_INTERVAL)))
    res = c.update_one({"chat_id": chat_id}, {"$set": {"custom_total": int(value), "custom_enabled": True,
                                                       "last_milestone": last, "updated_at": now}})
    return bool(getattr(res, "matched_count", 1))


def _cc_reset_sync(chat_id, now):
    """Custom Mode OFF. Both counters stay stored; the group goes back to its normal count."""
    c = M.col(GROUPS)
    g = c.find_one({"chat_id": chat_id})
    if g is None:
        return False
    last = prev_milestone(normal_count(g), int(g.get("initial", DEFAULT_INITIAL)), int(g.get("interval", DEFAULT_INTERVAL)))
    res = c.update_one({"chat_id": chat_id}, {"$set": {"custom_enabled": False, "last_milestone": last, "updated_at": now}})
    return bool(getattr(res, "matched_count", 1))


_CC_HELP = ("📖 <b>CUSTOM COUNT HELP</b>\n\n"
            "⚙️ <b>Set Custom Count</b>\nSet a custom total for the selected group.\n\n"
            "♻️ <b>Reset to Default</b>\nSwitch back to the group's normal message count.\n"
            "Your saved custom count will remain in the database.\n\n"
            "💬 <b>Automatic Counting</b>\nEligible new messages are counted automatically.\n"
            "The normal counter always continues updating.\nThe custom counter updates only while Custom Mode is ON.\n\n"
            "🔐 <b>Owner Only</b>\nOnly registered Bot Owners can change these settings.")


async def cc_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    chat = getattr(q.message, "chat", None)
    uid = q.from_user.id if q.from_user else None
    # server-side authorization on EVERY tap: private chat + OWNER_IDS (a visible button or a copied payload proves nothing)
    if chat is None or chat.type != "private" or not _cc_is_owner(uid) or chat.id != uid:
        await q.answer("Only registered Bot Owners can use this, in a private chat.", show_alert=True)
        return
    parts = (q.data or "").split(":")
    try:
        act = parts[1] if len(parts) > 1 else ""
        gid = int(parts[2]) if len(parts) > 2 and re.fullmatch(r"-?[0-9]{1,20}", parts[2]) else None
        if act == "l":
            await q.answer()
            await _edit(q, *await _cc_list(context.bot, gid or 0))
            return
        if gid is None or gid >= 0:
            await q.answer("This button is no longer valid.", show_alert=True)
            return
        if act == "g":
            _cc_pending.pop(uid, None)
            await q.answer()
            await _edit(q, *await asyncio.to_thread(_cc_dash_view, gid))
        elif act == "s":
            exists = await asyncio.to_thread(M.col(GROUPS).find_one, {"chat_id": gid})
            if exists is None:
                await q.answer("This group is no longer in the list.", show_alert=True)
                return
            if len(_cc_pending) > 200:
                _cc_pending.clear()
            _cc_pending[uid] = (gid, time.monotonic() + INPUT_SECS, "count")
            await q.answer()
            await _edit(q, "⚙️ <b>SET CUSTOM COUNT</b>\n\nEnter the new total message count for the selected group.\n\n"
                           f"Example: <code>50000</code>\n\nSend a whole number from 0 to {MAX_CUSTOM:,} within {INPUT_SECS // 60} minutes.",
                        KB([[B("❌ Cancel", callback_data=f"mcc:g:{gid}")]]))
        elif act in ("m", "mp"):
            g = await asyncio.to_thread(M.col(GROUPS).find_one, {"chat_id": gid})
            if g is None:
                await q.answer("This group is no longer in the list.", show_alert=True)
                return
            if act == "mp":                                # one of the quick values
                v = parts[3] if len(parts) > 3 else ""
                if not re.fullmatch(r"[0-9]{1,7}", v) or not (MIN_INTERVAL <= int(v) <= MAX_INTERVAL):
                    await q.answer("This button is no longer valid.", show_alert=True)
                    return
                _cc_pending.pop(uid, None)
                g2 = await asyncio.to_thread(_save_interval_sync, gid, int(v), _utcnow())
                await q.answer("Milestone saved.")
                nxt = next_milestone(int(g2.get("last_milestone", 0)), int(g2.get("initial", DEFAULT_INITIAL)), int(v))
                await _edit(q, *await asyncio.to_thread(
                    _cc_dash_view, gid, f"✅ <b>Milestone saved:</b> every {int(v):,} messages. Next milestone: {nxt:,}.\n\n"))
                return
            if len(_cc_pending) > 200:
                _cc_pending.clear()
            _cc_pending[uid] = (gid, time.monotonic() + INPUT_SECS, "interval")
            await q.answer()
            await _edit(q, "🎯 <b>MILESTONE</b>\n\n"
                           f"Now: every {int(g.get('interval', DEFAULT_INTERVAL)):,} messages.\n\n"
                           f"Tap a quick value or send your own whole number from {MIN_INTERVAL:,} to {MAX_INTERVAL:,} within {INPUT_SECS // 60} minutes.",
                        KB([[B("250", callback_data=f"mcc:mp:{gid}:250"), B("500", callback_data=f"mcc:mp:{gid}:500"),
                              B("1,000", callback_data=f"mcc:mp:{gid}:1000")],
                            [B("❌ Cancel", callback_data=f"mcc:g:{gid}")]]))
        elif act == "r":
            g = await asyncio.to_thread(M.col(GROUPS).find_one, {"chat_id": gid})
            if g is None:
                await q.answer("This group is no longer in the list.", show_alert=True)
                return
            await q.answer()
            await _edit(q, "♻️ <b>RESET TO DEFAULT</b>\n\nSwitch the selected group back to its normal message count?\n\n"
                           f"Normal Count: {normal_count(g):,}\nCustom Count: {int(g.get('custom_total', 0)):,}\n\n"
                           "Your saved custom count will not be deleted.",
                        KB([[B("✅ Confirm Reset", callback_data=f"mcc:ry:{gid}")],
                            [B("❌ Cancel", callback_data=f"mcc:g:{gid}")]]))
        elif act == "ry":
            ok = await asyncio.to_thread(_cc_reset_sync, gid, _utcnow())
            if not ok:
                await q.answer("This group is no longer in the list.", show_alert=True)
                return
            _off_until.pop(gid, None)
            await q.answer("Custom Mode is now OFF.")
            await _edit(q, *await asyncio.to_thread(_cc_dash_view, gid, "✅ <b>Switched back to the normal count.</b>\n\n"))
        elif act == "h":
            await q.answer()
            await _edit(q, _CC_HELP, KB([[B("🔙 Back to Dashboard", callback_data=f"mcc:g:{gid}")]]))
        else:
            await q.answer("This button is no longer valid.", show_alert=True)
    except PyMongoError:
        log.exception("msgcount: database error in custom-count callback %r", q.data)
        try:
            await q.answer(NO_DB, show_alert=True)
        except TelegramError:
            pass
    except TelegramError as e:
        log.warning("msgcount: Telegram error in custom-count callback %r: %s", q.data, e)
    except Exception:
        log.exception("msgcount: custom-count callback %r failed", q.data)
        try:
            await q.answer("Something went wrong. Please try again.", show_alert=True)
        except TelegramError:
            pass


async def cc_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """group=-28, private chats only: the number typed after ⚙️ Set Custom Count. Only the Bot Owner who tapped it, only
    for the group they chose, only within INPUT_SECS. Ignores everything else (never stops other handlers)."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg is None or chat is None or user is None or chat.type != "private" or not _cc_pending:
        return
    pend = _cc_pending.get(user.id)
    if pend is None:
        return
    gid, exp, mode = pend
    if exp <= time.monotonic():
        _cc_pending.pop(user.id, None)
        return
    if not _cc_is_owner(user.id):               # never trust a stored pending state on its own
        _cc_pending.pop(user.id, None)
        return
    text = (msg.text or "").strip()
    if mode == "interval":
        if not re.fullmatch(r"[0-9]{1,7}", text) or not (MIN_INTERVAL <= int(text) <= MAX_INTERVAL):
            await msg.reply_text(f"❌ Please send a whole number from {MIN_INTERVAL:,} to {MAX_INTERVAL:,}, or tap Cancel. Nothing was changed.")
            raise ApplicationHandlerStop
        value = int(text)
        try:
            exists = await asyncio.to_thread(M.col(GROUPS).find_one, {"chat_id": gid})
            g2 = await asyncio.to_thread(_save_interval_sync, gid, value, _utcnow()) if exists is not None else None
        except PyMongoError:
            log.exception("msgcount: saving the milestone failed for %s", gid)
            await msg.reply_text(NO_DB + " Nothing was changed.")
            raise ApplicationHandlerStop
        _cc_pending.pop(user.id, None)
        if g2 is None:
            await msg.reply_text("⚠️ That group is no longer in the list. Nothing was changed.")
            raise ApplicationHandlerStop
        nxt = next_milestone(int(g2.get("last_milestone", 0)), int(g2.get("initial", DEFAULT_INITIAL)), value)
        _, kb = await asyncio.to_thread(_cc_dash_view, gid)
        await msg.reply_html(f"✅ <b>MILESTONE SAVED</b>\n\nEvery {value:,} messages.\nNext milestone: {nxt:,}.", reply_markup=kb)
        raise ApplicationHandlerStop
    if not re.fullmatch(r"[0-9]{1,10}", text) or int(text) > MAX_CUSTOM:
        await msg.reply_text(f"❌ Please send a whole number from 0 to {MAX_CUSTOM:,}, or tap Cancel. Nothing was changed.")
        raise ApplicationHandlerStop
    value = int(text)
    try:
        ok = await asyncio.to_thread(_cc_set_sync, gid, value, _utcnow())
    except PyMongoError:
        log.exception("msgcount: saving the custom count failed for %s", gid)
        await msg.reply_text(NO_DB + " Nothing was changed.")      # no success message without a successful write
        raise ApplicationHandlerStop
    _cc_pending.pop(user.id, None)
    if not ok:
        await msg.reply_text("⚠️ That group is no longer in the list. Nothing was changed.")
        raise ApplicationHandlerStop
    _off_until.pop(gid, None)
    g = await asyncio.to_thread(M.col(GROUPS).find_one, {"chat_id": gid}) or {}
    text_out, kb = await asyncio.to_thread(_cc_dash_view, gid)
    await msg.reply_html(
        "✅ <b>CUSTOM COUNT UPDATED</b>\n\n"
        f"👥 Group: {_esc(g.get('name') or gid, 64)}\n"
        f"💬 Active Count: {active_count(g):,}\n"
        f"📊 Normal Count: {normal_count(g):,}\n"
        "🔧 Custom Mode: ON\n\n"
        "New eligible messages will automatically increment both the normal count and the active custom count.",
        reply_markup=kb)
    raise ApplicationHandlerStop


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


def register(app, owner_ids=None, groups_source=None):
    """Commands, button handler and the counter. Call once, after the database is connected.
    owner_ids: the bot's OWNER_IDS (the only people who may use the private custom-count dashboard).
    groups_source: async callable(bot) returning [(chat_id, title, link)] of the groups the bot is in now."""
    global _OWNERS, _GROUPS_SOURCE
    _OWNERS = frozenset(int(i) for i in (owner_ids or ()))
    _GROUPS_SOURCE = groups_source
    if id(app) in _registered:
        log.warning("msgcount.register called twice; ignoring the second call.")
        return
    _registered.add(id(app))
    ensure_indexes()
    app.add_handler(CommandHandler(["rank", "top", "overall"], rank_cmd))
    app.add_handler(CommandHandler("count", count_cmd))
    app.add_handler(CommandHandler("today", today_cmd))
    app.add_handler(CommandHandler("week", week_cmd))
    app.add_handler(CommandHandler("me", me_cmd))
    app.add_handler(CommandHandler("radmin", radmin_cmd))
    app.add_handler(CommandHandler("resetrank", resetrank_cmd))
    app.add_handler(CallbackQueryHandler(mc_callback, pattern=r"^mc:"))
    app.add_handler(CommandHandler("deleted", deleted_cmd))
    app.add_handler(CommandHandler("inactive", inactive_cmd))
    app.add_handler(CallbackQueryHandler(del_callback, pattern=r"^mcd:"))
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND, del_input), group=-27)
    app.add_handler(CallbackQueryHandler(cc_callback, pattern=r"^mcc:"))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.TEXT & ~filters.COMMAND, cc_input), group=-28)
    # own handler groups (nova.py uses -30..-1 and 0..5, 40, 41): none of them ever stops an update
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND, pending_input), group=-29)
    app.add_handler(MessageHandler(filters.ChatType.GROUPS & filters.UpdateType.MESSAGE & ~filters.StatusUpdate.ALL,
                                   count_message), group=60)
    app.add_handler(MessageHandler(filters.StatusUpdate.MIGRATE, on_migrate), group=42)
