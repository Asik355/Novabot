"""
Import / Export of a group's settings: /export, /import, /reset and the Import / Export buttons on /help page 2.

  /export [modules]   any admin: sends a JSON file with the group's configuration.
  /import [modules]   group CREATOR only: reply to an exported file; imports everything in it (or only the listed modules).
  /reset              group CREATOR only: removes the saved configuration of this group (asks to confirm first).

Only configuration is moved: it never exports or touches members' data (warnings, approvals, message counts, ranks).
The file is plain JSON, so settings you don't want can be deleted from it before importing.

Wired up from nova.py with one line:   importexport.register(app, SimpleNamespace(is_admin=..., is_bot_owner=...))
"""
import asyncio
import html
import io
import json
import logging
import time

from telegram import InlineKeyboardButton, InlineKeyboardMarkup
from telegram.constants import ChatMemberStatus
from telegram.error import TelegramError
from telegram.ext import CallbackQueryHandler, CommandHandler, ContextTypes

import extra
import migrate_to_mongo as store

log = logging.getLogger("importexport")
D = None  # helpers handed in by nova.py

FORMAT = "bot-chat-settings"
VERSION = 1
MAX_FILE_BYTES = 1_000_000
MAX_ITEMS = 1000            # notes / filters / blocklist words accepted from one file
MAX_VALUE_CHARS = 8000
COOLDOWN_SECS = 20          # "heavily rate limited": one import/export per group every 20 seconds
ANON_ADMIN_ID = 1087968824  # Telegram's "Group" anonymous-admin account

# module -> the per-group setting keys it owns (exact names; "prefixes" cover families such as lock_<type>)
MODULES = {
    "admin": {"keys": ("auto_approve",)},
    "antiflood": {"keys": ("flood_limit", "flood_secs", "flood_mode", "repeat_limit", "mention_limit",
                           "antispam", "spam_mode")},
    "blocklists": {"keys": ("blocklist_mode", "block_ads", "block_promo", "block_promo_auth", "block_punish",
                            "block_punish_secs", "bl_notice_secs", "nsfw_word", "nsfw_content", "nsfw_action",
                            "nsfw_secs", "nsfw_allow"),
                   "blocklist": True, "allowlist": True},
    "clean_command": {"keys": ()},
    "clean_service": {"keys": ()},
    "disabled": {"keys": ("disabled_cmds", "disable_del", "disable_admin")},
    "federations": {"keys": ()},
    "filters": {"keys": (), "filters": True},
    "greetings": {"keys": ("welcome", "welcome_on", "goodbye", "goodbye_on", "clean_welcome", "join_dm",
                           "join_dm_text", "join_delay", "captcha", "captcha_mode", "captcha_time",
                           "captcha_action")},
    "locks": {"keys": ("lock", "lockwarns"), "prefixes": ("lock_",)},
    "notes": {"keys": (), "notes": True},
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


def register(app, deps):
    """deps needs: is_admin(chat, user_id) (async) and is_bot_owner(user_id)."""
    global D
    D = deps
    app.add_handler(CommandHandler("export", export_cmd))
    app.add_handler(CommandHandler("import", import_cmd))
    app.add_handler(CommandHandler("reset", reset_cmd))
    app.add_handler(CallbackQueryHandler(ie_callback, pattern=r"^ie:"))
