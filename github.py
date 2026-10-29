"""Git manager: every GitHub feature of the bot lives here (commands all start with /git).

How it is wired: extra.register_blocking() calls register_git_handlers(app, deps) once at start-up, so nova.py is not touched.
Who may use it: everybody, ON THEIR OWN ACCOUNT ONLY. Each person connects their own token in a private chat (/gittoken);
it is stored encrypted (Fernet, key in the GIT_TOKEN_KEY environment variable) and is only ever used for that person.
The bot owners (OWNER_IDS) may also use the GITHUB_TOKEN environment variable; nobody else ever gets it.
All repo/file/ZIP commands work in private chat only, so tokens and file contents never show up in a group.
Environment: GIT_TOKEN_KEY (needed to save tokens), GITHUB_TOKEN (optional, owners only), GIT_UPDATE_REPO (optional, /gitupdate).
"""
from __future__ import annotations

import asyncio
import base64
import difflib
import hashlib
import html
import io
import logging
import os
import re
import secrets
import sys
import time
import urllib.parse
import zipfile
from collections import deque
from typing import Any, Optional

try:
    import requests
    _NetError = requests.RequestException
except ImportError:                      # the error is shown to the user instead of crashing the bot
    requests = None
    _NetError = OSError
try:
    from cryptography.fernet import Fernet, InvalidToken
except ImportError:
    Fernet = None
    InvalidToken = ValueError
from telegram import InlineKeyboardButton, InlineKeyboardMarkup
from telegram.error import TelegramError
from telegram.ext import CallbackQueryHandler, CommandHandler, MessageHandler, filters

try:
    from lang import lang as L
except ImportError:                      # lang.py uploaded next to this file instead of inside a lang/ folder
    import lang as L

log = logging.getLogger(__name__)

# ------------------------------------------------------------------ limits (all in one place)
API = "https://api.github.com"
API_VERSION = "2022-11-28"
TIMEOUT = (10, 30)                       # (connect, read) seconds for every GitHub call
ZIP_TIMEOUT = (10, 90)
MB = 1024 * 1024
MAX_TG_DOWNLOAD = 20 * MB                # Telegram lets a bot download files up to 20 MB
MAX_SEND = 45 * MB                       # ...and send files up to 50 MB
MAX_SINGLE = 10 * MB                     # one file through /gitput, /gitget
MAX_EDIT = 1 * MB                        # /gitedit only edits text files up to this size
MAX_TEXT_INPUT = 3500                    # pasted text for /gitedit
MAX_ZIP_FILES = 300                      # each changed file costs GitHub API calls
MAX_ZIP_UNPACKED = 40 * MB
MAX_ZIP_FILE = 10 * MB
MAX_RATIO = 200                          # compressed -> unpacked, for entries over 1 MB (zip bombs)
MAX_PATH = 300
RATE_HITS, RATE_SECS = 20, 60            # commands per person per minute
ZIP_COOLDOWN = 30                        # seconds between two ZIP jobs of one person
PENDING_SECS = 600                       # a confirm button lives this long
INPUT_SECS = 300                         # how long the bot waits for a file / text after a command
DELETE_SECS = 90                         # how long the typed repo name is accepted after /gitdelrepo
PAGE = 8
AUTO_REPOS = 10                         # a directly uploaded file is looked for in the 10 most recently updated repos
MAX_PENDING = 300

OWNER_RE = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$")
REPO_RE = re.compile(r"^[A-Za-z0-9._-]{1,100}$")
REF_RE = re.compile(r"^[A-Za-z0-9._/-]{1,100}$")
TOKEN_RE = re.compile(r"^(?:gh[pousr]_[A-Za-z0-9]{20,250}|github_pat_[A-Za-z0-9_]{20,250}|[0-9a-f]{40})$")
TOKEN_SCRUB = re.compile(r"(?:gh[pousr]_[A-Za-z0-9]{8,}|github_pat_[A-Za-z0-9_]{8,}|\b[0-9a-f]{40}\b)")
TOKEN_KEY = "git_token"                  # settings key, stored under the person's own user id (never a group)

_D: Any = None                           # deps from nova.py (get_setting, set_setting, owner_ids ...)
_registered: set = set()
_hits: dict = {}
_zip_last: dict = {}
_busy: set = set()
_ops: dict = {}                          # token -> pending confirm
_inputs: dict = {}                       # user id -> what the bot waits for next
_auto_pick: dict = {}                    # user id -> files found for a directly uploaded file (waiting for a tap)
_sel: dict = {}                          # user id -> "owner/repo" the person is working inside (/gitrepo)
SEL_MAX = 2000
GET_MAX = 10                             # files sent at once by /gitget


class GitError(Exception):
    """Carries the lang key (and values) of the message to show. Never carries a secret."""
    def __init__(self, key: str, **vals):
        super().__init__(key)
        self.key, self.vals = key, vals


# ================================================================== validation
def parse_repo(text: str) -> Optional[tuple]:
    """'owner/repo' -> (owner, repo), or None when it is not a plain, valid GitHub name."""
    parts = (text or "").strip().split("/")
    if len(parts) != 2 or not OWNER_RE.fullmatch(parts[0]) or not REPO_RE.fullmatch(parts[1]) or parts[1] in (".", "..") \
            or parts[1].lower().endswith(".git"):
        return None
    return parts[0], parts[1]


def safe_path(path: str, allow_empty: bool = False) -> Optional[str]:
    """A clean relative POSIX path inside a repo, or None: no absolute paths, drive letters, backslashes, control characters,
    '.' / '..' / empty parts, or a '.git' folder."""
    if not isinstance(path, str):
        return None
    if not path.strip():
        return "" if allow_empty else None
    if len(path) > MAX_PATH or any(ord(c) < 32 or ord(c) == 127 for c in path) or "\\" in path:
        return None
    if path.startswith(("/", "~")) or re.match(r"^[A-Za-z]:", path) or path.endswith("/"):
        return None
    parts = path.split("/")
    if any(p in ("", ".", "..") or p.lower() == ".git" or p != p.strip() for p in parts):
        return None
    return "/".join(parts)


def safe_ref(ref: str) -> Optional[str]:
    if not ref or not REF_RE.fullmatch(ref) or ".." in ref or ref.startswith(("/", "-")) or ref.endswith(("/", ".lock")) or "//" in ref:
        return None
    return ref


def scrub(text: Any, token: str = "") -> str:
    """Removes anything that looks like a token (and the token itself) from text that may be shown or logged."""
    text = str(text)
    if token:
        text = text.replace(token, "***")
    return TOKEN_SCRUB.sub("***", text)


def mask(token: str) -> str:
    return "…" + token[-4:]


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


# ================================================================== tokens: stored encrypted, bound to the person
def _fernet():
    key = os.environ.get("GIT_TOKEN_KEY", "").strip()
    if not key or Fernet is None:
        return None
    try:
        return Fernet(key.encode())
    except (ValueError, TypeError):
        return None


def encrypt_token(uid: int, token: str) -> Optional[str]:
    f = _fernet()
    return f.encrypt(f"{uid}:{token}".encode()).decode() if f else None


def decrypt_token(uid: int, blob: str) -> Optional[str]:
    """The token, only if the row was written for THIS person (a copied row never works for someone else)."""
    f = _fernet()
    if not f or not blob:
        return None
    try:
        plain = f.decrypt(blob.encode()).decode()
    except (InvalidToken, ValueError, TypeError):
        return None
    head = f"{uid}:"
    return plain[len(head):] if plain.startswith(head) else None


def _owner_ids() -> set:
    return set(getattr(_D, "owner_ids", None) or ())


def token_for(uid: int) -> tuple:
    """(token, source) for this person: their own saved one, else (owners only) the GITHUB_TOKEN variable. (None, None) if none."""
    own = decrypt_token(uid, _D.get_setting(uid, TOKEN_KEY, "") or "")
    if own:
        return own, "own"
    env = os.environ.get("GITHUB_TOKEN", "").strip()
    if env and uid in _owner_ids():
        return env, "env"
    return None, None


def save_token(uid: int, token: str) -> bool:
    blob = encrypt_token(uid, token)
    if blob is None:
        return False
    _D.set_setting(uid, TOKEN_KEY, blob)
    return True


def forget_token(uid: int) -> None:
    remove = getattr(_D, "del_setting", None)
    remove(uid, TOKEN_KEY) if remove else _D.set_setting(uid, TOKEN_KEY, "")


# ================================================================== GitHub API (synchronous: always run in a worker thread)
def _http(method: str, url: str, **kw):
    """The one place that touches the network (the tests replace it)."""
    return requests.request(method, url, **kw)


def _error_from(r, token: str) -> GitError:
    code = r.status_code
    try:
        msg = scrub((r.json() or {}).get("message", ""), token)[:160]
    except Exception:
        msg = ""
    if code == 401:
        return GitError("gt.e_401")
    if code in (403, 429):
        if r.headers.get("X-RateLimit-Remaining") == "0" or "rate limit" in msg.lower():
            try:
                mins = max(1, int((int(r.headers.get("X-RateLimit-Reset", "0")) - time.time()) // 60) + 1)
            except (TypeError, ValueError):
                mins = 60
            return GitError("gt.e_rate", mins=mins)
        return GitError("gt.e_403", msg=msg)
    if code == 404:
        return GitError("gt.e_404")
    if code == 409:
        return GitError("gt.e_409", msg=msg)
    if code == 422:
        return GitError("gt.e_422", msg=msg)
    return GitError("gt.e_http", code=code)


def _call(token: str, method: str, path: str, *, json=None, params=None, accept="application/vnd.github+json",
          stream=False, timeout=TIMEOUT):
    if requests is None:
        raise GitError("gt.no_requests")
    headers = {"Authorization": f"Bearer {token}", "Accept": accept, "X-GitHub-Api-Version": API_VERSION,
               "User-Agent": "telegram-group-bot-git-manager"}
    url = path if path.startswith("https://") else API + path
    try:
        r = _http(method, url, headers=headers, json=json, params=params, timeout=timeout, stream=stream, allow_redirects=True)
    except _NetError:
        raise GitError("gt.net")
    if r.status_code >= 400:
        raise _error_from(r, token)
    return r


def _q(path: str) -> str:
    return urllib.parse.quote(path, safe="/")


def _read_capped(r, limit: int) -> bytes:
    out, size = [], 0
    try:
        for chunk in r.iter_content(65536):
            size += len(chunk)
            if size > limit:
                raise GitError("gt.too_big", mb=limit // MB)
            out.append(chunk)
    finally:
        r.close()
    return b"".join(out)


def api_user(token: str) -> tuple:
    r = _call(token, "GET", "/user")
    return r.json().get("login", "?"), r.headers.get("X-OAuth-Scopes", "")


def api_repos(token: str, page: int) -> tuple:
    r = _call(token, "GET", "/user/repos", params={"per_page": PAGE, "page": page, "sort": "updated"})
    return r.json(), bool(getattr(r, "links", {}).get("next"))


def api_repo(token: str, o: str, n: str) -> dict:
    return _call(token, "GET", f"/repos/{o}/{n}").json()


def api_contents(token: str, o: str, n: str, path: str, ref: str = "") -> Any:
    return _call(token, "GET", f"/repos/{o}/{n}/contents/{_q(path)}", params={"ref": ref} if ref else None).json()


def api_file(token: str, o: str, n: str, path: str, ref: str = "", limit: int = MAX_SINGLE) -> tuple:
    """(meta, bytes) of one file; refuses folders and files over `limit`."""
    meta = api_contents(token, o, n, path, ref)
    if isinstance(meta, list) or meta.get("type") != "file":
        raise GitError("gt.not_file")
    if int(meta.get("size", 0)) > limit:
        raise GitError("gt.too_big", mb=limit // MB)
    r = _call(token, "GET", f"/repos/{o}/{n}/contents/{_q(path)}", params={"ref": ref} if ref else None,
              accept="application/vnd.github.raw", stream=True)
    return meta, _read_capped(r, limit)


def api_put_file(token, o, n, path, data: bytes, message: str, branch: str = "", sha: str = "") -> dict:
    body = {"message": message, "content": base64.b64encode(data).decode()}
    if branch:
        body["branch"] = branch
    if sha:
        body["sha"] = sha
    return _call(token, "PUT", f"/repos/{o}/{n}/contents/{_q(path)}", json=body).json()


def api_delete_file(token, o, n, path, sha: str, message: str, branch: str = "") -> dict:
    body = {"message": message, "sha": sha}
    if branch:
        body["branch"] = branch
    return _call(token, "DELETE", f"/repos/{o}/{n}/contents/{_q(path)}", json=body).json()


def api_create_repo(token: str, name: str, private: bool) -> dict:
    return _call(token, "POST", "/user/repos", json={"name": name, "private": private, "auto_init": True,
                                                       "description": "Created with the Telegram bot"}).json()


def api_set_private(token: str, o: str, n: str, private: bool) -> dict:
    return _call(token, "PATCH", f"/repos/{o}/{n}", json={"private": private}).json()


def api_delete_repo(token: str, o: str, n: str) -> None:
    _call(token, "DELETE", f"/repos/{o}/{n}")


def api_zip(token: str, o: str, n: str, ref: str = "") -> bytes:
    r = _call(token, "GET", f"/repos/{o}/{n}/zipball" + (f"/{_q(ref)}" if ref else ""), stream=True, timeout=ZIP_TIMEOUT)
    return _read_capped(r, MAX_SEND)


def api_tree(token: str, o: str, n: str, branch: str) -> tuple:
    """({path: blob sha}, truncated) of the branch."""
    j = _call(token, "GET", f"/repos/{o}/{n}/git/trees/{_q(branch)}", params={"recursive": "1"}).json()
    return {t["path"]: t["sha"] for t in j.get("tree", []) if t.get("type") == "blob"}, bool(j.get("truncated"))


def api_tree_sizes(token: str, o: str, n: str, branch: str) -> tuple:
    """({path: size in bytes}, truncated) of the branch."""
    j = _call(token, "GET", f"/repos/{o}/{n}/git/trees/{_q(branch)}", params={"recursive": "1"}).json()
    return {t["path"]: int(t.get("size") or 0) for t in j.get("tree", []) if t.get("type") == "blob"}, bool(j.get("truncated"))


def api_push_files(token: str, o: str, n: str, branch: str, files: dict, message: str) -> str:
    """One commit with all `files` ({path: bytes}) on top of `branch` (Git Data API). Returns the commit sha."""
    base = f"/repos/{o}/{n}/git"
    try:
        head = _call(token, "GET", f"{base}/ref/heads/{_q(branch)}").json()["object"]["sha"]
    except GitError as e:
        if e.key in ("gt.e_404", "gt.e_409"):
            raise GitError("gt.no_branch", branch=branch)
        raise
    tree_sha = _call(token, "GET", f"{base}/commits/{head}").json()["tree"]["sha"]
    entries = []
    for path, data in files.items():
        blob = _call(token, "POST", f"{base}/blobs", json={"content": base64.b64encode(data).decode(), "encoding": "base64"}).json()
        entries.append({"path": path, "mode": "100644", "type": "blob", "sha": blob["sha"]})   # never an executable file
    tree = _call(token, "POST", f"{base}/trees", json={"base_tree": tree_sha, "tree": entries}).json()["sha"]
    commit = _call(token, "POST", f"{base}/commits", json={"message": message, "tree": tree, "parents": [head]}).json()["sha"]
    _call(token, "PATCH", f"{base}/refs/heads/{_q(branch)}", json={"sha": commit, "force": False})
    return commit


# ================================================================== ZIP validation (never extracts to disk, never runs anything)
def read_zip(raw: bytes) -> tuple:
    """({path: bytes}, stripped folder name or "") from a ZIP, or GitError. The whole archive is refused if anything is unsafe."""
    if len(raw) > MAX_TG_DOWNLOAD:
        raise GitError("gt.zip_big")
    try:
        zf = zipfile.ZipFile(io.BytesIO(raw))
        infos = zf.infolist()
    except (zipfile.BadZipFile, ValueError, OSError, NotImplementedError):
        raise GitError("gt.zip_bad")
    with zf:
        files = []
        for i in infos:
            name = i.filename
            while name.startswith("./"):
                name = name[2:]
            if i.is_dir() or name.split("/")[0] == "__MACOSX" or name.rsplit("/", 1)[-1] == ".DS_Store":
                continue
            if i.flag_bits & 0x1:
                raise GitError("gt.zip_enc")
            if (i.external_attr >> 16) & 0o170000 == 0o120000:
                raise GitError("gt.zip_symlink")
            clean = safe_path(name)
            if clean is None:
                raise GitError("gt.zip_unsafe", name=html.escape(scrub(name)[:80]))
            if i.file_size > MAX_ZIP_FILE:
                raise GitError("gt.zip_file", name=html.escape(clean[:80]), mb=MAX_ZIP_FILE // MB)
            if i.file_size > MB and i.compress_size and i.file_size / i.compress_size > MAX_RATIO:
                raise GitError("gt.zip_bomb")
            files.append((i, clean))
        if not files:
            raise GitError("gt.zip_empty")
        if len(files) > MAX_ZIP_FILES:
            raise GitError("gt.zip_many", n=len(files), max=MAX_ZIP_FILES)
        if sum(i.file_size for i, _ in files) > MAX_ZIP_UNPACKED:
            raise GitError("gt.zip_unpacked", mb=MAX_ZIP_UNPACKED // MB)
        out, total = {}, 0
        for i, clean in files:                                  # the real bytes are counted again: declared sizes are not trusted
            if clean in out:
                raise GitError("gt.zip_dupe", name=html.escape(clean[:80]))
            try:
                with zf.open(i) as f:
                    data = f.read(MAX_ZIP_FILE + 1)
            except (zipfile.BadZipFile, RuntimeError, OSError, NotImplementedError, EOFError):
                raise GitError("gt.zip_bad")
            total += len(data)
            if len(data) > MAX_ZIP_FILE or total > MAX_ZIP_UNPACKED:
                raise GitError("gt.zip_unpacked", mb=MAX_ZIP_UNPACKED // MB)
            out[clean] = data
    roots = {p.split("/")[0] for p in out}
    stripped = ""
    if len(roots) == 1 and all("/" in p for p in out):          # GitHub's own ZIPs have one top folder: drop it
        stripped = roots.pop()
        out = {p.split("/", 1)[1]: d for p, d in out.items()}
        if any(safe_path(p) is None for p in out):
            raise GitError("gt.zip_unsafe", name=html.escape(stripped[:80]))
    return out, stripped


def plan_push(files: dict, remote: dict, truncated: bool) -> tuple:
    """(new, changed, unchanged) path lists. When GitHub cut the tree short, unknown files count as changed (safe)."""
    new, changed, same = [], [], []
    for path, data in sorted(files.items()):
        old = remote.get(path)
        if old is None:
            (changed if truncated else new).append(path)
        elif old == blob_sha(data):
            same.append(path)
        else:
            changed.append(path)
    return new, changed, same


def render_tree(full: str, branch: str, sizes: dict, folder: str = "", truncated: bool = False) -> str:
    """The text of the file-list document: folders first, files with their size."""
    base = folder.strip("/")
    items = {p: s for p, s in sizes.items() if not base or p.startswith(base + "/")}
    root: dict = {}
    for p, s in items.items():
        parts = (p[len(base) + 1:] if base else p).split("/")
        node = root
        for part in parts[:-1]:
            node = node.setdefault(part + "/", {})
        node[parts[-1]] = s
    lines = [f"{full} (branch {branch})" + (f" / {base}" if base else ""),
             f"{len(items)} files, {_fmt_size(sum(items.values()))}", ""]

    def walk(node: dict, indent: str) -> None:
        for k in sorted(node, key=lambda x: (not x.endswith("/"), x.lower())):
            v = node[k]
            if isinstance(v, dict):
                lines.append(f"{indent}\U0001F4C1 {k}")
                walk(v, indent + "    ")
            else:
                lines.append(f"{indent}\U0001F4C4 {k} ({_fmt_size(v)})")
    walk(root, "")
    if truncated:
        lines += ["", "(GitHub cut this list short, so some files are not shown.)"]
    return "\n".join(lines)


def diff_summary(old: str, new: str, max_lines: int = 24, max_chars: int = 1500) -> tuple:
    d = list(difflib.unified_diff(old.splitlines(), new.splitlines(), "old", "new", lineterm="", n=1))
    added = sum(1 for x in d if x.startswith("+") and not x.startswith("+++"))
    removed = sum(1 for x in d if x.startswith("-") and not x.startswith("---"))
    return added, removed, "\n".join(d[:max_lines])[:max_chars]


# ================================================================== Telegram plumbing
def _t(key: str, cid: Any = None, **vals) -> str:
    return L.t(key, cid, **vals)


def _fmt_size(n: int) -> str:
    return f"{n} B" if n < 1024 else (f"{n / 1024:.1f} KB" if n < MB else f"{n / MB:.1f} MB")


async def _say(msg, text: str, markup=None):
    return await msg.reply_html(text[:4000], reply_markup=markup, disable_web_page_preview=True)


async def _edit(q, text: str, markup=None):
    try:
        await q.edit_message_text(text[:4000], parse_mode="HTML", reply_markup=markup, disable_web_page_preview=True)
    except TelegramError:
        pass


def _show_error(e: GitError, cid: Any) -> str:
    vals = {k: (html.escape(str(v)) if k == "msg" else v) for k, v in e.vals.items()}
    return _t(e.key, cid, **vals)


def _rate_ok(uid: int) -> bool:
    now, q = time.monotonic(), _hits.setdefault(uid, deque())
    while q and now - q[0] > RATE_SECS:
        q.popleft()
    if len(q) >= RATE_HITS:
        return False
    q.append(now)
    if len(_hits) > 2000:
        for k in [k for k, v in _hits.items() if not v or now - v[-1] > RATE_SECS]:
            _hits.pop(k, None)
    return True


async def _gate(update, need_token: bool = True) -> Optional[tuple]:
    """Checks every command the same way: a person, a private chat, the rate limit, a token. (msg, uid, token) or None."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or not chat:
        return None
    if chat.type != "private":
        await _say(msg, _t("gt.private", chat.id))
        return None
    if not _rate_ok(user.id):
        await _say(msg, _t("gt.slow", chat.id))
        return None
    token, _ = token_for(user.id)
    if need_token and not token:
        await _say(msg, _t("gt.no_token", chat.id))
        return None
    return msg, user.id, token


def _guarded(fn):
    """Turns GitError into a friendly message and any other failure into a short, secret-free one."""
    async def wrapper(update, context):
        cid = update.effective_chat.id if update.effective_chat else None
        msg = update.effective_message
        try:
            await fn(update, context)
        except GitError as e:
            if msg:
                await _say(msg, _show_error(e, cid))
        except TelegramError as e:
            log.error("git: telegram error in %s: %s", fn.__name__, scrub(e))
            if msg:
                await _say(msg, _t("gt.tg_fail", cid))
        except Exception as e:
            log.error("git: %s failed: %s %s", fn.__name__, type(e).__name__, scrub(e)[:200])
            if msg:
                await _say(msg, _t("gt.unexpected", cid))
    wrapper.__name__ = fn.__name__
    return wrapper


def _run(fn, *a, **k):
    return asyncio.to_thread(fn, *a, **k)


def _new_op(uid: int, kind: str, **data) -> str:
    now = time.monotonic()
    for t in [t for t, p in _ops.items() if p["until"] < now or p["uid"] == uid]:
        _ops.pop(t, None)                                        # one open question per person
    while len(_ops) >= MAX_PENDING:
        _ops.pop(next(iter(_ops)))
    token = secrets.token_hex(4)
    _ops[token] = {"uid": uid, "kind": kind, "until": now + PENDING_SECS, **data}
    return token


def _confirm_markup(uid: int, token: str, cid: Any, yes_key: str = "gt.btn_yes") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton(_t(yes_key, cid), callback_data=f"gt:y:{uid}:{token}"),
                                  InlineKeyboardButton(_t("gt.btn_no", cid), callback_data=f"gt:n:{uid}:{token}")]])


def _wait_for(uid: int, kind: str, secs: int = INPUT_SECS, **data) -> None:
    _inputs[uid] = {"kind": kind, "until": time.monotonic() + secs, **data}
    if len(_inputs) > 2000:
        now = time.monotonic()
        for k in [k for k, v in _inputs.items() if v["until"] < now]:
            _inputs.pop(k, None)


def _args_repo(context, n: int = 1) -> Optional[tuple]:
    """(owner, repo, rest...) from context.args, or None when the repo is missing or invalid."""
    a = context.args or []
    rp = parse_repo(a[0]) if a else None
    return (*rp, *a[1:]) if rp and len(a) >= n else None


def _sel_set(uid: int, full: str) -> None:
    if uid not in _sel and len(_sel) >= SEL_MAX:
        _sel.pop(next(iter(_sel)))
    _sel[uid] = full


def _inrepo(uid: int, cid: Any) -> str:
    """'You are inside owner/repo' line for the top of a reply (empty when no repo is open)."""
    full = _sel.get(uid)
    return _t("gt.in_repo", cid, repo=html.escape(full)) + "\n\n" if full else ""


def _target(uid: int, args: list) -> Optional[tuple]:
    """(owner, repo, rest, inside) from 'owner/repo rest...' or, inside an opened repo, from the file names alone.
    A first word like src/nova.py counts as a repo only when no repo is open or its owner is the owner of the open repo."""
    sel = _sel.get(uid)
    rp = parse_repo(args[0]) if args else None
    if rp and (not sel or rp[0].lower() == sel.split("/")[0].lower()):
        return rp[0], rp[1], list(args[1:]), False
    if sel:
        o, n = sel.split("/")
        return o, n, list(args), True
    return None


async def _download_tg(bot, doc, limit: int) -> bytes:
    if (getattr(doc, "file_size", 0) or 0) > limit:
        raise GitError("gt.tg_big", mb=limit // MB)
    try:
        raw = bytes(await (await bot.get_file(doc.file_id)).download_as_bytearray())
    except TelegramError:
        raise GitError("gt.tg_dl")
    if len(raw) > limit:
        raise GitError("gt.tg_big", mb=limit // MB)
    return raw


# ================================================================== A. authentication
@_guarded
async def setgittoken_cmd(update, context):
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user:
        return
    args = context.args or []
    if chat.type != "private":
        if args:
            try:
                await msg.delete()
            except TelegramError:
                pass
            await context.bot.send_message(chat.id, _t("gt.token_public", chat.id))
        else:
            await _say(msg, _t("gt.private", chat.id))
        return
    if not _rate_ok(user.id):
        await _say(msg, _t("gt.slow", chat.id))
        return
    if not args:
        await _say(msg, _t("gt.token_help", chat.id))
        return
    raw = args[0]
    try:
        await msg.delete()                                       # the token must not stay in the chat
        gone = True
    except TelegramError:
        gone = False
    if not TOKEN_RE.fullmatch(raw):
        await context.bot.send_message(chat.id, _t("gt.token_bad", chat.id))
        return
    if _fernet() is None:
        await context.bot.send_message(chat.id, _t("gt.no_key", chat.id))
        return
    try:
        login, scopes = await _run(api_user, raw)
    except GitError as e:
        await context.bot.send_message(chat.id, _show_error(e, chat.id) if e.key != "gt.e_401" else _t("gt.token_rejected", chat.id))
        return
    if not save_token(user.id, raw):
        await context.bot.send_message(chat.id, _t("gt.no_key", chat.id))
        return
    _inputs.pop(user.id, None)
    text = _t("gt.token_ok", chat.id, login=html.escape(login), tail=mask(raw))
    await context.bot.send_message(chat.id, text + ("" if gone else _t("gt.token_delete_it", chat.id)), parse_mode="HTML")


async def _status_text(uid: int, token: str, cid: Any) -> str:
    _, source = token_for(uid)
    login, scopes = await _run(api_user, token)
    perms = html.escape(scopes) if scopes else _t("gt.scopes_fine", cid)
    return _t("gt.status_ok", cid, login=html.escape(login), tail=mask(token), source=_t("gt.src_" + source, cid), perms=perms)


@_guarded
async def gitstatus_cmd(update, context):
    g = await _gate(update, need_token=False)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    if not token:
        await _say(msg, _t("gt.status_none", cid, saving=_t("gt.saving_on" if _fernet() else "gt.saving_off", cid)))
        return
    await _say(msg, await _status_text(uid, token, cid))


@_guarded
async def removegittoken_cmd(update, context):
    g = await _gate(update, need_token=False)
    if not g:
        return
    msg, uid, _ = g
    had = bool(_D.get_setting(uid, TOKEN_KEY, ""))
    forget_token(uid)
    _sel.pop(uid, None)
    _inputs.pop(uid, None)
    for t in [t for t, p in _ops.items() if p["uid"] == uid]:
        _ops.pop(t, None)
    await _say(msg, _t("gt.removed" if had else "gt.removed_none", msg.chat.id))


# ================================================================== B. repositories
def _repo_line(r: dict) -> str:
    lock = "🔒" if r.get("private") else "🌐"
    desc = html.escape((r.get("description") or "")[:60])
    return f"{lock} <code>{html.escape(r.get('full_name', '?'))}</code> ⭐{r.get('stargazers_count', 0)}" + (f" — {desc}" if desc else "")


async def _repos_view(token: str, page: int, cid: Any, uid: int) -> tuple:
    repos, more = await _run(api_repos, token, page)
    if not repos:
        return _t("gt.repos_empty", cid), None
    text = _t("gt.repos_head", cid, page=page) + "\n\n" + "\n".join(_repo_line(r) for r in repos)
    row = []
    if page > 1:
        row.append(InlineKeyboardButton("⬅️", callback_data=f"gt:rp:{page - 1}"))
    if more:
        row.append(InlineKeyboardButton("➡️", callback_data=f"gt:rp:{page + 1}"))
    rows = ([row] if row else []) + [[InlineKeyboardButton(_t("pick.back", cid), callback_data="gt:b")]]
    return text, InlineKeyboardMarkup(rows)


@_guarded
async def gitrepos_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    page = int(context.args[0]) if context.args and context.args[0].isdigit() and 0 < int(context.args[0]) < 1000 else 1
    text, kb = await _repos_view(token, page, msg.chat.id, uid)
    await _say(msg, text, kb)


@_guarded
async def gitrepoinfo_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    args = context.args or []
    sel = _sel.get(uid)
    rp = parse_repo(args[0]) if args else (parse_repo(sel) if sel else None)
    if args and not rp:                                         # /gitinfo novabot: find the repo by its name
        hits = _pick_repos(await _run(api_all_repos, token), args[0][:100])
        if len(hits) > 1:
            await _say(msg, _t("gt.rp_many", msg.chat.id, list=_code_list(r["name"] for r in hits)))
            return
        rp = parse_repo(hits[0].get("full_name", "")) if hits else None
        if not rp:
            await _say(msg, _t("gt.rp_none", msg.chat.id, q=html.escape(args[0][:100])))
            return
    if not rp:
        await _say(msg, _t("gt.use_repoinfo", msg.chat.id))
        return
    a = rp
    r = await _run(api_repo, token, a[0], a[1])
    lic = (r.get("license") or {}).get("spdx_id") or "-"
    await _say(msg, _t("gt.repoinfo", msg.chat.id, name=html.escape(r.get("full_name", "?")),
                       vis=_t("gt.vis_private" if r.get("private") else "gt.vis_public", msg.chat.id),
                       desc=html.escape((r.get("description") or "-")[:300]), branch=html.escape(r.get("default_branch", "?")),
                       language=html.escape(str(r.get("language") or "-")), stars=r.get("stargazers_count", 0), forks=r.get("forks_count", 0),
                       issues=r.get("open_issues_count", 0), size=_fmt_size(int(r.get("size", 0)) * 1024), lic=html.escape(lic),
                       updated=html.escape(str(r.get("pushed_at") or "-")[:10]), url=html.escape(r.get("html_url", ""))))


@_guarded
async def gitrepofiles_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    tgt = _target(uid, context.args or [])
    if not tgt:                                                 # /gitls alone: pick a repo first
        await _ask_repo(msg, uid, token, "ls")
        return
    o, n, rest, inside = tgt
    path = safe_path(rest[0], allow_empty=True) if rest else ""
    if path is None:
        await _say(msg, _t("gt.bad_path", cid))
        return
    full = f"{o}/{n}"
    if not inside:
        _sel_set(uid, full)                                     # typing the repo opens it, so the buttons below work
    await _send_filelist(context.bot, cid, token, full, folder=path)


@_guarded
async def gitcreaterepo_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    a = context.args or []
    if not a or not REPO_RE.fullmatch(a[0]) or a[0] in (".", "..") or a[0].lower().endswith(".git") or (len(a) > 1 and a[1].lower() not in ("public", "private")):
        await _say(msg, _t("gt.use_createrepo", cid))
        return
    private = not (len(a) > 1 and a[1].lower() == "public")
    r = await _run(api_create_repo, token, a[0], private)
    await _say(msg, _t("gt.created", cid, name=html.escape(r.get("full_name", a[0])), url=html.escape(r.get("html_url", "")),
                       vis=_t("gt.vis_private" if private else "gt.vis_public", cid)))


@_guarded
async def gitdeleterepo_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    a = _args_repo(context)
    if not a:
        await _say(msg, _t("gt.use_deleterepo", cid))
        return
    r = await _run(api_repo, token, a[0], a[1])
    if not (r.get("permissions") or {}).get("admin"):
        await _say(msg, _t("gt.no_admin", cid))
        return
    full = f"{a[0]}/{a[1]}"
    _wait_for(uid, "delrepo", DELETE_SECS, repo=full)
    await _say(msg, _t("gt.delrepo_ask", cid, name=html.escape(full), secs=DELETE_SECS))


# ================================================================== B2. open a repo once, then work with file names only
async def _repo_files(token: str, o: str, n: str) -> tuple:
    """({path: sha}, truncated) of the default branch; an empty repo gives an empty tree."""
    info = await _run(api_repo, token, o, n)
    try:
        return await _run(api_tree, token, o, n, info.get("default_branch") or "main")
    except GitError as e:
        if e.key not in ("gt.e_404", "gt.e_409"):
            raise
        return {}, False


async def _send_filelist(bot, cid, token: str, full: str, branch: str = "", folder: str = "") -> tuple:
    """Sends the file list of a repo (or one folder) as a .txt document with download buttons. Returns (sorted paths, branch)."""
    o, n = full.split("/")
    if not branch:
        branch = (await _run(api_repo, token, o, n)).get("default_branch") or "main"
    try:
        sizes, cut = await _run(api_tree_sizes, token, o, n, branch)
    except GitError as e:
        if e.key not in ("gt.e_404", "gt.e_409"):               # an empty repo has no tree yet
            raise
        sizes, cut = {}, False
    files = sorted(sizes, key=str.lower)
    name = html.escape(full)
    if folder and folder in sizes:
        await bot.send_message(cid, _t("gt.is_file", cid, path=html.escape(folder), size=_fmt_size(sizes[folder])), parse_mode="HTML")
        return files, branch
    shown = [p for p in files if not folder or p.startswith(folder + "/")]
    if not shown:
        await bot.send_message(cid, _t("gt.ls_none", cid, repo=name, path=html.escape(folder or "/")), parse_mode="HTML")
        return files, branch
    buf = io.BytesIO(render_tree(full, branch, sizes, folder, cut).encode("utf-8"))
    buf.name = f"{n}-files.txt"
    kb = InlineKeyboardMarkup([[InlineKeyboardButton(_t("gt.btn_dlfile", cid), callback_data="gt:dl")],
                               [InlineKeyboardButton(_t("gt.btn_dlzip", cid), callback_data="gt:dz")]])
    await bot.send_document(cid, buf, filename=buf.name, caption=_t("gt.ls_cap", cid, repo=name, n=len(shown))[:1000],
                            parse_mode="HTML", reply_markup=kb)
    return files, branch


async def _enter_repo(msg, bot, uid, token, repo: dict, then: str = "") -> None:
    """Opens the repo for this person, says where they are, sends the file list, then starts the step that asked for it."""
    cid = msg.chat.id
    rp = parse_repo(repo.get("full_name", ""))
    if rp is None:
        raise GitError("gt.e_404")
    full = f"{rp[0]}/{rp[1]}"
    _inputs.pop(uid, None)
    _sel_set(uid, full)
    await _say(msg, _t("gt.in_now", cid, repo=html.escape(full)))
    if then == "zip":
        await _send_zip(bot, cid, uid, token, rp[0], rp[1])
        return
    files, _branch = await _send_filelist(bot, cid, token, full, repo.get("default_branch") or "")
    if then == "push":
        _wait_for(uid, "pushzip", repo=full, branch="", update=False)
        await _say(msg, _t("gt.push_wait", cid, repo=html.escape(full), mb=MAX_TG_DOWNLOAD // MB))
    elif then == "put":
        _wait_for(uid, "pickfile", repo=full, files=files)
        await _say(msg, _t("gt.put_ask", cid))
    elif then == "get":
        _wait_for(uid, "getfiles", repo=full)
        await _say(msg, _t("gt.get_ask", cid, max=GET_MAX))


async def _choose_sel(msg, bot, uid, token, q: str, then: str = "") -> None:
    """The person typed a repo name: open it, or ask again when there are none or several."""
    cid = msg.chat.id
    repos = await _run(api_all_repos, token)
    hits = _pick_repos(repos, q)
    if len(hits) == 1:
        await _enter_repo(msg, bot, uid, token, hits[0], then)
        return
    _wait_for(uid, "selrepo", then=then)
    if hits:
        await _say(msg, _t("gt.rp_many", cid, list=_code_list(r["name"] for r in hits)))
        return
    names = {r.get("name", "").lower(): r.get("name", "") for r in repos}
    close = [names[c] for c in difflib.get_close_matches(q.lower(), list(names), n=3, cutoff=0.5)]
    hint = _t("gt.rp_hint", cid, list=_code_list(close or names.values(), 10)) if names else ""
    await _say(msg, _t("gt.rp_none", cid, q=html.escape(q)) + hint)


async def _ask_repo(msg, uid, token, then: str = "") -> None:
    """Shows the person's repos and waits for the name of the one to open."""
    cid = msg.chat.id
    repos = await _run(api_all_repos, token)
    if not repos:
        await _say(msg, _t("gt.repos_empty", cid))
        return
    _wait_for(uid, "selrepo", then=then)
    more = _t("gt.sel_more", cid, n=len(repos) - 25) if len(repos) > 25 else ""
    await _say(msg, _t("gt.sel_ask", cid, list="\n".join(_repo_line(r) for r in repos[:25]), more=more))


@_guarded
async def gitselect_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    q = " ".join(context.args or []).strip()[:100]
    if q:
        await _choose_sel(msg, context.bot, uid, token, q)
        return
    sel = _sel.get(uid)
    if sel:
        await _say(msg, _t("gt.in_cur", msg.chat.id, repo=html.escape(sel)))
        return
    await _ask_repo(msg, uid, token)


def _panel_markup(cid) -> InlineKeyboardMarkup:
    btn = lambda key, data: InlineKeyboardButton(_t(key, cid), callback_data=data)
    return InlineKeyboardMarkup([
        [btn("gt.btn_guide", "gt:g"), btn("gt.btn_cmds", "gt:c")], [btn("gt.btn_repos", "gt:rp:1"), btn("gt.btn_status", "gt:s")],
        [btn("gt.btn_token", "gt:t"), btn("gt.btn_perms", "gt:p")], [btn("gt.btn_pick", "gt:sr")],
        [btn("gt.btn_replace", "gt:rf"), btn("gt.btn_vis", "gt:vs")], [btn("pick.back", "gt:m")]])


@_guarded
async def gitpanel_cmd(update, context):
    """/git and /github: the GitHub menu, without going through /help first."""
    g = await _gate(update, need_token=False)
    if not g:
        return
    msg, uid, _ = g
    cid = msg.chat.id
    await _say(msg, _inrepo(uid, cid) + _t("gt.panel", cid), _panel_markup(cid))


async def _pick_path(msg, token: str, o: str, n: str, text: str) -> Optional[str]:
    """A typed name -> the one file it points to in the repo (full path, file name, or name without extension).
    Tells the person when nothing or several files match, and returns None."""
    cid = msg.chat.id
    path = safe_path(text)
    if path is None:
        await _say(msg, _t("gt.bad_path", cid))
        return None
    tree, cut = await _repo_files(token, o, n)
    if path in tree:
        return path
    hits = _match_file(list(tree), text)
    if len(hits) == 1:
        return safe_path(hits[0])
    if len(hits) > 1:
        await _say(msg, _t("gt.fl_many", cid, list=_code_list(hits)))
        return None
    if cut:                                                     # GitHub cut the list short: trust the typed path
        return path
    await _say(msg, _t("gt.nofile", cid, q=html.escape(text[:100]), repo=html.escape(f"{o}/{n}")))
    return None


async def _send_files(bot, cid, token: str, o: str, n: str, names: list) -> None:
    """Sends each named file as a Telegram document (up to GET_MAX). A name can be a path, a file name, or a name without its extension."""
    full = f"{o}/{n}"
    many = len(names) > GET_MAX
    tree, cut = await _repo_files(token, o, n)
    files, bad = list(tree), []
    for name in names[:GET_MAX]:
        path = safe_path(name)
        if path is None:
            bad.append(name[:80])
            continue
        if path not in tree:
            hits = _match_file(files, name)
            if len(hits) == 1:
                path = hits[0]
            elif len(hits) > 1 or not cut:
                bad.append(name[:80])
                continue
        try:
            _meta, data = await _run(api_file, token, o, n, path)
        except GitError:
            bad.append(path[:80])
            continue
        buf = io.BytesIO(data)
        buf.name = path.rsplit("/", 1)[-1]
        await bot.send_document(cid, buf, filename=buf.name,
                                caption=_t("gt.file_cap", cid, repo=full, path=path, size=_fmt_size(len(data)))[:1000])
    if bad:
        await bot.send_message(cid, _t("gt.get_problems", cid, list=_code_list(bad)), parse_mode="HTML")
    if many:
        await bot.send_message(cid, _t("gt.get_many", cid, max=GET_MAX), parse_mode="HTML")


async def _send_zip(bot, cid, uid: int, token: str, o: str, n: str, ref: str = "") -> None:
    """The whole repo (or one branch) as a ZIP document."""
    left = _zip_wait(uid)
    if left:
        raise GitError("gt.zip_wait", secs=left)
    if uid in _busy:
        raise GitError("gt.busy")
    _busy.add(uid)
    try:
        _zip_last[uid] = time.monotonic()
        await bot.send_message(cid, _t("gt.downloading", cid), parse_mode="HTML")
        data = await _run(api_zip, token, o, n, ref)
        buf = io.BytesIO(data)
        buf.name = f"{n}{'-' + ref.replace('/', '_') if ref else ''}.zip"
        await bot.send_document(cid, buf, filename=buf.name, caption=_t("gt.zip_cap", cid, repo=f"{o}/{n}", size=_fmt_size(len(data))))
    except GitError as e:
        if e.key == "gt.too_big":
            raise GitError("gt.repo_too_big", mb=MAX_SEND // MB)
        raise
    finally:
        _busy.discard(uid)


# ================================================================== C. files
@_guarded
async def gitgetfile_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    tgt = _target(uid, context.args or [])
    if not tgt:
        await _ask_repo(msg, uid, token, "get")
        return
    o, n, names, inside = tgt
    full = f"{o}/{n}"
    if not names:
        if not inside:
            await _choose_sel(msg, context.bot, uid, token, full, "get")
            return
        await _send_filelist(context.bot, cid, token, full)
        _wait_for(uid, "getfiles", repo=full)
        await _say(msg, _t("gt.get_ask", cid, max=GET_MAX))
        return
    await _send_files(context.bot, cid, token, o, n, names)


@_guarded
async def gitdeletefile_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    tgt = _target(uid, context.args or [])
    if not tgt or not tgt[2]:
        await _say(msg, _t("gt.use_deletefile", cid))
        return
    o, n, rest, inside = tgt
    if inside:
        path = await _pick_path(msg, token, o, n, rest[0])
        if path is None:
            return
    else:
        path = safe_path(rest[0])
        if path is None:
            await _say(msg, _t("gt.bad_path", cid))
            return
    meta = await _run(api_contents, token, o, n, path)
    if isinstance(meta, list) or meta.get("type") != "file":
        raise GitError("gt.not_file")
    t = _new_op(uid, "delfile", repo=f"{o}/{n}", path=path, sha=meta["sha"])
    await _say(msg, _t("gt.delfile_ask", cid, repo=f"{o}/{n}", path=html.escape(path), size=_fmt_size(int(meta.get("size", 0)))),
               _confirm_markup(uid, t, cid, "gt.btn_delete"))


@_guarded
async def giteditfile_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    tgt = _target(uid, context.args or [])
    if not tgt or not tgt[2]:
        await _say(msg, _t("gt.use_editfile", cid))
        return
    o, n, rest, inside = tgt
    if inside:
        path = await _pick_path(msg, token, o, n, rest[0])
        if path is None:
            return
    else:
        path = safe_path(rest[0])
        if path is None:
            await _say(msg, _t("gt.bad_path", cid))
            return
    meta, data = await _run(api_file, token, o, n, path, "", MAX_EDIT)
    try:
        data.decode("utf-8")
    except UnicodeDecodeError:
        raise GitError("gt.not_text")
    buf = io.BytesIO(data)
    buf.name = path.rsplit("/", 1)[-1]
    await context.bot.send_document(cid, buf, filename=buf.name)
    _wait_for(uid, "edit", repo=f"{o}/{n}", path=path, sha=meta["sha"])
    await _say(msg, _t("gt.edit_ask", cid, path=html.escape(path), max=MAX_TEXT_INPUT))


@_guarded
async def gituploadfile_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    args = context.args or []
    tgt = _target(uid, args)
    if not tgt:                                                 # no repo open yet: pick one first
        if args:
            await _choose_sel(msg, context.bot, uid, token, args[0][:100], "put")
        else:
            await _ask_repo(msg, uid, token, "put")
        return
    o, n, rest, inside = tgt
    full = f"{o}/{n}"
    if not rest:
        if not inside:
            await _choose_sel(msg, context.bot, uid, token, full, "put")
            return
        files, _ = await _send_filelist(context.bot, cid, token, full)
        _wait_for(uid, "pickfile", repo=full, files=files)
        await _say(msg, _t("gt.put_ask", cid))
        return
    text = rest[0]
    if inside and not text.startswith("+"):                     # a file name: the one file it points to, else a new file
        tree, _cut = await _repo_files(token, o, n)
        hits = _match_file(list(tree), text)
        if len(hits) > 1:
            await _say(msg, _t("gt.fl_many", cid, list=_code_list(hits)))
            return
        path = safe_path(hits[0] if hits else text)
    else:
        path = safe_path(text[1:].strip() if text.startswith("+") else text)
    if path is None:
        await _say(msg, _t("gt.bad_path", cid))
        return
    _wait_for(uid, "upload", repo=full, path=path)
    await _say(msg, _t("gt.upload_ask", cid, path=html.escape(path), mb=MAX_SINGLE // MB))


# ================================================================== C2. easy replace: repo name -> file list -> file name -> upload
def api_all_repos(token: str) -> list:
    """Every repo this person can reach (up to 500), newest first."""
    out = []
    for page in range(1, 6):
        r = _call(token, "GET", "/user/repos", params={"per_page": 100, "page": page, "sort": "updated"})
        out += r.json()
        if not getattr(r, "links", {}).get("next"):
            break
    return out


def _norm(s: str) -> str:
    return re.sub(r"[^a-z0-9]", "", s.lower())


def _pick_repos(repos: list, q: str) -> list:
    """'nova' -> the repo called nova, else every repo whose name contains it. 'owner/name' must match exactly."""
    q = q.strip().strip("/")
    if "/" in q:
        return [r for r in repos if r.get("full_name", "").lower() == q.lower()][:1]
    exact = [r for r in repos if r.get("name", "").lower() == q.lower()]
    if exact:
        return exact[:1]
    qn = _norm(q)
    return [r for r in repos if qn and qn in _norm(r.get("name", ""))]


def _match_file(files: list, text: str) -> list:
    """Paths matching what the person typed: full path, file name, or the name without its extension ('nova' -> nova.py)."""
    t = text.strip().strip("/")
    base = lambda f: f.rsplit("/", 1)[-1].lower()
    for v in [t] + ([t.replace(" ", ".")] if " " in t else []):
        vl = v.lower()
        for hit in ([f for f in files if f.lower() == vl], [f for f in files if base(f) == vl],
                    [f for f in files if base(f).rsplit(".", 1)[0] == vl],
                    [f for f in files if f.lower().rsplit(".", 1)[0] == vl]):
            if hit:
                return hit
    return []


def _code_list(items, limit: int = 15) -> str:
    return "\n".join(f"<code>{html.escape(str(i)[:80])}</code>" for i in list(items)[:limit])


@_guarded
async def gitreplace_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    q = " ".join(context.args or []).strip()[:100]
    if not q:
        sel = _sel.get(uid)
        if sel:
            await _choose_sel(msg, context.bot, uid, token, sel, "put")
        else:
            await _ask_repo(msg, uid, token, "put")
        return
    await _choose_sel(msg, context.bot, uid, token, q, "put")


async def _choose_repo(msg, uid, token, q: str, kind: str = "pickrepo", target=None):
    cid = msg.chat.id
    repos = await _run(api_all_repos, token)
    hits = _pick_repos(repos, q)
    if len(hits) == 1:
        if kind == "visrepo":
            _inputs.pop(uid, None)
            await _vis_ask(msg, uid, hits[0], target)
        else:
            await _show_files(msg, uid, token, hits[0])
        return
    _wait_for(uid, kind, target=target)
    if hits:
        await _say(msg, _t("gt.rp_many", cid, list=_code_list(r["name"] for r in hits)))
        return
    names = {r.get("name", "").lower(): r.get("name", "") for r in repos}
    close = [names[c] for c in difflib.get_close_matches(q.lower(), list(names), n=3, cutoff=0.5)]
    hint = _t("gt.rp_hint", cid, list=_code_list(close or names.values(), 10)) if names else ""
    await _say(msg, _t("gt.rp_none", cid, q=html.escape(q)) + hint)


async def _show_files(msg, uid, token, repo: dict):
    cid = msg.chat.id
    full = repo.get("full_name", "")
    rp = parse_repo(full)
    if rp is None:
        raise GitError("gt.e_404")
    branch = repo.get("default_branch") or "main"
    try:
        paths, _cut = await _run(api_tree, token, rp[0], rp[1], branch)
    except GitError as e:
        if e.key not in ("gt.e_404", "gt.e_409"):                 # an empty repo has no tree yet
            raise
        paths = {}
    files = sorted(paths, key=str.lower)
    _wait_for(uid, "pickfile", repo=full, files=files)
    if not files:
        await _say(msg, _t("gt.fl_empty", cid, repo=html.escape(full)))
        return
    more = _t("gt.fl_more", cid, n=len(files) - 40) if len(files) > 40 else ""
    await _say(msg, _t("gt.fl_head", cid, repo=html.escape(full), branch=html.escape(branch), files=_code_list(files, 40), more=more))


async def _got_pickfile(msg, uid, want):
    cid = msg.chat.id
    text = (msg.text or "").strip()[:200]
    if not text:
        return
    files = want["files"]
    if text.startswith("+"):                                         # +name.py = a brand-new file
        path = safe_path(text[1:].strip())
        if path is None:
            await _say(msg, _t("gt.bad_path", cid))
            return
    else:
        hits = _match_file(files, text)
        if len(hits) > 1:
            _wait_for(uid, "pickfile", repo=want["repo"], files=files)
            await _say(msg, _t("gt.fl_many", cid, list=_code_list(hits)))
            return
        if not hits:
            _wait_for(uid, "pickfile", repo=want["repo"], files=files)
            bases = {}
            for f in files:
                bases.setdefault(f.rsplit("/", 1)[-1].lower(), []).append(f)
            close = [p for c in difflib.get_close_matches(text.lower(), list(bases), n=3, cutoff=0.5) for p in bases[c]]
            hint = _t("gt.rp_hint", cid, list=_code_list(close, 6)) if close else ""
            await _say(msg, _t("gt.fl_none", cid, q=html.escape(text)) + hint)
            return
        path = safe_path(hits[0])
        if path is None:
            await _say(msg, _t("gt.bad_path", cid))
            return
    _wait_for(uid, "upload", repo=want["repo"], path=path)             # the normal /gitput step takes over from here
    await _say(msg, _t("gt.upload_ask", cid, path=html.escape(path), mb=MAX_SINGLE // MB))


# ================================================================== C2b. send file(s) directly -> replace them where they already exist
BATCH_WAIT = 2.5                         # seconds to wait for more files (an album arrives as separate messages)
BATCH_MAX = 10
_batches: dict = {}                      # user id -> {"docs": [(name, file_id, size)], "msg": last message, "task": timer}
_bg: set = set()


def _tree_paths(token: str, repo: dict) -> list:
    rp = parse_repo(repo.get("full_name", ""))
    if rp is None:
        return []
    try:
        paths, _cut = api_tree(token, rp[0], rp[1], repo.get("default_branch") or "main")
    except GitError:
        return []                                                  # empty repo, no access ...: just no match here
    return list(paths)


def _queue_upload(msg, bot, uid) -> None:
    """A document sent with no command: collect it for a moment, so several files sent together are handled as one batch."""
    doc = msg.document
    b = _batches.setdefault(uid, {"docs": [], "msg": msg, "task": None})
    if len(b["docs"]) < BATCH_MAX:
        b["docs"].append(((doc.file_name or "").strip(), doc.file_id, getattr(doc, "file_size", 0) or 0))
    b["msg"] = msg
    if b["task"]:
        b["task"].cancel()
    b["task"] = asyncio.create_task(_flush_batch(uid, bot))
    _bg.add(b["task"])
    b["task"].add_done_callback(_bg.discard)


async def _flush_batch(uid, bot):
    try:
        await asyncio.sleep(BATCH_WAIT)
    except asyncio.CancelledError:
        return
    b = _batches.pop(uid, None)
    if not b:
        return
    msg = b["msg"]
    try:
        await _auto_replace(msg, bot, uid, b["docs"], _sel.get(uid))
    except GitError as e:
        await _say(msg, _show_error(e, msg.chat.id))
    except Exception as e:
        log.error("git: direct upload failed: %s %s", type(e).__name__, scrub(e)[:200])


async def _auto_replace(msg, bot, uid, docs, only: Optional[str] = None):
    """Looks each file name up in the person's repos. One file: replace it (a choice when it is in several places).
    Several files: ONE question for all of them, then ONE commit per repo. Silent when nothing matches."""
    token, _ = token_for(uid)
    if not token or not _rate_ok(uid):
        return
    cid = msg.chat.id
    if only:                                                   # inside a repo: look only there
        rp = parse_repo(only)
        if rp is None:
            return
        info = await _run(api_repo, token, rp[0], rp[1])
        if not (info.get("permissions") or {}).get("push"):
            raise GitError("gt.no_push")
        cands = [info]
        trees = [await _run(_tree_paths, token, info)]
    else:
        repos = await _run(api_all_repos, token)
        cands = [r for r in repos if (r.get("permissions") or {}).get("push")][:AUTO_REPOS]
        trees = await asyncio.gather(*[_run(_tree_paths, token, r) for r in cands])
    plan, skipped, several = {}, [], []
    for name, fid, size in docs:
        if not name or "/" in name or size > MAX_SINGLE:
            skipped.append(name or "?")
            continue
        low = name.lower()
        pairs = [(r["full_name"], p) for r, paths in zip(cands, trees) for p in paths]
        hits = ([h for h in pairs if h[1].rsplit("/", 1)[-1] == name] or [h for h in pairs if h[1].rsplit("/", 1)[-1].lower() == low])[:8]
        if len(docs) == 1 and len(hits) > 1:                       # a single file in several places: let the person choose
            _auto_pick[uid] = {"hits": hits, "file_id": fid, "until": time.monotonic() + PENDING_SECS}
            rows = [[InlineKeyboardButton(f"{r}: {p}"[:60], callback_data=f"gt:ap:{i}")] for i, (r, p) in enumerate(hits)]
            await _say(msg, _t("gt.ap_head", cid, name=html.escape(name)), InlineKeyboardMarkup(rows))
            return
        root = [h for h in hits if "/" not in h[1]]
        pick = hits[0] if len(hits) == 1 else (root[0] if len(root) == 1 else None)
        if pick is None:
            (several if hits else skipped).append(name)
        else:
            plan[pick] = fid                                       # the same target twice: the last file wins
    if not plan:
        if only and (skipped or several):
            await _say(msg, _inrepo(uid, cid) + _t("gt.sel_nomatch", cid, list=_code_list(skipped + several)))
        elif several:
            await _say(msg, _t("gt.mb_several", cid, list=_code_list(several)))
        return
    if len(docs) == 1:
        (repo, path), fid = next(iter(plan.items()))
        await _got_upload(msg, bot, uid, token, {"repo": repo, "path": path}, types_doc(fid))
        return
    items = [{"repo": r, "path": p, "file_id": f} for (r, p), f in plan.items()]
    t = _new_op(uid, "batch", repo=items[0]["repo"], items=items)
    lines = "\n".join(f"• <code>{html.escape(i['path'][:60])}</code> → {html.escape(i['repo'])}" for i in items)
    extra = ""
    if skipped or several:
        extra = _t("gt.sel_skip" if only else "gt.mb_skip", cid, list=_code_list(skipped + several))
    head = _inrepo(uid, cid) if only else ""
    await _say(msg, head + _t("gt.mb_head", cid, n=len(items), lines=lines) + extra, _confirm_markup(uid, t, cid, "gt.btn_overwrite_all"))


# ================================================================== C3. make a repo public / private
async def _vis_ask(msg, uid, repo: dict, target):
    """target: True = make private, False = make public, None = flip whatever it is now. Always asks before changing."""
    cid = msg.chat.id
    full = repo.get("full_name", "")
    if parse_repo(full) is None:
        raise GitError("gt.e_404")
    now_private = bool(repo.get("private"))
    want_private = (not now_private) if target is None else bool(target)
    name = html.escape(full)
    if want_private == now_private:
        await _say(msg, _t("gt.vis_same", cid, repo=name, state=_t("gt.vis_w_priv" if now_private else "gt.vis_w_pub", cid)))
        return
    t = _new_op(uid, "visibility", repo=full, private=want_private)
    await _say(msg, _t("gt.vis_ask_priv" if want_private else "gt.vis_ask_pub", cid, repo=name),
               _confirm_markup(uid, t, cid, "gt.btn_mkpriv" if want_private else "gt.btn_mkpub"))


async def _vis_cmd(update, context, target):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    args = list(context.args or [])
    if target is None and args and args[-1].lower() in ("public", "private"):
        target = args.pop().lower() == "private"
    q = " ".join(args).strip()[:100]
    if not q:
        _wait_for(uid, "visrepo", target=target)
        await _say(msg, _t("gt.rp_ask", msg.chat.id))
        return
    await _choose_repo(msg, uid, token, q, "visrepo", target)


@_guarded
async def gitvis_cmd(update, context):
    await _vis_cmd(update, context, None)


@_guarded
async def gitpublic_cmd(update, context):
    await _vis_cmd(update, context, False)


@_guarded
async def gitprivate_cmd(update, context):
    await _vis_cmd(update, context, True)


# ================================================================== D. ZIP download / push, and the owner-only update
def _zip_wait(uid: int) -> int:
    left = int(ZIP_COOLDOWN - (time.monotonic() - _zip_last.get(uid, -10 ** 9)))
    return left if left > 0 else 0


@_guarded
async def gitdownload_cmd(update, context):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    tgt = _target(uid, context.args or [])
    if not tgt:
        await _ask_repo(msg, uid, token, "zip")
        return
    o, n, rest, _inside = tgt
    ref = rest[0] if rest else ""
    if ref and safe_ref(ref) is None:
        await _say(msg, _t("gt.use_download", cid))
        return
    await _send_zip(context.bot, cid, uid, token, o, n, ref)


async def _push_preview(msg, uid: int, token: str, repo: str, branch: str, file_id: str, raw: bytes, update_mode: bool):
    """Reads and checks the ZIP, compares it with the branch, and asks for the confirmation. Nothing is written to GitHub here."""
    cid = msg.chat.id
    o, n = repo.split("/")
    files, stripped = await _run(read_zip, raw)
    info = await _run(api_repo, token, o, n)
    if not (info.get("permissions") or {}).get("push"):
        raise GitError("gt.no_push")
    branch = branch or info.get("default_branch") or "main"
    remote, truncated = await _run(api_tree, token, o, n, branch)
    new, changed, same = plan_push(files, remote, truncated)
    if not new and not changed:
        await _say(msg, _t("gt.push_same", cid))
        return
    shown = "\n".join(("➕ " if p in new else "✏️ ") + html.escape(p) for p in (new + changed)[:15])
    more = _t("gt.more_items", cid, n=len(new) + len(changed) - 15) if len(new) + len(changed) > 15 else ""
    t = _new_op(uid, "pushzip", repo=repo, branch=branch, file_id=file_id, update=update_mode)
    text = _t("gt.push_ask", cid, repo=html.escape(repo), branch=html.escape(branch), new=len(new), changed=len(changed), same=len(same),
              size=_fmt_size(sum(len(files[p]) for p in new + changed)), files=shown + more)
    if stripped:
        text += _t("gt.push_stripped", cid, name=html.escape(stripped))
    if update_mode:
        text += _t("gt.update_note", cid)
    await _say(msg, text, _confirm_markup(uid, t, cid, "gt.btn_push"))


async def _start_push(update, context, repo: Optional[str], update_mode: bool):
    g = await _gate(update)
    if not g:
        return
    msg, uid, token = g
    cid = msg.chat.id
    a = list(context.args or [])
    if repo is None:
        tgt = _target(uid, a)
        if not tgt:                                             # no repo open yet: pick one (or the one typed) first
            if a:
                await _choose_sel(msg, context.bot, uid, token, a[0][:100], "push")
            else:
                await _ask_repo(msg, uid, token, "push")
            return
        o, n, rest, _inside = tgt
        repo = f"{o}/{n}"
        branch = rest[0] if rest else ""
    else:
        branch = a[0] if update_mode and a else ""
    if branch and safe_ref(branch) is None:
        await _say(msg, _t("gt.use_pushzip", cid))
        return
    reply_doc = msg.reply_to_message.document if msg.reply_to_message else None
    if reply_doc is not None:
        await _push_from_doc(msg, context.bot, uid, token, repo, branch, reply_doc, update_mode)
        return
    _wait_for(uid, "pushzip", repo=repo, branch=branch, update=update_mode)
    await _say(msg, _t("gt.push_wait", cid, repo=html.escape(repo), mb=MAX_TG_DOWNLOAD // MB))


async def _push_from_doc(msg, bot, uid, token, repo, branch, doc, update_mode):
    left = _zip_wait(uid)
    if left:
        raise GitError("gt.zip_wait", secs=left)
    if uid in _busy:
        raise GitError("gt.busy")
    _busy.add(uid)
    try:
        _zip_last[uid] = time.monotonic()
        raw = await _download_tg(bot, doc, MAX_TG_DOWNLOAD)
        await _push_preview(msg, uid, token, repo, branch, doc.file_id, raw, update_mode)
    finally:
        _busy.discard(uid)


@_guarded
async def gitpushzip_cmd(update, context):
    await _start_push(update, context, None, False)


@_guarded
async def gitupdate_cmd(update, context):
    msg, uid = update.effective_message, update.effective_user.id if update.effective_user else 0
    if not msg:
        return
    if uid not in _owner_ids():                                   # owner IDs only: never a username, never a group admin
        await _say(msg, _t("gt.owner_only", msg.chat.id))
        return
    target = os.environ.get("GIT_UPDATE_REPO", "").strip()
    if not parse_repo(target):
        await _say(msg, _t("gt.update_unset", msg.chat.id))
        return
    await _start_push(update, context, target, True)


@_guarded
async def gitcancel_cmd(update, context):
    user, msg = update.effective_user, update.effective_message
    if not user or not msg:
        return
    had = _inputs.pop(user.id, None) is not None
    if _sel.pop(user.id, None) is not None:
        had = True
    for t in [t for t, p in _ops.items() if p["uid"] == user.id]:
        _ops.pop(t, None)
        had = True
    await _say(msg, _t("gt.cancelled" if had else "gt.nothing_to_cancel", msg.chat.id))


# ================================================================== what the bot waits for after a command
async def git_input(update, context):
    """group=109: the file / text / typed name a command asked for. Anything else is left alone."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or not chat or chat.type != "private":
        return
    want = _inputs.get(user.id)
    if not want:
        if msg.document is not None and token_for(user.id)[0]:        # files sent on their own: replace them where they already are
            _queue_upload(msg, context.bot, user.id)
        return
    if want["until"] < time.monotonic():
        _inputs.pop(user.id, None)
        return
    cid = chat.id
    try:
        token, _ = token_for(user.id)
        if not token:
            _inputs.pop(user.id, None)
            await _say(msg, _t("gt.no_token", cid))
            return
        kind = want["kind"]
        if kind == "delrepo":
            await _typed_delete(msg, user.id, token, want)
        elif kind == "edit":
            await _got_edit(msg, context.bot, user.id, token, want)
        elif kind == "upload" and msg.document is not None:
            await _got_upload(msg, context.bot, user.id, token, want)
        elif kind == "pushzip" and msg.document is not None:
            _inputs.pop(user.id, None)
            await _push_from_doc(msg, context.bot, user.id, token, want["repo"], want["branch"], msg.document, want["update"])
        elif kind in ("pickrepo", "visrepo") and msg.text:
            await _choose_repo(msg, user.id, token, msg.text.strip()[:100], kind, want.get("target"))
        elif kind == "pickfile" and msg.text:
            await _got_pickfile(msg, user.id, want)
        elif kind == "selrepo" and msg.text:
            await _choose_sel(msg, context.bot, user.id, token, msg.text.strip()[:100], want.get("then", ""))
        elif kind == "getfiles" and msg.text:
            _inputs.pop(user.id, None)
            o, n = want["repo"].split("/")
            await _send_files(context.bot, cid, token, o, n, msg.text.split())
        elif kind in ("pickrepo", "pickfile", "visrepo", "selrepo", "getfiles"):
            await _say(msg, _t("gt.send_name", cid))
        elif kind in ("upload", "pushzip"):
            await _say(msg, _t("gt.send_file", cid))
    except GitError as e:
        await _say(msg, _show_error(e, cid))
    except TelegramError as e:
        log.error("git: telegram error while reading input: %s", scrub(e))
        await _say(msg, _t("gt.tg_fail", cid))
    except Exception as e:
        log.error("git: reading input failed: %s %s", type(e).__name__, scrub(e)[:200])
        await _say(msg, _t("gt.unexpected", cid))


async def _typed_delete(msg, uid, token, want):
    cid = msg.chat.id
    if (msg.text or "").strip() != want["repo"]:
        _inputs.pop(uid, None)
        await _say(msg, _t("gt.delrepo_mismatch", cid))
        return
    _inputs.pop(uid, None)
    o, n = want["repo"].split("/")
    await _run(api_delete_repo, token, o, n)
    await _say(msg, _t("gt.delrepo_done", cid, name=html.escape(want["repo"])))


async def _got_edit(msg, bot, uid, token, want):
    cid = msg.chat.id
    if msg.document is not None:
        raw = await _download_tg(bot, msg.document, MAX_EDIT)
        try:
            new = raw.decode("utf-8")
        except UnicodeDecodeError:
            raise GitError("gt.not_text")
        file_id, text = msg.document.file_id, None
    elif msg.text and not msg.text.startswith("/"):
        new, file_id, text = msg.text, None, msg.text
        if len(new) > MAX_TEXT_INPUT:
            raise GitError("gt.text_long", max=MAX_TEXT_INPUT)
    else:
        return
    o, n = want["repo"].split("/")
    meta, data = await _run(api_file, token, o, n, want["path"], "", MAX_EDIT)
    if meta["sha"] != want["sha"]:
        _inputs.pop(uid, None)
        raise GitError("gt.edit_changed")
    old = data.decode("utf-8", "replace")
    if old == new:
        _inputs.pop(uid, None)
        await _say(msg, _t("gt.edit_same", cid))
        return
    added, removed, shown = diff_summary(old, new)
    _inputs.pop(uid, None)
    t = _new_op(uid, "edit", repo=want["repo"], path=want["path"], sha=want["sha"], file_id=file_id, text=text)
    await _say(msg, _t("gt.edit_preview", cid, path=html.escape(want["path"]), added=added, removed=removed) +
               f"\n\n<pre>{html.escape(shown)}</pre>", _confirm_markup(uid, t, cid, "gt.btn_save"))


async def _got_upload(msg, bot, uid, token, want, doc=None):
    cid = msg.chat.id
    doc = doc or msg.document
    raw = await _download_tg(bot, doc, MAX_SINGLE)
    o, n = want["repo"].split("/")
    sha, old_size = "", 0
    try:
        meta = await _run(api_contents, token, o, n, want["path"])
        if isinstance(meta, list) or meta.get("type") != "file":
            raise GitError("gt.not_file")
        sha, old_size = meta["sha"], int(meta.get("size", 0))
    except GitError as e:
        if e.key != "gt.e_404":
            raise
    fname = (getattr(doc, "file_name", "") or "").strip()
    if _name_mismatch(fname, want["path"]):
        await _ask_mismatch(msg, uid, want, doc, fname, len(raw))
        return
    _inputs.pop(uid, None)
    t = _new_op(uid, "upload", repo=want["repo"], path=want["path"], sha=sha, file_id=doc.file_id)
    key = "gt.upload_over" if sha else "gt.upload_new"
    await _say(msg, _t(key, cid, repo=want["repo"], path=html.escape(want["path"]), old=_fmt_size(old_size), new=_fmt_size(len(raw))),
               _confirm_markup(uid, t, cid, "gt.btn_overwrite" if sha else "gt.btn_create"))


# ================================================================== wrong file name check (/gitput group.py, then the wrong file is sent)
_VERSION_TAIL = re.compile(r"[\s_\-]*(\(\d+\)|new|updated|final|fixed|copy|v\d+|\d+)$")


def _clean_stem(name: str) -> tuple:
    base = name.rsplit("/", 1)[-1].lower()
    stem, dot, ext = base.rpartition(".")
    if not dot:
        stem, ext = base, ""
    prev = None
    while prev != stem:                                           # nova (1).py, nova_new.py, nova_v2.py all count as nova.py
        prev = stem
        stem = _VERSION_TAIL.sub("", stem)
    return stem, ext


def _name_mismatch(uploaded: str, target: str) -> bool:
    """True when the file the person sent clearly is not the file they asked to replace."""
    if not uploaded:
        return False
    us, ue = _clean_stem(uploaded)
    ts, te = _clean_stem(target)
    return not (us == ts and (ue == te or not ue or not te))


async def _ask_mismatch(msg, uid, want, doc, fname: str, new_size: int):
    cid = msg.chat.id
    folder = want["path"].rsplit("/", 1)[0] + "/" if "/" in want["path"] else ""
    alt = safe_path(folder + fname)
    alt = None if alt == want["path"] else alt
    _inputs.pop(uid, None)
    t = _new_op(uid, "mismatch", repo=want["repo"], path=want["path"], alt=alt, file_id=doc.file_id)
    base = lambda p: p.rsplit("/", 1)[-1][:28]
    cb = lambda c: f"gt:mm:{uid}:{t}:{c}"
    rows = [[InlineKeyboardButton(_t("gt.mm_target", cid, name=base(want["path"])), callback_data=cb("t"))]]
    if alt:
        rows.append([InlineKeyboardButton(_t("gt.mm_alt", cid, name=base(alt)), callback_data=cb("a"))])
    rows.append([InlineKeyboardButton(_t("gt.mm_again", cid), callback_data=cb("r"))])
    rows.append([InlineKeyboardButton(_t("gt.btn_no", cid), callback_data=cb("c"))])
    await _say(msg, _t("gt.mm_head", cid, path=html.escape(want["path"]), repo=html.escape(want["repo"]),
                       name=html.escape(fname[:60]), size=_fmt_size(new_size)), InlineKeyboardMarkup(rows))


async def _mismatch_button(q, context, chat, user, parts):
    cid = chat.id
    tok, choice = (parts[2] if len(parts) > 2 else ""), (parts[3] if len(parts) > 3 else "")
    op = _ops.get(tok)
    if len(parts) < 4 or not parts[1].isdigit() or int(parts[1]) != user.id or (op and op["uid"] != user.id):
        await q.answer(_t("gt.only_asker", cid), show_alert=True)
        return
    if op is None or op["kind"] != "mismatch" or op["until"] < time.monotonic() or chat.type != "private":
        _ops.pop(tok, None)
        await q.answer()
        await _edit(q, _t("gt.expired", cid))
        return
    if choice == "c":
        _ops.pop(tok, None)
        await q.answer(_t("gt.cancelled", cid))
        await _edit(q, _t("gt.cancelled", cid))
        return
    if choice == "r":                                              # wait for the right file for the same target
        _ops.pop(tok, None)
        _wait_for(user.id, "upload", repo=op["repo"], path=op["path"])
        await q.answer()
        await _edit(q, _t("gt.upload_ask", cid, path=html.escape(op["path"]), mb=MAX_SINGLE // MB))
        return
    path = op["alt"] if choice == "a" else op["path"] if choice == "t" else None
    if not path:
        await q.answer()
        return
    token, _ = token_for(user.id)
    if not token:
        await q.answer(_t("gt.no_token", cid), show_alert=True)
        return
    if user.id in _busy:
        await q.answer(_t("gt.busy", cid), show_alert=True)
        return
    _ops.pop(tok, None)
    _busy.add(user.id)
    await q.answer()
    try:
        await _edit(q, _t("gt.working", cid))
        o, n = op["repo"].split("/")
        sha = ""
        try:
            meta = await _run(api_contents, token, o, n, path)
            if isinstance(meta, list) or meta.get("type") != "file":
                raise GitError("gt.not_file")
            sha = meta["sha"]
        except GitError as e:
            if e.key != "gt.e_404":
                raise
        up = {"kind": "upload", "uid": user.id, "repo": op["repo"], "path": path, "sha": sha, "file_id": op["file_id"]}
        await _edit(q, await _do_confirmed(q, context, up, token))
    except GitError as e:
        await _edit(q, _show_error(e, cid))
    except TelegramError as e:
        log.error("git: telegram error while saving: %s", scrub(e))
        await _edit(q, _t("gt.tg_fail", cid))
    except Exception as e:
        log.error("git: saving failed: %s %s", type(e).__name__, scrub(e)[:200])
        await _edit(q, _t("gt.unexpected", cid))
    finally:
        _busy.discard(user.id)


# ================================================================== buttons: confirm / cancel / repo pages / help pages
async def _do_confirmed(q, context, op, token):
    """Runs a confirmed operation. Files that came from Telegram are downloaded and checked AGAIN here."""
    kind, uid = op["kind"], op["uid"]
    o, n = op["repo"].split("/")
    cid = q.message.chat.id
    if kind == "delfile":
        await _run(api_delete_file, token, o, n, op["path"], op["sha"], f"Delete {op['path']} via Telegram bot")
        return _t("gt.delfile_done", cid, path=html.escape(op["path"]))
    if kind == "edit":
        if op.get("text") is not None:
            data = op["text"].encode("utf-8")
        else:
            data = await _download_tg(context.bot, types_doc(op["file_id"]), MAX_EDIT)
            try:
                data.decode("utf-8")
            except UnicodeDecodeError:
                raise GitError("gt.not_text")
        await _run(api_put_file, token, o, n, op["path"], data, f"Edit {op['path']} via Telegram bot", "", op["sha"])
        return _t("gt.saved", cid, path=html.escape(op["path"]))
    if kind == "upload":
        data = await _download_tg(context.bot, types_doc(op["file_id"]), MAX_SINGLE)
        await _run(api_put_file, token, o, n, op["path"], data, f"{'Update' if op['sha'] else 'Add'} {op['path']} via Telegram bot", "", op["sha"])
        return _t("gt.saved", cid, path=html.escape(op["path"]))
    if kind == "visibility":
        await _run(api_set_private, token, o, n, bool(op["private"]))
        return _t("gt.vis_done_priv" if op["private"] else "gt.vis_done_pub", cid, repo=html.escape(op["repo"]))
    if kind == "batch":
        by_repo: dict = {}
        for it in op["items"]:
            by_repo.setdefault(it["repo"], []).append(it)
        out = []
        for full, items in by_repo.items():
            ro, rn = full.split("/")
            info = await _run(api_repo, token, ro, rn)
            if not (info.get("permissions") or {}).get("push"):
                raise GitError("gt.no_push")
            branch = info.get("default_branch") or "main"
            files = {it["path"]: await _download_tg(context.bot, types_doc(it["file_id"]), MAX_SINGLE) for it in items}
            remote, truncated = await _run(api_tree, token, ro, rn, branch)
            new, changed, _same = plan_push(files, remote, truncated)
            send = {p: files[p] for p in new + changed}
            if not send:
                out.append(_t("gt.push_same", cid))
                continue
            sha = await _run(api_push_files, token, ro, rn, branch, send, f"Update {len(send)} file(s) via Telegram bot")
            out.append(_t("gt.push_done", cid, n=len(send), repo=html.escape(full), branch=html.escape(branch), sha=sha[:7]))
        return "\n\n".join(out)
    if kind == "pushzip":
        raw = await _download_tg(context.bot, types_doc(op["file_id"]), MAX_TG_DOWNLOAD)
        files, _ = await _run(read_zip, raw)
        info = await _run(api_repo, token, o, n)
        if not (info.get("permissions") or {}).get("push"):
            raise GitError("gt.no_push")
        remote, truncated = await _run(api_tree, token, o, n, op["branch"])
        new, changed, _same = plan_push(files, remote, truncated)
        if not new and not changed:
            return _t("gt.push_same", cid)
        send = {p: files[p] for p in new + changed}
        sha = await _run(api_push_files, token, o, n, op["branch"], send, f"Update {len(send)} file(s) via Telegram bot")
        return _t("gt.push_done", cid, n=len(send), repo=html.escape(op["repo"]), branch=html.escape(op["branch"]), sha=sha[:7]) + \
            (_t("gt.update_done_note", cid) if op.get("update") else "")
    return _t("gt.expired", cid)


class _Doc:
    def __init__(self, file_id):
        self.file_id, self.file_size = file_id, 0


def types_doc(file_id: str) -> _Doc:
    return _Doc(file_id)


async def _menu_blocked(q) -> bool:
    fn = getattr(sys.modules.get("extra"), "menu_not_owner", None)      # /help menus belong to the person who opened them
    return bool(fn and await fn(q))


def _help_markup(cid, rows):
    return InlineKeyboardMarkup(rows)


PAGES = {"g": ("gt.how", ("gt.btn_token", "gt:t")), "c": ("gt.cmds", ("gt.btn_guide", "gt:g")),      # act -> (text key, side button)
         "t": ("gt.guide", ("gt.btn_guide", "gt:g")), "p": ("gt.perms", None)}


async def git_callback(update, context):
    """gt:m home (Buttons | Commands) · gt:b buttons panel · gt:g guide · gt:c commands · gt:t token · gt:p permissions · gt:s status · gt:rp:<page> repos · gt:y|n:<user>:<token>."""
    q = update.callback_query
    chat, user = (q.message.chat if q.message else None), q.from_user
    if chat is None:
        await q.answer()
        return
    cid, parts = chat.id, (q.data or "").split(":")[1:]
    act = parts[0] if parts else ""
    if act in ("y", "n"):
        await _confirm_button(q, context, chat, user, act, parts)
        return
    if act == "mm":                                                           # wrong file name: replace anyway / use its own name / resend
        await _mismatch_button(q, context, chat, user, parts)
        return
    if act == "ap":                                                           # which of several matching files to replace
        if chat.type != "private" or not _rate_ok(user.id):
            await q.answer(_t("gt.private" if chat.type != "private" else "gt.slow", cid), show_alert=True)
            return
        pick = _auto_pick.pop(user.id, None)
        i = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else -1
        token, _ = token_for(user.id)
        if not pick or pick["until"] < time.monotonic() or not 0 <= i < len(pick["hits"]) or not token:
            await q.answer(_t("gt.ap_gone", cid), show_alert=True)
            return
        await q.answer()
        repo, path = pick["hits"][i]
        try:
            await _got_upload(q.message, context.bot, user.id, token, {"repo": repo, "path": path}, types_doc(pick["file_id"]))
        except GitError as e:
            await _say(q.message, _show_error(e, cid))
        return
    if act in ("dl", "dz"):                                                   # buttons under the file-list document
        if chat.type != "private" or not _rate_ok(user.id):
            await q.answer(_t("gt.private" if chat.type != "private" else "gt.slow", cid), show_alert=True)
            return
        token, _ = token_for(user.id)
        sel = _sel.get(user.id)
        if not token or not sel:
            await q.answer(_t("gt.no_token" if not token else "gt.sel_none", cid), show_alert=True)
            return
        await q.answer()
        o, n = sel.split("/")
        try:
            if act == "dl":
                _wait_for(user.id, "getfiles", repo=sel)
                await context.bot.send_message(cid, _t("gt.get_ask", cid, max=GET_MAX), parse_mode="HTML")
            else:
                await _send_zip(context.bot, cid, user.id, token, o, n)
        except GitError as e:
            await context.bot.send_message(cid, _show_error(e, cid), parse_mode="HTML")
        except TelegramError as e:
            log.error("git: telegram error in a file-list button: %s", scrub(e))
            await context.bot.send_message(cid, _t("gt.tg_fail", cid), parse_mode="HTML")
        return
    if await _menu_blocked(q):
        return
    btn = lambda key, data: InlineKeyboardButton(_t(key, cid), callback_data=data)
    if act == "h":                                                            # the 🐙 GitHub button on /help page 1
        act = "m"
    if act == "m":                                                            # landing: 🔘 Buttons | ⌨️ Commands
        await q.answer()
        back = "help:main"
        await _edit(q, _t("gt.home", cid), InlineKeyboardMarkup([
            [btn("gt.btn_buttons", "gt:b"), btn("gt.btn_cmds", "gt:c")], [btn("pick.back", back)]]))
    elif act == "b":                                                          # every button of the Git panel
        await q.answer()
        await _edit(q, _inrepo(user.id, cid) + _t("gt.panel", cid), _panel_markup(cid))
    elif act in PAGES:                                                        # guide, commands, token guide, permissions
        await q.answer()
        key, side = PAGES[act]
        rows = ([[btn(side[0], side[1])]] if side else []) + [[btn("pick.back", "gt:m" if act == "c" else "gt:b")]]
        await _edit(q, _t(key, cid), InlineKeyboardMarkup(rows))
    elif act in ("rf", "vs", "sr"):                                           # 🔁 easy replace / 🔒 public-private / 📂 open a repo
        if chat.type != "private" or not _rate_ok(user.id):
            await q.answer(_t("gt.private" if chat.type != "private" else "gt.slow", cid), show_alert=True)
            return
        if not token_for(user.id)[0]:
            await q.answer(_t("gt.no_token", cid), show_alert=True)
            return
        await q.answer()
        if act in ("rf", "sr"):
            try:
                await _ask_repo(q.message, user.id, token_for(user.id)[0], "put" if act == "rf" else "")
            except GitError as e:
                await _say(q.message, _show_error(e, cid))
            return
        _wait_for(user.id, "visrepo", target=None)
        await context.bot.send_message(cid, _t("gt.rp_ask", cid), parse_mode="HTML")
    elif act == "s":
        if chat.type != "private" or not _rate_ok(user.id):
            await q.answer(_t("gt.private" if chat.type != "private" else "gt.slow", cid), show_alert=True)
            return
        token, _ = token_for(user.id)
        if not token:
            await q.answer(_t("gt.no_token", cid), show_alert=True)
            return
        await q.answer()
        try:
            text = await _status_text(user.id, token, cid)
        except GitError as e:
            text = _show_error(e, cid)
        await _edit(q, text, InlineKeyboardMarkup([[btn("pick.back", "gt:b")]]))
    elif act == "rp":
        if chat.type != "private" or not _rate_ok(user.id):
            await q.answer(_t("gt.private" if chat.type != "private" else "gt.slow", cid), show_alert=True)
            return
        token, _ = token_for(user.id)
        if not token:
            await q.answer(_t("gt.no_token", cid), show_alert=True)
            return
        await q.answer()
        page = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() and 0 < int(parts[1]) < 1000 else 1
        try:
            text, kb = await _repos_view(token, page, cid, user.id)
        except GitError as e:
            text, kb = _show_error(e, cid), InlineKeyboardMarkup([[btn("pick.back", "gt:b")]])
        await _edit(q, text, kb)
    else:
        await q.answer()


async def _confirm_button(q, context, chat, user, act, parts):
    cid = chat.id
    tok = parts[2] if len(parts) > 2 else ""
    op = _ops.get(tok)
    if len(parts) < 3 or not parts[1].isdigit() or int(parts[1]) != user.id or (op and op["uid"] != user.id):
        await q.answer(_t("gt.only_asker", cid), show_alert=True)             # nobody can confirm someone else's operation
        return
    if op is None or op["until"] < time.monotonic() or chat.type != "private":
        _ops.pop(tok, None)
        await q.answer()
        await _edit(q, _t("gt.expired", cid))
        return
    if act == "n":
        _ops.pop(tok, None)
        await q.answer(_t("gt.cancelled", cid))
        await _edit(q, _t("gt.cancelled", cid))
        return
    token, _ = token_for(user.id)
    if not token:
        await q.answer(_t("gt.no_token", cid), show_alert=True)
        return
    if user.id in _busy:
        await q.answer(_t("gt.busy", cid), show_alert=True)
        return
    _ops.pop(tok, None)                                                         # one tap, one run
    _busy.add(user.id)
    await q.answer()
    try:
        await _edit(q, _t("gt.working", cid))
        await _edit(q, await _do_confirmed(q, context, op, token))
    except GitError as e:
        await _edit(q, _show_error(e, cid))
    except TelegramError as e:
        log.error("git: telegram error while confirming: %s", scrub(e))
        await _edit(q, _t("gt.tg_fail", cid))
    except Exception as e:
        log.error("git: confirmed operation failed: %s %s", type(e).__name__, scrub(e)[:200])
        await _edit(q, _t("gt.unexpected", cid))
    finally:
        _busy.discard(user.id)


# ================================================================== registration
COMMANDS = (
    (("git", "github"), gitpanel_cmd),
    (("gitrepo", "gitselect"), gitselect_cmd),
    (("gittoken", "setgittoken"), setgittoken_cmd),
    (("gitstatus",), gitstatus_cmd),
    (("gitoff", "removegittoken"), removegittoken_cmd),
    (("gitrepos",), gitrepos_cmd),
    (("gitinfo", "gitrepoinfo"), gitrepoinfo_cmd),
    (("gitls", "gitfiles", "gitfile", "gitrepofiles"), gitrepofiles_cmd),
    (("gitnew", "gitcreaterepo"), gitcreaterepo_cmd),
    (("gitdelrepo", "gitdeleterepo"), gitdeleterepo_cmd),
    (("gitget", "gitdl", "gitgetfile"), gitgetfile_cmd),
    (("gitdel", "gitdeletefile"), gitdeletefile_cmd),
    (("gitedit", "giteditfile"), giteditfile_cmd),
    (("gitreplace", "gitchange"), gitreplace_cmd),
    (("gitvis", "gitvisibility"), gitvis_cmd),
    (("gitpublic",), gitpublic_cmd),
    (("gitprivate",), gitprivate_cmd),
    (("gitput", "gituploadfile"), gituploadfile_cmd),
    (("gitzip", "gitdownload"), gitdownload_cmd),
    (("gitpush", "gitpushzip"), gitpushzip_cmd),
    (("gitupdate",), gitupdate_cmd),
    (("gitcancel",), gitcancel_cmd),
)   # (names, handler): the first name is the one shown in /help, the others are old names that still work


def register_git_handlers(app, deps) -> None:
    """Called once by extra.register_blocking(). deps needs: get_setting, set_setting, owner_ids (del_setting is optional)."""
    global _D
    if id(app) in _registered:
        log.warning("register_git_handlers called twice; ignoring the second call.")
        return
    _registered.add(id(app))
    _D = deps
    for lang_dict, texts in ((L.EN, TEXTS_EN), (L.HINGLISH, TEXTS_HI)):          # the texts live next to the code
        for k, v in texts.items():
            lang_dict.setdefault(k, v)
    icon = os.environ.get("GIT_EMOJI_ID", "").strip()                          # optional: custom-emoji id of a GitHub logo
    if icon.isdigit():                                                          # shown in message headers (buttons cannot show it)
        for d in (L.EN, L.HINGLISH):
            for k in ("gt.panel", "gt.home", "gt.cmds"):
                if isinstance(d.get(k), str):
                    d[k] = d[k].replace("<b>🐙 Git</b>", f'<b><tg-emoji emoji-id="{icon}">🐙</tg-emoji> Git</b>')
    for names, fn in COMMANDS:
        app.add_handler(CommandHandler(list(names), fn))
    app.add_handler(CallbackQueryHandler(git_callback, pattern=r"^gt:"))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & (filters.Document.ALL | (filters.TEXT & ~filters.COMMAND)), git_input),
                    group=109)
    log.info("Git manager registered (%d commands).", len(COMMANDS))


# ================================================================== texts (English + Hinglish)
# Merged into lang.py's tables at start-up. Same keys and same {placeholders} in both; never name a placeholder lang / chat_id / key.
# Texts are sent as HTML: never put a raw < or > in them.
TEXTS_EN = {
    "mo.b_gt": "🐙 GitHub",
    "gt.btn_yes": "✅ Yes",
    "gt.btn_no": "❌ Cancel",
    "gt.btn_delete": "🗑 Yes, delete",
    "gt.btn_overwrite": "⚠️ Overwrite",
    "gt.btn_create": "✅ Create",
    "gt.btn_save": "💾 Save",
    "gt.btn_push": "⬆️ Push",
    "gt.btn_token": "🔑 Get token",
    "gt.btn_perms": "🔐 Permissions",
    "gt.panel": "<b>🐙 Git</b>\n\nPut your project on GitHub and manage it from Telegram with simple commands. It works in a private chat with me, and only on YOUR GitHub account.\n\nNew here? Tap 📖 Guide: it goes step by step.\nTap ⌨️ Commands to see every command, ready to copy.\nTap 📚 My repos or 🔑 Status to check your connection.",
    "gt.guide": "<b>🔑 Connect your GitHub</b>\n\n1. On GitHub: Settings → Developer settings → Personal access tokens → Fine-grained tokens → Generate new token.\n2. Pick only the repositories you want me to touch and the permissions you need (see 🔐 Permissions).\n3. Copy the token, open a PRIVATE chat with me and send:\n<code>/gittoken YOUR_TOKEN</code>\nI delete your message and save the token encrypted. I never show it again.\n\nNever post a token in a group. If you did, revoke it on GitHub at once.\nTo disconnect: /gitoff (then also revoke the token on GitHub).",
    "gt.perms": "<b>🔐 What each command needs</b>\n\nFine-grained token:\n• Read (/gitrepos, /gitinfo, /gitls, /gitget, /gitzip): Metadata + Contents: Read\n• Write (/gitedit, /gitput, /gitpush): Contents: Read and write\n• Delete a file (/gitdel): Contents: Read and write\n• /gitnew: Administration: Read and write (account permission)\n• /gitdelrepo: Administration: Read and write\n\nClassic token: <code>repo</code> (or <code>public_repo</code> for public repos only), plus <code>delete_repo</code> for /gitdelrepo.\n\nGive a token only what you will use.",
    "gt.private": "🔒 Use this in a private chat with me. Tokens and files never go through a group.",
    "gt.slow": "⏳ Too many commands. Try again in a minute.",
    "gt.busy": "⏳ Your previous Git job is still running.",
    "gt.no_requests": "⚠️ The server is missing the \"requests\" package, so Git commands are off.",
    "gt.no_token": "🔑 Connect your GitHub first: send /gittoken in this private chat (see the 🐙 Git button in /help for the guide).",
    "gt.token_help": "<b>🔑 /gittoken</b>\n\nSend: <code>/gittoken YOUR_TOKEN</code>\nI delete your message and save the token encrypted.\nNeed a token? Open /help → page 1 → 🐙 GitHub → 🔑 Token guide.",
    "gt.token_public": "⚠️ Never post a token in a group. I deleted that message if I could. Revoke that token on GitHub now, then send /gittoken in a private chat with me.",
    "gt.token_bad": "⚠️ That does not look like a GitHub token. I deleted your message.",
    "gt.token_rejected": "⚠️ GitHub rejected that token (wrong, expired or revoked). I deleted your message.",
    "gt.no_key": "⚠️ Saving tokens is switched off on this bot (the owner has not set GIT_TOKEN_KEY). Ask the owner.",
    "gt.token_ok": "✅ Connected as <b>{login}</b> (token ending {tail}). It is saved encrypted and used only for you.",
    "gt.token_delete_it": "\n⚠️ I could not delete your message. Please delete it yourself now.",
    "gt.saving_on": "Saving tokens: on",
    "gt.saving_off": "Saving tokens: OFF (owner must set GIT_TOKEN_KEY)",
    "gt.status_none": "🔑 No GitHub token connected.\n{saving}\nSend /gittoken in this chat.",
    "gt.status_ok": "✅ <b>GitHub connected</b>\nAccount: <b>{login}</b>\nToken: {tail}\nSource: {source}\nPermissions: {perms}",
    "gt.src_own": "your saved token",
    "gt.src_env": "the bot owner's server token",
    "gt.scopes_fine": "fine-grained token (set on GitHub)",
    "gt.removed": "🗑 Your token is removed from the bot. Also revoke it on GitHub if you will not use it.",
    "gt.removed_none": "You had no saved token.",
    "gt.e_401": "🔑 GitHub says the token is invalid or expired. Send /gittoken with a new one.",
    "gt.e_403": "🚫 GitHub refused: the token lacks the permission for this. {msg}\nSee 🐙 Git → 🔐 Permissions.",
    "gt.e_404": "❓ Not found (or your token cannot see it). Check the owner/repo and path.",
    "gt.e_409": "⚠️ Conflict: {msg}\nThe file or branch changed, or the repository is empty.",
    "gt.e_422": "⚠️ GitHub rejected this: {msg}",
    "gt.e_http": "⚠️ GitHub answered with an error ({code}). Try again later.",
    "gt.e_rate": "⏳ GitHub rate limit reached. Try again in about {mins} min.",
    "gt.net": "⚠️ I cannot reach GitHub right now. Try again later.",
    "gt.tg_fail": "⚠️ Telegram refused that. Try again.",
    "gt.unexpected": "⚠️ Something went wrong. Nothing was changed. Try again later.",
    "gt.working": "⏳ Working...",
    "gt.expired": "⌛ This request expired. Start the command again.",
    "gt.cancelled": "Cancelled.",
    "gt.nothing_to_cancel": "Nothing to cancel.",
    "gt.only_asker": "Only the person who started this can answer.",
    "gt.owner_only": "Only the bot owner can use this.",
    "gt.bad_path": "⚠️ That path is not allowed. Use a normal relative path like docs/readme.md (no .., no leading /, no backslashes, no .git).",
    "gt.not_file": "⚠️ That is a folder, not a file. Use /gitls to list it.",
    "gt.not_text": "⚠️ That is not a UTF-8 text file, so it cannot be edited here.",
    "gt.too_big": "⚠️ That is bigger than the {mb} MB limit.",
    "gt.tg_big": "⚠️ That file is bigger than the {mb} MB limit.",
    "gt.tg_dl": "⚠️ I could not download that file from Telegram.",
    "gt.send_file": "Send the file as a document (or /gitcancel).",
    "gt.more_items": "\n…and {n} more",
    "gt.vis_private": "private",
    "gt.vis_public": "public",
    "gt.repos_head": "<b>📚 Your repositories</b> (page {page})",
    "gt.repos_empty": "No repositories on this page.",
    "gt.use_repoinfo": "Use: /gitinfo owner/repo",
    "gt.use_repofiles": "Use: /gitls owner/repo [path]",
    "gt.use_createrepo": "Use: /gitnew name [public]\nPrivate is the default. Letters, numbers, . _ - only.",
    "gt.use_deleterepo": "Use: /gitdelrepo owner/repo",
    "gt.use_getfile": "Use: /gitget owner/repo path",
    "gt.use_deletefile": "Use: /gitdel owner/repo path",
    "gt.use_editfile": "Use: /gitedit owner/repo path",
    "gt.use_uploadfile": "Use: /gitput owner/repo path",
    "gt.use_download": "Use: /gitzip owner/repo [branch]",
    "gt.use_pushzip": "Use: /gitpush owner/repo [branch]\nThen send the ZIP (or reply to a ZIP with the command).",
    "gt.repoinfo": "<b>{name}</b> ({vis})\n{desc}\n\nDefault branch: {branch}\nLanguage: {language}\n⭐ {stars}  🍴 {forks}  🐞 {issues}\nSize: {size}\nLicense: {lic}\nLast push: {updated}\n{url}",
    "gt.is_file": "📄 <code>{path}</code> is a file ({size}). Use /gitget to download it.",
    "gt.files_head": "<b>📂 {repo}</b> <code>{path}</code>",
    "gt.created": "✅ Created <b>{name}</b> ({vis}) with a README.\n{url}",
    "gt.no_admin": "🚫 You need admin rights on that repository to delete it.",
    "gt.delrepo_ask": "🗑 <b>Delete {name}?</b>\nThis cannot be undone.\n\nTo confirm, type the full name exactly: <code>{name}</code>\nYou have {secs} seconds. Anything else cancels.",
    "gt.delrepo_mismatch": "Cancelled: the name did not match. Nothing was deleted.",
    "gt.delrepo_done": "🗑 Deleted <b>{name}</b>.",
    "gt.file_cap": "{repo}: {path} ({size})",
    "gt.delfile_ask": "🗑 Delete <code>{path}</code> from <b>{repo}</b> ({size})?\nThis makes a commit that removes the file.",
    "gt.delfile_done": "🗑 Deleted <code>{path}</code>.",
    "gt.edit_ask": "✏️ I sent you the current file. Now send the full new text (up to {max} characters) or the edited file as a document. I show you the changes before saving. /gitcancel to stop.\n(<code>{path}</code>)",
    "gt.edit_changed": "⚠️ The file changed on GitHub since you started. Run /gitedit again.",
    "gt.edit_same": "No changes: the new text is the same as the file.",
    "gt.edit_preview": "✏️ <b>Save changes to {path}?</b>\n+{added} lines, -{removed} lines",
    "gt.text_long": "⚠️ That text is longer than {max} characters. Send the edited file as a document instead.",
    "gt.saved": "✅ Saved <code>{path}</code> to GitHub.",
    "gt.upload_ask": "📤 Send the file for <code>{path}</code> as a document (up to {mb} MB), or /gitcancel.",
    "gt.upload_new": "📤 Create <code>{path}</code> in <b>{repo}</b> ({new})?",
    "gt.upload_over": "⚠️ <code>{path}</code> already exists in <b>{repo}</b> ({old}). Overwrite it with the new file ({new})?",
    "gt.downloading": "⏳ Downloading the repository...",
    "gt.zip_cap": "📦 {repo} ({size})",
    "gt.zip_wait": "⏳ Wait {secs} more seconds before the next ZIP job.",
    "gt.repo_too_big": "⚠️ The repository ZIP is bigger than {mb} MB, which Telegram will not take. Clone it instead.",
    "gt.push_wait": "📦 Send the ZIP for <b>{repo}</b> as a document (up to {mb} MB), or /gitcancel.\nI check it first and show you what will change.",
    "gt.no_push": "🚫 Your token cannot write to that repository.",
    "gt.no_branch": "⚠️ Branch {branch} was not found, or the repository is empty. Create a first file with /gitput.",
    "gt.push_same": "✅ Nothing to push: every file in the ZIP is already identical on GitHub.",
    "gt.push_ask": "⬆️ <b>Push this ZIP to {repo}</b> (branch {branch})?\n➕ {new} new · ✏️ {changed} changed · = {same} unchanged\nSize: {size}\n\n{files}\n\nOne commit. Files not in the ZIP are NOT deleted. Nothing in the ZIP is ever run.",
    "gt.push_stripped": "\nThe top folder {name} was removed from the paths.",
    "gt.push_done": "✅ Pushed {n} file(s) to <b>{repo}</b> ({branch}) in one commit {sha}.",
    "gt.update_note": "\n\n🔄 <b>Bot update.</b> Whether Render redeploys depends on the Auto-Deploy setting of your service. I do not restart or redeploy anything myself.",
    "gt.update_done_note": "\nCheck your Render dashboard: it redeploys only if Auto-Deploy is on for this branch.",
    "gt.update_unset": "⚠️ Set GIT_UPDATE_REPO (owner/repo of the bot's repository) in the server settings first.",
    "gt.zip_bad": "⚠️ That is not a readable ZIP file.",
    "gt.zip_big": "⚠️ That ZIP is too big for Telegram's 20 MB download limit.",
    "gt.zip_empty": "⚠️ The ZIP has no files.",
    "gt.zip_enc": "⚠️ Password-protected ZIPs are not supported.",
    "gt.zip_symlink": "🚫 The ZIP contains a symbolic link, so I refused it.",
    "gt.zip_unsafe": "🚫 The ZIP has an unsafe path: <code>{name}</code>. Nothing was uploaded.",
    "gt.zip_file": "🚫 <code>{name}</code> in the ZIP is bigger than {mb} MB.",
    "gt.zip_bomb": "🚫 The ZIP looks like a zip bomb (extreme compression), so I refused it.",
    "gt.zip_many": "🚫 The ZIP has {n} files; the limit is {max}.",
    "gt.zip_unpacked": "🚫 The ZIP unpacks to more than {mb} MB.",
    "gt.zip_dupe": "🚫 The ZIP has the same path twice: <code>{name}</code>.",
    "gt.how": "<b>📖 Step by step</b>\nTap a line to copy it, paste it in a PRIVATE chat with me, and change the words.\n\n<b>1. Connect (once)</b>\nMake a token (button 🔑 Get token), then send:\n<code>/gittoken ghp_yourtoken</code>\nI delete your message and keep the token safe.\n\n<b>2. Make a new repository</b>\n<code>/gitnew mybot</code>\nIt is private. For a public one:\n<code>/gitnew mybot public</code>\n\n<b>3. Put your files on GitHub</b>\nMake a ZIP of your project folder, then send:\n<code>/gitpush yourname/mybot</code>\nThen send me the ZIP. I show what is new or changed. Tap ⬆️ Push to confirm. Nothing is deleted from GitHub.\n\n<b>4. Change one file</b>\nReplace it with a new file:\n<code>/gitput yourname/mybot bot.py</code>\nEdit its text here in Telegram:\n<code>/gitedit yourname/mybot bot.py</code>\nI always show the change first.\n\n<b>5. Look, download, delete</b>\nSee the files:\n<code>/gitls yourname/mybot</code>\nGet one file:\n<code>/gitget yourname/mybot bot.py</code>\nGet everything as a ZIP:\n<code>/gitzip yourname/mybot</code>\nDelete a file (asks first):\n<code>/gitdel yourname/mybot bot.py</code>\n\nYour GitHub name and repo names are in <code>/gitrepos</code>.\nStuck? <code>/gitcancel</code> stops whatever I was waiting for.",
    "gt.cmds": "<b>⌨️ All commands</b>\nTap a <b>blue</b> command to run it. Tap the grey example to copy it.\n\n<b>Connect</b>\n/gittoken <code>ghp_yourtoken</code> connect your GitHub\n/gitstatus who you are connected as\n/gitoff disconnect\n\n<b>Repositories</b>\n/gitvis <code>nova</code> make a repo public or private (asks first)\n/gitrepos your repos\n/gitinfo <code>yourname/mybot</code> repo details\n/gitls <code>yourname/mybot</code> list the files\n/gitls <code>yourname/mybot src</code> list a folder\n/gitnew <code>mybot</code> new private repo\n/gitnew <code>mybot public</code> new public repo\n/gitdelrepo <code>yourname/mybot</code> delete a repo (you type its name to confirm)\n\n<b>Files</b>\n/gitreplace easiest way: send the repo name, pick a file, send the new file\n📎 Or just send me one or many files at once: names already in your repos get replaced (I ask once)\n/gitget <code>yourname/mybot bot.py</code> download a file\n/gitput <code>yourname/mybot bot.py</code> upload or replace a file\n/gitedit <code>yourname/mybot bot.py</code> edit a text file\n/gitdel <code>yourname/mybot bot.py</code> delete a file (asks first)\n\n<b>ZIP</b>\n/gitzip <code>yourname/mybot</code> download everything as a ZIP\n/gitpush <code>yourname/mybot</code> upload a ZIP of files, then send the ZIP\n\n<b>Other</b>\n/gitcancel stop a step I am waiting for\n/gitupdate bot owner only: update the bot's own repo",
    "gt.btn_guide": "📖 Guide",
    "gt.btn_cmds": "⌨️ Commands",
    "gt.btn_buttons": "🔘 Buttons",
    "gt.home": "<b>🐙 Git</b>\n\nChoose how you want to use it:\n🔘 <b>Buttons</b>: tap through everything with buttons.\n⌨️ <b>Commands</b>: see every command, ready to copy.",
    "gt.btn_repos": "📚 My repos",
    "gt.btn_status": "🔑 Status",
}

TEXTS_HI = {
    "mo.b_gt": "🐙 GitHub",
    "gt.btn_yes": "✅ Haan",
    "gt.btn_no": "❌ Cancel",
    "gt.btn_delete": "🗑 Haan, delete karo",
    "gt.btn_overwrite": "⚠️ Overwrite",
    "gt.btn_create": "✅ Banao",
    "gt.btn_save": "💾 Save",
    "gt.btn_push": "⬆️ Push",
    "gt.btn_token": "🔑 Get token",
    "gt.btn_perms": "🔐 Permissions",
    "gt.panel": "<b>🐙 Git</b>\n\nApna project GitHub par rakho aur Telegram se simple commands se sambhalo. Yeh mere private chat mein chalta hai, aur sirf TUMHARE GitHub account par.\n\nNaye ho? 📖 Guide dabao: yeh step by step batata hai.\nSaari commands copy karne ke liye ⌨️ Commands dabao.\nConnection check karne ke liye 📚 My repos ya 🔑 Status dabao.",
    "gt.guide": "<b>🔑 Apna GitHub connect karo</b>\n\n1. GitHub par: Settings → Developer settings → Personal access tokens → Fine-grained tokens → Generate new token.\n2. Sirf wahi repositories chuno jinhe mujhe chhuna hai aur zaroori permissions do (🔐 Permissions dekho).\n3. Token copy karo, mere PRIVATE chat mein bhejo:\n<code>/gittoken YOUR_TOKEN</code>\nMain tumhara message delete kar deta hoon aur token encrypted save karta hoon. Dobara kabhi nahi dikhata.\n\nToken kabhi group mein mat bhejo. Bhej diya to turant GitHub par revoke karo.\nDisconnect karne ke liye: /gitoff (phir GitHub par bhi revoke karo).",
    "gt.perms": "<b>🔐 Har command ko kya chahiye</b>\n\nFine-grained token:\n• Read (/gitrepos, /gitinfo, /gitls, /gitget, /gitzip): Metadata + Contents: Read\n• Write (/gitedit, /gitput, /gitpush): Contents: Read and write\n• File delete (/gitdel): Contents: Read and write\n• /gitnew: Administration: Read and write (account permission)\n• /gitdelrepo: Administration: Read and write\n\nClassic token: <code>repo</code> (sirf public repos ke liye <code>public_repo</code>), aur /gitdelrepo ke liye <code>delete_repo</code>.\n\nToken ko sirf utna do jitna use karoge.",
    "gt.private": "🔒 Ise mere private chat mein use karo. Token aur files kabhi group se nahi guzarte.",
    "gt.slow": "⏳ Bahut zyada commands. Ek minute baad try karo.",
    "gt.busy": "⏳ Tumhara pichla Git kaam abhi chal raha hai.",
    "gt.no_requests": "⚠️ Server par \"requests\" package nahi hai, isliye Git commands band hain.",
    "gt.no_token": "🔑 Pehle apna GitHub connect karo: is private chat mein /gittoken bhejo (guide ke liye /help mein 🐙 Git button).",
    "gt.token_help": "<b>🔑 /gittoken</b>\n\nBhejo: <code>/gittoken YOUR_TOKEN</code>\nMain tumhara message delete kar deta hoon aur token encrypted save karta hoon.\nToken chahiye? /help → page 1 → 🐙 GitHub → 🔑 Token guide.",
    "gt.token_public": "⚠️ Token kabhi group mein mat bhejo. Maine wo message delete kar diya agar ho saka. Us token ko abhi GitHub par revoke karo, phir mere private chat mein /gittoken bhejo.",
    "gt.token_bad": "⚠️ Yeh GitHub token jaisa nahi lagta. Maine tumhara message delete kar diya.",
    "gt.token_rejected": "⚠️ GitHub ne yeh token reject kar diya (galat, expired ya revoked). Maine tumhara message delete kar diya.",
    "gt.no_key": "⚠️ Is bot par token save karna band hai (owner ne GIT_TOKEN_KEY set nahi kiya). Owner se kaho.",
    "gt.token_ok": "✅ <b>{login}</b> ke roop mein connect ho gaya (token ka ant {tail}). Encrypted save hai aur sirf tumhare liye use hota hai.",
    "gt.token_delete_it": "\n⚠️ Main tumhara message delete nahi kar paya. Please ab khud delete kar do.",
    "gt.saving_on": "Token save: on",
    "gt.saving_off": "Token save: BAND (owner ko GIT_TOKEN_KEY set karna hai)",
    "gt.status_none": "🔑 Koi GitHub token connect nahi hai.\n{saving}\nIs chat mein /gittoken bhejo.",
    "gt.status_ok": "✅ <b>GitHub connected</b>\nAccount: <b>{login}</b>\nToken: {tail}\nSource: {source}\nPermissions: {perms}",
    "gt.src_own": "tumhara saved token",
    "gt.src_env": "bot owner ka server token",
    "gt.scopes_fine": "fine-grained token (GitHub par set hota hai)",
    "gt.removed": "🗑 Tumhara token bot se hata diya. Agar use nahi karoge to GitHub par bhi revoke karo.",
    "gt.removed_none": "Tumhara koi saved token nahi tha.",
    "gt.e_401": "🔑 GitHub kehta hai token galat ya expired hai. Naye token ke saath /gittoken bhejo.",
    "gt.e_403": "🚫 GitHub ne mana kiya: token ke paas iski permission nahi hai. {msg}\n🐙 Git → 🔐 Permissions dekho.",
    "gt.e_404": "❓ Nahi mila (ya tumhara token ise dekh nahi sakta). owner/repo aur path check karo.",
    "gt.e_409": "⚠️ Conflict: {msg}\nFile ya branch badal gayi, ya repository khali hai.",
    "gt.e_422": "⚠️ GitHub ne yeh reject kiya: {msg}",
    "gt.e_http": "⚠️ GitHub ne error diya ({code}). Baad mein try karo.",
    "gt.e_rate": "⏳ GitHub ki rate limit poori ho gayi. Lagbhag {mins} minute baad try karo.",
    "gt.net": "⚠️ Abhi GitHub tak nahi pahunch pa raha. Baad mein try karo.",
    "gt.tg_fail": "⚠️ Telegram ne yeh mana kar diya. Dobara try karo.",
    "gt.unexpected": "⚠️ Kuch gadbad ho gayi. Kuch nahi badla. Baad mein try karo.",
    "gt.working": "⏳ Kaam chal raha hai...",
    "gt.expired": "⌛ Yeh request khatam ho gayi. Command dobara chalao.",
    "gt.cancelled": "Cancel ho gaya.",
    "gt.nothing_to_cancel": "Cancel karne ko kuch nahi.",
    "gt.only_asker": "Sirf wahi jawab de sakta hai jisne yeh shuru kiya.",
    "gt.owner_only": "Ise sirf bot owner use kar sakta hai.",
    "gt.bad_path": "⚠️ Yeh path allowed nahi hai. docs/readme.md jaisa normal relative path do (.. nahi, shuru mein / nahi, backslash nahi, .git nahi).",
    "gt.not_file": "⚠️ Yeh folder hai, file nahi. List dekhne ke liye /gitls use karo.",
    "gt.not_text": "⚠️ Yeh UTF-8 text file nahi hai, isliye yahan edit nahi ho sakti.",
    "gt.too_big": "⚠️ Yeh {mb} MB ki limit se badi hai.",
    "gt.tg_big": "⚠️ Yeh file {mb} MB ki limit se badi hai.",
    "gt.tg_dl": "⚠️ Telegram se woh file download nahi ho payi.",
    "gt.send_file": "File ko document ke roop mein bhejo (ya /gitcancel).",
    "gt.more_items": "\n…aur {n} aur",
    "gt.vis_private": "private",
    "gt.vis_public": "public",
    "gt.repos_head": "<b>📚 Tumhari repositories</b> (page {page})",
    "gt.repos_empty": "Is page par koi repository nahi.",
    "gt.use_repoinfo": "Aise: /gitinfo owner/repo",
    "gt.use_repofiles": "Aise: /gitls owner/repo [path]",
    "gt.use_createrepo": "Aise: /gitnew name [public]\nDefault private hai. Sirf letters, numbers, . _ -",
    "gt.use_deleterepo": "Aise: /gitdelrepo owner/repo",
    "gt.use_getfile": "Aise: /gitget owner/repo path",
    "gt.use_deletefile": "Aise: /gitdel owner/repo path",
    "gt.use_editfile": "Aise: /gitedit owner/repo path",
    "gt.use_uploadfile": "Aise: /gitput owner/repo path",
    "gt.use_download": "Aise: /gitzip owner/repo [branch]",
    "gt.use_pushzip": "Aise: /gitpush owner/repo [branch]\nPhir ZIP bhejo (ya ZIP par command se reply karo).",
    "gt.repoinfo": "<b>{name}</b> ({vis})\n{desc}\n\nDefault branch: {branch}\nLanguage: {language}\n⭐ {stars}  🍴 {forks}  🐞 {issues}\nSize: {size}\nLicense: {lic}\nLast push: {updated}\n{url}",
    "gt.is_file": "📄 <code>{path}</code> ek file hai ({size}). Download ke liye /gitget use karo.",
    "gt.files_head": "<b>📂 {repo}</b> <code>{path}</code>",
    "gt.created": "✅ <b>{name}</b> ({vis}) README ke saath ban gayi.\n{url}",
    "gt.no_admin": "🚫 Repository delete karne ke liye tumhare paas us par admin rights chahiye.",
    "gt.delrepo_ask": "🗑 <b>{name} delete karein?</b>\nYeh undo nahi hoga.\n\nConfirm karne ke liye poora naam bilkul waisa hi type karo: <code>{name}</code>\nTumhare paas {secs} second hain. Kuch aur likha to cancel.",
    "gt.delrepo_mismatch": "Cancel: naam match nahi hua. Kuch delete nahi hua.",
    "gt.delrepo_done": "🗑 <b>{name}</b> delete ho gayi.",
    "gt.file_cap": "{repo}: {path} ({size})",
    "gt.delfile_ask": "🗑 <b>{repo}</b> se <code>{path}</code> ({size}) delete karein?\nIsse ek commit banega jo file hata deta hai.",
    "gt.delfile_done": "🗑 <code>{path}</code> delete ho gayi.",
    "gt.edit_ask": "✏️ Maine abhi wali file bhej di. Ab poora naya text bhejo ({max} characters tak) ya edit ki hui file document ke roop mein. Save se pehle badlav dikhaunga. Rokne ke liye /gitcancel.\n(<code>{path}</code>)",
    "gt.edit_changed": "⚠️ Tumhare shuru karne ke baad file GitHub par badal gayi. /gitedit dobara chalao.",
    "gt.edit_same": "Koi badlav nahi: naya text file jaisa hi hai.",
    "gt.edit_preview": "✏️ <b>{path} mein badlav save karein?</b>\n+{added} lines, -{removed} lines",
    "gt.text_long": "⚠️ Yeh text {max} characters se lamba hai. Edit ki hui file document ke roop mein bhejo.",
    "gt.saved": "✅ <code>{path}</code> GitHub par save ho gayi.",
    "gt.upload_ask": "📤 <code>{path}</code> ke liye file document ke roop mein bhejo ({mb} MB tak), ya /gitcancel.",
    "gt.upload_new": "📤 <b>{repo}</b> mein <code>{path}</code> ({new}) banayein?",
    "gt.upload_over": "⚠️ <code>{path}</code> <b>{repo}</b> mein pehle se hai ({old}). Nayi file ({new}) se overwrite karein?",
    "gt.downloading": "⏳ Repository download ho rahi hai...",
    "gt.zip_cap": "📦 {repo} ({size})",
    "gt.zip_wait": "⏳ Agla ZIP kaam shuru karne se pehle {secs} second aur ruko.",
    "gt.repo_too_big": "⚠️ Repository ZIP {mb} MB se badi hai, Telegram ise nahi lega. Uski jagah clone karo.",
    "gt.push_wait": "📦 <b>{repo}</b> ke liye ZIP document ke roop mein bhejo ({mb} MB tak), ya /gitcancel.\nPehle main ise check karta hoon aur dikhata hoon ki kya badlega.",
    "gt.no_push": "🚫 Tumhara token us repository mein likh nahi sakta.",
    "gt.no_branch": "⚠️ Branch {branch} nahi mili, ya repository khali hai. /gitput se pehli file banao.",
    "gt.push_same": "✅ Push karne ko kuch nahi: ZIP ki har file GitHub par pehle se same hai.",
    "gt.push_ask": "⬆️ <b>Yeh ZIP {repo} mein push karein</b> (branch {branch})?\n➕ {new} nayi · ✏️ {changed} badli · = {same} same\nSize: {size}\n\n{files}\n\nEk hi commit. ZIP mein jo files nahi hain wo delete NAHI hoti. ZIP ka kuch bhi run nahi hota.",
    "gt.push_stripped": "\nTop folder {name} paths se hata diya gaya.",
    "gt.push_done": "✅ {n} file(s) <b>{repo}</b> ({branch}) mein ek commit {sha} mein push ho gayi.",
    "gt.update_note": "\n\n🔄 <b>Bot update.</b> Render redeploy karega ya nahi, wo tumhari service ki Auto-Deploy setting par depend karta hai. Main khud kuch restart ya redeploy nahi karta.",
    "gt.update_done_note": "\nRender dashboard dekho: redeploy tabhi hoga jab is branch ke liye Auto-Deploy on ho.",
    "gt.update_unset": "⚠️ Pehle server settings mein GIT_UPDATE_REPO (bot ki repository ka owner/repo) set karo.",
    "gt.zip_bad": "⚠️ Yeh padhne layak ZIP file nahi hai.",
    "gt.zip_big": "⚠️ Yeh ZIP Telegram ki 20 MB download limit se badi hai.",
    "gt.zip_empty": "⚠️ ZIP mein koi file nahi hai.",
    "gt.zip_enc": "⚠️ Password wali ZIP support nahi hai.",
    "gt.zip_symlink": "🚫 ZIP mein symbolic link hai, isliye maine mana kar diya.",
    "gt.zip_unsafe": "🚫 ZIP mein unsafe path hai: <code>{name}</code>. Kuch upload nahi hua.",
    "gt.zip_file": "🚫 ZIP mein <code>{name}</code> {mb} MB se badi hai.",
    "gt.zip_bomb": "🚫 ZIP zip bomb jaisi lagti hai (bahut zyada compression), isliye maine mana kar diya.",
    "gt.zip_many": "🚫 ZIP mein {n} files hain; limit {max} hai.",
    "gt.zip_unpacked": "🚫 ZIP khulne par {mb} MB se zyada ho jaati hai.",
    "gt.zip_dupe": "🚫 ZIP mein ek hi path do baar hai: <code>{name}</code>.",
    "gt.how": "<b>📖 Step by step</b>\nLine par tap karke copy karo, mere PRIVATE chat mein paste karo, aur shabd badlo.\n\n<b>1. Connect karo (ek baar)</b>\nToken banao (button 🔑 Get token), phir bhejo:\n<code>/gittoken ghp_yourtoken</code>\nMain tumhara message delete kar deta hoon aur token safe rakhta hoon.\n\n<b>2. Nayi repository banao</b>\n<code>/gitnew mybot</code>\nYeh private hoti hai. Public ke liye:\n<code>/gitnew mybot public</code>\n\n<b>3. Apni files GitHub par daalo</b>\nApne project folder ki ZIP banao, phir bhejo:\n<code>/gitpush yourname/mybot</code>\nPhir mujhe ZIP bhejo. Main dikhata hoon kya nayi ya badli hai. Confirm ke liye ⬆️ Push dabao. GitHub se kuch delete nahi hota.\n\n<b>4. Ek file badlo</b>\nNayi file se replace karo:\n<code>/gitput yourname/mybot bot.py</code>\nUska text yahin Telegram mein edit karo:\n<code>/gitedit yourname/mybot bot.py</code>\nMain badlav pehle hamesha dikhata hoon.\n\n<b>5. Dekho, download karo, delete karo</b>\nFiles dekho:\n<code>/gitls yourname/mybot</code>\nEk file lo:\n<code>/gitget yourname/mybot bot.py</code>\nSab kuch ZIP mein lo:\n<code>/gitzip yourname/mybot</code>\nFile delete karo (pehle poochta hoon):\n<code>/gitdel yourname/mybot bot.py</code>\n\nTumhara GitHub naam aur repo ke naam <code>/gitrepos</code> mein hain.\nAtak gaye? <code>/gitcancel</code> jo main wait kar raha tha use rok deta hai.",
    "gt.cmds": "<b>⌨️ Saari commands</b>\n<b>Neeli</b> command par tap karo to chalegi. Grey example par tap karo to copy hoga.\n\n<b>Connect</b>\n/gittoken <code>ghp_yourtoken</code> apna GitHub connect karo\n/gitstatus kis account se connected ho\n/gitoff disconnect karo\n\n<b>Repositories</b>\n/gitvis <code>nova</code> repo ko public ya private karo (pehle poochta hoon)\n/gitrepos tumhari repos\n/gitinfo <code>yourname/mybot</code> repo ki details\n/gitls <code>yourname/mybot</code> files ki list\n/gitls <code>yourname/mybot src</code> folder ki list\n/gitnew <code>mybot</code> nayi private repo\n/gitnew <code>mybot public</code> nayi public repo\n/gitdelrepo <code>yourname/mybot</code> repo delete karo (confirm ke liye uska naam type karo)\n\n<b>Files</b>\n/gitreplace sabse aasan: repo ka naam bhejo, file chuno, nayi file bhejo\n📎 Ya seedha ek ya kai files ek saath bhejo: jinke naam tumhari repo mein hain wo replace hongi (main ek baar poochta hoon)\n/gitget <code>yourname/mybot bot.py</code> file download karo\n/gitput <code>yourname/mybot bot.py</code> file upload ya replace karo\n/gitedit <code>yourname/mybot bot.py</code> text file edit karo\n/gitdel <code>yourname/mybot bot.py</code> file delete karo (pehle poochta hoon)\n\n<b>ZIP</b>\n/gitzip <code>yourname/mybot</code> sab kuch ZIP mein download karo\n/gitpush <code>yourname/mybot</code> files ki ZIP upload karo, phir ZIP bhejo\n\n<b>Aur</b>\n/gitcancel jo step main wait kar raha hoon use roko\n/gitupdate sirf bot owner: bot ki apni repo update karo",
    "gt.btn_guide": "📖 Guide",
    "gt.btn_cmds": "⌨️ Commands",
    "gt.btn_buttons": "🔘 Buttons",
    "gt.home": "<b>🐙 Git</b>\n\nChuno kaise use karna hai:\n🔘 <b>Buttons</b>: sab kuch buttons se chalao.\n⌨️ <b>Commands</b>: saari commands copy karne ke liye dekho.",
    "gt.btn_repos": "📚 My repos",
    "gt.btn_status": "🔑 Status",
}


TEXTS_EN.update({
    "gt.btn_replace": "🔁 Replace a file",
    "gt.rp_ask": "📦 Which repo? Send just its name, for example <code>nova</code>. /gitcancel to stop.",
    "gt.rp_many": "I found more than one repo. Send the exact name:\n\n{list}",
    "gt.rp_none": "❌ I could not find a repo like <code>{q}</code>. Send the name again, or /gitcancel.",
    "gt.rp_hint": "\n\nMaybe one of these:\n{list}",
    "gt.fl_empty": "📦 <b>{repo}</b> has no files yet.\n\nSend <code>+filename.py</code> to add the first file, or /gitcancel.",
    "gt.fl_head": "📦 <b>{repo}</b> (branch {branch})\n\n{files}{more}\n\n✏️ Send the name of the file you want to replace, for example <code>nova.py</code>. To add a new file send <code>+newfile.py</code>. /gitcancel to stop.",
    "gt.fl_more": "\n… and {n} more (type the name or the full path)",
    "gt.fl_many": "More than one file matches. Send the full path:\n\n{list}",
    "gt.fl_none": "❌ No file like <code>{q}</code> in this repo. Send the name again, or /gitcancel.",
    "gt.send_name": "Send the name as text (or /gitcancel).",
})
TEXTS_HI.update({
    "gt.btn_replace": "🔁 File replace karo",
    "gt.rp_ask": "📦 Kaun si repo? Bas uska naam bhejo, jaise <code>nova</code>. Rokne ke liye /gitcancel.",
    "gt.rp_many": "Ek se zyada repo mili. Poora naam bhejo:\n\n{list}",
    "gt.rp_none": "❌ <code>{q}</code> jaisi repo nahi mili. Naam dobara bhejo, ya /gitcancel.",
    "gt.rp_hint": "\n\nShayad inme se koi:\n{list}",
    "gt.fl_empty": "📦 <b>{repo}</b> mein abhi koi file nahi hai.\n\nPehli file jodne ke liye <code>+filename.py</code> bhejo, ya /gitcancel.",
    "gt.fl_head": "📦 <b>{repo}</b> (branch {branch})\n\n{files}{more}\n\n✏️ Jis file ko replace karna hai uska naam bhejo, jaise <code>nova.py</code>. Nayi file jodne ke liye <code>+newfile.py</code> bhejo. Rokne ke liye /gitcancel.",
    "gt.fl_more": "\n… aur {n} files (naam ya poora path likho)",
    "gt.fl_many": "Ek se zyada file match hui. Poora path bhejo:\n\n{list}",
    "gt.fl_none": "❌ Is repo mein <code>{q}</code> jaisi file nahi mili. Naam dobara bhejo, ya /gitcancel.",
    "gt.send_name": "Naam text mein bhejo (ya /gitcancel).",
})

TEXTS_EN.update({
    "gt.btn_vis": "🔒 Public / Private",
    "gt.btn_mkpriv": "🔒 Make private",
    "gt.btn_mkpub": "🌐 Make public",
    "gt.vis_w_priv": "private",
    "gt.vis_w_pub": "public",
    "gt.vis_same": "ℹ️ <b>{repo}</b> is already {state}.",
    "gt.vis_ask_priv": "🔒 <b>{repo}</b> is public now.\n\nMake it <b>private</b>? Only you (and people you added) will be able to see it.",
    "gt.vis_ask_pub": "🌐 <b>{repo}</b> is private now.\n\nMake it <b>public</b>? ⚠️ Everybody on the internet can then read every file and the whole history. Check that no token, password or .env file is inside.",
    "gt.vis_done_priv": "✅ <b>{repo}</b> is now 🔒 private.",
    "gt.vis_done_pub": "✅ <b>{repo}</b> is now 🌐 public.",
})
TEXTS_HI.update({
    "gt.btn_vis": "🔒 Public / Private",
    "gt.btn_mkpriv": "🔒 Private karo",
    "gt.btn_mkpub": "🌐 Public karo",
    "gt.vis_w_priv": "private",
    "gt.vis_w_pub": "public",
    "gt.vis_same": "ℹ️ <b>{repo}</b> pehle se {state} hai.",
    "gt.vis_ask_priv": "🔒 <b>{repo}</b> abhi public hai.\n\n<b>Private</b> karna hai? Sirf tum (aur jinhe tumne joda) dekh paoge.",
    "gt.vis_ask_pub": "🌐 <b>{repo}</b> abhi private hai.\n\n<b>Public</b> karna hai? ⚠️ Phir internet par har koi har file aur poori history padh sakta hai. Dekh lo ki andar koi token, password ya .env file na ho.",
    "gt.vis_done_priv": "✅ <b>{repo}</b> ab 🔒 private hai.",
    "gt.vis_done_pub": "✅ <b>{repo}</b> ab 🌐 public hai.",
})

TEXTS_EN.update({
    "gt.ap_head": "📎 <code>{name}</code> is in more than one place. Which one should I replace?",
    "gt.ap_gone": "⌛ That choice expired. Send the file again.",
})
TEXTS_HI.update({
    "gt.ap_head": "📎 <code>{name}</code> ek se zyada jagah hai. Kaun si replace karun?",
    "gt.ap_gone": "⌛ Yeh choice expire ho gaya. File dobara bhejo.",
})

TEXTS_EN.update({
    "gt.btn_overwrite_all": "⚠️ Overwrite all",
    "gt.mb_head": "📎 Replace these {n} files?\n\n{lines}",
    "gt.mb_skip": "\n\n⏭ Skipped (not found in your repos, or in several places):\n{list}",
    "gt.mb_several": "⚠️ These files exist in several repos, so I did not guess. Send each one alone and pick the repo:\n\n{list}",
})
TEXTS_HI.update({
    "gt.btn_overwrite_all": "⚠️ Sab overwrite karo",
    "gt.mb_head": "📎 Yeh {n} files replace karni hain?\n\n{lines}",
    "gt.mb_skip": "\n\n⏭ Chhod di (tumhari repos mein nahi mili, ya kai jagah hain):\n{list}",
    "gt.mb_several": "⚠️ Yeh files kai repos mein hain, isliye maine andaza nahi lagaya. Har file akeli bhejo aur repo chuno:\n\n{list}",
})

TEXTS_EN.update({
    "gt.mm_head": "⚠️ <b>Is this the right file?</b>\n\nYou asked me to replace <code>{path}</code> in <b>{repo}</b>, but the file you sent is called <code>{name}</code> ({size}).\n\nWhat do you want to do?",
    "gt.mm_target": "✅ Replace {name} with it",
    "gt.mm_alt": "📄 Save it as {name} instead",
    "gt.mm_again": "🔁 Send another file",
})
TEXTS_HI.update({
    "gt.mm_head": "⚠️ <b>Kya yeh sahi file hai?</b>\n\nTumne <b>{repo}</b> mein <code>{path}</code> replace karne ko kaha tha, par jo file bheji uska naam <code>{name}</code> hai ({size}).\n\nKya karna hai?",
    "gt.mm_target": "✅ {name} ko isse replace karo",
    "gt.mm_alt": "📄 Isse {name} naam se save karo",
    "gt.mm_again": "🔁 Doosri file bhejo",
})


# ================================================================== texts for: open a repo once, file-list document, plain-words help
TEXTS_EN.update({
    "gt.in_repo": "📂 <b>You are inside {repo}</b>",
    "gt.in_now": "📂 <b>You are now inside {repo}</b>\n\nSend a file name to work with it. Example: <code>/gitget nova.py</code>\nSend /gitls to see the files, or /gitrepo to switch to another repo.",
    "gt.in_cur": "📂 <b>You are inside {repo}</b>\n\nTo switch, send <code>/gitrepo reponame</code>. To see all your repos, send /gitrepos. To leave this repo, send /gitcancel.",
    "gt.sel_ask": "📚 <b>Your repos</b>\n\n{list}{more}\n\n✏️ Send the name of the repo you want to open, for example <code>novabot</code>. /gitcancel to stop.",
    "gt.sel_more": "\n… and {n} more. Send a name and I will find it.",
    "gt.ls_cap": "📂 <b>{repo}</b>\n{n} files. Open the document to see them all.\nUse the buttons below to download files.",
    "gt.ls_none": "📂 <b>{repo}</b>\n\nNo files found in <code>{path}</code>. Send /gitls to see everything.",
    "gt.btn_dlfile": "⬇️ Download a file",
    "gt.btn_dlzip": "📦 Download all (ZIP)",
    "gt.btn_pick": "📂 Open a repo",
    "gt.get_ask": "⬇️ Send the names of the files you want, one per line. Example:\n<code>nova.py\nextra.py</code>\n\nUp to {max} files at a time. /gitcancel to stop.",
    "gt.put_ask": "✏️ Send the name of the file you want to replace, for example <code>nova.py</code>.\nTo add a new file, send <code>+newfile.py</code>.\n/gitcancel to stop.",
    "gt.get_problems": "⚠️ I could not send these:\n{list}\n\nThe name was not found, the file is too big, or the name matches more than one file (then send the full path, like <code>src/nova.py</code>). Send /gitls to see the names.",
    "gt.get_many": "ℹ️ I sent the first {max} files. Send the rest again.",
    "gt.nofile": "❌ No file like <code>{q}</code> in <b>{repo}</b>. Send /gitls to see the file names.",
    "gt.sel_none": "📂 Open a repo first: send /gitrepo.",
    "gt.sel_nomatch": "No file in this repo has exactly the same name as:\n{list}\n\nNothing was changed. To add a new file, use /gitput.",
    "gt.sel_skip": "\n\n⏭ Skipped (no file with exactly this name in this repo, or the name is in several folders):\n{list}",
    "gt.use_repoinfo": "ℹ️ <b>Repo details</b>\nSend the command and the repo name.\nExample: <code>/gitinfo novabot</code>\nNot sure of the name? Send /gitrepos.",
    "gt.use_repofiles": "📂 <b>See the files in a repo</b>\nSend /gitls, then pick your repo.\nOr type it: <code>/gitls yourname/novabot</code>\nTo open a folder, add its name: <code>/gitls src</code>",
    "gt.use_getfile": "⬇️ <b>Download files</b>\nOpen a repo with /gitrepo, then send the command and the file name.\nExample: <code>/gitget nova.py</code>",
    "gt.use_deletefile": "🗑 <b>Delete a file</b>\nOpen a repo with /gitrepo, then send the command and the file name.\nExample: <code>/gitdel old.py</code>\nI always ask before deleting.",
    "gt.use_editfile": "✏️ <b>Edit a text file</b>\nOpen a repo with /gitrepo, then send the command and the file name.\nExample: <code>/gitedit nova.py</code>",
    "gt.use_uploadfile": "⬆️ <b>Upload or replace a file</b>\nSend /gitput, then pick your repo.\nOr type it: <code>/gitput nova.py</code>",
    "gt.use_download": "📦 <b>Download a repo as a ZIP</b>\nSend /gitzip, then pick your repo.\nOr type it: <code>/gitzip yourname/novabot</code>\nFor another branch, add its name: <code>/gitzip yourname/novabot dev</code>",
    "gt.use_pushzip": "⬆️ <b>Send a ZIP of your project to GitHub</b>\nSend /gitpush, then pick your repo, then send the ZIP.\nOr type it: <code>/gitpush yourname/novabot</code>\nFor another branch, add its name: <code>/gitpush yourname/novabot dev</code>",
    "gt.update_unset": "⚠️ /gitupdate is not set up yet. The bot owner must set GIT_UPDATE_REPO on the server.",
    "gt.how": "<b>📖 Guide</b>\n\n1️⃣ <b>Connect GitHub:</b> send <code>/gittoken yourtoken</code> (see the token guide).\n2️⃣ <b>Open a repo:</b> send /gitrepo, then the repo name. I remember it, and every reply shows 📂 where you are.\n3️⃣ <b>See the files:</b> send /gitls. You get a document with every file. The buttons under it download one file, or the whole repo as a ZIP.\n4️⃣ <b>Replace files:</b> just send me one or many files. A file with exactly the same name in the repo replaces the old one. I show a list and ask once.\n5️⃣ <b>More jobs inside the repo:</b> <code>/gitget nova.py</code> download, <code>/gitput nova.py</code> upload, <code>/gitedit nova.py</code> edit, <code>/gitdel nova.py</code> delete.\n6️⃣ <b>Send a whole project:</b> send /gitpush, then your ZIP.\n\n/gitcancel stops a step and leaves the repo.",
    "gt.cmds": "<b>⌨️ All commands</b>\nTap a blue command to run it. Tap the grey example to copy it.\n\n<b>Start here</b>\n/git open this GitHub menu\n/gittoken <code>yourtoken</code> connect your GitHub\n/gitrepo open the repo you want to work in. After that you only type file names.\n\n<b>See your repos and files</b>\n/gitrepos your repos\n/gitls the files of your repo, as a document you can download\n/gitls <code>src</code> the files of one folder\n/gitinfo <code>novabot</code> details of a repo\n\n<b>Download</b>\n/gitget <code>nova.py</code> send a file here (many names: one per line)\n/gitzip send the whole repo as a ZIP\n\n<b>Change files</b>\n📎 Just send me one or many files: files with exactly the same name replace the old ones\n/gitput <code>nova.py</code> upload or replace one file\n/gitedit <code>nova.py</code> edit a text file\n/gitdel <code>nova.py</code> delete a file (I ask first)\n/gitpush send a ZIP of your project to GitHub\n\n<b>Repos</b>\n/gitnew <code>mybot</code> create a private repo (add <code>public</code> for a public one)\n/gitvis <code>novabot</code> make a repo public or private\n/gitdelrepo <code>yourname/novabot</code> delete a repo\n\n<b>Other</b>\n/gitstatus check your connection\n/gitoff disconnect your GitHub\n/gitcancel stop a step and leave the repo\n/gitupdate update the bot itself (bot owner only)",
})
TEXTS_HI.update({
    "gt.in_repo": "📂 <b>Tum {repo} ke andar ho</b>",
    "gt.in_now": "📂 <b>Ab tum {repo} ke andar ho</b>\n\nKaam karne ke liye bas file ka naam bhejo. Jaise: <code>/gitget nova.py</code>\nFiles dekhne ke liye /gitls bhejo, doosri repo ke liye /gitrepo.",
    "gt.in_cur": "📂 <b>Tum {repo} ke andar ho</b>\n\nBadalne ke liye <code>/gitrepo reponame</code> bhejo. Saari repos dekhne ke liye /gitrepos. Is repo se bahar nikalne ke liye /gitcancel.",
    "gt.sel_ask": "📚 <b>Tumhari repos</b>\n\n{list}{more}\n\n✏️ Jo repo kholni hai uska naam bhejo, jaise <code>novabot</code>. Rokne ke liye /gitcancel.",
    "gt.sel_more": "\n… aur {n} repos. Naam bhejo, main dhoondh lunga.",
    "gt.ls_cap": "📂 <b>{repo}</b>\n{n} files. Saari files dekhne ke liye document kholo.\nFiles download karne ke liye neeche ke buttons dabao.",
    "gt.ls_none": "📂 <b>{repo}</b>\n\n<code>{path}</code> mein koi file nahi mili. Sab dekhne ke liye /gitls bhejo.",
    "gt.btn_dlfile": "⬇️ File download karo",
    "gt.btn_dlzip": "📦 Sab download karo (ZIP)",
    "gt.btn_pick": "📂 Repo kholo",
    "gt.get_ask": "⬇️ Jo files chahiye unke naam bhejo, ek line mein ek. Jaise:\n<code>nova.py\nextra.py</code>\n\nEk baar mein {max} files tak. Rokne ke liye /gitcancel.",
    "gt.put_ask": "✏️ Jo file replace karni hai uska naam bhejo, jaise <code>nova.py</code>.\nNayi file jodne ke liye <code>+newfile.py</code> bhejo.\nRokne ke liye /gitcancel.",
    "gt.get_problems": "⚠️ Yeh files nahi bhej paya:\n{list}\n\nNaam nahi mila, file bahut badi hai, ya naam ek se zyada files se milta hai (tab poora path bhejo, jaise <code>src/nova.py</code>). Naam dekhne ke liye /gitls bhejo.",
    "gt.get_many": "ℹ️ Maine pehli {max} files bhej di. Baaki dobara bhejo.",
    "gt.nofile": "❌ <b>{repo}</b> mein <code>{q}</code> jaisi file nahi mili. File ke naam dekhne ke liye /gitls bhejo.",
    "gt.sel_none": "📂 Pehle repo kholo: /gitrepo bhejo.",
    "gt.sel_nomatch": "Is repo mein in naamon ki bilkul same file nahi mili:\n{list}\n\nKuch nahi badla. Nayi file jodne ke liye /gitput use karo.",
    "gt.sel_skip": "\n\n⏭ Chhod di (is repo mein bilkul same naam ki file nahi, ya naam kai folders mein hai):\n{list}",
    "gt.use_repoinfo": "ℹ️ <b>Repo ki details</b>\nCommand ke saath repo ka naam bhejo.\nJaise: <code>/gitinfo novabot</code>\nNaam yaad nahi? /gitrepos bhejo.",
    "gt.use_repofiles": "📂 <b>Repo ki files dekho</b>\n/gitls bhejo, phir apni repo chuno.\nYa likh ke: <code>/gitls yourname/novabot</code>\nFolder kholne ke liye uska naam jodo: <code>/gitls src</code>",
    "gt.use_getfile": "⬇️ <b>Files download karo</b>\nPehle /gitrepo se repo kholo, phir command ke saath file ka naam bhejo.\nJaise: <code>/gitget nova.py</code>",
    "gt.use_deletefile": "🗑 <b>File delete karo</b>\nPehle /gitrepo se repo kholo, phir command ke saath file ka naam bhejo.\nJaise: <code>/gitdel old.py</code>\nDelete se pehle main hamesha poochta hoon.",
    "gt.use_editfile": "✏️ <b>Text file edit karo</b>\nPehle /gitrepo se repo kholo, phir command ke saath file ka naam bhejo.\nJaise: <code>/gitedit nova.py</code>",
    "gt.use_uploadfile": "⬆️ <b>File upload ya replace karo</b>\n/gitput bhejo, phir apni repo chuno.\nYa likh ke: <code>/gitput nova.py</code>",
    "gt.use_download": "📦 <b>Repo ko ZIP mein download karo</b>\n/gitzip bhejo, phir apni repo chuno.\nYa likh ke: <code>/gitzip yourname/novabot</code>\nDoosri branch ke liye uska naam jodo: <code>/gitzip yourname/novabot dev</code>",
    "gt.use_pushzip": "⬆️ <b>Apne project ka ZIP GitHub par bhejo</b>\n/gitpush bhejo, phir apni repo chuno, phir ZIP bhejo.\nYa likh ke: <code>/gitpush yourname/novabot</code>\nDoosri branch ke liye uska naam jodo: <code>/gitpush yourname/novabot dev</code>",
    "gt.update_unset": "⚠️ /gitupdate abhi set up nahi hai. Bot owner ko server par GIT_UPDATE_REPO set karna hoga.",
    "gt.how": "<b>📖 Guide</b>\n\n1️⃣ <b>GitHub jodo:</b> <code>/gittoken yourtoken</code> bhejo (token guide dekho).\n2️⃣ <b>Repo kholo:</b> /gitrepo bhejo, phir repo ka naam. Main yaad rakhta hoon, aur har reply mein 📂 dikhta hai ki tum kahan ho.\n3️⃣ <b>Files dekho:</b> /gitls bhejo. Saari files ka document milega. Neeche ke buttons se ek file ya poori repo ZIP mein download karo.\n4️⃣ <b>Files replace karo:</b> bas ek ya kai files bhej do. Repo mein bilkul same naam ki file purani ko replace karti hai. Main list dikhakar ek baar poochta hoon.\n5️⃣ <b>Repo ke andar aur kaam:</b> <code>/gitget nova.py</code> download, <code>/gitput nova.py</code> upload, <code>/gitedit nova.py</code> edit, <code>/gitdel nova.py</code> delete.\n6️⃣ <b>Poora project bhejo:</b> /gitpush bhejo, phir ZIP.\n\n/gitcancel kisi bhi step ko rokta hai aur repo se bahar nikalta hai.",
    "gt.cmds": "<b>⌨️ Saari commands</b>\nNeeli command dabao to chalegi. Grey example dabao to copy hoga.\n\n<b>Yahan se shuru karo</b>\n/git yeh GitHub menu kholo\n/gittoken <code>yourtoken</code> apna GitHub jodo\n/gitrepo wo repo kholo jisme kaam karna hai. Uske baad sirf file ka naam likhna hai.\n\n<b>Repos aur files dekho</b>\n/gitrepos tumhari repos\n/gitls repo ki files, document mein jo download ho sakta hai\n/gitls <code>src</code> ek folder ki files\n/gitinfo <code>novabot</code> repo ki details\n\n<b>Download</b>\n/gitget <code>nova.py</code> file yahan bhejo (kai naam: ek line mein ek)\n/gitzip poori repo ZIP mein\n\n<b>Files badlo</b>\n📎 Bas ek ya kai files bhej do: bilkul same naam ki files purani ko replace karti hain\n/gitput <code>nova.py</code> ek file upload ya replace\n/gitedit <code>nova.py</code> text file edit\n/gitdel <code>nova.py</code> file delete (pehle poochta hoon)\n/gitpush apne project ka ZIP GitHub par bhejo\n\n<b>Repos</b>\n/gitnew <code>mybot</code> private repo banao (public ke liye <code>public</code> jodo)\n/gitvis <code>novabot</code> repo public ya private karo\n/gitdelrepo <code>yourname/novabot</code> repo delete karo\n\n<b>Aur</b>\n/gitstatus connection check karo\n/gitoff apna GitHub hatao\n/gitcancel step rokho aur repo se bahar niklo\n/gitupdate bot ko update karo (sirf bot owner)",
})
