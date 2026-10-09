"""Checks which of your Gemini models really work with your key. Never prints the key.

Usage (in the folder with your bot):
    python check_gemini.py                 # reads GEMINI_API_KEY etc. from the environment
    python check_gemini.py path/to/.env    # or from your env file (KEY=VALUE lines)
"""
import os
import sys

import requests

if len(sys.argv) > 1:
    for line in open(sys.argv[1], encoding="utf-8"):
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            os.environ.setdefault(k.strip(), v.strip().strip("\"'"))

key = (os.environ.get("GEMINI_API_KEY") or "").strip().strip("\"'")
if not key:
    sys.exit("GEMINI_API_KEY not found (pass your env file path as an argument).")


def names(raw):
    return [m.strip().strip("\"'").removeprefix("models/") for m in (raw or "").replace(";", ",").split(",") if m.strip()]


text_models = list(dict.fromkeys(names(os.environ.get("SEARCH_GEMINI_MODELS")) + names(os.environ.get("GEMINI_MODEL"))
                                 + ["gemini-3.8-flash", "gemini-3.7-flash", "gemini-3.6-flash", "gemini-3.5-flash", "gemini-2.5-flash"]))
image_models = list(dict.fromkeys(names(os.environ.get("IMAGE_GEMINI_MODELS")) + ["gemini-3.1-flash-image", "gemini-2.5-flash-image"]))
URL = "https://generativelanguage.googleapis.com/v1beta/models/{}:generateContent"


def call(model, payload):
    try:
        r = requests.post(URL.format(model), params={"key": key}, json=payload, timeout=60)
    except requests.RequestException as exc:
        return f"NETWORK ERROR ({type(exc).__name__})"
    if r.status_code != 200:
        try:
            msg = r.json().get("error", {}).get("message", "")
        except ValueError:
            msg = r.text
        return f"HTTP {r.status_code}: {msg[:140]}"
    parts = ((r.json().get("candidates") or [{}])[0].get("content") or {}).get("parts") or []
    if any(p.get("inlineData") or p.get("inline_data") for p in parts):
        return "OK (returned an image)"
    txt = "".join(p.get("text", "") for p in parts).strip()
    return f"OK: {txt[:60]!r}" if txt else "EMPTY REPLY (this model gave no text)"


print("Models your key can really use (from Google; copy names from here into your env file):")
try:
    r = requests.get("https://generativelanguage.googleapis.com/v1beta/models", params={"key": key, "pageSize": 1000}, timeout=30)
    if r.status_code == 200:
        avail = sorted(m["name"].removeprefix("models/") for m in r.json().get("models", [])
                       if "generateContent" in m.get("supportedGenerationMethods", []))
        print("  " + (", ".join(avail) or "(none returned)"))
    else:
        print(f"  could not list models: HTTP {r.status_code}")
except requests.RequestException as exc:
    print(f"  could not list models: NETWORK ERROR ({type(exc).__name__})")
print()
print("TEXT models (GEMINI_MODEL / SEARCH_GEMINI_MODELS):")
for m in text_models:
    print(f"  {m:28} {call(m, {'contents': [{'parts': [{'text': 'Reply with the single word: ready'}]}]})}")
print("\nIMAGE models (IMAGE_GEMINI_MODELS), used only for reply-to-photo /imagine:")
for m in image_models:
    print(f"  {m:28} {call(m, {'contents': [{'parts': [{'text': 'A small red circle on white'}]}], 'generationConfig': {'responseModalities': ['TEXT', 'IMAGE']}})}")
