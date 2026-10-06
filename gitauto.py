import calendar
import hashlib
import json
import os
import re
import shutil
import sys
import time
import urllib.parse
import zipfile

import feedparser
import requests

FEEDS = [
    "https://feeds.simplecast.com/54nAGcIl",
    "https://techblogwriter.libsyn.com/rss",
    "https://feeds.feedburner.com/TEDTalks_audio",
    "https://feeds.simplecast.com/ZgXQt_UM",
    "https://podcasts.files.bbci.co.uk/p02nq0gn.rss",
    "https://feed.podbean.com/dailyworldbrief/feed.xml",
    "https://rss.amperwave.net/v2/feed/audacynetwork/4cbf0abf775be3cab2bd61a739939f1b",
    "https://www.omnycontent.com/d/playlist/397b9456-4f75-4509-acff-ac0600b4a6a4/6b5c19f7-a385-49c0-bb95-ad4a0071daea/08535d76-8bf4-4bf2-af8d-ad4a007205a3/podcast.rss",
    "https://feeds.megaphone.fm/GLT1412515089",
    "https://omnycontent.com/d/playlist/e73c998e-6e60-432f-8610-ae210140c5b1/A91018A4-EA4F-4130-BF55-AE270180C327/44710ECC-10BB-48D1-93C7-AE270180C33E/podcast.rss",
    "https://www.omnycontent.com/d/playlist/2ee97a4e-8795-4260-9648-accf00a38c6a/ac2da21e-2193-4683-bcb5-accf011076ad/409bad89-c4c2-46cb-b69b-accf01152781/podcast.rss",
    "https://www.spreaker.com/show/6951904/episodes/feed",
    "https://feeds.simplecast.com/qm_9xx0g",
    "https://feeds.simplecast.com/JZSQrle9",
    "https://feeds.megaphone.fm/WWO7410387571",
    "https://feeds.megaphone.fm/RSV1597324942",
    "https://rss2.flightcast.com/xmsftuzjjykcmqwolaqn6mdn",
    "https://www.omnycontent.com/d/playlist/e73c998e-6e60-432f-8610-ae210140c5b1/32f1779e-bc01-4d36-89e6-afcb01070c82/e0c8382f-48d4-42bb-89d5-afcb01075cb4/podcast.rss",
    "https://anchor.fm/s/1007c648c/podcast/rss",
    "https://anchor.fm/s/102ae1cf0/podcast/rss",
    "https://tonyrobbins.libsyn.com/rss",
    "https://feeds.acast.com/public/shows/67587e77c705e441797aff96",
    "https://feeds.megaphone.fm/ESP6921732651",
    "https://feeds.megaphone.fm/the-rich-roll-podcast",
    "https://anchor.fm/s/10d9805f4/podcast/rss",
    "https://podcastfeeds.nbcnews.com/dateline-nbc",
    "https://www.spreaker.com/show/5956723/episodes/feed",
    "https://feeds.megaphone.fm/SIXMSB5088139739",
    "https://feeds.npr.org/510298/podcast.xml",
    "https://feeds.transistor.fm/think-fast-talk-smart-communication-techniques",
    "https://feeds.megaphone.fm/NRD2548999404",
    "https://api.substack.com/feed/podcast/1449053.rss",
]

STATE_FILE = "seen.json"           # פיד -> מזהה הפרק האחרון שנשלח
DOWNLOAD_DIR = "podcasts"          # חייב להיות תואם ל-Workflow
TMP_DIR = "tmp_dl"
META_DIR = "meta"
META_EPISODES = os.path.join(META_DIR, "episodes.json")
OUT_DIR = "out"

TEST_SEND = os.environ.get("TEST_SEND") == "true"
STAMP = os.environ.get("STAMP", time.strftime("%Y-%m-%d_%H-%M"))

# False = בכל ריצה לוקחים את הפרק האחרון מכל RSS (גם אם כבר נשלח).
# True  = מדלגים על פיד שהפרק האחרון שלו כבר נשלח בריצה קודמת.
ONLY_NEW = False

ZIP_LIMIT = 1_999_000_000          # ~1,999MB לקובץ ZIP (מתחת למגבלת 2GiB של GitHub)
ZIP_ENTRY_OVERHEAD = 1000          # מרווח לכותרות ה-ZIP לכל קובץ
MAX_SHOW_LEN = 50
MAX_TITLE_LEN = 200

EPISODES = []                      # פרקים שהורדו בריצה הזו

# ---------------------------------------------------------------------------
# State
# ---------------------------------------------------------------------------


def load_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                # מתעלמים מהפורמט הישן (מספרים / רשימות)
                return {k: v for k, v in data.items() if isinstance(v, str)}
        except Exception as e:
            print(f"Could not read {STATE_FILE}: {e}")
    return {}


def save_state(state):
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=2)


# ---------------------------------------------------------------------------
# Names
# ---------------------------------------------------------------------------

_FORBIDDEN = re.compile(r'[<>:"/\\|?*\x00-\x1f\x7f]')
_INVISIBLE = re.compile('[\u200b-\u200f\u202a-\u202e\u2066-\u2069\ufeff]')
_RESERVED = {"CON", "PRN", "AUX", "NUL"} | {f"COM{i}" for i in range(1, 10)} | {f"LPT{i}" for i in range(1, 10)}


def safe_filename(title, max_len):
    name = _INVISIBLE.sub("", title or "")
    name = _FORBIDDEN.sub("", name)
    name = re.sub(r"\s+", " ", name).strip()
    name = name[:max_len].rstrip(" .")
    if not name:
        name = "episode"
    if name.split(".")[0].upper() in _RESERVED:
        name = "_" + name
    return name


def unique_path(folder, base, ext):
    path = os.path.join(folder, f"{base}.{ext}")
    k = 2
    while os.path.exists(path):
        path = os.path.join(folder, f"{base} ({k}).{ext}")
        k += 1
    return path


# ---------------------------------------------------------------------------
# File type detection
# ---------------------------------------------------------------------------

TYPE_EXT = {
    "audio/mpeg": "mp3", "audio/mp3": "mp3", "audio/mpeg3": "mp3", "audio/x-mpeg": "mp3",
    "audio/mp4": "m4a", "audio/x-m4a": "m4a", "audio/m4a": "m4a",
    "audio/aac": "aac", "audio/aacp": "aac", "audio/x-aac": "aac",
    "audio/ogg": "ogg", "application/ogg": "ogg", "audio/opus": "opus", "audio/x-opus+ogg": "opus",
    "audio/wav": "wav", "audio/x-wav": "wav", "audio/wave": "wav",
    "audio/flac": "flac", "audio/x-flac": "flac",
    "audio/webm": "webm", "video/webm": "webm",
    "video/mp4": "mp4", "video/x-m4v": "m4v", "video/quicktime": "mov",
}
KNOWN_EXT = set(TYPE_EXT.values())


def ext_from_type(content_type):
    if not content_type:
        return None
    return TYPE_EXT.get(content_type.split(";")[0].strip().lower())


def ext_from_url(url):
    ext = os.path.splitext(urllib.parse.urlparse(url).path)[1].lower().lstrip(".")
    return ext if ext in KNOWN_EXT else None


def sniff_ext(head, hint):
    if head[:3] == b"ID3":
        return "mp3"
    if head[:4] == b"OggS":
        return "opus" if b"OpusHead" in head else "ogg"
    if head[:4] == b"RIFF" and head[8:12] == b"WAVE":
        return "wav"
    if head[:4] == b"fLaC":
        return "flac"
    if head[:4] == b"\x1aE\xdf\xa3":
        return "webm"
    if head[4:8] == b"ftyp":
        brand = head[8:12]
        if brand in (b"M4A ", b"M4B ", b"M4P "):
            return "m4a"
        return "m4a" if hint in ("m4a", "mp3", "aac", "ogg", "opus", "wav", "flac") else "mp4"
    if len(head) >= 2 and head[0] == 0xFF and (head[1] & 0xE0) == 0xE0:
        return "aac" if (head[1] & 0x06) == 0 else "mp3"
    return None


def pick_enclosure(entry):
    encs = entry.get("enclosures") or []
    for e in encs:
        t = (e.get("type") or "").lower()
        if e.get("href") and (t.startswith("audio/") or t.startswith("video/") or t == "application/ogg"):
            return e
    for e in encs:
        if e.get("href") and not (e.get("type") or "").lower().startswith("image/"):
            return e
    return None


# ---------------------------------------------------------------------------
# Download
# ---------------------------------------------------------------------------

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
}


def download_to(url, dest):
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    for attempt in range(1, 4):
        try:
            with requests.get(url, headers=HEADERS, stream=True, timeout=(30, 300)) as r:
                r.raise_for_status()
                ctype = r.headers.get("Content-Type", "")
                with open(dest, "wb") as f:
                    for chunk in r.iter_content(chunk_size=1024 * 512):
                        if chunk:
                            f.write(chunk)
            return ctype
        except Exception as e:
            print(f"ניסיון {attempt} נכשל בהורדה: {e}")
            if attempt == 3:
                raise
            time.sleep(5)


def process_entry(feed_url, feed_title, entry):
    """True אם הפרק טופל (ירד, או שאין מה להוריד). False אם נכשל."""
    title = (entry.get("title") or "").strip() or "New episode"
    show = (feed_title or "").strip() or "Podcast"
    enc = pick_enclosure(entry)
    if not enc:
        print(f"No audio file found for: {title}")
        return True

    url = enc["href"]
    tmp = os.path.join(TMP_DIR, hashlib.md5((feed_url + url).encode()).hexdigest() + ".part")

    try:
        ctype = download_to(url, tmp)

        size = os.path.getsize(tmp)
        with open(tmp, "rb") as f:
            head = f.read(64)
        if size < 1024 or head.lstrip()[:1] == b"<":
            raise ValueError(f"התקבל קובץ לא תקין ({size} bytes)")

        hint = ext_from_type(enc.get("type")) or ext_from_url(url) or ext_from_type(ctype)
        ext = sniff_ext(head, hint) or hint or "mp3"

        os.makedirs(DOWNLOAD_DIR, exist_ok=True)
        base = f"{safe_filename(show, MAX_SHOW_LEN)} - {safe_filename(title, MAX_TITLE_LEN)}"
        path = unique_path(DOWNLOAD_DIR, base, ext)
        shutil.move(tmp, path)

        pub = entry.get("published_parsed")
        if pub:
            ts = calendar.timegm(pub)
            if ts > 315532800:  # ZIP לא תומך בתאריכים לפני 1980
                os.utime(path, (ts, ts))

        EPISODES.append({"file": os.path.basename(path), "show": show, "title": title})
        print(f"Downloaded: {os.path.basename(path)}")
        return True
    except Exception as e:
        print(f"Failed to download '{title}': {e}")
        return False
    finally:
        if os.path.exists(tmp):
            try:
                os.remove(tmp)
            except OSError:
                pass


# ---------------------------------------------------------------------------
# Fetch mode (default)
# ---------------------------------------------------------------------------


def entry_ts(e):
    p = e.get("published_parsed") or e.get("updated_parsed")
    return calendar.timegm(p) if p else None


def entry_id(e):
    return e.get("id") or e.get("link") or e.get("title") or ""


def newest_entry(entries):
    """הפרק החדש ביותר לפי תאריך. אם אין תאריכים - הראשון בפיד."""
    dated = [(entry_ts(e), i) for i, e in enumerate(entries) if entry_ts(e)]
    if dated:
        return entries[max(dated, key=lambda x: (x[0], -x[1]))[1]]
    return entries[0]


def main():
    state = load_state()
    feeds = [f for f in FEEDS if f.strip()]
    if TEST_SEND:
        feeds = feeds[:2]

    for feed_url in feeds:
        parsed = feedparser.parse(feed_url)
        if not parsed.entries:
            print(f"הפיד ריק או לא נטען, מדלג: {feed_url}")
            continue

        feed_title = parsed.feed.get("title", "Podcast")
        entry = newest_entry(parsed.entries)
        eid = entry_id(entry)

        if ONLY_NEW and not TEST_SEND and state.get(feed_url) == eid:
            print(f"אין פרק חדש: {feed_title}")
            continue

        if process_entry(feed_url, feed_title, entry) and eid:
            state[feed_url] = eid

    save_state(state)

    if EPISODES:
        os.makedirs(META_DIR, exist_ok=True)
        with open(META_EPISODES, "w", encoding="utf-8") as f:
            json.dump(EPISODES, f, ensure_ascii=False, indent=2)


# ---------------------------------------------------------------------------
# Publish mode: ZIP רגיל אחד (או כמה חלקים אם עובר את המגבלה) + הערות Release
# ---------------------------------------------------------------------------


def split_into_parts(files):
    """מחלק קבצים לחלקים כך שכל חלק לא עובר את ZIP_LIMIT."""
    parts, cur, cur_size = [], [], 0
    for path in files:
        size = os.path.getsize(path) + ZIP_ENTRY_OVERHEAD
        if size > ZIP_LIMIT:
            print(f"אזהרה: {os.path.basename(path)} גדול מהמגבלה, ההעלאה עלולה להיכשל")
        if cur and cur_size + size > ZIP_LIMIT:
            parts.append(cur)
            cur, cur_size = [], 0
        cur.append(path)
        cur_size += size
    if cur:
        parts.append(cur)
    return parts


def publish():
    if not os.path.exists(META_EPISODES):
        print("אין פרקים חדשים לפרסום.")
        return
    with open(META_EPISODES, "r", encoding="utf-8") as f:
        episodes = json.load(f)

    episodes = [e for e in episodes if os.path.isfile(os.path.join(DOWNLOAD_DIR, e["file"]))]
    episodes.sort(key=lambda e: e["show"].lower())
    if not episodes:
        print("אין קבצים לפרסום.")
        return

    os.makedirs(OUT_DIR, exist_ok=True)
    files = [os.path.join(DOWNLOAD_DIR, e["file"]) for e in episodes]
    parts = split_into_parts(files)

    zip_of = {}   # שם קובץ -> שם ה-ZIP שבו הוא נמצא
    for i, part_files in enumerate(parts, 1):
        zip_name = f"podcasts_{STAMP}.zip" if len(parts) == 1 else f"podcasts_{STAMP}_part{i}.zip"
        out_path = os.path.join(OUT_DIR, zip_name)
        with zipfile.ZipFile(out_path, "w", zipfile.ZIP_STORED, allowZip64=True) as z:
            for p in part_files:
                z.write(p, os.path.basename(p))
                zip_of[os.path.basename(p)] = zip_name
        print(f"{zip_name}: {len(part_files)} קבצים, {os.path.getsize(out_path) / 1e6:.0f}MB")

    lines = [f"## ארכיון פודקאסטים - {STAMP}", "",
             f"{len(episodes)} פרקים (הפרק האחרון מכל RSS)", "",
             "| קובץ ZIP | שם התוכנית | פרק |", "|---|---|---|"]
    for e in episodes:
        lines.append(f"| {zip_of[e['file']]} | {e['show'].replace('|', '¦')} | {e['title'].replace('|', '¦')} |")
    with open(os.path.join(OUT_DIR, "notes.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "publish":
        publish()
    else:
        main()
