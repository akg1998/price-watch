#!/usr/bin/env python3
"""
Black Friday price watcher.

Three kinds of watches (all in config.json):

  products         A product page (geizhals.de, idealo.de, amazon.de/dp/..., MediaMarkt, ...).
                   Geizhals/idealo pages give the lowest price across many shops (incl. Amazon).
  amazon_searches  Searches amazon.de and takes the lowest price among results whose title
                   matches your keywords (so all colours of a model are covered).
  deal_feeds       Reads the mydealz.de "new deals" feed and pings you for every new deal
                   whose title matches your keywords (e.g. curved monitors, PS5).

You get a push notification when:
  * a price falls to or below your target price, or
  * a price beats the lowest price seen so far (or the last price - your choice), or
  * a new matching deal is posted on mydealz, or
  * a page keeps failing (so you never miss something silently).

Only the Python standard library is needed.

Usage:
  (On Windows use "py" instead of "python3".)
  python3 price_watch.py               # run everything that is due, once
  python3 price_watch.py --loop 5      # keep running, wake up every 5 min
  python3 price_watch.py --dry-run     # print prices only (no alerts, nothing saved)
  python3 price_watch.py --force       # ignore schedules, check everything now
  python3 price_watch.py --test-notify # send a test notification
"""

import argparse
import gzip
import html as htmllib
import json
import os
import random
import re
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import zlib
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_CONFIG = HERE / "config.json"
DEFAULT_STATE = HERE / "state.json"

USER_AGENTS = [
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/131.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14.6; rv:132.0) Gecko/20100101 Firefox/132.0",
]


class FetchError(Exception):
    pass


# --------------------------------------------------------------------------- #
# Text helpers
# --------------------------------------------------------------------------- #

def parse_price(value):
    """'1.299,00 €', '1299.00', '799,-', 799  ->  float (or None)."""
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    s = htmllib.unescape(str(value)).replace("\xa0", " ").replace(" ", " ")
    m = re.search(r"\d[\d.,\s]*", s)
    if not m:
        return None
    n = m.group(0).replace(" ", "").rstrip(".,")
    if "," in n and "." in n:
        if n.rfind(",") > n.rfind("."):      # 1.299,00
            n = n.replace(".", "").replace(",", ".")
        else:                                 # 1,299.00
            n = n.replace(",", "")
    elif "," in n:
        n = n.replace(",", ".") if re.search(r",\d{1,2}$", n) else n.replace(",", "")
    elif "." in n and re.search(r"\.\d{3}$", n):  # 1.299
        n = n.replace(".", "")
    try:
        return float(n)
    except ValueError:
        return None


EURO_RE = re.compile(
    r"(?:€\s*(\d{1,3}(?:\.\d{3})+(?:,\d{1,2})?|\d+(?:,\d{1,2})?))"
    r"|(?:(\d{1,3}(?:\.\d{3})+(?:,\d{1,2})?|\d+(?:,\d{1,2})?)\s*(?:€|EUR\b|Euro\b))"
)


def first_euro_price(text):
    for m in EURO_RE.finditer(text or ""):
        p = parse_price(m.group(1) or m.group(2))
        if p:
            return p
    return None


def strip_tags(s):
    s = re.sub(r"<!\[CDATA\[(.*?)\]\]>", r"\1", s or "", flags=re.S)
    s = re.sub(r"<[^>]+>", " ", s)
    return re.sub(r"\s+", " ", htmllib.unescape(s)).strip()


def norm(s):
    """Lowercase and drop spaces/punctuation: 'iPhone 17 Pro, 256 GB' -> 'iphone17pro256gb'."""
    return re.sub(r"[\W_]+", "", htmllib.unescape(s or "").lower())


def title_matches(title, include=(), exclude=()):
    """include: every term must appear ('a|b' = a or b). exclude: none may appear."""
    t = norm(title)
    for term in include:
        if not any(norm(alt) in t for alt in str(term).split("|") if alt.strip()):
            return False
    for term in exclude:
        if norm(term) and norm(term) in t:
            return False
    return True


def eur(x):
    return f"{x:,.2f} €".replace(",", "X").replace(".", ",").replace("X", ".")


# --------------------------------------------------------------------------- #
# Price extraction from product pages
# --------------------------------------------------------------------------- #

LD_RE = re.compile(
    r"<script[^>]+type=[\"']application/ld\+json[\"'][^>]*>(.*?)</script>", re.S | re.I
)


def _walk(obj):
    if isinstance(obj, dict):
        yield obj
        for v in obj.values():
            yield from _walk(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from _walk(v)


def _types(node):
    t = node.get("@type")
    return t if isinstance(t, list) else [t]


def _offer_prices(offers):
    out = []
    for node in _walk(offers):
        if any(t in ("Offer", "AggregateOffer") for t in _types(node)) or (
            "price" in node or "lowPrice" in node
        ):
            for key in ("lowPrice", "price"):
                p = parse_price(node.get(key))
                if p:
                    out.append(p)
                    break
    return out


def prices_from_json_ld(page, product_name=None):
    blocks = []
    for raw in LD_RE.findall(page):
        raw = raw.strip()
        for candidate in (raw, htmllib.unescape(raw)):
            try:
                blocks.append(json.loads(candidate))
                break
            except Exception:
                continue
    for data in blocks:                       # the first Product = the main product
        for node in _walk(data):
            if "Product" in _types(node) and node.get("offers"):
                if product_name and str(node.get("name", "")).strip().lower() != product_name.lower():
                    continue
                prices = _offer_prices(node["offers"])
                if prices:
                    return prices
    prices = []
    if product_name:
        return prices
    for data in blocks:
        for node in _walk(data):
            if any(t in ("Offer", "AggregateOffer") for t in _types(node)):
                prices += _offer_prices(node)
    return prices


META_PATTERNS = [
    r'<[^>]+itemprop=["\'](?:lowPrice|price)["\'][^>]*content=["\']([^"\']+)["\']',
    r'<[^>]+content=["\']([^"\']+)["\'][^>]*itemprop=["\'](?:lowPrice|price)["\']',
    r'<meta[^>]+property=["\'](?:product:price:amount|og:price:amount)["\'][^>]+content=["\']([^"\']+)["\']',
    r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\'](?:product:price:amount|og:price:amount)["\']',
]

AMAZON_PAGE_PATTERNS = [
    r'id=["\']corePrice(?:Display_desktop)?_feature_div["\'].*?<span class=["\']a-offscreen["\']>([^<]+)<',
    r'id=["\']apex_desktop["\'].*?<span class=["\']a-offscreen["\']>([^<]+)<',
    r'<span class=["\']a-price-whole["\']>([^<]+)<',
]


def parse_geizhals_offers(page):
    """[{price, shop, via, link}, ...] from a geizhals product page, cheapest first."""
    offers = []
    for block in re.split(r'id="offer-index-\d+"', page)[1:]:
        block = block[:25000]
        pm = re.search(r"price:\s*'([\d.]+)'", block) or re.search(
            r'class="gh_price">\s*€\s*([\d.,]+)', block)
        if not pm:
            continue
        price = float(pm.group(1)) if "'" in pm.group(0) else parse_price(pm.group(1))
        nm = (re.search(r'class="merchant__logo-caption">\s*(.*?)\s*</div>', block, re.S)
              or re.search(r'data-merchant-name="([^"]+)"', block))
        lm = re.search(r'href="(https://geizhals\.[a-z]+/redir/[^"]+)"', block)
        via = re.search(r'class="offer__merchant-link">\s*\(via\s*([^)<]+)\)', block)

        def cell(cls):
            i = block.find(cls)
            if i < 0:
                return ""
            j = block.find("offer-cell", i + len(cls) + 5)
            return strip_tags("<" + block[i:j if j > 0 else i + 3000])

        delivery = cell("offer__delivery offer-cell")
        if re.search(r"gratis|versandkostenfrei|kostenlos", delivery, re.I):
            shipping = 0.0
        else:
            shipping = first_euro_price(delivery)
        avail = re.split(r"\b(?:Kreditkarte|PayPal|Lastschrift|Vorkasse|Nachnahme|Rechnung|Klarna|"
                         r"Sofort|Apple Pay|Google Pay|Amazon Pay|€|GRATIS)", delivery)[0]
        avail = re.sub(r"^[^A-Za-zÄÖÜäöü]*", "", avail).strip(" .,")
        for de, en in (("Auf Lager", "In stock"), ("Nicht lagernd", "Not in stock"),
                       ("lagernd", "in stock"), ("Lieferzeit", "Delivery"),
                       ("Werktage", "working days"), ("Werktag", "working day"),
                       ("Tage", "days"), ("Lieferbar", "Available"), ("ab", "from")):
            avail = re.sub(rf"\b{de}\b", en, avail)
        details = cell("offer__details offer-cell")
        shop_title = re.split(r"\s*(?:Preis vom:|\[Energie|Energieeffizienz)", details)[0].strip()
        rating_txt = cell("offer__merchant-rating")
        rm = re.search(r"Bewertung:\s*([\d.,]+)\s*von\s*5.*?([\d.]+)\s*Bewertungen", rating_txt)
        rating = (f"{rm.group(1)}/5 ({rm.group(2)} reviews)" if rm
                  else "no shop reviews yet" if "keine" in rating_txt else "")

        offers.append({
            "price": price,
            "shop": strip_tags(nm.group(1)) if nm else "?",
            "via": via.group(1).strip() if via else "",
            "link": htmllib.unescape(lm.group(1)) if lm else "",
            "shipping": shipping,
            "availability": avail[:60],
            "shop_title": shop_title[:160],
            "rating": rating,
        })
    return sorted(offers, key=lambda o: o["price"])


def official_store_info(page, url):
    """Shop name, normal price and saving for official brand stores."""
    info = {"shop": "", "regular": None, "saving": None}
    if "store.google." in url:
        info["shop"] = "Google Store"
        m = re.search(r'data:\[\[0,0,\["EUR",(\d+(?:,\d+)?)\],\d+,\["EUR",(\d+)\],\["EUR",[\d,]+\],\["EUR",(\d+)\]', page)
        if m and int(m.group(2)) > 0:
            info["saving"] = float(m.group(2))
            info["regular"] = float(m.group(3))
    elif "apple.com" in url:
        info["shop"] = "Apple Store"
    elif "samsung.com" in url:
        info["shop"] = "Samsung Shop"
    return info


def geizhals_product_name(page):
    m = re.search(r"<title>\s*(.*?)\s+ab\s+(?:€|&euro;)", page, re.S)
    return strip_tags(m.group(1)) if m else ""


def shop_label(offer):
    return offer["shop"] + (f" (via {offer['via']})" if offer.get("via") else "")


def offer_details(o, product=""):
    """Multi-line description of one offer, for the notification."""
    lines = []
    if product:
        lines.append(f"📦 Product: {product}")
    shop = f"🏪 Shop: {shop_label(o)}"
    if o.get("rating"):
        shop += f" · {o['rating']}" if o["rating"].startswith("no ") else f" · rating {o['rating']}"
    lines.append(shop)
    if o.get("shipping") is not None:
        ship = "free shipping" if o["shipping"] == 0 else f"+ {eur(o['shipping'])} shipping"
        lines.append(f"💶 Total: {eur(o['price'] + o['shipping'])} ({eur(o['price'])} {ship})")
    if o.get("availability"):
        lines.append(f"🚚 {o['availability']}")
    if o.get("shop_title"):
        lines.append(f"🔎 Shop's title: {o['shop_title']}")
    return "\n".join(lines)


def extract_price(page, url="", custom_regex=None, min_plausible=0, product_name=None):
    """Find the product price on a page. Returns (price, method) or (None, None)."""
    def ok(p):
        return p is not None and p >= min_plausible

    if custom_regex:
        m = re.search(custom_regex, page, re.S)
        if m:
            p = parse_price(m.group(1) if m.groups() else m.group(0))
            if ok(p):
                return p, "custom regex"

    if "amazon." in url:
        for pat in AMAZON_PAGE_PATTERNS:
            m = re.search(pat, page, re.S)
            if m and ok(parse_price(m.group(1))):
                return parse_price(m.group(1)), "amazon"

    prices = [p for p in prices_from_json_ld(page, product_name) if ok(p)]
    if prices:
        return min(prices), "json-ld"
    if product_name:
        return None, None

    for pat in META_PATTERNS:
        vals = [v for v in (parse_price(x) for x in re.findall(pat, page, re.I)) if ok(v)]
        if vals:
            return min(vals), "meta tag"

    # Comparison sites put the lowest price in the page title: "... ab € 838,55 ..."
    m = re.search(r"<title>[^<]*?\bab\s*(?:€|&euro;|EUR)(?:\s|&#xa0;|&nbsp;|\xa0)*([\d.]+,\d{2})", page, re.I)
    if m and ok(parse_price(m.group(1))):
        return parse_price(m.group(1)), "page title"

    # Last resort for comparison sites: lowest "€ 1.234,56" in the offer list.
    if "geizhals." in url or "idealo." in url or "preisvergleich" in url:
        vals = []
        for m in re.finditer(r"€\s*(\d{1,3}(?:\.\d{3})*,\d{2}|\d+,\d{2})", page):
            p = parse_price(m.group(1))
            if ok(p):
                vals.append(p)
        if vals:
            return min(vals), "offer list"

    return None, None


# --------------------------------------------------------------------------- #
# Amazon search + mydealz feed parsing
# --------------------------------------------------------------------------- #

def parse_amazon_search(page):
    """[(title, price, link), ...] from an amazon.de search results page."""
    results = []
    for chunk in re.split(r'data-component-type=["\']s-search-result["\']', page)[1:]:
        chunk = chunk[:30000]
        m = (re.search(r'<h2[^>]*aria-label=["\']([^"\']+)["\']', chunk)
             or re.search(r"<h2[^>]*>(.*?)</h2>", chunk, re.S))
        title = strip_tags(m.group(1)) if m else ""
        pm = re.search(r'<span class=["\']a-offscreen["\']>([^<]+)</span>', chunk)
        price = parse_price(pm.group(1)) if pm else None
        am = re.search(r"/dp/([A-Z0-9]{10})", chunk)
        link = f"https://www.amazon.de/dp/{am.group(1)}" if am else None
        if title and price:
            results.append((title, price, link))
    return results


def parse_feed(xml):
    """[{id, title, link, price, merchant}, ...] from an RSS feed (mydealz/pepper)."""
    items = []
    for it in re.findall(r"<item\b[^>]*>(.*?)</item>", xml, re.S):
        def tag(name):
            m = re.search(rf"<{name}\b[^>]*>(.*?)</{name}>", it, re.S)
            return strip_tags(m.group(1)) if m else ""
        title, link, desc = tag("title"), tag("link"), tag("description")
        mp = re.search(r'<pepper:merchant\b[^>]*\bprice=["\']([^"\']+)["\']', it)
        mn = re.search(r'<pepper:merchant\b[^>]*\bname=["\']([^"\']+)["\']', it)
        price = parse_price(mp.group(1)) if mp else None
        price = price or first_euro_price(title) or first_euro_price(desc[:250])
        merchant = htmllib.unescape(mn.group(1)).strip() if mn else ""
        if not merchant:
            mm = re.search(r"€\s*[-–@]\s*([A-Za-z0-9.\- ]{2,25})", desc[:250])
            merchant = mm.group(1).strip() if mm else ""
        cmp_m = re.search(r"(?:Vergleichspreis|VGP|PVG|statt|UVP|sonst|regulär)[^0-9€]{0,40}?"
                          r"(\d{1,3}(?:\.\d{3})*(?:,\d{1,2})?|\d+(?:,\d{1,2})?)\s*€", desc, re.I)
        compare = parse_price(cmp_m.group(1)) if cmp_m else None
        body = re.sub(r"^\s*[\d.,]+\s*€\s*-\s*[^ ]+\s*", "", desc).strip()   # drop "23,98€ - Amazon"
        posted = ""
        pm2 = re.search(r"<pubDate>[^<]*?(\d{1,2}) (\w{3}) \d{4} (\d{2}:\d{2})", it)
        if pm2:
            posted = f"{pm2.group(1)} {pm2.group(2)}, {pm2.group(3)}"
        items.append({"id": tag("guid") or link or title, "title": title, "link": link,
                      "price": price, "merchant": merchant, "compare": compare,
                      "text": body, "posted": posted, "category": tag("category")})
    return items


# --------------------------------------------------------------------------- #
# Fetching
# --------------------------------------------------------------------------- #

def fetch(url, timeout=25):
    req = urllib.request.Request(url, headers={
        "User-Agent": random.choice(USER_AGENTS),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "de-DE,de;q=0.9,en;q=0.8",
        "Accept-Encoding": "gzip, deflate",
        "Cache-Control": "no-cache",
    })
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            raw = r.read()
            enc = (r.headers.get("Content-Encoding") or "").lower()
            charset = r.headers.get_content_charset() or "utf-8"
    except urllib.error.HTTPError as e:
        hint = " (the site is probably blocking scripts)" if e.code in (403, 429, 503) else ""
        raise FetchError(f"HTTP {e.code}{hint}")
    except Exception as e:
        msg = str(e)
        if "CERTIFICATE_VERIFY_FAILED" in msg:
            msg += (" -> on Mac run: open '/Applications/Python 3.x/Install Certificates.command'"
                    if sys.platform == "darwin" else " -> update Python / your certificates")
        raise FetchError(msg)
    if enc == "gzip":
        raw = gzip.decompress(raw)
    elif enc == "deflate":
        raw = zlib.decompress(raw)
    page = raw.decode(charset, errors="replace")
    low = page[:200000].lower()
    if ("captcha" in low or "robot check" in low) and "ld+json" not in low and "<rss" not in low:
        raise FetchError("got a captcha page (the site is blocking scripts right now)")
    return page


# --------------------------------------------------------------------------- #
# Notifications
# --------------------------------------------------------------------------- #

def _post(url, data, headers):
    req = urllib.request.Request(url, data=data, headers=headers, method="POST")
    with urllib.request.urlopen(req, timeout=20) as r:
        r.read()


def notify(ncfg, title, message, click_url=None, priority=4, tags=None, buttons=None):
    """Send to ntfy / Telegram / desktop. Always prints too.
    buttons: [(label, url), ...] shown under the notification (max 3)."""
    print(f"\n🔔 {title}\n   {message}\n   {click_url or ''}\n")
    sent = False
    buttons = [(l, u) for l, u in (buttons or []) if u] or (
        [("Open deal", click_url)] if click_url else [])

    topic = os.environ.get("NTFY_TOPIC") or ncfg.get("ntfy_topic")
    if topic and "CHANGE-ME" not in topic:
        server = (os.environ.get("NTFY_SERVER") or ncfg.get("ntfy_server") or "https://ntfy.sh").rstrip("/")
        body = {"topic": topic, "title": title, "message": message,
                "priority": priority}
        if tags:
            body["tags"] = tags
        if click_url:
            body["click"] = click_url
        if buttons:
            body["actions"] = [{"action": "view", "label": l[:40], "url": u} for l, u in buttons[:3]]
        try:
            _post(server, json.dumps(body).encode(), {"Content-Type": "application/json"})
            sent = True
        except Exception as e:
            print(f"   ! ntfy failed: {e}")

    token = os.environ.get("TELEGRAM_BOT_TOKEN") or ncfg.get("telegram_bot_token")
    chat = os.environ.get("TELEGRAM_CHAT_ID") or ncfg.get("telegram_chat_id")
    if token and chat:
        text = f"{title}\n{message}" + (f"\n{click_url}" if click_url else "")
        data = urllib.parse.urlencode({"chat_id": chat, "text": text}).encode()
        try:
            _post(f"https://api.telegram.org/bot{token}/sendMessage", data,
                  {"Content-Type": "application/x-www-form-urlencoded"})
            sent = True
        except Exception as e:
            print(f"   ! Telegram failed: {e}")

    if ncfg.get("desktop_notification", ncfg.get("mac_notification", True)):
        sent = desktop_notify(title, message) or sent
    return sent


# Windows toast via built-in PowerShell (no extra installs). Text is passed in
# environment variables, so quotes or symbols in deal titles can't break it.
_WIN_TOAST = r"""
[Windows.UI.Notifications.ToastNotificationManager, Windows.UI.Notifications, ContentType = WindowsRuntime] > $null
$t = [Windows.UI.Notifications.ToastNotificationManager]::GetTemplateContent([Windows.UI.Notifications.ToastTemplateType]::ToastText02)
$x = $t.GetElementsByTagName('text')
$x.Item(0).AppendChild($t.CreateTextNode($env:PW_TITLE)) > $null
$x.Item(1).AppendChild($t.CreateTextNode($env:PW_MSG)) > $null
$app = '{1AC14E77-02E7-4E5D-B744-2EB1AE5198B7}\WindowsPowerShell\v1.0\powershell.exe'
[Windows.UI.Notifications.ToastNotificationManager]::CreateToastNotifier($app).Show([Windows.UI.Notifications.ToastNotification]::new($t))
"""


def desktop_notify(title, message):
    """Pop-up on the computer itself: Mac Notification Centre or Windows toast."""
    try:
        if sys.platform == "darwin":
            script = (f"display notification {json.dumps(message, ensure_ascii=False)} "
                      f"with title {json.dumps(title, ensure_ascii=False)} sound name \"Glass\"")
            subprocess.run(["osascript", "-e", script], timeout=15, capture_output=True)
            return True
        if sys.platform.startswith("win"):
            env = dict(os.environ, PW_TITLE=title[:120], PW_MSG=message[:250])
            r = subprocess.run(
                ["powershell.exe", "-NoProfile", "-NonInteractive", "-ExecutionPolicy", "Bypass",
                 "-Command", _WIN_TOAST],
                env=env, timeout=30, capture_output=True,
                creationflags=0x08000000)  # CREATE_NO_WINDOW: no black window flashing up
            return r.returncode == 0
    except Exception as e:
        print(f"   ! desktop notification failed: {e}")
    return False


# --------------------------------------------------------------------------- #
# Alert rules
# --------------------------------------------------------------------------- #

_QUEUE = []


def queue_alert(ncfg, title, message, click_url=None, priority=4, buttons=None):
    """Collect alerts during a run; flush_alerts() sends them together."""
    _QUEUE.append({"title": title, "message": message, "url": click_url,
                   "priority": priority, "buttons": buttons})


def flush_alerts(ncfg, max_items=15):
    """1 alert -> the full detailed notification. Several -> ONE list."""
    items, _QUEUE[:] = list(_QUEUE), []
    if not items:
        return
    if len(items) == 1:
        a = items[0]
        notify(ncfg, a["title"], a["message"], a["url"], priority=a["priority"], buttons=a["buttons"])
        return
    deals = [a for a in items if not a["title"].startswith("⚠️")]
    warns = [a for a in items if a["title"].startswith("⚠️")]
    lines = []
    for n, a in enumerate(deals[:max_items], 1):
        lines.append(f"{n}. {a['title']}")
        if a.get("url"):
            lines.append(f"   {a['url']}")
    if len(deals) > max_items:
        lines.append(f"…and {len(deals) - max_items} more")
    if warns:
        lines.append("")
        lines += [a["title"] for a in warns]
    if deals and warns:
        title = f"🛍️ {len(deals)} deals / price drops (+ {len(warns)} warnings)"
    elif deals:
        title = f"🛍️ {len(deals)} new deals / price drops"
    else:
        title = f"⚠️ {len(warns)} watches can't be read right now"
    buttons = [(f"Open {n}", a["url"]) for n, a in enumerate(deals[:3], 1) if a.get("url")]
    notify(ncfg, title, "\n".join(lines)[:3800],
           deals[0]["url"] if deals else None,
           priority=max(a["priority"] for a in items), buttons=buttons)


def decide_alerts(entry, price, prev, settings):
    """Return [(title, message, priority)] for a new price reading.
    Never alerts twice for the same (or a higher) price."""
    told = prev.get("last_alert_price")
    min_drop_ = float(entry.get("min_drop_eur", settings.get("min_drop_eur", 10)))
    if told is not None and price > told - min_drop_:
        return []
    return _decide_alerts(entry, price, prev, settings)


def next_alert_price(prev, price, alerted):
    """Remember the last price we told you about. If the price later goes back up
    by 3% or more (the deal ended), forget it, so a new drop alerts again."""
    if alerted:
        return price
    told = prev.get("last_alert_price")
    if told is not None and price >= told * 1.03:
        return None
    return told


def _decide_alerts(entry, price, prev, settings):
    name = entry["name"]
    target = entry.get("target_price")
    on_drop = entry.get("alert_on_any_drop", settings.get("alert_on_any_drop", True))
    min_drop = float(entry.get("min_drop_eur", settings.get("min_drop_eur", 10)))
    compare_to = entry.get("compare_to", settings.get("compare_to", "lowest"))
    last, lowest = prev.get("last_price"), prev.get("lowest_price")
    ref = lowest if compare_to == "lowest" else last

    if target is not None and price <= target:
        if last is None or last > target or (ref is not None and price <= ref - min_drop):
            msg = f"{eur(price)} (your target: {eur(target)})"
            if last is not None and last != price:
                msg += f" · was {eur(last)}"
            return [(f"🎯 {name} is below your target!", msg, 5)]
        return []

    if on_drop and ref is not None and price <= ref - min_drop:
        new_low = lowest is None or price < lowest
        word = "lowest price so far" if new_low else "price drop"
        msg = f"{eur(ref)} → {eur(price)} (−{eur(ref - price)}) · {word}"
        if target is not None:
            msg += f" · target {eur(target)}"
        return [(f"📉 {name}: {eur(price)}", msg, 4)]
    return []


def record_price(prev, name, price, now, extra=None):
    out = {
        "name": name,
        "last_alert_price": prev.get("last_alert_price"),
        "last_price": price,
        "lowest_price": min(price, prev.get("lowest_price") or price),
        "last_checked": now,
        "failures": 0,
        "history": (prev.get("history", []) + [[now, price]])[-300:],
    }
    out.update(extra or {})
    return out


def record_failure(prev, err, ncfg, fail_limit, name, url, dry_run):
    fails = prev.get("failures", 0) + 1
    print(f"  ✗ {name}: {err}  [failure {fails}]")
    if dry_run:
        return prev
    prev = dict(prev, failures=fails, last_error=str(err))
    if fails >= fail_limit and time.time() - prev.get("warned_at", 0) > 24 * 3600:
        prev["warned_at"] = time.time()
        extra = (" Amazon prices still reach you via geizhals and mydealz."
                 if "(Amazon)" in name else " The other watches keep running.")
        queue_alert(ncfg, f"⚠️ Can't read: {name}",
               f"{fail_limit} checks failed in a row: {err}.{extra}",
               url, priority=3)
    return prev


# --------------------------------------------------------------------------- #
# Checks
# --------------------------------------------------------------------------- #

def check_product(entry, prev, settings, ncfg, dry_run, now):
    url, name = entry["url"], entry["name"]
    fail_limit = int(settings.get("warn_after_failures", 3))
    lo = float(entry.get("min_plausible_price", 0))
    try:
        page = fetch(url)
        offers = []
        if "geizhals." in url:
            skip = [s.lower() for s in entry.get("skip_shops", settings.get("skip_shops", []))]
            offers = [o for o in parse_geizhals_offers(page) if o["price"] >= lo
                      and not any(s in shop_label(o).lower() for s in skip)]
        if offers:
            price, method = offers[0]["price"], "offers"
        else:
            price, method = extract_price(page, url, entry.get("price_regex"), lo,
                                          entry.get("product_name"))
        if price is None:
            raise FetchError("page loaded but no price found")
    except FetchError as e:
        return record_failure(prev, e, ncfg, fail_limit, name, url, dry_run)

    best = offers[0] if offers else None
    store = official_store_info(page, url)
    amazon = next((o for o in offers if "amazon" in o["shop"].lower() and not o["via"]), None)
    shop = f" @ {shop_label(best)}" if best else ""
    last, low = prev.get("last_price"), prev.get("lowest_price")
    info = "" if last is None else f"  (last {eur(last)}, lowest {eur(low)})"
    amz = f" · Amazon {eur(amazon['price'])}" if amazon and amazon is not best else ""
    if store["shop"]:
        shop = f" @ {store['shop']}"
        if store["saving"]:
            shop += f" (normally {eur(store['regular'])}, −{eur(store['saving'])})"
    print(f"  ✓ {name}: {eur(price)}{shop}{amz}{info}  [{method}]")
    if dry_run:
        return prev
    alerts = decide_alerts(entry, price, prev, settings)
    for title, msg, prio in alerts:
        if best:
            title += f" @ {best['shop']}"
            msg += "\n\n" + offer_details(best, geizhals_product_name(page))
            others = [o for o in offers[1:] if not o["via"]][:3]   # next big shops
            if amazon and amazon is not best and amazon not in others:
                others = [amazon] + others[:2]
            if others:
                msg += "\n\n📋 Other shops: " + " · ".join(
                    f"{o['shop']} {eur(o['price'])}" for o in others)
        if store["shop"]:
            title += f" @ {store['shop']}"
            lines = [f"📦 Product: {entry.get('product_name') or name} (new, sold by {store['shop']})"]
            p = f"💶 Price: {eur(price)}"
            if store["saving"]:
                p += f" (normally {eur(store['regular'])}, you save {eur(store['saving'])})"
            lines.append(p)
            if entry.get("note"):
                lines.append(f"ℹ️ {entry['note']}")
            msg += "\n\n" + "\n".join(lines)
        buttons = [(f"Buy at {best['shop']}", best["link"])] if best else []
        if store["shop"]:
            buttons = [(f"Open {store['shop']}", url)]
        if amazon and amazon is not best:
            buttons.append(("Amazon", amazon["link"]))
        if not store["shop"]:
            buttons.append(("All shops", url))
        queue_alert(ncfg, title, msg, url, priority=prio, buttons=buttons)
    return record_price(prev, name, price, now,
                        {"best_shop": shop_label(best) if best else None,
                         "last_alert_price": next_alert_price(prev, price, bool(alerts))})


def check_amazon_search(entry, prev, settings, ncfg, dry_run, now):
    name = f"{entry['name']} (Amazon)"
    url = "https://www.amazon.de/s?" + urllib.parse.urlencode({"k": entry["query"]})
    # Amazon blocks scripts now and then, so only warn after a longer losing streak.
    fail_limit = int(settings.get("amazon_warn_after_failures", 8))
    excl = list(entry.get("exclude", [])) + list(settings.get("amazon_exclude", []))
    try:
        page = fetch(url)
        results = parse_amazon_search(page)
        if not results:
            raise FetchError("Amazon showed a bot-check page instead of results"
                             if len(page) < 20000 else "no results could be read from the page")
        lo = float(entry.get("min_plausible_price", 0))
        hits = [r for r in results
                if r[1] >= lo and title_matches(r[0], entry.get("include", []), excl)]
        if not hits:
            raise FetchError(f"{len(results)} results, but none matched the keywords")
    except FetchError as e:
        return record_failure(prev, e, ncfg, fail_limit, name, url, dry_run)

    title, price, link = min(hits, key=lambda r: r[1])
    last = prev.get("last_price")
    info = "" if last is None else f"  (last {eur(last)}, lowest {eur(prev.get('lowest_price'))})"
    print(f"  ✓ {name}: {eur(price)}{info}  [{len(hits)} matching] {title[:70]}")
    if dry_run:
        return prev
    alerts = decide_alerts(dict(entry, name=name), price, prev, settings)
    for t, msg, prio in alerts:
        queue_alert(ncfg, t, f"{msg}\n{title[:120]}", link or url, priority=prio)
    return record_price(prev, name, price, now, {"best_title": title, "best_link": link,
                        "last_alert_price": next_alert_price(prev, price, bool(alerts))})


def deal_details(it):
    """Multi-line description of a mydealz deal, for the notification."""
    lines = [f"📦 {it['title']}"]
    if it.get("merchant"):
        lines.append(f"🏪 Shop: {it['merchant']}")
    if it.get("price"):
        p = f"💶 Price: {eur(it['price'])}"
        c = it.get("compare")
        if c and c > it["price"]:
            p += f" (normally ~{eur(c)}, −{round(100 * (1 - it['price'] / c))}%)"
        lines.append(p)
    if it.get("posted"):
        lines.append(f"🕒 Posted: {it['posted']}")
    if it.get("text"):
        t = it["text"]
        lines.append(f"📝 {t[:280]}{'…' if len(t) > 280 else ''}")
    return "\n".join(lines)


def deal_buttons(it):
    """Open the deal, plus a direct search for the product at the shop."""
    q = urllib.parse.quote_plus(it["title"][:100])
    shop = (it.get("merchant") or "").lower()
    if "amazon" in shop:
        search = ("Search on Amazon", f"https://www.amazon.de/s?k={q}")
    elif "mediamarkt" in shop:
        search = ("Search on MediaMarkt", f"https://www.mediamarkt.de/de/search.html?query={q}")
    elif "saturn" in shop:
        search = ("Search on Saturn", f"https://www.saturn.de/de/search.html?query={q}")
    elif "otto" in shop:
        search = ("Search on Otto", f"https://www.otto.de/suche/{urllib.parse.quote(it['title'][:100])}")
    else:
        search = ("Search on Google", "https://www.google.com/search?q="
                  + urllib.parse.quote_plus(f"{it.get('merchant', '')} {it['title'][:100]}".strip()))
    compare = ("Compare prices", f"https://geizhals.de/?fs={q}")
    return [("Open deal", it["link"]), search, compare]


def merchant_ok(merchant, allowed):
    """True if the deal's shop is one of the allowed shops (whole words, any case)."""
    m = (merchant or "").lower().replace("-", " ")
    if not m:
        return False
    for a in allowed:
        a = a.lower().replace("-", " ").strip()
        if a and re.search(rf"(?<![a-z0-9]){re.escape(a)}(?![a-z0-9])", m):
            return True
    return False


def check_feed(feed, prev, settings, ncfg, dry_run, now):
    name = feed.get("name", "mydealz")
    fail_limit = int(settings.get("warn_after_failures", 3))
    items, used, errors = None, None, []
    for url in feed.get("urls") or [feed["url"]]:
        try:
            items = parse_feed(fetch(url))
            if items:
                used = url
                break
            errors.append(f"{url}: no items")
        except FetchError as e:
            errors.append(f"{url}: {e}")
    if not items:
        return record_failure(prev, "; ".join(errors), ncfg, fail_limit, name,
                              (feed.get("urls") or [feed["url"]])[0], dry_run)

    seen = set(prev.get("seen", []))
    first_run = not seen
    print(f"  ✓ {name}: {len(items)} deals in feed ({used})")
    for it in items:
        if it["id"] in seen:
            continue
        for w in feed.get("watches", []):
            if not title_matches(it["title"], w.get("include", []),
                                 list(w.get("exclude", [])) + list(feed.get("exclude", []))):
                continue
            if w.get("max_price") and it["price"] and it["price"] > w["max_price"]:
                continue
            if w.get("min_price") and it["price"] and it["price"] < w["min_price"]:
                continue   # skips accessories, games and contract deals with tiny upfront prices
            shops = w.get("only_merchants")
            if shops == "trusted":
                shops = settings.get("trusted_shops", [])
            elif shops == "brand":
                shops = [b for term in w.get("include", []) for b in str(term).split("|")]
            if shops and not merchant_ok(it["merchant"], shops):
                continue
            price = eur(it["price"]) if it["price"] else "price n/a"
            shop = f" @ {it['merchant']}" if it["merchant"] else ""
            if first_run or dry_run:
                print(f"     · [{w['name']}] {price}{shop}: {it['title'][:90]}")
            else:
                queue_alert(ncfg, f"🔥 {w['name']}: {price}{shop}", deal_details(it),
                       it["link"], priority=w.get("priority", 4),
                       buttons=deal_buttons(it))
            break
    if first_run and not dry_run:
        print("     (first run: these are saved as already seen, alerts start from the next new deal)")
    if dry_run:
        return prev
    ids = [it["id"] for it in items]
    keep = ids + [i for i in prev.get("seen", []) if i not in set(ids)]
    return {"seen": keep[:2000], "last_checked": now, "failures": 0}


# --------------------------------------------------------------------------- #
# Main loop
# --------------------------------------------------------------------------- #

def load_json(path, default):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return default


def save_json(path, data):
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps(data, indent=1, ensure_ascii=False), encoding="utf-8")
    tmp.replace(path)


def is_due(state, key, minutes, force):
    if force:
        return True
    last = state.get("_last_run", {}).get(key)
    return last is None or time.time() - last >= minutes * 60 - 30


def run_once(config, state, dry_run=False, force=False):
    settings = config.get("settings", {})
    ncfg = config.get("notify", {})
    now = datetime.now().isoformat(timespec="seconds")
    state.setdefault("_last_run", {})
    jobs = []
    for e in config.get("products", []):
        if e.get("enabled", True):
            key = e.get("id") or (e["url"] + ("#" + e["product_name"] if e.get("product_name") else ""))
            jobs.append(("p:" + key, e, check_product,
                         e.get("every_minutes", settings.get("product_every_minutes", 30))))
    # Amazon blocks cloud servers (GitHub etc.), so skip its searches there.
    # Amazon prices still come in via geizhals and mydealz.
    in_cloud = bool(os.environ.get("GITHUB_ACTIONS") or os.environ.get("PW_CLOUD"))
    skip_amazon = in_cloud and not settings.get("amazon_in_cloud", False)
    for e in [] if skip_amazon else config.get("amazon_searches", []):
        if e.get("enabled", True):
            jobs.append(("a:" + e["query"], e, check_amazon_search,
                         e.get("every_minutes", settings.get("amazon_every_minutes", 30))))
    for e in config.get("deal_feeds", []):
        if e.get("enabled", True):
            jobs.append(("f:" + e.get("name", "feed"), e, check_feed,
                         e.get("every_minutes", settings.get("feed_every_minutes", 10))))

    due = [j for j in jobs if is_due(state, j[0], j[3], force)]
    print(f"[{now}] {len(due)} of {len(jobs)} watches due")
    hosts_seen = {}
    for key, entry, fn, _ in due:
        host = urllib.parse.urlparse(entry.get("url") or (entry.get("urls") or ["https://www.amazon.de"])[0]).netloc
        if host in hosts_seen:
            time.sleep(random.uniform(3, 7))      # be polite to each site
        hosts_seen[host] = True
        state[key] = fn(entry, state.get(key, {}), settings, ncfg, dry_run, now)
        if not dry_run:
            state["_last_run"][key] = time.time()
    if not dry_run:
        flush_alerts(ncfg)
    return state


def setup_output(log_path=None):
    """UTF-8 output everywhere (the Windows console can't print emoji otherwise),
    optionally into a log file that is kept under ~2 MB."""
    if log_path:
        log = Path(log_path)
        if not log.is_absolute():
            log = HERE / log
        if log.exists() and log.stat().st_size > 2_000_000:
            log.replace(log.with_name(log.stem + ".old" + log.suffix))
        f = open(log, "a", encoding="utf-8", buffering=1)
        sys.stdout = sys.stderr = f
        return
    for s in (sys.stdout, sys.stderr):
        try:
            s.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass  # e.g. pythonw on Windows has no console at all


def main():
    ap = argparse.ArgumentParser(description="Black Friday price watcher")
    ap.add_argument("--config", default=str(DEFAULT_CONFIG))
    ap.add_argument("--state", default=str(DEFAULT_STATE))
    ap.add_argument("--loop", type=float, metavar="MINUTES", help="keep running, wake every N minutes")
    ap.add_argument("--dry-run", action="store_true", help="print prices only")
    ap.add_argument("--force", action="store_true", help="check everything now, ignore schedules")
    ap.add_argument("--test-notify", action="store_true", help="send a test notification")
    ap.add_argument("--log", metavar="FILE", help="write output to this file (used by the background jobs)")
    args = ap.parse_args()
    setup_output(args.log)

    config = load_json(args.config, None)
    if config is None:
        sys.exit(f"Config not found: {args.config}")

    if args.test_notify:
        ok = notify(config.get("notify", {}), "✅ Price watcher is set up",
                    "You will get alerts like this when a price drops.")
        sys.exit(0 if ok else 1)

    while True:
        try:
            state = load_json(args.state, {})
            state = run_once(config, state, dry_run=args.dry_run, force=args.force or args.dry_run)
            if not args.dry_run:
                save_json(args.state, state)
        except Exception:
            import traceback
            traceback.print_exc()   # log it, but keep running next time
            if not args.loop:
                sys.exit(1)
        if not args.loop:
            break
        try:
            time.sleep(args.loop * 60)
        except KeyboardInterrupt:
            break


if __name__ == "__main__":
    main()
