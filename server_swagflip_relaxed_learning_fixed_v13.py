# server.py
# SwagFlip Brain — local copilot server for RuneLite plugin
# - Suggestion engine + SQLite ledger (lots/trades/recs)
# - Auto-migrates SQLite schema in-place (keeps history)
# - Implements /prices and profit-tracking endpoints with the binary/msgpack formats the plugin expects

import os
import time
import math
import json
import re
import csv
import io
import threading
import sqlite3
import uuid
import struct
import datetime
import statistics
import zlib
import logging
from logging.handlers import RotatingFileHandler
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Dict, Any, Optional, List, Set, Tuple

from html import escape as html_escape

import requests
import msgpack
from flask import Flask, request, jsonify, Response, g

def _now() -> int:
    return int(time.time())


# ============================================================
# CONFIG
# ============================================================
HOST = os.getenv("SWAGFLIP_BIND_HOST", "127.0.0.1")
PORT = int(os.getenv("SWAGFLIP_PORT", "5000"))

PRICES_BASE = "https://prices.runescape.wiki/api/v1/osrs"
USER_AGENT = os.getenv("SWAGFLIP_USER_AGENT", "SwagFlipBrain/final")
REFRESH_SECONDS = int(os.getenv("SWAGFLIP_REFRESH_SECONDS", "60"))

DEBUG_REJECTIONS = os.getenv("SWAGFLIP_DEBUG_REJECTIONS", "true").lower() == "true"
USE_OSRSBOX = os.getenv("SWAGFLIP_USE_OSRSBOX", "true").lower() == "true"

# Trading constraints
MAX_CASH_FRACTION = float(os.getenv("SWAGFLIP_MAX_CASH_FRACTION", "0.90"))
BUY_BUDGET_CAP = int(os.getenv("SWAGFLIP_BUY_BUDGET_CAP", "10000000"))
TARGET_FILL_MINUTES = float(os.getenv("SWAGFLIP_TARGET_FILL_MINUTES", "5.0"))

# Aggressive flip knobs (used in buy/sell model)
BUY_OVERBID_GP = int(os.getenv("SWAGFLIP_BUY_OVERBID_GP", "2"))
SELL_UNDERCUT_GP = int(os.getenv("SWAGFLIP_SELL_UNDERCUT_GP", "2"))
FILL_FRACTION = float(os.getenv("SWAGFLIP_FILL_FRACTION", "0.25"))

# Trend-assisted scoring (used for 30m/2h/8h horizons)
ENABLE_TRENDS = os.getenv("SWAGFLIP_ENABLE_TRENDS", "1") not in ("0", "false", "False")
TREND_CACHE_TTL_SECONDS = int(os.getenv("SWAGFLIP_TREND_CACHE_TTL", "180"))
TREND_RECHECK_TOP_N = int(os.getenv("SWAGFLIP_TREND_TOP_N", "20"))

MIN_BUY_PRICE = int(os.getenv("SWAGFLIP_MIN_BUY_PRICE", "1"))
MIN_MARGIN_GP = int(os.getenv("SWAGFLIP_MIN_MARGIN_GP", "1"))
MIN_TOTAL_PROFIT_GP = int(os.getenv("SWAGFLIP_MIN_TOTAL_PROFIT_GP", "5000"))
MAX_INVENTORY_LOSS_GP = int(os.getenv("SWAGFLIP_MAX_INVENTORY_LOSS_GP", "50000"))

# ============================================================
# "Good flips" CSV prior (optional)
# If enabled, item_ids found in this CSV receive a small score boost.
# This is NOT a hard filter unless SWAGFLIP_ONLY_WINNING_ITEMS is enabled.
# ============================================================
GOOD_CSV_ENABLED = os.getenv("SWAGFLIP_GOOD_CSV_ENABLED", "true").strip().lower() not in ("0", "false", "no", "off")
GOOD_CSV_PATH = os.getenv("SWAGFLIP_GOOD_CSV_PATH", os.getenv("SWAGFLIP_WINNING_FLIPS_CSV", "DaityasPls.csv"))
WINNING_FLIPS_CSV = GOOD_CSV_PATH  # legacy alias
GOOD_CSV_SCORE_BOOST = float(os.getenv("SWAGFLIP_GOOD_CSV_SCORE_BOOST", "1.15"))

# Legacy knobs (kept for compatibility)
ONLY_WINNING_ITEMS = os.getenv("SWAGFLIP_ONLY_WINNING_ITEMS", "0").strip().lower() not in ("0", "false", "no", "off")
WINNER_SCORE_MULT = float(os.getenv("SWAGFLIP_WINNER_SCORE_MULT", str(GOOD_CSV_SCORE_BOOST)))
WINNER_MIN_PROFIT_FRACTION = float(os.getenv("SWAGFLIP_WINNER_MIN_PROFIT_FRACTION", "0.35"))
WINNER_MAX_MINS_MULT = float(os.getenv("SWAGFLIP_WINNER_MAX_MINS_MULT", "1.5"))
WINNER_EXTRA_BUY_BUMP = float(os.getenv("SWAGFLIP_WINNER_EXTRA_BUY_BUMP", "0.002"))

# Aggressive fast-fill bump on buys (capped later so we don't pay away the whole spread)
BUY_FAST_BUMP_PCT = float(os.getenv("SWAGFLIP_BUY_FAST_BUMP_PCT", "0.006"))
MIN_ROI = float(os.getenv("SWAGFLIP_MIN_ROI", "0.0005"))
MAX_ROI = float(os.getenv("SWAGFLIP_MAX_ROI", "0.40"))

# Hard volume filter (avg daily volume)
MIN_DAILY_VOLUME = int(os.getenv("SWAGFLIP_MIN_DAILY_VOLUME", "100000"))
MAX_DAILY_VOLUME = int(os.getenv("SWAGFLIP_MAX_DAILY_VOLUME", "1000000000"))

# Tax rule: items under this sell price are tax-free (default 50 gp)
GE_TAX_FREE_UNDER_PRICE = int(os.getenv("SWAGFLIP_GE_TAX_FREE_UNDER_PRICE", "50"))

# Inventory safety: do not auto-sell if we don't know cost basis unless enabled
AUTO_SELL_UNKNOWN_BASIS = os.getenv("SWAGFLIP_AUTO_SELL_UNKNOWN_BASIS", "true").strip().lower() not in ("0", "false", "no", "off")

# Tax (server-side profit estimates for crash guard + lots PnL)
SELLER_TAX_RATE = float(os.getenv("SWAGFLIP_SELLER_TAX_RATE", "0.02"))


# GE tax logic (match plugin util.GeTax)
MAX_PRICE_FOR_GE_TAX = 250000000
GE_TAX_CAP = 5000000
# Items exempt list copied from plugin util.GeTax (IDs)
GE_TAX_EXEMPT_ITEMS: Set[int] = {
    8011, 365, 2309, 882, 806, 1891, 8010, 1755, 28824, 2140, 2142, 8009, 5325, 1785, 2347, 347,
    884, 807, 28790, 379, 8008, 355, 2327, 558, 1733, 13190, 233, 351, 5341, 2552, 329, 8794, 5329,
    5343, 1735, 315, 952, 886, 808, 8013, 361, 8007, 5331
}

def ge_post_tax_price(item_id: int, price: int) -> int:
    """Return the per-unit price AFTER GE tax.

    New rule: if sell price is under GE_TAX_FREE_UNDER_PRICE (default 50 gp), tax is 0.
    """
    if price <= 0:
        return 0
    p = int(price)

    # New rule: low-priced items are tax-free
    if p < GE_TAX_FREE_UNDER_PRICE:
        return p

    iid = int(item_id)
    if iid in GE_TAX_EXEMPT_ITEM_IDS:
        return p

    # Official GE tax cap behavior: for very expensive items, tax is capped.
    if p >= MAX_PRICE_FOR_GE_TAX:
        return max(p - GE_TAX_CAP, 0)

    tax = int(math.floor(p * SELLER_TAX_RATE))
    return max(p - tax, 0)

def ge_tax_per_unit(item_id: int, price: int) -> int:
    return max(int(price) - ge_post_tax_price(item_id, price), 0)

# Buy-limit window (GE reset): typically 4h
BUY_LIMIT_RESET_SECONDS = int(os.getenv("SWAGFLIP_BUY_LIMIT_RESET_SECONDS", str(4 * 60 * 60)))

# If item has NO recorded cost basis, sell fast using low price and require est under this
FAST_SELL_TARGET_MINUTES = float(os.getenv("SWAGFLIP_FAST_SELL_TARGET_MINUTES", "2.0"))

# Crash-guard aggressiveness
CRASH_PROFIT_PER_ITEM_MIN = int(os.getenv("SWAGFLIP_CRASH_PROFIT_PER_ITEM_MIN", "3"))
REPRICE_OVER_MARKET_PCT = float(os.getenv("SWAGFLIP_REPRICE_OVER_MARKET_PCT", "0.02"))

# Recommendation "failed buy" timeout (seconds)
BUY_REC_TIMEOUT_SECONDS = int(os.getenv("SWAGFLIP_BUY_REC_TIMEOUT_SECONDS", str(20 * 60)))  # 20 min

# Abort feature knobs
ABORT_COOLDOWN_SECONDS = int(os.getenv("SWAGFLIP_ABORT_COOLDOWN_SECONDS", "120"))
STUCK_BUY_ABORT_SECONDS = int(os.getenv("SWAGFLIP_STUCK_BUY_ABORT_SECONDS", str(20 * 60)))

# NEW: Stale offer inactivity window
STALE_OFFER_SECONDS = int(os.getenv("SWAGFLIP_STALE_OFFER_SECONDS", "120"))  # 2 minutes

# Profit tracking account mapping:
# If you make a new OSRS character (new display_name) but want the same profit history,
# enable single-account merge (default: true when only one account exists).
PT_MERGE_SINGLE_ACCOUNT = os.getenv("SWAGFLIP_PT_MERGE_SINGLE_ACCOUNT", "true").lower() == "true"

# Optional aliases: "new_name=old_name, alt=old_name"
# This lets you explicitly map a new character name onto an existing account id.
_PT_ALIASES_RAW = os.getenv("SWAGFLIP_PT_ALIASES", "").strip()
PT_ALIASES: Dict[str, str] = {}
if _PT_ALIASES_RAW:
    for part in _PT_ALIASES_RAW.split(","):
        part = part.strip()
        if not part or "=" not in part:
            continue
        k, v = part.split("=", 1)
        k = (k or "").strip()
        v = (v or "").strip()
        if k and v:
            PT_ALIASES[k.lower()] = v

def _canonical_display_name(dn: str) -> str:
    raw = (dn or "").strip() or "default"
    mapped = PT_ALIASES.get(raw.lower())
    if mapped:
        mapped = (mapped or "").strip()
        if mapped:
            return mapped
    return raw


# Queue file (only queue; all trade history is in SQLite)
LEDGER_PATH = os.getenv("SWAGFLIP_LEDGER_PATH", "ledger.json")

# SQLite DB (durable dataset)
DB_PATH = os.getenv("SWAGFLIP_DB_PATH", "swagflip.db")

# Optional token if you expose beyond localhost
DASH_TOKEN = os.getenv("SWAGFLIP_DASH_TOKEN", "").strip()

# Logging
_default_log = os.path.join(os.path.expanduser("~"), "Desktop", "swagflip_server.txt")
LOG_PATH = os.getenv("SWAGFLIP_LOG_PATH", _default_log)
LOG_LEVEL = os.getenv("SWAGFLIP_LOG_LEVEL", "INFO").upper()
LOG_MAX_BYTES = int(os.getenv("SWAGFLIP_LOG_MAX_BYTES", str(5 * 1024 * 1024)))
LOG_BACKUPS = int(os.getenv("SWAGFLIP_LOG_BACKUPS", "5"))
LOG_TRUNCATE_ON_START = os.getenv("SWAGFLIP_LOG_TRUNCATE_ON_START", "1").strip().lower() in ("1","true","yes","y")

# ============================================================

# ============================================================
# RESET HELPERS (optional)
# ============================================================
# Set SWAGFLIP_RESET_ON_START=1 to: (old SWAGFLIP_RESET is ignored)
#  - truncate swagflip.log
#  - clear ONLY profit-tracking tables (pt_transactions, pt_flips)
#  - clear buy_queue in ledger.json
# (Keeps other history tables intact.)
SWAGFLIP_RESET_ON_START = os.getenv("SWAGFLIP_RESET_ON_START", "0").strip().lower() in ("1", "true", "yes", "y")

def _reset_profit_and_logs_if_requested():
    if not SWAGFLIP_RESET_ON_START:
        return
    # 1) truncate log
    try:
        if os.path.exists(LOG_PATH):
            with open(LOG_PATH, "w", encoding="utf-8"):
                pass
        print(f"[RESET] truncated log: {LOG_PATH}")
    except Exception as e:
        print(f"[RESET] failed to truncate log: {e}")

    # 2) clear profit tracking tables (keep accounts table)
    try:
        if os.path.exists(DB_PATH):
            conn = sqlite3.connect(DB_PATH)
            conn.execute("PRAGMA journal_mode=WAL;")
            cur = conn.cursor()
            # tables might not exist yet on first run
            cur.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='pt_transactions';")
            if cur.fetchone():
                cur.execute("DELETE FROM pt_transactions;")
            cur.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='pt_flips';")
            if cur.fetchone():
                cur.execute("DELETE FROM pt_flips;")
            conn.commit()
            conn.close()
        print("[RESET] cleared profit-tracking tables (pt_transactions, pt_flips)")
    except Exception as e:
        print(f"[RESET] failed to clear profit tables: {e}")

    # 3) clear buy_queue so we start “fresh”
    try:
        # Do not call load_ledger() here (it may not be defined yet during import).
        if os.path.exists(LEDGER_PATH):
            with open(LEDGER_PATH, "w", encoding="utf-8") as f:
                json.dump(
                    {"buy_queue": [], "buy_queue_ts": [], "last_reset_ts": int(time.time())},
                    f,
                    indent=2,
                    sort_keys=True,
                )
        print("[RESET] cleared ledger buy_queue")
    except Exception as e:
        print(f"[RESET] failed to reset ledger: {e}")

# NOTE: profit/log reset is NOT run automatically.
# If you really want to wipe profit tables/log on startup, set:
#   SWAGFLIP_RESET_ON_START=1
# and restart.
# NOTE: startup reset disabled to avoid accidental wipes
# If you want to reset, run the helper manually or add a dashboard button/endpoints.
# FLASK + HTTP
# ============================================================
app = Flask(__name__)

# Logging setup
logger = logging.getLogger("swagflip")

def configure_logging(flask_app: Flask) -> None:
    lvl = getattr(logging, LOG_LEVEL, logging.INFO)
    logger.setLevel(lvl)
    logger.propagate = False

    fmt = logging.Formatter("%(asctime)s | %(levelname)s | %(threadName)s | %(message)s")
    # Ensure log directory exists (Windows-safe)
    try:
        log_dir = os.path.dirname(os.path.abspath(LOG_PATH))
        if log_dir and not os.path.exists(log_dir):
            os.makedirs(log_dir, exist_ok=True)
    except Exception:
        pass

    # Start fresh each run (default)
    if LOG_TRUNCATE_ON_START:
        try:
            with open(LOG_PATH, "w", encoding="utf-8"):
                pass
        except Exception:
            # If truncation fails, continue with console logging
            pass

    fh = RotatingFileHandler(LOG_PATH, maxBytes=LOG_MAX_BYTES, backupCount=LOG_BACKUPS, encoding="utf-8")
    fh.setFormatter(fmt)
    fh.setLevel(lvl)

    sh = logging.StreamHandler()
    sh.setFormatter(fmt)
    sh.setLevel(lvl)

    # Avoid duplicates if reloaded
    if not any(isinstance(h, RotatingFileHandler) for h in logger.handlers):
        logger.addHandler(fh)
    if not any(isinstance(h, logging.StreamHandler) for h in logger.handlers):
        logger.addHandler(sh)

    flask_app.logger.handlers = logger.handlers
    flask_app.logger.setLevel(lvl)

    werk = logging.getLogger("werkzeug")
    werk.handlers = logger.handlers
    werk.setLevel(lvl)

configure_logging(app)

@app.before_request
def _req_start():
    g._t0 = time.time()
    g.request_id = uuid.uuid4().hex[:10]

@app.after_request
def _req_done(resp):
    try:
        dt_ms = int((time.time() - getattr(g, "_t0", time.time())) * 1000)
        rid = getattr(g, "request_id", "-")
        resp.headers["X-Request-ID"] = rid
        logger.info(f"{rid} {request.method} {request.path} -> {resp.status_code} ({dt_ms}ms)")
    except Exception:
        pass
    return resp


# ------------------------------------------------------------
# AUTH COMPAT (LOCAL MODE)
# The Flipping Copilot RuneLite plugin expects to POST /login with HTTP Basic auth.
# When you're running SwagFlip locally, we accept any credentials and return a dummy JWT
# so the plugin can proceed without talking to the official servers.
# ------------------------------------------------------------
@app.route("/login", methods=["POST"])
def copilot_login():
    # If you ever expose this server beyond localhost and want to lock it down,
    # add your own checks here (e.g., require SWAGFLIP_DASH_TOKEN).
    token = "local-" + uuid.uuid4().hex
    return jsonify({"jwt": token, "user_id": 0})


# HTTP session
session = requests.Session()
session.headers.update({"User-Agent": USER_AGENT})

# ============================================================
# LAST STATUS SNAPSHOT (dashboard "current offers")
# ============================================================
_last_status_lock = threading.Lock()
LAST_STATUS: Dict[str, Any] = {
    "updated_unix": 0,
    "offers": [],
    "items": [],
    "coins": 0,
    "inv": [],
}

def update_last_status(status: Dict[str, Any]) -> None:
    offers = status.get("offers") or []
    items = status.get("items") or []
    coins = 0
    inv: List[Tuple[int, int]] = []
    for it in items:
        try:
            iid = int(it.get("item_id", 0))
            amt = int(it.get("amount", 0))
            if iid == 995:
                coins += amt
            elif iid > 0 and amt > 0:
                inv.append((iid, amt))
        except Exception:
            continue
    with _last_status_lock:
        LAST_STATUS["updated_unix"] = int(time.time())
        LAST_STATUS["offers"] = offers
        LAST_STATUS["items"] = items
        LAST_STATUS["coins"] = coins
        LAST_STATUS["inv"] = inv

# ============================================================
# MODELS + PRICE CACHE
# ============================================================
@dataclass
class ItemMeta:
    id: int
    name: str
    limit: Optional[int]

# ============================================================
# WINNER CSV PARSER + STATS
# ============================================================
_WINNER_STATS_BY_NAME: Dict[str, Dict[str, Any]] = {}
_WINNER_STATS_BY_ID: Dict[int, Dict[str, Any]] = {}
_WINNER_ITEM_IDS: Set[int] = set()
_WINNER_LOADED: bool = False

_NAME_NORM_RE = re.compile(r"\s+")

def _norm_name(s: str) -> str:
    return _NAME_NORM_RE.sub(" ", (s or "").strip().lower())

def _parse_winning_flips_csv(path: str) -> Dict[str, Dict[str, Any]]:
    """
    Parse DaityasPls.csv-style exports:

        # Displaying trades for selected time interval: All
        name,date,quantity,price,state
        Super restore(4),2026-01-31 09:01 PM,215,10552,BOUGHT
        Super restore(4),2026-01-31 09:02 PM,215,10600,SOLD
        # Total profit: 10320

    Returns a dict keyed by *normalized* item name with lightweight stats.
    This is used as a prior/boost, not as ground-truth accounting.
    """
    if not path or not os.path.exists(path):
        return {}

    # We want the header row "name,date,quantity,price,state".
    # The file contains banner lines starting with "#", plus "# Total profit:" lines.
    out: Dict[str, Dict[str, Any]] = {}
    last_item_name: Optional[str] = None

    # We'll also compute an approximate "mins" per block when timestamps are present.
    # (Not strictly required; used only for winner weighting/diagnostics.)
    cur_times: List[datetime.datetime] = []

    total_profit_re = re.compile(r"^#\s*Total profit:\s*([-0-9,]+)\s*$", re.IGNORECASE)

    def _flush_profit(profit_val: Optional[int]) -> None:
        nonlocal last_item_name, cur_times
        if not last_item_name:
            cur_times = []
            return
        key = _norm_name(last_item_name)
        st = out.setdefault(key, {"name": last_item_name, "count": 0, "profit_sum": 0, "wins": 0, "mins_sum": 0.0, "profits": []})
        if profit_val is None:
            # still count a block if we have activity
            st["count"] += 1
            cur_times = []
            return
        st["count"] += 1
        st["profit_sum"] += int(profit_val)
        st["profits"].append(int(profit_val))
        if profit_val > 0:
            st["wins"] += 1
        # duration
        if cur_times:
            mins = max(0.25, (max(cur_times) - min(cur_times)).total_seconds() / 60.0)
        else:
            mins = 5.0
        st["mins_sum"] += float(mins)
        cur_times = []

    try:
        with open(path, "r", encoding="utf-8", errors="replace", newline="") as f:
            for raw in f:
                line = raw.replace("\ufeff", "").strip()
                if not line:
                    continue

                # Profit summary line
                m_tot = total_profit_re.match(line)
                if m_tot:
                    try:
                        profit = int(m_tot.group(1).replace(",", ""))
                    except Exception:
                        profit = None
                    _flush_profit(profit)
                    continue

                # Skip banners/comments
                if line.startswith("#"):
                    continue

                # Parse CSV row: name,date,quantity,price,state
                # Use csv reader on the single line to handle commas safely.
                try:
                    row = next(csv.reader([line]))
                except Exception:
                    continue
                if not row or len(row) < 5:
                    continue
                # If header row, skip
                if row[0].strip().lower() == "name" and "state" in (row[-1].strip().lower()):
                    continue

                name = row[0].strip()
                date_s = row[1].strip()
                state = row[4].strip().upper()

                if name:
                    last_item_name = name

                # Only treat SOLD blocks as winners; but we still track blocks even without SOLD.
                # We keep timestamps for approximate duration.
                try:
                    # Example: 2026-01-31 09:02 PM
                    dt = datetime.datetime.strptime(date_s, "%Y-%m-%d %I:%M %p")
                    cur_times.append(dt)
                except Exception:
                    pass

                # If we see a SOLD row but there is no profit line (rare), count it as a win-ish hint.
                if state == "SOLD" and name:
                    key = _norm_name(name)
                    st = out.setdefault(key, {"name": name, "count": 0, "profit_sum": 0, "wins": 0, "mins_sum": 0.0, "profits": []})
                    # no immediate increment here; the profit line will flush the block.
                    # but ensure name is stored
                    st["name"] = name
    except Exception:
        logger.exception("[GOODCSV] parse failed")
        return {}

    # Final flush if file ends without a profit line
    if last_item_name and cur_times:
        _flush_profit(None)

    # Derive convenience stats
    for k, st in list(out.items()):
        c = int(st.get("count", 0) or 0)
        if c <= 0:
            continue
        st["avg_profit"] = int(round(int(st.get("profit_sum", 0)) / max(c, 1)))
        st["win_rate"] = float(int(st.get("wins", 0)) / max(c, 1))
        st["avg_mins"] = float(st.get("mins_sum", 0.0)) / max(c, 1)
        # profit per minute
        st["profit_per_min"] = float(int(st.get("profit_sum", 0)) / max(float(st.get("mins_sum", 0.0)) or 1.0, 1.0))
    return out

def _init_winners_from_mapping(mapping: Dict[int, "ItemMeta"]) -> None:
    """Load a "good flips" CSV (DaityasPls.csv) as a lightweight prior.

    - If the CSV contains an item_id column, we load those IDs directly.
    - Otherwise we fall back to name-based mapping using OSRSBox item mapping.
    - By default this is a *score boost*, not a hard filter.
      (Hard filter only if ONLY_WINNING_ITEMS=True.)
    """
    global _WINNER_LOADED, _WINNER_STATS_BY_NAME, _WINNER_STATS_BY_ID, _WINNER_ITEM_IDS
    if _WINNER_LOADED:
        return
    _WINNER_LOADED = True

    if not GOOD_CSV_ENABLED:
        logger.info("[GOODCSV] disabled")
        return

    # Resolve CSV path relative to server file first, then CWD.
    csv_path = (GOOD_CSV_PATH or "").strip()
    if not csv_path:
        logger.info("[GOODCSV] no path set")
        return

    if not os.path.isabs(csv_path):
        here = os.path.dirname(os.path.abspath(__file__))
        cand1 = os.path.join(here, csv_path)
        cand2 = os.path.join(os.getcwd(), csv_path)
        if os.path.exists(cand1):
            csv_path = cand1
        elif os.path.exists(cand2):
            csv_path = cand2

    if not os.path.exists(csv_path):
        logger.info(f"[GOODCSV] file not found: {csv_path}")
        return

    # 1) Prefer direct item_id column when present.
    good_ids: Set[int] = set()
    try:
        with open(csv_path, "r", encoding="utf-8", errors="replace", newline="") as f:
            # Strip banner/comment lines that start with "#" so csv.DictReader sees the real header row.
            raw_lines = [ln for ln in f if ln.strip() and not ln.lstrip().startswith("#")]
        reader = csv.DictReader(io.StringIO("".join(raw_lines)))
        fields = reader.fieldnames or []
        id_col = None
        for c in fields:
            lc = (c or "").strip().lower()
            if lc in ("item_id", "itemid", "id"):
                id_col = c
                break
        if id_col:
            for row in reader:
                raw = (row.get(id_col) or "").strip()
                if not raw:
                    continue
                try:
                    good_ids.add(int(float(raw)))
                except Exception:
                    continue
    except Exception as e:
        logger.info(f"[GOODCSV] failed reading ids: {e}")

    # 2) Also parse name-based stats (optional; used for bump / thresholds)
    #    This parser is forgiving and supports typical exports.
    name_stats = _parse_winning_flips_csv(csv_path)
    _WINNER_STATS_BY_NAME = name_stats or {}

    if good_ids:
        _WINNER_ITEM_IDS = good_ids
        logger.info(f"[GOODCSV] loaded {len(good_ids)} item_ids from CSV")
    elif not name_stats:
        logger.info("[GOODCSV] none loaded (missing/empty)")
        return

    # Map any name_stats to IDs so we can optionally do winner-aware bump/guardrails.
    if name_stats:
        inv_map = {_norm_name(meta.name): iid for iid, meta in mapping.items()}
        id_stats: Dict[int, Dict[str, Any]] = {}
        id_set: Set[int] = set(_WINNER_ITEM_IDS or set())
        for nm_lc, st in name_stats.items():
            iid = inv_map.get(nm_lc)
            if iid is None:
                continue
            id_stats[iid] = st
            id_set.add(iid)
        _WINNER_STATS_BY_ID = id_stats
        _WINNER_ITEM_IDS = id_set
        logger.info(f"[GOODCSV] mapped {len(id_stats)} names -> item_ids (total ids={len(id_set)})")



class PriceCache:
    """Thread-safe cache for OSRS prices.

    - mapping: item_id -> ItemMeta (name, GE limit)
    - latest: item_id -> {high, low, highTime, lowTime}
    - volumes: item_id -> 24h trade volume (proxy for daily volume)

    Uses the OSRS Wiki prices API:
      - /mapping (metadata)
      - /latest (high/low)
      - /24h   (volume fields)
    """

    def __init__(self):
        self._lock = threading.RLock()
        self.mapping: Dict[int, ItemMeta] = {}
        self.latest: Dict[int, Dict[str, Any]] = {}
        self.volumes: Dict[int, int] = {}
        self.last_refresh: float = 0.0
        self.last_err: str = ""

    def refresh_once(self) -> None:
        try:
            # Metadata mapping (name, limit) — only needs occasional refresh
            mapping_url = f"{PRICES_BASE}/mapping"
            latest_url = f"{PRICES_BASE}/latest"
            vol_url = f"{PRICES_BASE}/24h"

            # mapping
            mapping_list = session.get(mapping_url, timeout=20).json()
            mapping: Dict[int, ItemMeta] = {}
            for row in mapping_list:
                try:
                    iid = int(row.get('id'))
                except Exception:
                    continue
                name = str(row.get('name') or '')
                lim = row.get('limit')
                try:
                    lim_i = int(lim) if lim is not None else 0
                except Exception:
                    lim_i = 0
                mapping[iid] = ItemMeta(id=iid, name=name, limit=lim_i)

            # latest
            latest_json = session.get(latest_url, timeout=20).json()
            latest_data = latest_json.get('data') or {}
            latest: Dict[int, Dict[str, Any]] = {}
            for k,v in latest_data.items():
                try:
                    iid = int(k)
                except Exception:
                    continue
                latest[iid] = v if isinstance(v, dict) else {}

            # 24h volumes
            vol_json = session.get(vol_url, timeout=20).json()
            vol_data = vol_json.get('data') or {}
            volumes: Dict[int, int] = {}
            for k,v in vol_data.items():
                try:
                    iid = int(k)
                except Exception:
                    continue
                if not isinstance(v, dict):
                    continue
                hv = v.get('highPriceVolume', 0) or 0
                lv = v.get('lowPriceVolume', 0) or 0
                try:
                    volumes[iid] = int(hv) + int(lv)
                except Exception:
                    volumes[iid] = 0

            try:
                _init_winners_from_mapping(mapping)
            except Exception:
                logger.exception("[GOODCSV] init failed")

            with self._lock:
                self.mapping = mapping
                self.latest = latest
                self.volumes = volumes
                self.last_refresh = time.time()
                self.last_err = ""

            logger.info(f"[PRICES] mapping loaded: {len(mapping)} items")
            logger.info(f"[PRICES] latest refreshed: {len(latest)} items")
            logger.info(f"[PRICES] volumes refreshed: {len(volumes)} items")

        except Exception as e:
            with self._lock:
                self.last_err = str(e)
            logger.exception("[PRICES] refresh failed")

    def refresh_forever(self) -> None:
        while True:
            self.refresh_once()
            time.sleep(REFRESH_SECONDS)

    def snapshot(self):
        with self._lock:
            # Shallow copies are fine — values are primitives / small dicts / ItemMeta
            return (dict(self.mapping), dict(self.latest), dict(self.volumes), self.last_refresh)


prices = PriceCache()

def db_connect() -> sqlite3.Connection:
    # check_same_thread=False keeps sqlite happy if used across flask threads
    conn = sqlite3.connect(DB_PATH, timeout=30, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    try:
        conn.execute("PRAGMA journal_mode=WAL;")
    except Exception as e:
        logger.warning(f"[DB] WAL not available, falling back to DELETE mode: {e}")
        conn.execute("PRAGMA journal_mode=DELETE;")
    conn.execute("PRAGMA synchronous=NORMAL;")
    conn.execute("PRAGMA busy_timeout=5000;")
    return conn

@contextmanager
def _db():
    """Context-managed DB connection for request and worker code."""
    conn = db_connect()
    try:
        yield conn
    finally:
        try:
            conn.close()
        except Exception:
            pass

def _columns(conn: sqlite3.Connection, table: str) -> Set[str]:
    cur = conn.cursor()
    try:
        cur.execute(f"PRAGMA table_info({table})")
        return {str(r[1]) for r in cur.fetchall()}  # r[1] = column name
    except Exception:
        return set()

def _ensure_table(conn: sqlite3.Connection, create_sql: str) -> None:
    conn.execute(create_sql)

def _ensure_column(conn: sqlite3.Connection, table: str, col: str, col_def: str) -> None:
    cols = _columns(conn, table)
    if col in cols:
        return
    conn.execute(f"ALTER TABLE {table} ADD COLUMN {col} {col_def}")
    logger.info(f"[DB] migrated: added column {table}.{col} {col_def}")

def db_init() -> None:
    """
    Creates any missing tables, and migrates older swagflip.db schemas in-place
    by adding newly-required columns. Keeps all history.
    """
    with _db_lock:
        conn = db_connect()
        try:
            cur = conn.cursor()

            # --- Create tables if missing (safe even if they exist) ---
            _ensure_table(conn, """
                CREATE TABLE IF NOT EXISTS lots (
                    tx_id TEXT PRIMARY KEY,
                    item_id INTEGER NOT NULL,
                    item_name TEXT NOT NULL,
                    buy_price INTEGER NOT NULL,
                    qty_total INTEGER NOT NULL,
                    qty_remaining INTEGER NOT NULL,
                    buy_ts INTEGER NOT NULL,
                    buy_offer_id INTEGER,
                    buy_rec_id TEXT
                )
            """)

            _ensure_table(conn, """
                CREATE TABLE IF NOT EXISTS offer_instances (
                    offer_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    box_id INTEGER NOT NULL,
                    status TEXT NOT NULL,
                    item_id INTEGER NOT NULL,
                    price INTEGER NOT NULL,
                    amount_total INTEGER NOT NULL,
                    start_ts INTEGER NOT NULL,
                    first_fill_ts INTEGER,
                    done_ts INTEGER,
                    last_seen_ts INTEGER NOT NULL,
                    last_traded INTEGER NOT NULL,
                    last_trade_ts INTEGER,
                    active INTEGER NOT NULL,
                    rec_id TEXT
                )
            """)

            _ensure_table(conn, """
                CREATE TABLE IF NOT EXISTS buy_fills (
                    fill_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    item_id INTEGER NOT NULL,
                    item_name TEXT NOT NULL,
                    qty INTEGER NOT NULL,
                    buy_price INTEGER NOT NULL,
                    fill_ts INTEGER NOT NULL,
                    offer_id INTEGER,
                    rec_id TEXT
                )
            """)

            _ensure_table(conn, """
                CREATE TABLE IF NOT EXISTS realized_trades (
                    trade_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    item_id INTEGER NOT NULL,
                    item_name TEXT NOT NULL,
                    qty INTEGER NOT NULL,
                    buy_price INTEGER NOT NULL,
                    sell_price INTEGER NOT NULL,
                    buy_ts INTEGER NOT NULL,
                    sell_ts INTEGER NOT NULL,
                    profit INTEGER NOT NULL,
                    sell_offer_id INTEGER,
                    sell_rec_id TEXT,
                    buy_rec_id TEXT
                )
            """)

            _ensure_table(conn, """
                CREATE TABLE IF NOT EXISTS recommendations (
                    rec_id TEXT PRIMARY KEY,
                    issued_ts INTEGER NOT NULL,
                    rec_type TEXT NOT NULL,
                    box_id INTEGER NOT NULL,
                    item_id INTEGER NOT NULL,
                    item_name TEXT NOT NULL,
                    price INTEGER NOT NULL,
                    qty INTEGER NOT NULL,
                    expected_profit REAL NOT NULL,
                    expected_duration REAL NOT NULL,
                    note TEXT,
                    linked_offer_id INTEGER,
                    outcome_status TEXT NOT NULL,
                    buy_first_fill_ts INTEGER,
                    buy_done_ts INTEGER,
                    buy_phase_seconds INTEGER,
                    first_sell_ts INTEGER,
                    last_sell_ts INTEGER,
                    sell_phase_seconds INTEGER,
                    realized_profit INTEGER,
                    realized_cost INTEGER,
                    realized_roi REAL,
                    realized_vs_expected REAL,
                    closed_ts INTEGER
                )
            """)

            # --- Profit tracking tables (durable) ---
            _ensure_table(conn, """
                CREATE TABLE IF NOT EXISTS pt_accounts (
                    display_name TEXT PRIMARY KEY,
                    account_id INTEGER NOT NULL,
                    created_ts INTEGER NOT NULL
                )
            """)

            _ensure_table(conn, """
                CREATE TABLE IF NOT EXISTS pt_flips (
                    flip_uuid TEXT PRIMARY KEY,
                    display_name TEXT NOT NULL,
                    account_id INTEGER NOT NULL,
                    item_id INTEGER NOT NULL,
                    opened_time INTEGER NOT NULL,
                    opened_qty INTEGER NOT NULL,
                    spent INTEGER NOT NULL,
                    closed_time INTEGER NOT NULL,
                    closed_qty INTEGER NOT NULL,
                    received_post_tax INTEGER NOT NULL,
                    profit INTEGER NOT NULL,
                    tax_paid INTEGER NOT NULL,
                    status_ord INTEGER NOT NULL,
                    updated_time INTEGER NOT NULL,
                    deleted INTEGER NOT NULL
                )
            """)

            _ensure_table(conn, """
                CREATE TABLE IF NOT EXISTS pt_transactions (
                    tx_id TEXT PRIMARY KEY,
                    display_name TEXT NOT NULL,
                    account_id INTEGER NOT NULL,
                    flip_uuid TEXT NOT NULL,
                    time INTEGER NOT NULL,
                    item_id INTEGER NOT NULL,
                    quantity INTEGER NOT NULL,
                    price INTEGER NOT NULL,
                    box_id INTEGER NOT NULL,
                    amount_spent INTEGER NOT NULL,
                    was_copilot_suggestion INTEGER NOT NULL,
                    copilot_price_used INTEGER NOT NULL,
                    login INTEGER NOT NULL,
                    raw_json TEXT
                )
            """)

            try:
                cur.execute("CREATE INDEX IF NOT EXISTS idx_pt_flips_account_updated ON pt_flips(account_id, updated_time)")
                cur.execute("CREATE INDEX IF NOT EXISTS idx_pt_tx_display_time ON pt_transactions(display_name, time)")
                cur.execute("CREATE INDEX IF NOT EXISTS idx_pt_tx_account_time ON pt_transactions(account_id, time)")
                conn.commit()
            except Exception:
                pass

            # --- Migrate older DBs (add missing columns) ---
            _ensure_column(conn, "lots", "buy_offer_id", "INTEGER")
            _ensure_column(conn, "lots", "buy_rec_id", "TEXT")

            _ensure_column(conn, "buy_fills", "offer_id", "INTEGER")
            _ensure_column(conn, "buy_fills", "rec_id", "TEXT")

            _ensure_column(conn, "realized_trades", "sell_offer_id", "INTEGER")
            _ensure_column(conn, "realized_trades", "sell_rec_id", "TEXT")
            _ensure_column(conn, "realized_trades", "buy_rec_id", "TEXT")

            _ensure_column(conn, "offer_instances", "rec_id", "TEXT")
            _ensure_column(conn, "offer_instances", "last_trade_ts", "INTEGER")

            _ensure_column(conn, "recommendations", "linked_offer_id", "INTEGER")
            _ensure_column(conn, "recommendations", "buy_first_fill_ts", "INTEGER")
            _ensure_column(conn, "recommendations", "buy_done_ts", "INTEGER")
            _ensure_column(conn, "recommendations", "buy_phase_seconds", "INTEGER")
            _ensure_column(conn, "recommendations", "first_sell_ts", "INTEGER")
            _ensure_column(conn, "recommendations", "last_sell_ts", "INTEGER")
            _ensure_column(conn, "recommendations", "sell_phase_seconds", "INTEGER")
            _ensure_column(conn, "recommendations", "realized_profit", "INTEGER")
            _ensure_column(conn, "recommendations", "realized_cost", "INTEGER")
            _ensure_column(conn, "recommendations", "realized_roi", "REAL")
            _ensure_column(conn, "recommendations", "realized_vs_expected", "REAL")
            _ensure_column(conn, "recommendations", "closed_ts", "INTEGER")
            _ensure_column(conn, "recommendations", "note", "TEXT")

            # Profit tracking schema migrations
            _ensure_column(conn, "pt_transactions", "tx_id", "TEXT")
            _ensure_column(conn, "pt_transactions", "display_name", "TEXT")
            _ensure_column(conn, "pt_transactions", "account_id", "INTEGER")
            _ensure_column(conn, "pt_transactions", "flip_uuid", "TEXT")
            _ensure_column(conn, "pt_transactions", "time", "INTEGER")
            _ensure_column(conn, "pt_transactions", "item_id", "INTEGER")
            _ensure_column(conn, "pt_transactions", "quantity", "INTEGER")
            _ensure_column(conn, "pt_transactions", "price", "INTEGER")
            _ensure_column(conn, "pt_transactions", "box_id", "INTEGER")
            _ensure_column(conn, "pt_transactions", "amount_spent", "INTEGER")
            _ensure_column(conn, "pt_transactions", "was_copilot_suggestion", "INTEGER")
            _ensure_column(conn, "pt_transactions", "copilot_price_used", "INTEGER")
            _ensure_column(conn, "pt_transactions", "login", "INTEGER")
            _ensure_column(conn, "pt_transactions", "raw_json", "TEXT")

            # Profit-tracking: pt_flips migration (older DBs may be missing newer columns)
            _ensure_column(conn, "pt_flips", "display_name", "TEXT")
            _ensure_column(conn, "pt_flips", "account_id", "INTEGER")
            _ensure_column(conn, "pt_flips", "item_id", "INTEGER")
            _ensure_column(conn, "pt_flips", "opened_time", "INTEGER")
            _ensure_column(conn, "pt_flips", "opened_qty", "INTEGER")
            _ensure_column(conn, "pt_flips", "spent", "INTEGER")
            _ensure_column(conn, "pt_flips", "closed_time", "INTEGER")
            _ensure_column(conn, "pt_flips", "closed_qty", "INTEGER")
            _ensure_column(conn, "pt_flips", "received_post_tax", "INTEGER")
            _ensure_column(conn, "pt_flips", "profit", "INTEGER")
            _ensure_column(conn, "pt_flips", "tax_paid", "INTEGER")
            _ensure_column(conn, "pt_flips", "status_ord", "INTEGER")
            _ensure_column(conn, "pt_flips", "flip_uuid", "TEXT")
            _ensure_column(conn, "pt_flips", "updated_time", "INTEGER")
            _ensure_column(conn, "pt_flips", "deleted", "INTEGER")
            try:
                conn.execute("UPDATE pt_flips SET flip_uuid = lower(hex(randomblob(16))) WHERE flip_uuid IS NULL OR flip_uuid = ''")
                conn.commit()
            except Exception:
                pass

            # Profit-tracking: pt_accounts migration
            _ensure_column(conn, "pt_accounts", "display_name", "TEXT")
            _ensure_column(conn, "pt_accounts", "account_id", "INTEGER")
            _ensure_column(conn, "pt_accounts", "created_ts", "INTEGER")


            # --- Indexes (safe) ---
            cur.execute("CREATE INDEX IF NOT EXISTS idx_offer_open ON offer_instances(box_id, done_ts)")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_offer_item ON offer_instances(item_id, done_ts)")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_buyfills_item_ts ON buy_fills(item_id, fill_ts)")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_trades_sellts ON realized_trades(sell_ts)")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_recs_item_ts ON recommendations(item_id, issued_ts)")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_recs_type_box_ts ON recommendations(rec_type, box_id, issued_ts)")

            conn.commit()
        finally:
            conn.close()

# ============================================================
# MATH / HELPERS
# ============================================================
def seller_tax(price: int, item_id: Optional[int] = None) -> int:
    """Estimate GE seller tax for profit displays.

    This mirrors ge_tax_per_unit() and includes the tax-free-under-price rule.
    """
    if price <= 0:
        return 0
    p = int(price)

    # New rule: low-priced items are tax-free
    if p < GE_TAX_FREE_UNDER_PRICE:
        return 0

    if item_id is not None and int(item_id) in GE_TAX_EXEMPT_ITEM_IDS:
        return 0

    if p >= MAX_PRICE_FOR_GE_TAX:
        return GE_TAX_CAP

    tax = int(math.floor(p * SELLER_TAX_RATE))
    # Legacy cap (defaults to 5m) — kept for compatibility
    cap = int(os.getenv("SWAGFLIP_SELLER_TAX_CAP", "5000000"))
    return min(tax, cap)

def estimate_minutes_from_daily(qty: int, daily_vol: Optional[int]) -> float:
    if daily_vol is None or daily_vol <= 0:
        return 999999.0
    per_min = max(daily_vol / 1440.0, 1e-6)
    return qty / per_min

def min_profitable_sell_price(avg_buy: int) -> int:
    if avg_buy <= 0:
        return 1
    guess = int(math.ceil((avg_buy + 1) / 0.98))
    start = max(1, guess - 30)
    for p in range(start, guess + 500):
        if p - avg_buy - seller_tax(p) >= 1:
            return p
    return max(guess, 1)

def offer_is_empty(o: Dict[str, Any]) -> bool:
    return str(o.get("status", "")).lower() == "empty"

def offer_is_done(o: Dict[str, Any]) -> bool:
    return (str(o.get("status", "")).lower() != "empty") and (not bool(o.get("active", False)))

def offer_is_buy(o: Dict[str, Any]) -> bool:
    return str(o.get("status", "")).lower() == "buy"

def offer_is_sell(o: Dict[str, Any]) -> bool:
    return str(o.get("status", "")).lower() == "sell"


def offer_is_active(o: Dict[str, Any]) -> bool:
    # Payloads usually contain "active". If missing, treat non-empty/non-done as active.
    if bool(o.get("active", False)):
        return True
    return (not offer_is_empty(o)) and (not offer_is_done(o))

def offer_box_id(o: Dict[str, Any]) -> int:
    try:
        return int(o.get("box_id") or o.get("boxId") or o.get("slot") or 0)
    except Exception:
        return 0

def offer_item_id(o: Dict[str, Any]) -> int:
    try:
        return int(o.get("item_id") or o.get("itemId") or 0)
    except Exception:
        return 0

def offer_price_gp(o: Dict[str, Any]) -> int:
    try:
        return int(o.get("price") or o.get("price_gp") or o.get("priceGp") or 0)
    except Exception:
        return 0

def offer_amount_total(o: Dict[str, Any]) -> int:
    try:
        return int(o.get("amount_total") or o.get("amountTotal") or o.get("amount") or o.get("quantity") or 0)
    except Exception:
        return 0

def item_name_safe(item_id: int) -> str:
    try:
        mapping, _latest, _vol, _t = prices.snapshot()
        meta = mapping.get(int(item_id))
        if meta and getattr(meta, "name", None):
            return str(meta.name)
    except Exception:
        pass
    return f"Item {item_id}"

def latest_low_high(item_id: int) -> Tuple[int, int]:
    try:
        _mapping, latest, _vol, _t = prices.snapshot()
        row = latest.get(int(item_id)) or {}
        low = int(row.get("low") or 0)
        high = int(row.get("high") or 0)
        return low, high
    except Exception:
        return 0, 0

def first_empty_slot_id(offers: List[Dict[str, Any]]) -> Optional[int]:
    for o in offers:
        if offer_is_empty(o):
            try:
                return int(o.get("box_id", 0))
            except Exception:
                return 0
    return None

def active_offer_item_ids(offers: List[Dict[str, Any]]) -> Set[int]:
    s: Set[int] = set()
    for o in offers:
        if bool(o.get("active", False)):
            try:
                iid = int(o.get("item_id", 0))
                if iid > 0:
                    s.add(iid)
            except Exception:
                pass
    return s

def _requested_types(status: Dict[str, Any]) -> Set[str]:
    try:
        arr = status.get("requested_suggestion_types") or []
        return {str(x).lower() for x in arr if x}
    except Exception:
        return set()

def _type_allowed(requested: Set[str], t: str) -> bool:
    return (not requested) or (t in requested)


def _status_timeframe_minutes(status: Dict[str, Any]) -> int:
    """How often the client wants to adjust offers (minutes).
    RuneLite UI presets: 5, 30, 120, 480 (5m, 30m, 2h, 8h).
    """
    tf = None
    try:
        tf = status.get("timeframe")
    except Exception:
        tf = None

    if tf is None:
        return max(1, int(round(TARGET_FILL_MINUTES)))

    try:
        if isinstance(tf, str):
            s = tf.strip().lower()
            if s.endswith("m"):
                tfm = int(float(s[:-1]))
            elif s.endswith("h"):
                tfm = int(float(s[:-1]) * 60)
            else:
                tfm = int(float(s))
        else:
            tfm = int(tf)
    except Exception:
        tfm = max(1, int(round(TARGET_FILL_MINUTES)))

    if tfm <= 0:
        tfm = max(1, int(round(TARGET_FILL_MINUTES)))

    # clamp to something sane (up to 24h)
    return max(1, min(tfm, 24 * 60))


# ============================================================
# LEDGER (queue only)
# ============================================================
def load_ledger() -> Dict[str, Any]:
    # Queue-only file; all trade history is in SQLite.
    if not os.path.exists(LEDGER_PATH):
        return {"buy_queue": [], "action_queue": []}
    try:
        with open(LEDGER_PATH, "r", encoding="utf-8") as f:
            led = json.load(f) or {}
        led.setdefault("buy_queue", [])
        led.setdefault("action_queue", [])
        return led
    except Exception:
        return {"buy_queue": [], "action_queue": []}

def save_ledger(ledger: Dict[str, Any]) -> None:
    tmp = LEDGER_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(ledger, f, indent=2)
    os.replace(tmp, LEDGER_PATH)

# ============================================================
# COMMAND BUILDERS (internal JSON shape)
# ============================================================
def build_wait(msg: str) -> Dict[str, Any]:
    return {
        "type": "wait",
        "box_id": 0,
        "item_id": -1,
        "price": 0,
        "quantity": 0,
        "name": "",
        "command_id": 0,
        "message": msg,
        "expectedProfit": 0.0,
        "expectedDuration": 0.0,
    }

def build_buy(box_id: int, item_id: int, name: str, price: int, qty: int,
              exp_profit: float, exp_min: float, note: str = "") -> Dict[str, Any]:
    rec_id = uuid.uuid4().hex
    msg = f"Buy {qty} {name} @ {price}"
    if note:
        msg += f" — {note}"
    return {
        "type": "buy",
        "rec_id": rec_id,
        "issued_unix": int(time.time()),
        "box_id": int(box_id),
        "item_id": int(item_id),
        "price": int(price),
        "quantity": int(qty),
        "name": name,
        "command_id": 1,
        "message": msg,
        "expectedProfit": float(exp_profit),
        "expectedDuration": float(exp_min),
        "note": note,
    }

def build_sell(box_id: int, item_id: int, name: str, price: int, qty: int,
                exp_profit: float, exp_min: float, note: str = "") -> Dict[str, Any]:
    rec_id = uuid.uuid4().hex
    msg = f"Sell {qty} {name} @ {price}"
    if note:
        msg += f" — {note}"
    return {
        "type": "sell",
        "rec_id": rec_id,
        "issued_unix": int(time.time()),
        "box_id": int(box_id),
        "item_id": int(item_id),
        "price": int(price),
        "quantity": int(qty),
        "name": name,
        "command_id": 2,
        "message": msg,
        "expectedProfit": float(exp_profit),
        "expectedDuration": float(exp_min),
        "note": note,
    }

def build_abort(box_id: int, item_id: int, name: str, reason: str) -> Dict[str, Any]:
    rec_id = uuid.uuid4().hex
    msg = f"ABORT slot {box_id}: {reason}"
    return {
        "type": "abort",
        "rec_id": rec_id,
        "issued_unix": int(time.time()),
        "box_id": int(box_id),
        "item_id": int(item_id),
        "price": 0,
        "quantity": 0,
        "name": name,
        "command_id": 3,
        "message": msg,
        "expectedProfit": 0.0,
        "expectedDuration": 0.0,
        "note": reason,
    }

# ============================================================
# MSGPACK ENCODERS FOR THE JAVA CLIENT
# ============================================================
def _wants_msgpack() -> bool:
    accept = (request.headers.get("Accept") or "").lower()
    return "application/x-msgpack" in accept

def _suggestion_to_msgpack(action: Dict[str, Any]) -> bytes:
    """
    Java expects keys: t,b,i,p,q,n,id,m,ed,ep,(gd optional)
    """
    payload = {
        "t": str(action.get("type", "")),
        "b": int(action.get("box_id", 0)),
        "i": int(action.get("item_id", 0)),
        "p": int(action.get("price", 0)),
        "q": int(action.get("quantity", 0)),
        "n": str(action.get("name", "")),
        "id": int(action.get("command_id", 0)),
        "m": str(action.get("message", "")),
        "ed": float(action.get("expectedDuration", 0.0)),
        "ep": float(action.get("expectedProfit", 0.0)),
    }
    return msgpack.packb(payload, use_bin_type=True)

def _item_price_to_msgpack(buy_price: int, sell_price: int, message: str = "") -> bytes:
    """
    Java expects keys: bp, sp, m, (gd optional)
    """
    payload = {
        "bp": int(buy_price),
        "sp": int(sell_price),
        "m": str(message or ""),
        # omit "gd" (graph data) for now; plugin handles missing graph
    }
    return msgpack.packb(payload, use_bin_type=True)

def _visualize_flip_response_to_msgpack() -> bytes:
    """
    Java expects keys: bt,bv,bp,st,sv,sp,(gd optional)
    We'll return empty series so the UI doesn't error.
    """
    payload = {"bt": [], "bv": [], "bp": [], "st": [], "sv": [], "sp": []}
    return msgpack.packb(payload, use_bin_type=True)

# ============================================================
# RECOMMENDATION RECORDING (for ML)
# ============================================================
def record_recommendation(action: Dict[str, Any]) -> None:
    t = str(action.get("type", "")).lower()
    if t not in ("buy", "sell", "abort"):
        return
    rec_id = str(action.get("rec_id", "")).strip()
    if not rec_id:
        return

    issued_ts = int(action.get("issued_unix") or time.time())
    box_id = int(action.get("box_id") or 0)
    item_id = int(action.get("item_id") or 0)
    item_name = str(action.get("name") or item_id)
    price = int(action.get("price") or 0)
    qty = int(action.get("quantity") or 0)
    exp_profit = float(action.get("expectedProfit") or 0.0)
    exp_dur = float(action.get("expectedDuration") or 0.0)
    note = str(action.get("note") or "")

    with _db_lock:
        conn = db_connect()
        try:
            cur = conn.cursor()
            cur.execute("""
                INSERT OR IGNORE INTO recommendations (
                    rec_id, issued_ts, rec_type, box_id, item_id, item_name, price, qty,
                    expected_profit, expected_duration, note,
                    linked_offer_id, outcome_status,
                    buy_first_fill_ts, buy_done_ts, buy_phase_seconds,
                    first_sell_ts, last_sell_ts, sell_phase_seconds,
                    realized_profit, realized_cost, realized_roi, realized_vs_expected,
                    closed_ts
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, NULL, 'issued',
                          NULL, NULL, NULL, NULL, NULL, NULL,
                          NULL, NULL, NULL, NULL, NULL)
            """, (
                rec_id, issued_ts, t, box_id, item_id, item_name, price, qty,
                exp_profit, exp_dur, note
            ))
            conn.commit()
        finally:
            conn.close()

def should_throttle_abort(conn: sqlite3.Connection, box_id: int, now: int) -> bool:
    cur = conn.cursor()
    cur.execute("""
        SELECT issued_ts
        FROM recommendations
        WHERE rec_type = 'abort' AND box_id = ?
        ORDER BY issued_ts DESC
        LIMIT 1
    """, (int(box_id),))
    row = cur.fetchone()
    if not row:
        return False
    last_ts = int(row["issued_ts"])
    return (now - last_ts) < ABORT_COOLDOWN_SECONDS

# ============================================================
# OFFER INSTANCE + FILL SYNC (tracks actual fills + phases)
# ============================================================
def get_open_offer_instance(conn: sqlite3.Connection, box_id: int) -> Optional[sqlite3.Row]:
    cur = conn.cursor()
    cur.execute("""
        SELECT *
        FROM offer_instances
        WHERE box_id = ? AND done_ts IS NULL
        ORDER BY offer_id DESC
        LIMIT 1
    """, (int(box_id),))
    return cur.fetchone()

def close_offer_instance(conn: sqlite3.Connection, offer_id: int, now: int) -> None:
    cur = conn.cursor()
    cur.execute("""
        UPDATE offer_instances
        SET done_ts = COALESCE(done_ts, ?), last_seen_ts = ?
        WHERE offer_id = ?
    """, (int(now), int(now), int(offer_id)))

def create_offer_instance(conn: sqlite3.Connection, box_id: int, status: str, item_id: int,
                          price: int, amount_total: int, traded: int, active: bool, now: int) -> int:
    cur = conn.cursor()
    first_fill_ts = int(now) if int(traded) > 0 else None
    last_trade_ts = int(now) if int(traded) > 0 else None
    cur.execute("""
        INSERT INTO offer_instances (
            box_id, status, item_id, price, amount_total,
            start_ts, first_fill_ts, done_ts, last_seen_ts,
            last_traded, last_trade_ts, active, rec_id
        ) VALUES (?, ?, ?, ?, ?, ?, ?, NULL, ?, ?, ?, ?, NULL)
    """, (
        int(box_id), str(status), int(item_id), int(price), int(amount_total),
        int(now), first_fill_ts,
        int(now), int(traded), last_trade_ts, 1 if active else 0
    ))
    return int(cur.lastrowid)

def maybe_link_offer_to_recent_rec(conn: sqlite3.Connection, status: str,
                                   box_id: int, item_id: int, now: int) -> Optional[str]:
    cur = conn.cursor()
    cur.execute("""
        SELECT rec_id
        FROM recommendations
        WHERE rec_type = ?
          AND box_id = ?
          AND item_id = ?
          AND linked_offer_id IS NULL
          AND outcome_status IN ('issued')
          AND issued_ts >= ?
        ORDER BY issued_ts DESC
        LIMIT 1
    """, (status, int(box_id), int(item_id), int(now) - 15 * 60))
    row = cur.fetchone()
    if not row:
        return None
    return str(row["rec_id"])

def db_insert_lot(conn: sqlite3.Connection, item_id: int, item_name: str, buy_price: int,
                  qty: int, buy_ts: int, buy_offer_id: int, buy_rec_id: Optional[str]) -> None:
    tx = uuid.uuid4().hex
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO lots (tx_id, item_id, item_name, buy_price, qty_total, qty_remaining, buy_ts, buy_offer_id, buy_rec_id)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (tx, int(item_id), str(item_name), int(buy_price), int(qty), int(qty), int(buy_ts), int(buy_offer_id), buy_rec_id))

def db_insert_buy_fill(conn: sqlite3.Connection, item_id: int, item_name: str, buy_price: int,
                        qty: int, fill_ts: int, offer_id: int, rec_id: Optional[str]) -> None:
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO buy_fills (item_id, item_name, qty, buy_price, fill_ts, offer_id, rec_id)
        VALUES (?, ?, ?, ?, ?, ?, ?)
    """, (int(item_id), str(item_name), int(qty), int(buy_price), int(fill_ts), int(offer_id), rec_id))

def db_open_qty_and_avg_cost(conn: sqlite3.Connection, item_id: int) -> Tuple[int, int, int]:
    cur = conn.cursor()
    cur.execute("""
        SELECT
          COALESCE(SUM(qty_remaining), 0) AS q,
          COALESCE(SUM(qty_remaining * buy_price), 0) AS v
        FROM lots
        WHERE item_id = ? AND qty_remaining > 0
    """, (int(item_id),))
    row = cur.fetchone()
    q = int(row["q"]) if row else 0
    v = int(row["v"]) if row else 0
    avg = int(v / q) if q > 0 else 0
    return q, avg, v

def db_consume_lots_fifo_for_sell(conn: sqlite3.Connection, item_id: int, sell_price: int,
                                  sell_qty: int, sell_ts: int, sell_offer_id: int,
                                  sell_rec_id: Optional[str]) -> int:
    cur = conn.cursor()
    qty_left = int(sell_qty)
    consumed = 0

    while qty_left > 0:
        cur.execute("""
            SELECT tx_id, item_name, buy_price, qty_remaining, buy_ts, buy_rec_id
            FROM lots
            WHERE item_id = ? AND qty_remaining > 0
            ORDER BY buy_ts ASC
            LIMIT 1
        """, (int(item_id),))
        lot = cur.fetchone()
        if not lot:
            break

        take = min(qty_left, int(lot["qty_remaining"]))
        if take <= 0:
            break

        buy_price = int(lot["buy_price"])
        buy_ts = int(lot["buy_ts"])
        buy_rec_id = lot["buy_rec_id"]

        tax = ge_tax_per_unit(item_id, sell_price)
        profit_per = sell_price - buy_price - tax
        profit = profit_per * take

        cur.execute("""
            INSERT INTO realized_trades (
                item_id, item_name, qty, buy_price, sell_price, buy_ts, sell_ts, profit,
                sell_offer_id, sell_rec_id, buy_rec_id
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            int(item_id), str(lot["item_name"]), int(take), int(buy_price),
            int(sell_price), int(buy_ts), int(sell_ts), int(profit),
            int(sell_offer_id), sell_rec_id, buy_rec_id
        ))

        new_rem = int(lot["qty_remaining"]) - take
        if new_rem <= 0:
            cur.execute("DELETE FROM lots WHERE tx_id = ?", (str(lot["tx_id"]),))
        else:
            cur.execute("UPDATE lots SET qty_remaining = ? WHERE tx_id = ?", (int(new_rem), str(lot["tx_id"])))

        qty_left -= take
        consumed += take

    return consumed

def db_bought_qty_in_window(conn: sqlite3.Connection, item_id: int, cutoff_ts: int) -> int:
    cur = conn.cursor()
    cur.execute("""
        SELECT COALESCE(SUM(qty), 0) AS s
        FROM buy_fills
        WHERE item_id = ? AND fill_ts >= ?
    """, (int(item_id), int(cutoff_ts)))
    row = cur.fetchone()
    return int(row["s"]) if row else 0

def update_recommendation_outcomes(conn: sqlite3.Connection, now: int) -> None:
    cur = conn.cursor()

    # timeout failures (buy recs with no fill)
    cur.execute("""
        SELECT rec_id, issued_ts
        FROM recommendations
        WHERE rec_type = 'buy'
          AND outcome_status IN ('issued','linked')
          AND (buy_first_fill_ts IS NULL)
    """)
    for row in cur.fetchall():
        rec_id = str(row["rec_id"])
        issued_ts = int(row["issued_ts"])
        if now - issued_ts >= BUY_REC_TIMEOUT_SECONDS:
            cur.execute("""
                UPDATE recommendations
                SET outcome_status = 'failed_no_fill',
                    closed_ts = ?
                WHERE rec_id = ? AND outcome_status IN ('issued','linked')
            """, (int(now), rec_id))

    # rolling realized metrics for buy recs
    cur.execute("""
        SELECT rec_id, expected_profit
        FROM recommendations
        WHERE rec_type = 'buy'
          AND outcome_status NOT LIKE 'failed_%'
          AND outcome_status != 'completed'
    """)
    for r in cur.fetchall():
        rec_id = str(r["rec_id"])
        expected_profit = float(r["expected_profit"] or 0.0)

        cur.execute("SELECT COALESCE(SUM(qty),0) AS q FROM buy_fills WHERE rec_id = ?", (rec_id,))
        bought_qty = int(cur.fetchone()["q"])
        if bought_qty <= 0:
            continue

        cur.execute("SELECT COALESCE(SUM(qty_remaining),0) AS q FROM lots WHERE buy_rec_id = ?", (rec_id,))
        remaining_qty = int(cur.fetchone()["q"])

        cur.execute("""
            SELECT
              COALESCE(SUM(profit), 0) AS p,
              COALESCE(SUM(qty * buy_price), 0) AS c,
              MIN(sell_ts) AS fst,
              MAX(sell_ts) AS lst
            FROM realized_trades
            WHERE buy_rec_id = ?
        """, (rec_id,))
        s = cur.fetchone()
        realized_profit = int(s["p"] or 0)
        realized_cost = int(s["c"] or 0)
        first_sell_ts = int(s["fst"]) if s["fst"] is not None else None
        last_sell_ts = int(s["lst"]) if s["lst"] is not None else None

        realized_roi = (realized_profit / realized_cost) if realized_cost > 0 else None
        realized_vs_expected = (realized_profit / expected_profit) if expected_profit > 0 else None
        sell_phase_seconds = (last_sell_ts - first_sell_ts) if (first_sell_ts and last_sell_ts) else None

        cur.execute("""
            UPDATE recommendations
            SET realized_profit = ?,
                realized_cost = ?,
                realized_roi = ?,
                realized_vs_expected = ?,
                first_sell_ts = ?,
                last_sell_ts = ?,
                sell_phase_seconds = ?
            WHERE rec_id = ?
        """, (
            realized_profit, realized_cost, realized_roi, realized_vs_expected,
            first_sell_ts, last_sell_ts, sell_phase_seconds, rec_id
        ))

        if remaining_qty <= 0 and last_sell_ts is not None:
            cur.execute("""
                UPDATE recommendations
                SET outcome_status = 'completed',
                    closed_ts = COALESCE(closed_ts, ?)
                WHERE rec_id = ? AND outcome_status NOT LIKE 'failed_%'
            """, (int(last_sell_ts), rec_id))

    # buy phase from linked offer_instances (if present)
    cur.execute("""
        SELECT r.rec_id, r.linked_offer_id
        FROM recommendations r
        WHERE r.rec_type = 'buy'
          AND r.linked_offer_id IS NOT NULL
          AND (r.buy_phase_seconds IS NULL)
          AND r.outcome_status NOT LIKE 'failed_%'
    """)
    for row in cur.fetchall():
        rec_id = str(row["rec_id"])
        offer_id = int(row["linked_offer_id"])
        cur.execute("SELECT first_fill_ts, done_ts FROM offer_instances WHERE offer_id = ?", (offer_id,))
        o = cur.fetchone()
        if not o:
            continue
        ff = int(o["first_fill_ts"]) if o["first_fill_ts"] is not None else None
        dn = int(o["done_ts"]) if o["done_ts"] is not None else None
        if ff and dn and dn >= ff:
            cur.execute("""
                UPDATE recommendations
                SET buy_first_fill_ts = COALESCE(buy_first_fill_ts, ?),
                    buy_done_ts = COALESCE(buy_done_ts, ?),
                    buy_phase_seconds = COALESCE(buy_phase_seconds, ?),
                    outcome_status = CASE
                        WHEN outcome_status IN ('linked','issued','buy_started') THEN 'buy_done'
                        ELSE outcome_status
                    END
                WHERE rec_id = ?
            """, (ff, dn, dn - ff, rec_id))
        elif ff and not dn:
            cur.execute("""
                UPDATE recommendations
                SET buy_first_fill_ts = COALESCE(buy_first_fill_ts, ?),
                    outcome_status = CASE
                        WHEN outcome_status IN ('linked','issued') THEN 'buy_started'
                        ELSE outcome_status
                    END
                WHERE rec_id = ?
            """, (ff, rec_id))

def sync_offers_and_fills(mapping: Dict[int, ItemMeta], offers: List[Dict[str, Any]]) -> None:
    now = int(time.time())

    with _db_lock:
        conn = db_connect()
        try:
            cur = conn.cursor()

            for o in offers:
                try:
                    box_id = int(o.get("box_id", 0))
                except Exception:
                    box_id = 0

                status = str(o.get("status", "")).lower()
                active = bool(o.get("active", False))

                if status == "empty":
                    open_inst = get_open_offer_instance(conn, box_id)
                    if open_inst is not None:
                        # If a linked buy offer is cancelled with 0 fills, mark as failed_cancelled
                        rec = open_inst["rec_id"]
                        if rec and str(open_inst["status"]) == "buy" and int(open_inst["last_traded"]) == 0:
                            cur.execute("""
                                UPDATE recommendations
                                SET outcome_status = 'failed_cancelled',
                                    closed_ts = ?
                                WHERE rec_id = ? AND outcome_status NOT LIKE 'failed_%' AND outcome_status != 'completed'
                            """, (int(now), str(rec)))
                        close_offer_instance(conn, int(open_inst["offer_id"]), now)
                    continue

                if status not in ("buy", "sell"):
                    continue

                try:
                    item_id = int(o.get("item_id", 0))
                    price = int(o.get("price", 0))
                    amount_total = int(o.get("amount_total", 0))
                    traded = int(o.get("amount_traded", 0))
                except Exception:
                    continue

                if item_id <= 0 or price <= 0 or amount_total < 0 or traded < 0:
                    continue

                open_inst = get_open_offer_instance(conn, box_id)
                if open_inst is None:
                    offer_id = create_offer_instance(conn, box_id, status, item_id, price, amount_total, traded, active, now)
                else:
                    old_status = str(open_inst["status"])
                    old_item = int(open_inst["item_id"])
                    old_total = int(open_inst["amount_total"])
                    if old_status != status or old_item != item_id or old_total != amount_total:
                        close_offer_instance(conn, int(open_inst["offer_id"]), now)
                        offer_id = create_offer_instance(conn, box_id, status, item_id, price, amount_total, traded, active, now)
                    else:
                        offer_id = int(open_inst["offer_id"])

                cur.execute("SELECT rec_id, last_traded, first_fill_ts FROM offer_instances WHERE offer_id = ?", (offer_id,))
                inst_row = cur.fetchone()
                inst_rec = inst_row["rec_id"] if inst_row else None
                prev_traded = int(inst_row["last_traded"]) if inst_row else 0
                prev_first_fill = inst_row["first_fill_ts"] if inst_row else None

                if inst_rec is None:
                    inst_rec = maybe_link_offer_to_recent_rec(conn, status, box_id, item_id, now)
                    if inst_rec:
                        cur.execute("UPDATE offer_instances SET rec_id = ? WHERE offer_id = ? AND rec_id IS NULL", (inst_rec, offer_id))
                        cur.execute("""
                            UPDATE recommendations
                            SET linked_offer_id = ?, outcome_status = 'linked'
                            WHERE rec_id = ? AND linked_offer_id IS NULL
                        """, (int(offer_id), inst_rec))

                delta = traded - prev_traded
                new_last_trade_ts = now if delta > 0 else None

                if delta > 0:
                    name = mapping[item_id].name if item_id in mapping else str(item_id)
                    if status == "buy":
                        db_insert_lot(conn, item_id, name, price, delta, now, offer_id, inst_rec)
                        db_insert_buy_fill(conn, item_id, name, price, delta, now, offer_id, inst_rec)
                    else:
                        db_consume_lots_fifo_for_sell(conn, item_id, price, delta, now, offer_id, inst_rec)

                first_fill_ts = None
                if prev_first_fill is not None:
                    first_fill_ts = int(prev_first_fill)
                elif traded > 0:
                    first_fill_ts = now

                done_ts = None
                if (not active) or (amount_total > 0 and traded >= amount_total):
                    done_ts = now

                cur.execute("""
                    UPDATE offer_instances
                    SET price = ?,
                        amount_total = ?,
                        first_fill_ts = COALESCE(first_fill_ts, ?),
                        done_ts = COALESCE(done_ts, ?),
                        last_seen_ts = ?,
                        last_traded = ?,
                        last_trade_ts = COALESCE(?, last_trade_ts),
                        active = ?,
                        rec_id = COALESCE(rec_id, ?)
                    WHERE offer_id = ?
                """, (
                    int(price), int(amount_total), first_fill_ts, done_ts,
                    int(now), int(traded),
                    new_last_trade_ts,
                    1 if active else 0, inst_rec, int(offer_id)
                ))

            update_recommendation_outcomes(conn, now)
            conn.commit()
        finally:
            conn.close()

# ============================================================
# CRASH GUARD: reprice active sell offers while still profitable
# ============================================================
def maybe_reprice_active_sell(mapping: Dict[int, ItemMeta], latest: Dict[int, Dict[str, Any]],
                              volumes: Dict[int, int], offers: List[Dict[str, Any]], stale_seconds: int) -> Optional[Dict[str, Any]]:
    """Crash-guard active sells.

    If a SELL offer is priced meaningfully above the current market and it has not traded for the
    user's selected "Adjust offers" timeframe, suggest an abort/relist at a more realistic price.

    **Important tweak (your request):**
    - If the offer is "crashing" such that we *cannot* reprice profitably (below your basis after tax),
      we STILL return an **ABORT** suggestion (red highlight) — same behavior as stale-offer aborts.
      In that case we do **not** queue a relist.
    """
    now = _now()

    for o in offers:
        try:
            if not bool(o.get("active", False)):
                continue
            if not offer_is_sell(o):
                continue

            iid = offer_item_id(o)
            box_id = offer_box_id(o)
            offer_price = offer_price_gp(o)
            total = int(o.get("amount_total") or 0)
            traded = int(o.get("amount_traded") or 0)
        except Exception:
            continue

        if iid <= 0 or offer_price <= 0 or box_id <= 0:
            continue

        remaining = max(total - traded, 0)
        if remaining <= 0:
            continue

        # Respect adjust-offers timeframe: don't reprice too often.
        if stale_seconds:
            no_trade_for = 0
            try:
                with _db_lock:
                    conn = db_connect()
                    try:
                        cur = conn.cursor()
                        cur.execute(
                            "SELECT COALESCE(last_trade_ts, start_ts) AS last_ts "
                            "FROM offer_instances WHERE box_id = ? AND done_ts IS NULL "
                            "ORDER BY start_ts DESC LIMIT 1",
                            (box_id,),
                        )
                        row = cur.fetchone()
                        if row and row["last_ts"]:
                            no_trade_for = max(0, now - int(row["last_ts"]))
                    finally:
                        conn.close()
            except Exception:
                no_trade_for = 0

            if no_trade_for < stale_seconds:
                continue

        lp = latest.get(iid) or {}
        try:
            high = int(lp.get("high") or 0)
            low = int(lp.get("low") or 0)
        except Exception:
            continue

        if high <= 0 or low <= 0:
            continue

        name = mapping[iid].name if iid in mapping else str(iid)

        with _db_lock:
            conn = db_connect()
            try:
                open_qty, avg_buy, _ = db_open_qty_and_avg_cost(conn, iid)
            finally:
                conn.close()

        avg_buy = avg_buy or low

        # If we're only slightly above market, don't touch it.
        target_market = max(1, high - 1)
        if offer_price <= target_market + 2:
            continue

        # Nudge down: either near market, or a 1% cut, whichever is higher.
        desired = max(target_market, int(offer_price * 0.99))
        desired = min(desired, offer_price - 1)

        profit_per = desired - avg_buy - ge_tax_per_unit(iid, desired)

        # Cooldown so we don't spam abort every tick
        with _db_lock:
            conn = db_connect()
            try:
                if should_throttle_abort(conn, box_id=box_id, now=now):
                    continue
            finally:
                conn.close()

        # If we'd be selling below our basis after tax, still suggest ABORT (red), but don't relist.
        if profit_per <= 0:
            if avg_buy > low:
                with _db_lock:
                    conn = db_connect()
                    try:
                        note_abort(conn, box_id=box_id, item_id=iid, now=now)
                    finally:
                        conn.close()
                return build_abort(box_id, iid, name, "crash-guard: market moved below basis (abort; no profitable relist)")
            continue

        # Ask user to abort/cancel so we can re-list at a better price (plugin can't 'edit' an offer).
        with _db_lock:
            conn = db_connect()
            try:
                note_abort(conn, box_id=box_id, item_id=iid, now=now)
            finally:
                conn.close()

        abort_action = build_abort(box_id, iid, name, f"reprice sell -> {desired}gp (crash-guard)")
        try:
            mins = estimate_minutes_from_daily(remaining, volumes.get(iid))
            exp_profit = float(max(profit_per, 0) * remaining)
            queued = build_sell(0, iid, name, int(desired), int(remaining), exp_profit, mins, note="relist after abort (crash-guard)")
            abort_action["_queue_action"] = queued
        except Exception:
            pass
        return abort_action

    return None
def maybe_handle_stale_offers(status_payload: Dict[str, Any],
                              mapping: Dict[int, ItemMeta],
                              latest: Dict[int, Dict[str, Any]],
                              volumes: Dict[int, int],
                              offers: List[Dict[str, Any]],
                              coins: int,
                              inv: List[Tuple[int, int]],
                              inv_full: bool) -> Optional[Dict[str, Any]]:
    now = int(time.time())
    requested = _requested_types(status_payload)
    tf_min = _status_timeframe_minutes(status_payload)
    stale_seconds = max(STALE_OFFER_SECONDS, tf_min * 60)

    for o in offers:
        try:
            if not bool(o.get("active", False)):
                continue
            st = str(o.get("status", "")).lower()
            if st not in ("buy", "sell"):
                continue
            box_id = int(o.get("box_id", 0))
            item_id = int(o.get("item_id", 0))
            price = int(o.get("price", 0))
            total = int(o.get("amount_total", 0))
            traded = int(o.get("amount_traded", 0))
        except Exception:
            continue

        if item_id <= 0 or price <= 0:
            continue

        with _db_lock:
            conn = db_connect()
            try:
                inst = get_open_offer_instance(conn, box_id)
                if not inst:
                    continue

                start_ts = int(inst["start_ts"] or now)
                last_trade_ts = inst["last_trade_ts"]
                last_ts = int(last_trade_ts) if last_trade_ts is not None else start_ts
                no_trade_for = now - last_ts

                if no_trade_for < stale_seconds:
                    continue

                name = mapping[item_id].name if item_id in mapping else str(item_id)

                # Stale SELL: fast-dump to low while still profitable (if we have tracked cost basis)
                if st == "sell":
                    # If sells aren't allowed right now, consider abort if allowed
                    if not _type_allowed(requested, "sell"):
                        if _type_allowed(requested, "abort"):
                            inv_has_item = any(i == item_id for i, _ in inv)
                            can_abort_sell = (not inv_full) or inv_has_item
                            if can_abort_sell and (not should_throttle_abort(conn, box_id, now)):
                                return build_abort(box_id, item_id, name, f"stale sell > {stale_seconds}s")
                        continue

                    remaining = max(total - traded, 0)
                    if remaining <= 0:
                        continue

                    lp = latest.get(item_id) or {}
                    try:
                        low = int(lp.get("low", 0))
                        high = int(lp.get("high", 0))
                    except Exception:
                        continue
                    if low <= 0 or high <= 0:
                        continue

                    open_qty, avg_buy, _ = db_open_qty_and_avg_cost(conn, item_id)
                    if open_qty > 0 and avg_buy > 0:
                        min_profit_price = min_profitable_sell_price(avg_buy)
                        desired = max(low, min_profit_price)

                        if desired < price:
                            mins = estimate_minutes_from_daily(remaining, volumes.get(item_id))
                            profit_per = desired - avg_buy - ge_tax_per_unit(item_id, desired)
                            exp_profit = float(max(profit_per, 0) * remaining)
                            return_action = build_abort(box_id, item_id, name, f"stale sell > {stale_seconds}s (relist @ {desired}gp)")
                            try:
                                queued = build_sell(0, item_id, name, int(desired), int(remaining), exp_profit, mins, note=f"stale>{stale_seconds}s relist after abort")
                                return_action["_queue_action"] = queued
                            except Exception:
                                pass
                            return return_action

                    # If we can't reprice down (or no basis), abort if allowed and safe
                    if _type_allowed(requested, "abort"):
                        inv_has_item = any(i == item_id for i, _ in inv)
                        can_abort_sell = (not inv_full) or inv_has_item
                        if can_abort_sell and (not should_throttle_abort(conn, box_id, now)):
                            return build_abort(box_id, item_id, name, f"stale sell > {stale_seconds}s (no trades)")
                    continue

                # Stale BUY: abort to free cash/slot
                if st == "buy":
                    if not _type_allowed(requested, "abort"):
                        continue

                    can_abort_buy = (not inv_full) or (coins > 0)
                    if not can_abort_buy:
                        continue

                    if should_throttle_abort(conn, box_id, now):
                        continue

                    return build_abort(box_id, item_id, name, f"stale buy > {stale_seconds}s (no trades)")

            finally:
                conn.close()

    return None

# ============================================================
# PROFIT TRACKING (durable SQLite + binary formats the client expects)
# ============================================================
_profit_lock = threading.Lock()

_db_lock = threading.RLock()

def _stable_account_id(display_name: str) -> int:
    # Python's built-in hash() is randomized per-process; use a stable hash instead.
    dn = (display_name or "").strip().lower()
    if not dn:
        dn = "default"
    aid = (zlib.crc32(dn.encode("utf-8")) & 0x7fffffff)
    return aid if aid != 0 else 1

def _pt_get_or_create_account(conn: sqlite3.Connection, display_name: str) -> int:
    """
    Returns an account_id for the given display_name.

    By default, profit tracking is keyed by account_id (used by /client-flips-delta).
    To make switching characters painless, we support:
      - Explicit aliases via SWAGFLIP_PT_ALIASES ("new=old")
      - Auto-merge when there is exactly ONE existing account and SWAGFLIP_PT_MERGE_SINGLE_ACCOUNT=true
    """
    dn_raw = (display_name or "").strip() or "default"
    dn_can = _canonical_display_name(dn_raw)
    now = int(time.time())
    cur = conn.cursor()

    # Exact match
    cur.execute("SELECT account_id FROM pt_accounts WHERE display_name = ?", (dn_raw,))
    row = cur.fetchone()
    if row:
        return int(row["account_id"])

    # Alias to canonical display name if it already exists
    if dn_can != dn_raw:
        cur.execute("SELECT account_id FROM pt_accounts WHERE display_name = ?", (dn_can,))
        row = cur.fetchone()
        if row:
            aid = int(row["account_id"])
            cur.execute(
                "INSERT OR REPLACE INTO pt_accounts(display_name, account_id, created_ts) VALUES(?,?,?)",
                (dn_raw, aid, now),
            )
            conn.commit()
            return aid

    # Auto-merge if there's exactly one existing account_id
    if PT_MERGE_SINGLE_ACCOUNT:
        cur.execute("SELECT COUNT(DISTINCT account_id) AS c FROM pt_accounts")
        c_row = cur.fetchone()
        c = int(c_row["c"]) if c_row and c_row["c"] is not None else 0
        if c == 1:
            cur.execute("SELECT account_id FROM pt_accounts ORDER BY created_ts ASC LIMIT 1")
            one = cur.fetchone()
            if one:
                aid = int(one["account_id"])
                cur.execute(
                    "INSERT OR REPLACE INTO pt_accounts(display_name, account_id, created_ts) VALUES(?,?,?)",
                    (dn_raw, aid, now),
                )
                if dn_can and dn_can != dn_raw:
                    cur.execute(
                        "INSERT OR REPLACE INTO pt_accounts(display_name, account_id, created_ts) VALUES(?,?,?)",
                        (dn_can, aid, now),
                    )
                conn.commit()
                return aid

    # Otherwise create a new stable account id from canonical name
    aid = _stable_account_id(dn_can)
    cur.execute(
        "INSERT OR REPLACE INTO pt_accounts(display_name, account_id, created_ts) VALUES(?,?,?)",
        (dn_raw, int(aid), now),
    )
    if dn_can and dn_can != dn_raw:
        cur.execute(
            "INSERT OR REPLACE INTO pt_accounts(display_name, account_id, created_ts) VALUES(?,?,?)",
            (dn_can, int(aid), now),
        )
    conn.commit()
    return int(aid)

def _i64(x: int) -> int:
    # clamp into signed 64-bit for Java long
    if x >= (1 << 63):
        x -= (1 << 64)
    if x < -(1 << 63):
        x = -(1 << 63)
    return int(x)

def _pack_uuid(u: uuid.UUID) -> Tuple[int, int]:
    # Java UUID is two signed longs (msb, lsb)
    msb = (u.int >> 64) & ((1 << 64) - 1)
    lsb = u.int & ((1 << 64) - 1)
    if msb >= (1 << 63):
        msb -= (1 << 64)
    if lsb >= (1 << 63):
        lsb -= (1 << 64)
    return int(msb), int(lsb)

def _flip_to_raw(f: Dict[str, Any]) -> bytes:
    """FlipV2 RAW record (BIG_ENDIAN), 84 bytes (matches client FlipV2.RAW_SIZE)."""
    msb, lsb = _pack_uuid(f["uuid"])
    return struct.pack(
        ">qqiiiiqiiqqqiii",
        msb, lsb,
        int(f["account_id"]), int(f["item_id"]),
        int(f["opened_time"]), int(f["opened_qty"]),
        _i64(int(f["spent"])),
        int(f.get("closed_time", 0)), int(f.get("closed_qty", 0)),
        _i64(int(f.get("received_post_tax", 0))),
        _i64(int(f.get("profit", 0))),
        _i64(int(f.get("tax_paid", 0))),
        int(f.get("status_ord", 0)),
        int(f.get("updated_time", int(time.time()))),
        int(f.get("deleted", 0)),
    )

def _acked_tx_to_raw(tx: Dict[str, Any]) -> bytes:
    """AckedTransaction RAW record (BIG_ENDIAN), 56 bytes (matches client AckedTransaction.RAW_SIZE)."""
    tx_uuid = uuid.UUID(tx["tx_id"])
    flip_uuid = uuid.UUID(tx["flip_uuid"]) if tx.get("flip_uuid") else tx_uuid
    msb1, lsb1 = _pack_uuid(tx_uuid)
    msb2, lsb2 = _pack_uuid(flip_uuid)
    return struct.pack(
        ">qqqqiiiiii",
        msb1, lsb1,
        msb2, lsb2,
        int(tx["account_id"]),
        int(tx["time"]),
        int(tx["item_id"]),
        int(tx["quantity"]),
        int(tx["price"]),
        int(tx["amount_spent"]),
    )

def _pt_flip_row_to_dict(row: sqlite3.Row) -> Dict[str, Any]:
    return {
        "uuid": uuid.UUID(row["flip_uuid"]),
        "account_id": int(row["account_id"]),
        "item_id": int(row["item_id"]),
        "opened_time": int(row["opened_time"]),
        "opened_qty": int(row["opened_qty"]),
        "spent": int(row["spent"]),
        "closed_time": int(row["closed_time"]),
        "closed_qty": int(row["closed_qty"]),
        "received_post_tax": int(row["received_post_tax"]),
        "profit": int(row["profit"]),
        "tax_paid": int(row["tax_paid"]),
        "status_ord": int(row["status_ord"]),
        "updated_time": int(row["updated_time"]),
        "deleted": int(row["deleted"]),
    }

def _pt_get_open_flip(conn: sqlite3.Connection, account_id: int, item_id: int) -> Optional[sqlite3.Row]:
    cur = conn.cursor()
    cur.execute(
        """
        SELECT * FROM pt_flips
        WHERE account_id = ? AND item_id = ? AND deleted = 0 AND status_ord != 2
        ORDER BY updated_time DESC
        LIMIT 1
        """,
        (int(account_id), int(item_id)),
    )
    return cur.fetchone()

def _pt_create_flip(conn: sqlite3.Connection, display_name: str, account_id: int, item_id: int, opened_time: int, status_ord: int) -> sqlite3.Row:
    flip_uuid = str(uuid.uuid4())
    now = int(time.time())
    conn.execute(
        """
        INSERT INTO pt_flips(
            flip_uuid, display_name, account_id, item_id,
            opened_time, opened_qty, spent,
            closed_time, closed_qty, received_post_tax, profit, tax_paid,
            status_ord, updated_time, deleted
        ) VALUES (?,?,?,?, ?,?,?, ?,?,?, ?,?, ?,?,?)
        """,
        (
            flip_uuid, (display_name or "default"), int(account_id), int(item_id),
            int(opened_time), 0, 0,
            0, 0, 0, 0, 0,
            int(status_ord), int(now), 0
        ),
    )
    conn.commit()
    cur = conn.cursor()
    cur.execute("SELECT * FROM pt_flips WHERE flip_uuid = ?", (flip_uuid,))
    return cur.fetchone()

def _pt_estimate_cost_basis(conn: sqlite3.Connection, item_id: int, latest_low: int = 0, latest_high: int = 0) -> int:
    # Prefer open-lot average cost (tracked), then last buy fill, then latest low/high.
    try:
        open_qty, avg_buy, _ = db_open_qty_and_avg_cost(conn, int(item_id))
        if open_qty > 0 and avg_buy > 0:
            return int(avg_buy)
    except Exception:
        pass

    cur = conn.cursor()
    cur.execute("SELECT buy_price FROM buy_fills WHERE item_id = ? ORDER BY fill_ts DESC LIMIT 1", (int(item_id),))
    row = cur.fetchone()
    if row and int(row[0]) > 0:
        return int(row[0])

    if latest_low > 0:
        return int(latest_low)
    if latest_high > 0:
        return int(latest_high)
    return 0

# ---------------------------------------------------------------------------
# PROFIT TRACKING — resilient aggregation (handles out-of-order history)
#
# The plugin may send GE history in bulk and not in chronological ingest order.
# Instead of closing a flip immediately when a SELL arrives without a prior BUY,
# we rebuild an aggregated flip (per account_id + item_id) from pt_transactions.
# This makes profit start showing as soon as the BUY history arrives.
# ---------------------------------------------------------------------------

def _pt_get_or_create_flip_uuid(conn: sqlite3.Connection, account_id: int, item_id: int) -> str:
    row = conn.execute(
        """SELECT flip_uuid FROM pt_flips
               WHERE account_id=? AND item_id=?
               ORDER BY updated_time DESC, rowid DESC
               LIMIT 1""",
        (account_id, item_id),
    ).fetchone()
    if row and row[0]:
        return str(row[0])
    return str(uuid.uuid4())


def _pt_recompute_aggregate_flip(
    conn: sqlite3.Connection,
    display_name: str,
    account_id: int,
    item_id: int,
    latest_low: int = 0,
    latest_high: int = 0,
) -> dict:
    # Pull all transactions for this (account,item). Order by time so opened/closed times are stable.
    rows = conn.execute(
        """SELECT tx_id, time, item_id, quantity, price, amount_spent, flip_uuid
               FROM pt_transactions
              WHERE account_id=? AND item_id=?
              ORDER BY time ASC, rowid ASC""",
        (account_id, item_id),
    ).fetchall()

    flip_uuid = _pt_get_or_create_flip_uuid(conn, account_id, item_id)

    bought_qty = 0
    sold_qty = 0
    spent = 0
    received_post_tax = 0
    tax_paid = 0
    opened_time = 0
    closed_time = 0
    last_time = 0

    for r in rows:
        ts = int(r[1] or 0)
        qty = int(r[3] or 0)
        price = int(r[4] or 0)
        amt_spent = int(r[5] or 0)

        if ts > last_time:
            last_time = ts

        if qty > 0:
            bought_qty += qty
            # Prefer server-calculated amount_spent; fallback to qty*price.
            spent += (amt_spent if amt_spent > 0 else qty * price)
            if opened_time == 0 or ts < opened_time:
                opened_time = ts
        elif qty < 0:
            q = -qty
            sold_qty += q
            post_tax_unit = _osrs_ge_post_tax(price)
            received_post_tax += post_tax_unit * q
            tax_paid += (price - post_tax_unit) * q
            if ts > closed_time:
                closed_time = ts

    # If we have sells without enough buys, estimate missing basis for the extra quantity.
    opened_qty = max(bought_qty, sold_qty)
    closed_qty = sold_qty
    spent_est = spent

    if sold_qty > bought_qty:
        extra = sold_qty - bought_qty
        basis = _pt_estimate_cost_basis(conn, item_id, latest_low, latest_high)
        if basis <= 0:
            # Fall back to latest mid if available; else use a conservative estimate from observed sells.
            mid = 0
            if latest_low and latest_high:
                mid = (latest_low + latest_high) // 2
            elif latest_low or latest_high:
                mid = latest_low or latest_high
            basis = mid
        if basis <= 0 and rows:
            # Use the lowest observed sell price as a final fallback.
            obs = [int(rr[4] or 0) for rr in rows if int(rr[3] or 0) < 0 and int(rr[4] or 0) > 0]
            basis = min(obs) if obs else 0
        if basis > 0:
            spent_est += int(basis) * extra

    # Profit definition matches client: received_post_tax - spent - tax already baked into received_post_tax.
    profit = received_post_tax - spent_est

    # Status: 0=BUYING, 1=SELLING, 2=FINISHED
    if opened_qty <= 0:
        status_ord = 0
    elif closed_qty == 0:
        status_ord = 0
    elif closed_qty < opened_qty:
        status_ord = 1
    else:
        status_ord = 2

    updated_time = last_time if last_time > 0 else int(time.time())

    # If no buys exist, use first transaction time as opened_time for display.
    if opened_time == 0:
        opened_time = last_time

    # Upsert into pt_flips
    existing = conn.execute(
        """SELECT rowid FROM pt_flips WHERE flip_uuid=? LIMIT 1""",
        (flip_uuid,),
    ).fetchone()

    if existing:
        conn.execute(
            """UPDATE pt_flips
                   SET display_name=?, account_id=?, item_id=?,
                       opened_time=?, opened_quantity=?, spent=?,
                       closed_time=?, closed_quantity=?, received_post_tax=?,
                       profit=?, tax_paid=?, status_ord=?, updated_time=?, deleted=0
                 WHERE flip_uuid=?""",
            (
                display_name,
                account_id,
                item_id,
                int(opened_time or 0),
                int(opened_qty or 0),
                int(spent_est or 0),
                int(closed_time or 0),
                int(closed_qty or 0),
                int(received_post_tax or 0),
                int(profit or 0),
                int(tax_paid or 0),
                int(status_ord),
                int(updated_time),
                flip_uuid,
            ),
        )
    else:
        conn.execute(
            """INSERT INTO pt_flips(
                       flip_uuid, display_name, account_id, item_id,
                       opened_time, opened_quantity, spent,
                       closed_time, closed_quantity, received_post_tax,
                       profit, tax_paid, status_ord, updated_time, deleted
                   ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (
                flip_uuid,
                display_name,
                account_id,
                item_id,
                int(opened_time or 0),
                int(opened_qty or 0),
                int(spent_est or 0),
                int(closed_time or 0),
                int(closed_qty or 0),
                int(received_post_tax or 0),
                int(profit or 0),
                int(tax_paid or 0),
                int(status_ord),
                int(updated_time),
                0,
            ),
        )

    # Ensure transactions carry this flip_uuid (helps acks + debugging)
    conn.execute(
        """UPDATE pt_transactions SET flip_uuid=?
              WHERE account_id=? AND item_id=? AND (flip_uuid IS NULL OR flip_uuid='')""",
        (flip_uuid, account_id, item_id),
    )

    row = conn.execute(
        """SELECT flip_uuid, display_name, account_id, item_id,
                   opened_time, opened_quantity, spent,
                   closed_time, closed_quantity, received_post_tax,
                   profit, tax_paid, status_ord, updated_time, deleted
              FROM pt_flips WHERE flip_uuid=?""",
        (flip_uuid,),
    ).fetchone()

    return {
        "flip_uuid": row[0],
        "display_name": row[1],
        "account_id": int(row[2]),
        "item_id": int(row[3]),
        "opened_time": int(row[4] or 0),
        "opened_quantity": int(row[5] or 0),
        "spent": int(row[6] or 0),
        "closed_time": int(row[7] or 0),
        "closed_quantity": int(row[8] or 0),
        "received_post_tax": int(row[9] or 0),
        "profit": int(row[10] or 0),
        "tax_paid": int(row[11] or 0),
        "status_ord": int(row[12] or 0),
        "updated_time": int(row[13] or 0),
        "deleted": int(row[14] or 0),
    }


def _pt_apply_buy(conn: sqlite3.Connection, flip: sqlite3.Row, qty: int, price: int, ts: int) -> sqlite3.Row:
    opened_qty = int(flip["opened_qty"]) + int(qty)
    spent = int(flip["spent"]) + int(price) * int(qty)
    status_ord = 0 if int(flip["closed_qty"]) == 0 else 1
    updated_time = int(ts)

    conn.execute(
        "UPDATE pt_flips SET opened_qty=?, spent=?, status_ord=?, updated_time=? WHERE flip_uuid=?",
        (opened_qty, spent, status_ord, updated_time, flip["flip_uuid"]),
    )
    conn.commit()
    cur = conn.cursor()
    cur.execute("SELECT * FROM pt_flips WHERE flip_uuid = ?", (flip["flip_uuid"],))
    return cur.fetchone()

def _pt_apply_sell(conn: sqlite3.Connection, flip: sqlite3.Row, sell_qty: int, price: int, ts: int, latest_low: int, latest_high: int) -> sqlite3.Row:
    # Ensure we have a basis. If the flip has 0 opened qty, synthesize a buy so profit can be shown.
    opened_qty = int(flip["opened_qty"])
    spent = int(flip["spent"])

    if opened_qty <= 0:
        basis = _pt_estimate_cost_basis(conn, int(flip["item_id"]), latest_low=latest_low, latest_high=latest_high)
        if basis <= 0:
            basis = int(price)
        opened_qty = int(sell_qty)
        spent = int(basis) * int(sell_qty)
    elif int(flip["closed_qty"]) + int(sell_qty) > opened_qty:
        # Selling more than we tracked as bought (extra inventory). Extend basis with an estimate.
        extra = (int(flip["closed_qty"]) + int(sell_qty)) - opened_qty
        basis = _pt_estimate_cost_basis(conn, int(flip["item_id"]), latest_low=latest_low, latest_high=latest_high)
        if basis <= 0:
            basis = int(price)
        opened_qty += int(extra)
        spent += int(basis) * int(extra)

    post_tax_price = ge_post_tax_price(int(flip["item_id"]), int(price))
    per_tax = int(price) - int(post_tax_price)
    received_post_tax = int(flip["received_post_tax"]) + int(post_tax_price) * int(sell_qty)
    tax_paid = int(flip["tax_paid"]) + int(per_tax) * int(sell_qty)

    closed_qty = int(flip["closed_qty"]) + int(sell_qty)
    closed_time = int(ts)
    updated_time = int(ts)

    status_ord = 1  # SELLING
    profit = int(received_post_tax - spent)
    if closed_qty >= opened_qty:
        status_ord = 2  # FINISHED

    conn.execute(
        """UPDATE pt_flips
           SET opened_qty=?, spent=?,
               closed_time=?, closed_qty=?,
               received_post_tax=?, tax_paid=?, profit=?,
               status_ord=?, updated_time=?
           WHERE flip_uuid=?""",
        (opened_qty, spent, closed_time, closed_qty, received_post_tax, tax_paid, profit, status_ord, updated_time, flip["flip_uuid"]),
    )
    conn.commit()
    cur = conn.cursor()
    cur.execute("SELECT * FROM pt_flips WHERE flip_uuid = ?", (flip["flip_uuid"],))
    return cur.fetchone()


def _pt_get_or_create_account_id(display_name: str) -> int:
    """Compatibility wrapper: returns stable account_id for display_name."""
    dn = str(display_name or "")
    with _db() as conn:
        return int(_pt_get_or_create_account(conn, dn))


def _pt_ingest_transactions(display_name: str, tx_list: list) -> list:
    """Ingest transactions and recompute aggregate flips per item.

    This is intentionally resilient to ingest order: we rebuild the flip from
    pt_transactions so a SELL that arrives before its BUY history will be fixed
    once the BUY transactions are later seeded from GE history.
    """
    if not tx_list:
        return []

    dn = str(display_name or "")
    account_id = _pt_get_or_create_account_id(dn)
    changed_items = set()

    with _db() as conn:
        for tx in tx_list:
            try:
                if not isinstance(tx, dict):
                    continue

                tx_id = str(tx.get("id") or tx.get("tx_id") or "")
                if not tx_id:
                    tx_id = str(uuid.uuid4())

                ts = int(tx.get("time") or tx.get("timestamp") or tx.get("ts") or 0)
                item_id = int(tx.get("itemId") or tx.get("item_id") or 0)
                qty = int(tx.get("quantity") or tx.get("qty") or 0)
                price = int(tx.get("price") or 0)
                box_id = int(tx.get("boxId") or tx.get("box_id") or -1)
                amt_spent = int(tx.get("amountSpent") or tx.get("amount_spent") or 0)
                flip_uuid = str(tx.get("flip_uuid") or tx.get("flipUuid") or tx.get("flip") or "")
                if not flip_uuid:
                    flip_uuid = f"auto-{tx_id}"

                if item_id <= 0 or qty == 0:
                    continue

                # De-dupe by tx_id
                exists = conn.execute(
                    "SELECT 1 FROM pt_transactions WHERE tx_id=? LIMIT 1",
                    (tx_id,),
                ).fetchone()
                if exists:
                    continue

                conn.execute(
                    """INSERT INTO pt_transactions(
                           tx_id, display_name, account_id, item_id,
                           time, quantity, price, amount_spent, box_id,
                           flip_uuid, raw_json
                       ) VALUES (?,?,?,?,?,?,?,?,?,?,?)""",
                    (
                        tx_id,
                        dn,
                        account_id,
                        item_id,
                        ts,
                        qty,
                        price,
                        amt_spent,
                        box_id,
                        flip_uuid,
                        json.dumps(tx, separators=(",", ":"), ensure_ascii=False),
                    ),
                )
                changed_items.add(item_id)
            except Exception:
                logger.exception("[PROFIT] failed to ingest transaction")

        # Recompute flips for each affected item
        flips_out = []
        for iid in sorted(changed_items):
            try:
                latest = PRICES_LATEST.get(iid, {}) if isinstance(PRICES_LATEST, dict) else {}
                latest_low = int(latest.get("low", 0) or 0)
                latest_high = int(latest.get("high", 0) or 0)
                flip = _pt_recompute_aggregate_flip(conn, dn, account_id, iid, latest_low=latest_low, latest_high=latest_high)
                flips_out.append(flip)
            except Exception:
                logging.exception("[PROFIT] failed to recompute flip")

        return flips_out

def _pt_fetch_flips_delta(account_id_time: Dict[int, int]) -> Tuple[int, List[Dict[str, Any]]]:
    now = int(time.time())
    flips: List[Dict[str, Any]] = []
    max_time = now
    if not account_id_time:
        return max_time, flips

    with _db_lock:
        conn = db_connect()
        try:
            cur = conn.cursor()
            for aid, last_t in account_id_time.items():
                try:
                    aid_i = int(aid)
                    last_i = int(last_t)
                except Exception:
                    continue
                cur.execute(
                    "SELECT * FROM pt_flips WHERE account_id = ? AND updated_time > ?",
                    (aid_i, last_i),
                )
                rows = cur.fetchall() or []
                for r in rows:
                    flips.append(_pt_flip_row_to_dict(r))
                    max_time = max(max_time, int(r["updated_time"]))
            return int(max_time), flips
        finally:
            conn.close()

@app.get("/profit-tracking/rs-account-names")
def rs_account_names():
    # Client expects JSON object Map<String,Integer>.
    # Some clients may include ?display_name=...; if so, create/alias it so it appears immediately.
    qdn = (request.args.get("display_name") or "").strip()

    with _db_lock:
        conn = db_connect()
        try:
            if qdn:
                try:
                    _pt_get_or_create_account(conn, qdn)
                except Exception:
                    pass
            cur = conn.cursor()
            cur.execute("SELECT display_name, account_id FROM pt_accounts ORDER BY display_name ASC")
            rows = cur.fetchall() or []
            out = {str(r["display_name"]): int(r["account_id"]) for r in rows}
        finally:
            conn.close()
    return jsonify(out), 200

@app.route("/profit-tracking/account-client-transactions", methods=["POST"])
def account_client_transactions():
    # Client expects AckedTransaction.listFromRaw (recordCount + records)
    display_name = request.args.get("display_name", "").strip() or "default"
    payload = request.get_json(silent=True) or {}
    try:
        limit = int(payload.get("limit", 30))
    except Exception:
        limit = 30
    try:
        end = int(payload.get("end", int(time.time())))
    except Exception:
        end = int(time.time())
    limit = max(1, min(limit, 200))

    with _db_lock:
        conn = db_connect()
        try:
            account_id = _pt_get_or_create_account(conn, display_name)
            cur = conn.cursor()
            cur.execute(
                """SELECT tx_id, flip_uuid, account_id, time, item_id, quantity, price, amount_spent
                   FROM pt_transactions
                   WHERE account_id = ? AND time <= ?
                   ORDER BY time DESC
                   LIMIT ?""",
                (int(account_id), int(end), int(limit)),
            )
            rows = cur.fetchall() or []
        finally:
            conn.close()

    out = bytearray()
    out += struct.pack(">i", int(len(rows)))
    for r in rows:
        out += _acked_tx_to_raw({
            "tx_id": r["tx_id"],
            "flip_uuid": r["flip_uuid"],
            "account_id": r["account_id"],
            "time": r["time"],
            "item_id": r["item_id"],
            "quantity": r["quantity"],
            "price": r["price"],
            "amount_spent": r["amount_spent"],
        })

    return Response(bytes(out), status=200, content_type="application/x-bytes")

@app.route("/profit-tracking/client-transactions", methods=["POST","GET"])

def client_transactions():
    display_name = request.args.get("display_name", "")

    txs = None
    try:
        txs = request.get_json(silent=True)
    except Exception:
        txs = None

    if txs is None:
        # Some client builds send msgpack
        try:
            txs = msgpack.loads(request.data, raw=False)
        except Exception:
            txs = []

    if not isinstance(txs, list):
        txs = []

    flips = _pt_ingest_transactions(display_name, txs)

    # return FlipV2[] raw
    buf = bytearray()
    buf.extend(struct.pack(">i", len(flips)))
    for f in flips:
        buf.extend(_flip_to_raw(f))

    return Response(bytes(buf), content_type="application/octet-stream")


def client_flips_delta():
    # Expected body: { accountIdToSyncTime: { <int>: <int> } }
    payload = None
    try:
        payload = request.get_json(silent=True)
    except Exception:
        payload = None

    if payload is None:
        try:
            payload = msgpack.loads(request.data, raw=False)
        except Exception:
            payload = {}

    if not isinstance(payload, dict):
        payload = {}

    acct_map = payload.get("accountIdToSyncTime") or payload.get("accountIdToLastSyncTime") or payload.get("accounts") or {}
    if not isinstance(acct_map, dict):
        acct_map = {}

    now = int(time.time())

    flips = []
    with _db() as conn:
        for k, v in acct_map.items():
            try:
                account_id = int(k)
                since = int(v)
            except Exception:
                continue

            rows = conn.execute(
                """SELECT flip_uuid, display_name, account_id, item_id,
                           opened_time, opened_quantity, spent,
                           closed_time, closed_quantity, received_post_tax,
                           profit, tax_paid, status_ord, updated_time, deleted
                      FROM pt_flips
                     WHERE account_id=? AND updated_time>? AND deleted=0
                     ORDER BY updated_time ASC""",
                (account_id, since),
            ).fetchall()

            for r in rows:
                flips.append({
                    "flip_uuid": r[0],
                    "display_name": r[1],
                    "account_id": int(r[2]),
                    "item_id": int(r[3]),
                    "opened_time": int(r[4] or 0),
                    "opened_quantity": int(r[5] or 0),
                    "spent": int(r[6] or 0),
                    "closed_time": int(r[7] or 0),
                    "closed_quantity": int(r[8] or 0),
                    "received_post_tax": int(r[9] or 0),
                    "profit": int(r[10] or 0),
                    "tax_paid": int(r[11] or 0),
                    "status_ord": int(r[12] or 0),
                    "updated_time": int(r[13] or 0),
                    "deleted": int(r[14] or 0),
                })

    buf = bytearray()
    # First int: serverTime
    buf.extend(struct.pack(">i", now))
    # Second int: recordCount
    buf.extend(struct.pack(">i", len(flips)))
    for f in flips:
        buf.extend(_flip_to_raw(f))

    return Response(bytes(buf), content_type="application/octet-stream")


def orphan_transaction():
    display_name = request.args.get("display_name", "")

    tx = None
    try:
        tx = request.get_json(silent=True)
    except Exception:
        tx = None

    if tx is None:
        try:
            tx = msgpack.loads(request.data, raw=False)
        except Exception:
            tx = {}

    if not isinstance(tx, dict):
        tx = {}

    # Insert if missing
    dn = str(display_name or "")
    account_id = _pt_get_or_create_account_id(dn)
    item_id = int(tx.get("itemId") or tx.get("item_id") or 0)

    if item_id <= 0:
        return Response(struct.pack(">i", 0), content_type="application/octet-stream")

    with _db() as conn:
        tx_id = str(tx.get("id") or tx.get("tx_id") or "") or str(uuid.uuid4())
        ts = int(tx.get("time") or tx.get("timestamp") or tx.get("ts") or 0)
        qty = int(tx.get("quantity") or tx.get("qty") or 0)
        price = int(tx.get("price") or 0)
        box_id = int(tx.get("boxId") or tx.get("box_id") or -1)
        amt_spent = int(tx.get("amountSpent") or tx.get("amount_spent") or 0)

        exists = conn.execute("SELECT 1 FROM pt_transactions WHERE tx_id=? LIMIT 1", (tx_id,)).fetchone()
        if not exists and qty != 0:
            conn.execute(
                """INSERT INTO pt_transactions(
                       tx_id, display_name, account_id, item_id,
                       time, quantity, price, amount_spent, box_id,
                       flip_uuid, raw_json
                   ) VALUES (?,?,?,?,?,?,?,?,?,?,?)""",
                (
                    tx_id,
                    dn,
                    account_id,
                    item_id,
                    ts,
                    qty,
                    price,
                    amt_spent,
                    box_id,
                    None,
                    json.dumps(tx, separators=(",", ":"), ensure_ascii=False),
                ),
            )

        latest = PRICES_LATEST.get(item_id, {}) if isinstance(PRICES_LATEST, dict) else {}
        latest_low = int(latest.get("low", 0) or 0)
        latest_high = int(latest.get("high", 0) or 0)
        flip = _pt_recompute_aggregate_flip(conn, dn, account_id, item_id, latest_low=latest_low, latest_high=latest_high)

    buf = bytearray()
    buf.extend(struct.pack(">i", 1))
    buf.extend(_flip_to_raw(flip))
    return Response(bytes(buf), content_type="application/octet-stream")


def delete_transaction():
    payload = None
    try:
        payload = request.get_json(silent=True)
    except Exception:
        payload = None

    if payload is None:
        try:
            payload = msgpack.loads(request.data, raw=False)
        except Exception:
            payload = {}

    if not isinstance(payload, dict):
        payload = {}

    tx_id = str(payload.get("tx_id") or payload.get("id") or "")
    if not tx_id:
        return Response(struct.pack(">i", 0), content_type="application/octet-stream")

    with _db() as conn:
        row = conn.execute(
            "SELECT account_id, display_name, item_id FROM pt_transactions WHERE tx_id=? LIMIT 1",
            (tx_id,),
        ).fetchone()
        if not row:
            return Response(struct.pack(">i", 0), content_type="application/octet-stream")

        account_id = int(row[0])
        display_name = str(row[1] or "")
        item_id = int(row[2])

        conn.execute("DELETE FROM pt_transactions WHERE tx_id=?", (tx_id,))

        latest = PRICES_LATEST.get(item_id, {}) if isinstance(PRICES_LATEST, dict) else {}
        latest_low = int(latest.get("low", 0) or 0)
        latest_high = int(latest.get("high", 0) or 0)
        flip = _pt_recompute_aggregate_flip(conn, display_name, account_id, item_id, latest_low=latest_low, latest_high=latest_high)

    buf = bytearray()
    buf.extend(struct.pack(">i", 1))
    buf.extend(_flip_to_raw(flip))
    return Response(bytes(buf), content_type="application/octet-stream")

def visualize_flip():
    # Client expects msgpack VisualizeFlipResponse.
    data = _visualize_flip_response_to_msgpack()
    return Response(data, status=200, content_type="application/x-msgpack")


# ============================================================
# ITEM PRICES ENDPOINT (msgpack) — supports GET + POST
# ============================================================

@app.route("/profit-tracking/client-flips-delta", methods=["POST","GET"])
def profit_tracking_client_flips_delta():
    # Some client builds poll this endpoint; return an empty payload to prevent 404 spam.
    return Response(b"\x00" * 12, status=200, content_type="application/x-bytes")


@app.route("/prices", methods=["GET", "POST"])
def prices_endpoint():
    # Plugin may POST JSON {"item_id": ...} and expect msgpack ItemPrice
    item_id = 0
    if request.method == "POST":
        payload = request.get_json(silent=True) or {}
        try:
            item_id = int(payload.get("item_id", 0))
        except Exception:
            item_id = 0
    else:
        try:
            item_id = int(request.args.get("item_id", "0"))
        except Exception:
            item_id = 0

    mapping, latest, _, _ = prices.snapshot()
    lp = latest.get(item_id) or {}
    try:
        low = int(lp.get("low", 0))
        high = int(lp.get("high", 0))
    except Exception:
        low, high = 0, 0

    if low <= 0 and high <= 0:
        packed = _item_price_to_msgpack(0, 0, "No price data")
        resp = Response(packed, status=200, content_type="application/x-msgpack")
        resp.headers["Content-Length"] = str(len(packed))
        return resp

    buy_price = max(low, 1) if low > 0 else max(high, 1)
    sell_price = max(high, 1) if high > 0 else max(low, 1)

    packed = _item_price_to_msgpack(buy_price, sell_price, "")
    resp = Response(packed, status=200, content_type="application/x-msgpack")
    resp.headers["Content-Length"] = str(len(packed))
    return resp

# ============================================================
# DASH AUTH + DASHBOARD (dark mode tables)
# ============================================================
def dashboard_allowed() -> bool:
    if not DASH_TOKEN:
        return True
    token = request.args.get("token", "")
    return token == DASH_TOKEN

def format_ts(ts: int) -> str:
    if not ts:
        return "-"
    try:
        return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(int(ts)))
    except Exception:
        return str(ts)

@app.get("/")
@app.get("/dashboard")
def dashboard():
    if not dashboard_allowed():
        return "Forbidden", 403

    try:
        mapping, latest, volumes, last_refresh = prices.snapshot()

        with _db_lock:
            conn = db_connect()
            try:
                cur = conn.cursor()
                cur.execute("SELECT COALESCE(SUM(profit), 0) AS p FROM realized_trades")
                realized_profit = int(cur.fetchone()["p"])

                cur.execute("SELECT COALESCE(SUM(qty * buy_price), 0) AS c FROM realized_trades")
                realized_cost = int(cur.fetchone()["c"])

                roi = (realized_profit / realized_cost) if realized_cost > 0 else 0.0

                cur.execute("""SELECT COALESCE(SUM(qty_remaining * buy_price), 0) AS open_cost
                               FROM lots WHERE qty_remaining > 0""")
                open_cost_total = int(cur.fetchone()["open_cost"])

                cur.execute("""
                    SELECT item_id, item_name,
                           SUM(qty_remaining) AS open_qty,
                           SUM(qty_remaining * buy_price) AS open_cost
                    FROM lots
                    WHERE qty_remaining > 0
                    GROUP BY item_id, item_name
                    ORDER BY open_cost DESC
                    LIMIT 200
                """)
                open_rows = [dict(x) for x in cur.fetchall()]

                cur.execute("""
                    SELECT trade_id, item_id, item_name, qty, buy_price, sell_price, sell_ts, profit
                    FROM realized_trades
                    ORDER BY sell_ts DESC
                    LIMIT 100
                """)
                hist_rows = [dict(x) for x in cur.fetchall()]
            finally:
                conn.close()

        with _last_status_lock:
            st = dict(LAST_STATUS)
        last_status_ts = int(st.get("updated_unix", 0))
        coins = int(st.get("coins", 0))
        offers = st.get("offers", []) or []

        offer_rows_html = ""
        for o in offers[:50]:
            try:
                status = str(o.get("status", "")).lower()
                active = bool(o.get("active", False))
                iid = int(o.get("item_id", 0))
                box_id = int(o.get("box_id", 0))
                price = int(o.get("price", 0))
                total = int(o.get("amount_total", 0))
                traded = int(o.get("amount_traded", 0))
                gp_to_collect = int(o.get("gp_to_collect", 0))
            except Exception:
                continue
            name = mapping[iid].name if iid in mapping else str(iid)
            offer_rows_html += (
                "<tr>"
                f"<td>{box_id}</td>"
                f"<td>{html_escape(status)}</td>"
                f"<td>{'yes' if active else 'no'}</td>"
                f"<td>{iid}</td>"
                f"<td>{html_escape(name)}</td>"
                f"<td>{price:,}</td>"
                f"<td>{traded:,}/{total:,}</td>"
                f"<td>{gp_to_collect:,}</td>"
                "</tr>"
            )
        if not offer_rows_html:
            offer_rows_html = "<tr><td colspan='8' style='opacity:0.8;'>No offers received yet (open GE / let plugin POST /suggestion)</td></tr>"

        open_pos_html = ""
        for r in open_rows:
            iid = int(r["item_id"])
            name = str(r["item_name"])
            open_qty = int(r["open_qty"])
            open_cost = int(r["open_cost"])
            avg_buy = int(open_cost / open_qty) if open_qty > 0 else 0

            lp = latest.get(iid) or {}
            high = int(lp.get("high", 0)) if isinstance(lp, dict) else 0
            sell_px = max(high - 1, 1) if high > 0 else 0
            tax = ge_tax_per_unit(iid, sell_px) if sell_px > 0 else 0
            unreal_per = (sell_px - avg_buy - tax) if sell_px > 0 else 0
            unreal = unreal_per * open_qty if sell_px > 0 else 0

            open_pos_html += (
                "<tr>"
                f"<td>{iid}</td>"
                f"<td>{html_escape(name)}</td>"
                f"<td>{open_qty:,}</td>"
                f"<td>{avg_buy:,}</td>"
                f"<td>{open_cost:,}</td>"
                f"<td>{sell_px:,}</td>"
                f"<td>{unreal:,}</td>"
                "</tr>"
            )
        if not open_pos_html:
            open_pos_html = "<tr><td colspan='7' style='opacity:0.8;'>No open lots (nothing currently held)</td></tr>"

        hist_html = ""
        for t in hist_rows:
            hist_html += (
                "<tr>"
                f"<td>{int(t['trade_id'])}</td>"
                f"<td>{int(t['item_id'])}</td>"
                f"<td>{html_escape(str(t['item_name']))}</td>"
                f"<td>{int(t['qty']):,}</td>"
                f"<td>{int(t['buy_price']):,}</td>"
                f"<td>{int(t['sell_price']):,}</td>"
                f"<td>{int(t['profit']):,}</td>"
                f"<td>{html_escape(format_ts(int(t['sell_ts'])))} </td>"
                "</tr>"
            )
        if not hist_html:
            hist_html = "<tr><td colspan='8' style='opacity:0.8;'>No realized trades yet</td></tr>"

        html = f"""
        <html>
        <head>
          <title>SwagFlip Dashboard</title>
          <style>
            body {{
              font-family: system-ui, sans-serif;
              padding: 22px;
              background: #0f1115;
              color: #f2f2f2;
            }}
            a {{ color: #8ab4ff; text-decoration: none; }}
            a:hover {{ text-decoration: underline; }}
            .grid {{ display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 12px; margin-bottom: 16px; }}
            .card {{ background: #161a22; border: 1px solid #2a3243; border-radius: 10px; padding: 12px; }}
            .k {{ opacity: 0.78; font-size: 12px; }}
            .v {{ font-size: 20px; font-weight: 800; margin-top: 4px; }}
            .row {{ display:flex; gap: 10px; flex-wrap: wrap; margin: 10px 0 18px; }}
            .pill {{ background:#161a22; border:1px solid #2a3243; border-radius:999px; padding:8px 12px; font-size:13px; }}
            .wrap {{ max-height: 340px; overflow:auto; border-radius: 10px; border: 1px solid #2a3243; }}

            table {{
              width: 100%;
              border-collapse: collapse;
              background: #11151d;
              color: #f2f2f2;
            }}
            th, td {{
              border: 1px solid #2a3243;
              padding: 8px;
              text-align: left;
              color: #f2f2f2;
            }}
            th {{
              background: #141a26;
              position: sticky;
              top: 0;
            }}
            h2 {{ margin: 18px 0 10px; }}
          </style>
        </head>
        <body>
          <h1 style="margin:0 0 8px;">SwagFlip Dashboard</h1>

          <div class="row">
            <div class="pill">DB: <span style="opacity:0.85">{html_escape(DB_PATH)}</span></div>
            <div class="pill">Prices refreshed: <span style="opacity:0.85">{html_escape(format_ts(int(last_refresh)))}</span></div>
            <div class="pill">Last plugin status: <span style="opacity:0.85">{html_escape(format_ts(int(last_status_ts)))}</span></div>
            <div class="pill">Coins (last status): <span style="opacity:0.85">{coins:,}</span></div>
            <div class="pill">Buy-limit window: <span style="opacity:0.85">{BUY_LIMIT_RESET_SECONDS}s</span></div>
            <div class="pill">Logs: <a href="/debug/logs" style="opacity:0.95">/debug/logs</a></div>
          </div>

          <div class="grid">
            <div class="card"><div class="k">Realized Profit</div><div class="v">{realized_profit:,} gp</div></div>
            <div class="card"><div class="k">Realized Cost</div><div class="v">{realized_cost:,} gp</div></div>
            <div class="card"><div class="k">Realized ROI</div><div class="v">{roi*100:.2f}%</div></div>
            <div class="card"><div class="k">Open Cost Basis</div><div class="v">{open_cost_total:,} gp</div></div>
          </div>

          <h2>Current Offers (from last /suggestion payload)</h2>
          <div class="wrap">
            <table>
              <tr>
                <th>Box</th><th>Status</th><th>Active</th><th>Item ID</th><th>Name</th><th>Price</th><th>Traded</th><th>GP to Collect</th>
              </tr>
              {offer_rows_html}
            </table>
          </div>

          <h2>Open Positions (lots aggregated)</h2>
          <div class="wrap">
            <table>
              <tr>
                <th>Item ID</th><th>Name</th><th>Open Qty</th><th>Avg Buy</th><th>Open Cost</th><th>Est Sell (high-1)</th><th>Unrealized (est)</th>
              </tr>
              {open_pos_html}
            </table>
          </div>

          <h2>Recent Realized Trades</h2>
          <div class="wrap">
            <table>
              <tr>
                <th>ID</th><th>Item ID</th><th>Name</th><th>Qty</th><th>Buy</th><th>Sell</th><th>Profit</th><th>Sold</th>
              </tr>
              {hist_html}
            </table>
          </div>
        </body>
        </html>
        """
        return html, 200

    except Exception:
        rid = getattr(g, "request_id", uuid.uuid4().hex[:10])
        logger.exception(f"[DASHBOARD] crash rid={rid}")
        return f"<h1>Dashboard error</h1><p>Request ID: {rid}</p><pre>Check {html_escape(LOG_PATH)} or /debug/logs</pre>", 500

# ============================================================
# DEBUG
# ============================================================
@app.get("/health")
def health():
    _, _, _, refreshed = prices.snapshot()
    return jsonify({"ok": True, "last_price_refresh_unix": refreshed, "db": DB_PATH, "log": LOG_PATH}), 200

def _tail_file(path: str, lines: int = 250) -> str:
    try:
        if not os.path.exists(path):
            return f"(no log file yet) {path}\n"
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            data = f.readlines()
        return "".join(data[-max(1, lines):])
    except Exception as e:
        return f"(failed reading log) {e}\n"



@app.get("/debug/pt-status")
def debug_pt_status():
    """JSON snapshot of profit-tracking state (counts + last update)."""
    try:
        with _db() as conn:
            # counts
            tx_count = conn.execute("SELECT COUNT(*) FROM pt_transactions").fetchone()[0]
            flip_count = conn.execute("SELECT COUNT(*) FROM pt_flips WHERE deleted=0").fetchone()[0]
            # last timestamps
            last_tx = conn.execute("SELECT MAX(time) FROM pt_transactions").fetchone()[0] or 0
            last_flip = conn.execute("SELECT MAX(updated_time) FROM pt_flips").fetchone()[0] or 0
            # accounts known
            accounts = conn.execute("SELECT display_name, account_id FROM pt_accounts ORDER BY display_name").fetchall()
        return jsonify({
            "db_path": os.path.abspath(DB_PATH),
            "log_path": os.path.abspath(LOG_PATH),
            "pt_transactions": int(tx_count),
            "pt_flips": int(flip_count),
            "last_tx_time": int(last_tx),
            "last_flip_updated_time": int(last_flip),
            "accounts": {row[0]: int(row[1]) for row in accounts},
        })
    except Exception:
        rid = _rid()
        log_exception("[DEBUG] pt-status failed", rid=rid)
        return jsonify({"error": "pt-status failed", "rid": rid}), 500

@app.get("/debug/logs")



@app.route("/debug/code_index", methods=["GET"])
def debug_code_index():
    """
    Returns line-number anchors for the most important buy/sell logic sections.
    Helps you jump straight to the right code in a text editor.
    """
    import inspect
    targets = {
        "suggestion_endpoint": suggestion,
        "inventory_sell_block": suggestion,  # same function; use find strings in your editor
        "buy_candidate_scoring": compute_buy_candidates if "compute_buy_candidates" in globals() else suggestion,
        "seller_tax": seller_tax,
        "ge_post_tax_price": ge_post_tax_price if "ge_post_tax_price" in globals() else seller_tax,
    }
    out = {}
    for k, fn in targets.items():
        try:
            lines, start = inspect.getsourcelines(fn)
            out[k] = {"start_line": int(start), "end_line": int(start + len(lines) - 1), "name": getattr(fn, "__name__", str(fn))}
        except Exception:
            out[k] = None
    return jsonify(out), 200


@app.route("/debug/winners", methods=["GET"])
def debug_winners():
    """Sanity check: did the winners CSV load and match OSRS item IDs?"""
    top = []
    try:
        items = []
        for iid, st in _WINNER_STATS_BY_ID.items():
            mins = max(float(st.get("avg_mins", 999.0)), 0.25)
            ppm = float(st.get("avg_profit", 0)) / mins
            items.append((ppm, iid, st))
        items.sort(reverse=True, key=lambda x: x[0])
        for ppm, iid, st in items[:50]:
            top.append({
                "item_id": int(iid),
                "name": st.get("name"),
                "count": int(st.get("count", 0)),
                "avg_profit": int(st.get("avg_profit", 0)),
                "avg_mins": float(st.get("avg_mins", 0.0)),
                "profit_per_min": float(ppm),
                "win_rate": float(st.get("win_rate", 0.0)),
            })
    except Exception:
        logger.exception("[WINNERS] debug_winners failed")

    return jsonify({
        "csv": WINNING_FLIPS_CSV,
        "only_winners": ONLY_WINNING_ITEMS,
        "names_loaded": len(_WINNER_STATS_BY_NAME),
        "matched_item_ids": len(_WINNER_STATS_BY_ID),
        "top": top,
    })

def debug_logs():
    if not dashboard_allowed():
        return "Forbidden", 403
    try:
        n = int(request.args.get("n", "250"))
    except Exception:
        n = 250
    return Response(_tail_file(LOG_PATH, n), status=200, content_type="text/plain; charset=utf-8")

# ============================================================
# MAIN SUGGESTION ENDPOINT
# ============================================================
@app.post("/suggestion")
def suggestion():
    try:
        status = request.get_json(silent=True) or {}
        update_last_status(status)

        offers: List[Dict[str, Any]] = status.get("offers") or []
        items: List[Dict[str, Any]] = status.get("items") or []

        mapping, latest, volumes, _ = prices.snapshot()

        # parse coins + inventory (needed for stale logic + safety checks)
        coins = 0
        inv: List[Tuple[int, int]] = []
        for it in items:
            try:
                iid = int(it.get("item_id", 0))
                amt = int(it.get("amount", 0))
                if iid == 995:
                    coins += amt
                elif iid > 0 and amt > 0:
                    inv.append((iid, amt))
            except Exception:
                continue

        # Check for full inventory (28 slots)
        used_inv_slots = len(inv) + (1 if coins > 0 else 0)
        inv_full = (used_inv_slots >= 28)

        # Client-configurable offer adjust window (minutes). Presets: 5, 30, 120, 480.
        tf_minutes = _status_timeframe_minutes(status)
        stale_seconds = max(STALE_OFFER_SECONDS, tf_minutes * 60)

        # Use the adjust-offers window as a rough "flip horizon":
        # longer windows => accept slower items, but demand higher margins/ROI.
        if tf_minutes <= 5:
            min_roi_eff = MIN_ROI
            min_margin_eff = max(1, MIN_MARGIN_GP)
            max_buy_mins = float(TARGET_FILL_MINUTES) * 3.0
        elif tf_minutes <= 30:
            min_roi_eff = max(MIN_ROI, 0.003)   # 0.3%
            min_margin_eff = max(MIN_MARGIN_GP, 25)
            max_buy_mins = 60.0
        elif tf_minutes <= 120:
            min_roi_eff = max(MIN_ROI, 0.006)   # 0.6%
            min_margin_eff = max(MIN_MARGIN_GP, 50)
            max_buy_mins = 240.0
        else:
            min_roi_eff = max(MIN_ROI, 0.010)   # 1.0%
            min_margin_eff = max(MIN_MARGIN_GP, 100)
            max_buy_mins = 720.0



        # 1) sync offers -> DB (fills, lots, trades, rec metrics)
        try:
            sync_offers_and_fills(mapping, offers)
        except Exception:
            logger.exception("[SYNC] error")
        # 1.5) stale offers (abort stale buys, fast-dump stale sells)
        stale_action = maybe_handle_stale_offers(status, mapping, latest, volumes, offers, coins, inv, inv_full)
        if stale_action is not None:
            queued = None
            try:
                queued = stale_action.pop("_queue_action", None)
            except Exception:
                queued = None

            if queued:
                try:
                    led2 = load_ledger()
                    led2.setdefault("action_queue", [])
                    led2["action_queue"].append(queued)
                    save_ledger(led2)
                except Exception:
                    pass

            record_recommendation(stale_action)
            return _reply_suggestion(stale_action)
        # 2) crash-guard: reprice active sells while still profitable (no free slot required)
        crash_action = maybe_reprice_active_sell(mapping, latest, volumes, offers, stale_seconds)
        if crash_action is not None:
            queued = None
            try:
                queued = crash_action.pop("_queue_action", None)
            except Exception:
                queued = None

            if queued:
                try:
                    led2 = load_ledger()
                    led2.setdefault("action_queue", [])
                    led2["action_queue"].append(queued)
                    save_ledger(led2)
                except Exception:
                    pass

            record_recommendation(crash_action)
            return _reply_suggestion(crash_action)

        # Derive offer-slot stats (used below)
        empty_slot_id = first_empty_slot_id(offers)

        # If any offer is DONE, you must COLLECT before anything else.
        # We send a "sell next" suggestion so the plugin highlights the collect button,
        # then (after collect) inventory-first will relist ASAP.
        done_offers = [o for o in offers if offer_is_done(o)]
        if done_offers:
            # Completed BUY: prompt collect + immediate relist (SELL) so the slot can be reused ASAP.
            done_buy = next((o for o in done_offers if offer_is_buy(o)), None)
            if done_buy:
                iid = offer_item_id(done_buy)
                qty = int(offer_amount_total(done_buy) or offer_amount_traded(done_buy) or 1)
                buy_p = int(offer_price_gp(done_buy) or 1)

                low, high = latest_low_high(iid)
                sell_p = max(1, int(high or low or (buy_p + 1)))

                # Best-effort expected profit (after GE tax on the sale).
                try:
                    exp_profit = int((sell_p - buy_p - ge_tax_per_unit(iid, sell_p)) * qty)
                except Exception:
                    exp_profit = 0

                action = build_sell(
                    box_id=int(offer_box_id(done_buy) or 0),
                    item_id=iid,
                    name=item_name_safe(iid),
                    price=sell_p,
                    qty=qty,
                    exp_profit=exp_profit,
                    exp_min=0,
                    note="collect then relist ASAP (buy filled)",
                )
                return _reply_suggestion(action)

            # Otherwise (usually completed SELL): prompt the user to COLLECT.
            o = done_offers[0]
            iid = offer_item_id(o) or 995
            action = build_buy(
                box_id=int(offer_box_id(o) or 0),
                item_id=iid,
                name=item_name_safe(iid),
                price=int(offer_price_gp(o) or 1),
                qty=1,
                exp_profit=0,
                exp_min=0,
                note="collect completed offer",
            )
            return _reply_suggestion(action)

        # Inventory-first SELL: prioritize selling inventory before new buys.

        # User preference: sell inventory unless the *estimated realized loss* would exceed MAX_INVENTORY_LOSS_GP.

        # (We only apply the loss threshold when we have a known basis from server history.)

        inv: Dict[int, int] = {}

        for it in items:

            try:

                # tolerate different client schemas
                iid = int(
                    it.get("id")
                    or it.get("item_id")
                    or it.get("itemId")
                    or it.get("itemID")
                    or it.get("item")
                    or 0
                )

                qty = int(
                    it.get("qty")
                    or it.get("quantity")
                    or it.get("count")
                    or it.get("stack")
                    or it.get("amount")
                    or 0
                )

            except Exception:

                continue

            if iid <= 0 or qty <= 0 or iid == 995:

                continue

            inv[iid] = inv.get(iid, 0) + qty


        if inv:

            if empty_slot_id is None:

                # No slot available to list a sell, so don't start new buys that could clog inventory.

                return _reply_suggestion(build_wait("Inventory has items to sell but no empty GE slot. Free a slot first."))


            active_iids: Set[int] = set()

            for o in offers:

                if offer_is_active(o):

                    oi = offer_item_id(o)

                    if oi > 0:

                        active_iids.add(oi)


            def _basis_from_history(conn, item_id: int, price_hint: int) -> Tuple[int, bool]:

                """Return (basis_per_unit, basis_known). basis_known=False means we had to guess."""

                row = conn.execute(

                    "SELECT buy_price FROM buy_fills WHERE item_id=? ORDER BY fill_ts DESC LIMIT 1",

                    (item_id,),

                ).fetchone()

                if row and row[0]:

                    return int(row[0]), True

                try:

                    row2 = conn.execute(

                        "SELECT buy_price FROM lots WHERE item_id=? ORDER BY buy_ts DESC LIMIT 1",

                        (item_id,),

                    ).fetchone()

                    if row2 and row2[0]:

                        return int(row2[0]), True

                except Exception:

                    pass

                return int(price_hint), False


            conn = get_db()

            try:

                # Ledger presence (items previously seen by the bot) — prefer selling UNKNOWN (not on ledger) items first.
                try:
                    ledger_iids: Set[int] = set()
                    for (x,) in conn.execute("SELECT DISTINCT item_id FROM lots").fetchall():
                        try:
                            ledger_iids.add(int(x))
                        except Exception:
                            pass
                    for (x,) in conn.execute("SELECT DISTINCT item_id FROM buy_fills").fetchall():
                        try:
                            ledger_iids.add(int(x))
                        except Exception:
                            pass
                except Exception:
                    ledger_iids = set()
                for iid, qty in sorted(
                    inv.items(),
                    key=lambda kv: (0 if kv[0] not in ledger_iids else 1, -int(kv[1])),
                ):

                    if iid in active_iids:

                        continue

                    name = item_name_safe(iid)

                    low, high = latest_low_high(iid)

                    # Sell inventory fast: aim at current "low" (insta-sell). If missing, fall back to high.

                    sell_p = int((high - SELL_UNDERCUT_GP) if (high and high > 0) else ((low or 0) if (low and low > 0) else 1))

                    sell_p = max(1, sell_p)


                    basis, basis_known = _basis_from_history(conn, iid, sell_p)

                    if (not basis_known) and (not AUTO_SELL_UNKNOWN_BASIS):
                        logger.info("[INV] skip unknown basis (manual): %s x%s | sell_p=%s", name, qty, sell_p)
                        continue

                    post_tax = ge_post_tax_price(iid, sell_p)

                    est_profit_total = (post_tax - basis) * int(qty)


                    if basis_known and est_profit_total < -MAX_INVENTORY_LOSS_GP:

                        logger.info("[INV] leave for manual: %s x%s | est_profit=%s (loss>%s)", name, qty, est_profit_total, MAX_INVENTORY_LOSS_GP)

                        continue


                    action = build_sell(

                        box_id=int(empty_slot_id),

                        item_id=iid,

                        name=name,

                        price=sell_p,

                        qty=max(1, int(qty)),

                        exp_profit=int(est_profit_total),

                        exp_min=0,

                        note=("inventory sell (fast)" + ("" if est_profit_total >= 0 else " — small loss ok")),

                    )

                    return _reply_suggestion(action)

            finally:

                try:

                    conn.close()

                except Exception:

                    pass


        # keep marker line below

        slots_open = sum(1 for o in offers if offer_is_empty(o))
        active_ids = active_offer_item_ids(offers)
        blocked: Set[int] = set()  # hook for future item-blocking

        # Drain queued actions first whenever a slot is open (queued SELL/BUY)
        try:
            led = load_ledger()
        except Exception:
            led = {}
        if empty_slot_id is not None:
            # 1) queued actions (usually SELLs that couldn't be placed before)
            try:
                aq = led.get("action_queue") or []
                if isinstance(aq, list) and len(aq) > 0:
                    q = aq.pop(0)
                    if isinstance(q, dict) and q.get("type") in ("sell", "buy"):
                        q["boxId"] = int(empty_slot_id)
                        led["action_queue"] = aq
                        save_ledger(led)
                        record_recommendation(q)
                        return _reply_suggestion(q)
            except Exception:
                pass

            # 2) queued buys (fills additional slots one-by-one)
            try:
                bq = led.get("buy_queue") or []
                if isinstance(bq, list) and len(bq) > 0:
                    q = bq.pop(0)
                    if isinstance(q, dict):
                        q["boxId"] = int(empty_slot_id)
                        led["buy_queue"] = bq
                        save_ledger(led)
                        record_recommendation(q)
                        return _reply_suggestion(q)
            except Exception:
                pass

        # PRIORITY 3: NEW BUYS
        # ====================================================
        sell_only = bool(status.get("sell_only", False))
        if slots_open > 0 and (not sell_only) and empty_slot_id is not None:
            budget_total = min(int(coins * MAX_CASH_FRACTION), BUY_BUDGET_CAP)
            if budget_total <= 0:
                return _reply_suggestion(build_wait("Wait (no cash)"))

            per_slot_budget = max(int(budget_total / max(slots_open, 1)), 1)

            reject_counts: Dict[str, int] = {}
            def rej(reason: str):
                if DEBUG_REJECTIONS:
                    reject_counts[reason] = reject_counts.get(reason, 0) + 1

            now = int(time.time())
            cutoff = now - BUY_LIMIT_RESET_SECONDS

            candidates: List[Dict[str, Any]] = []
            for item_id, lp in latest.items():
                if item_id in blocked:
                    rej("blocked"); continue
                if item_id in active_ids:
                    rej("already_active"); continue
                if item_id not in mapping:
                    rej("no_mapping"); continue

                daily_vol = volumes.get(item_id)
                if daily_vol is None:
                    rej("no_daily_volume"); continue
                if not (MIN_DAILY_VOLUME <= daily_vol <= MAX_DAILY_VOLUME):
                    rej("daily_volume_out_of_range"); continue

                try:
                    low = int(lp.get("low", 0))
                    high = int(lp.get("high", 0))
                    if low <= 0 or high <= 0:
                        rej("bad_prices"); continue
                    if low < MIN_BUY_PRICE:
                        rej("below_min_buy_price"); continue

                    buy_price = max(low + BUY_OVERBID_GP, 1)
                    sell_price = max(high - SELL_UNDERCUT_GP, buy_price + 1)

                    # Aggressive cross model: profit + speed via 24h volume
                    margin = sell_price - buy_price
                    if margin < MIN_MARGIN_GP:
                        rej("margin_too_small"); continue

                    profit_per = sell_price - buy_price - seller_tax(sell_price, item_id)
                    if profit_per < max(1, int(min_margin_eff)):
                        rej("profit_after_tax_too_small"); continue

                    roi = profit_per / float(buy_price)
                    if roi < min_roi_eff:
                        rej("roi_too_low"); continue
                    if roi > MAX_ROI:
                        rej("roi_too_high"); continue
# Quantity sizing: cap quantity so it should fill quickly based on 24h volume
                    qty_budget = int(per_slot_budget // max(1, buy_price))
                    if qty_budget <= 0:
                        rej("qty_zero_budget"); continue

                    per_min = daily_vol / 1440.0
                    qty_speed_cap = max(1, int(per_min * max(TARGET_FILL_MINUTES, 0.1) * max(FILL_FRACTION, 0.01)))
                    qty = min(qty_budget, qty_speed_cap)

                    # Respect buy limit (4h)
                    lim = item_buy_limit(item_id) or 0
                    note = ""
                    if lim > 0:
                        used = int(_buy_queue_used.get(item_id, 0))
                        remaining = max(0, lim - used)
                        if remaining <= 0:
                            rej("limit_reached"); continue
                        qty = min(qty, remaining)
                        note = f"limit remaining {remaining}/{lim} (4h)"

                    if qty <= 0:
                        rej("qty_zero"); continue

                    mins = estimate_minutes_from_daily(qty, daily_vol)
                    if mins > (TARGET_FILL_MINUTES * 3.0):
                        rej("too_slow"); continue

                    expected_profit = profit_per * qty
                    if expected_profit < MIN_TOTAL_PROFIT_GP:
                        rej("min_total_profit"); continue

                    speed_weight = 2.0 / math.sqrt(max(mins, 0.25))
                    score = (expected_profit / max(mins, 0.25)) * speed_weight
                    # Prior boost from "good flips" CSV
                    if GOOD_CSV_ENABLED and _WINNER_ITEM_IDS and item_id in _WINNER_ITEM_IDS:
                        score *= GOOD_CSV_SCORE_BOOST

                    candidates.append({
                        "item_id": item_id,
                        "name": meta.name,
                        "price": buy_price,
                        "quantity": qty,
                        "expectedProfit": float(expected_profit),
                        "expectedDuration": float(mins),
                        "score": float(score),
                        "note": note,
                    })
                except Exception:
                    rej("exception"); continue

            if not candidates:
                if DEBUG_REJECTIONS and reject_counts:
                    top = sorted(reject_counts.items(), key=lambda x: x[1], reverse=True)[:12]
                    logger.info("[REJECTS] top reasons: " + ", ".join([f"{k}={v}" for k, v in top]))
                return _reply_suggestion(build_wait("Wait (no buy candidates)"))

            candidates.sort(key=lambda x: x["score"], reverse=True)

            # Optional trend assist: for longer horizons, re-score top candidates using recent timeseries direction.
            if ENABLE_TRENDS and tf_minutes > 5 and candidates:
                top_n = min(len(candidates), max(1, TREND_RECHECK_TOP_N))
                influence = 2.0 if tf_minutes <= 30 else (3.5 if tf_minutes <= 120 else 5.0)
                for c in candidates[:top_n]:
                    try:
                        trend = TREND_CACHE.get(int(c.get("item_id") or 0), tf_minutes)
                    except Exception:
                        trend = 0.0

                    # store for debugging/UI
                    c["trend"] = float(trend)

                    # clamp and adjust score gently
                    t = max(-0.05, min(0.05, float(trend)))
                    c["score"] = float(c["score"]) * (1.0 + (t * influence))

                    # for 2h/8h horizons, strongly negative trends are usually bad holds
                    if tf_minutes >= 120 and float(trend) < -0.03:
                        c["score"] *= 0.5

                candidates.sort(key=lambda x: x["score"], reverse=True)


            buy_queue: List[Dict[str, Any]] = []
            for c in candidates[:max(slots_open, 1)]:
                buy_queue.append(
                    build_buy(
                        int(empty_slot_id),
                        int(c["item_id"]),
                        str(c["name"]),
                        int(c["price"]),
                        int(c["quantity"]),
                        float(c["expectedProfit"]),
                        float(c["expectedDuration"]),
                        note=str(c.get("note", "")),
                    )
                )

            led["buy_queue"] = buy_queue[1:]
            save_ledger(led)

            first = buy_queue[0]
            record_recommendation(first)
            return _reply_suggestion(first)

        if slots_open <= 0:
            return _reply_suggestion(build_wait("Wait (all 8 GE slots full)"))

        return _reply_suggestion(build_wait("Wait (no actionable move)"))

    except Exception:
        logger.exception("[SUGGESTION] fatal error")
        return _reply_suggestion(build_wait("Wait (server issue — check swagflip.log)"))

def _reply_suggestion(action: Dict[str, Any]):
    """
    If client Accepts msgpack, reply in msgpack format and include the split-length headers
    the Java client uses for graph data (we send 0 graph bytes for now).
    Otherwise, reply as JSON.
    """
    if _wants_msgpack():
        suggestion_bytes = _suggestion_to_msgpack(action)
        graph_bytes = b""
        resp = Response(suggestion_bytes + graph_bytes, status=200, content_type="application/x-msgpack")
        resp.headers["X-SUGGESTION-CONTENT-LENGTH"] = str(len(suggestion_bytes))
        resp.headers["X-GRAPH-DATA-CONTENT-LENGTH"] = "0"
        return resp
    return jsonify(action), 200

# ============================================================
# BOOT
# ============================================================
def main():
    db_init()
    t = threading.Thread(target=prices.refresh_forever, daemon=True)
    t.start()

    logger.info("--------------------------------------------------")
    logger.info("   SWAGFLIP BRAIN — ONLINE")
    logger.info("   POST /suggestion")
    logger.info(f"   Dashboard: http://{HOST}:{PORT}/")
    if DASH_TOKEN:
        logger.info("   Dashboard token enabled: add ?token=YOUR_TOKEN")
    logger.info(f"   DB (durable): {DB_PATH}")
    logger.info(f"   Log file: {LOG_PATH}")
    logger.info(f"   Abort cooldown: {ABORT_COOLDOWN_SECONDS}s | Stuck buy abort: {STUCK_BUY_ABORT_SECONDS}s | Stale offer: {STALE_OFFER_SECONDS}s")
    logger.info("   Profit tracking endpoints enabled: /profit-tracking/*")
    logger.info("   Item prices endpoint enabled: /prices (GET/POST)")
    logger.info("--------------------------------------------------")

    app.run(host=HOST, port=PORT, debug=False)

if __name__ == "__main__":
    main()