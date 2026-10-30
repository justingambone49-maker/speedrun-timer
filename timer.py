

"""
Speedrun Split Timer — desktop version (tkinter; Pillow optional for images)

Features:
- Create/select multiple games, each with its own segments, PB, and
  best-ever ("gold") individual segment times.
- Hotkeys for Split/Start, Pause/Resume, Reset and Unsplit.
  Defaults: Enter / Space / Shift+Enter / Backspace.
  Keybinds are stored PER GAME and rebindable in Settings.
- Optional "hotkeys work when the window is not focused" checkbox in
  Settings (Windows only; uses ctypes, no extra packages needed).
- Segments editable (add/remove/reorder/rename/icon) per game.
- Green/red split deltas vs PB, gold highlight for best-ever segments.
- Live "Best Possible Time" while running, "Sum of Best" while idle.
- Stats shown on EVERY split row (they shrink to "…" and then hide when
  the window is too narrow):
    * weekly average (last 7 days), last 10 and last 5 averages
    * reach % (share of runs that made it to this split)
- "Runs since reaching <split>" counter (split picked in Settings per game).
- COUNTDOWN MODE (Settings > Behavior): the split key first shows a live
  "-0:10.00" countdown on the current split's row (where the final +/-
  will appear); press it a second time to actually split. It also pops up by itself once you
  pass the target (+0, into the red).
- Pop-out window: timer + current split (and optionally the next few) with
  split / gold / cumulative times.
- When a run finishes, the +/- deltas stay on screen (compared with the PB
  you were racing, even if you just beat it) so you can screenshot them.
- "No Mistakes" time after a finished run: takes the faster segment of the
  old PB and the run you just did for every split and adds them up.
- Appearance settings: colors (with presets), fonts and sizes, background
  image (needs Pillow: pip install pillow), which columns to show,
  always-on-top, window opacity.
- EVERY setting (colors, fonts, background image, columns, window options,
  pop-out, countdown mode, hotkeys, keybinds) is stored per game and swaps
  when you switch games.
- GOAL TIMES (Settings): up to 5 times to beat (someone's PB, the world
  record...). Each shows on every split row (split on top, cumulative
  below) with a +/- next to it once you've split.
- "See-through" button: makes the window background transparent (Windows)
  for screen recording; press "Solid view" to go back.
- Everything is saved to a local JSON file so it persists between runs.

PB / GOLD RULES:
- PB is the best COMPLETED FULL RUN.
- When a new full-run PB happens, the ENTIRE PB split array is
  replaced by that run's cumulative splits.
- Individual PB splits are NOT independently compared when deciding
  whether the run is a PB.
- Golds are independent individual segment records.
- A gold updates whenever a segment is faster than the existing gold.
- Reset/DNF/partial runs may update golds.
- Reset/DNF/partial runs can NEVER update the PB.
- A slower segment can therefore be part of a faster overall PB.
- Gold-only changes do not create PB-history entries.

Run with: python3 split_timer.py
"""

import collections
import copy
import json
import math
import os
import random
import sys
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
from datetime import date
from pathlib import Path
from tkinter import colorchooser, filedialog, messagebox, ttk

try:
    from PIL import Image, ImageTk
    HAVE_PIL = True
    _RESAMPLE = getattr(Image, "Resampling", Image).BILINEAR
except Exception:  # Pillow is optional
    HAVE_PIL = False
    _RESAMPLE = None


IS_WINDOWS = sys.platform.startswith("win")

if IS_WINDOWS:
    import ctypes


# ---------------------------------------------------------------- storage --

DATA_DIR = Path.home() / ".speedrun_timer"
DATA_FILE = DATA_DIR / "data.json"

DEFAULT_KEYBINDS = {
    "split": "<Return>",
    "pause": "<space>",
    "reset": "<Shift-Return>",
    "unsplit": "<BackSpace>",
}

KEY_ACTIONS = (
    ("split", "Split / Start"),
    ("pause", "Pause / Resume"),
    ("reset", "Reset"),
    ("unsplit", "Unsplit"),
)

COUNTDOWN_TARGETS = {
    "PB split time": "pb_split",
    "PB cumulative time": "pb_cum",
    "Gold split time": "gold",
}

MIN_SPLIT_INTERVAL_MS = 30_000
WEEK_SECONDS = 7 * 24 * 3600

DEFAULT_GAME_NAME = "SMO"
DEFAULT_SINCE_SPLIT = "Metro Kingdom"

DEFAULT_GAME_SEGMENTS = [
    {"name": "Cap Kingdom", "icon": "🎩"},
    {"name": "Cascade Kingdom", "icon": "🦖"},
    {"name": "Sand Kingdom", "icon": "🏜"},
    {"name": "Lake Kingdom", "icon": "🌊"},
    {"name": "Wooded Kingdom", "icon": "🌲"},
    {"name": "Cloud Kingdom", "icon": "☁"},
    {"name": "Lost Kingdom", "icon": "🌋"},
    {"name": "Metro Kingdom", "icon": "🏙"},
    {"name": "Snow Kingdom", "icon": "❄"},
    {"name": "Seaside Kingdom", "icon": "🐚"},
    {"name": "Luncheon Kingdom", "icon": "🍝"},
    {"name": "Ruined Kingdom", "icon": "🐉"},
    {"name": "Bowser's Kingdom", "icon": "👑"},
    {"name": "Moon Kingdom", "icon": "🌙"},
]


def new_game_data(segments=None):
    return {
        "segments": segments if segments is not None else [],
        "pb": [],
        "best": [],
        "pb_history": [],
        "pb_split_mode": False,
        "split_stats": {},
        "since_split": None,
        "keybinds": dict(DEFAULT_KEYBINDS),
        # Every setting belongs to its own game.
        "appearance": merge_appearance(None),
        "countdown_mode": False,
        "countdown_target": "pb_split",
        "global_hotkeys": False,
        "pre_countdown": 0,
        "random_names": False,
        "goals": [],
        "goal_split_mode": False,
    }


def load_data():
    if DATA_FILE.exists():
        try:
            store = json.loads(DATA_FILE.read_text(encoding="utf-8"))
        except Exception:
            store = None

        if isinstance(store, dict):
            _remove_seeded_smo_pb(store)
            return store

    # First run: start with no PB.
    # First completed full run becomes the PB.
    smo = new_game_data([dict(s) for s in DEFAULT_GAME_SEGMENTS])
    smo["since_split"] = DEFAULT_SINCE_SPLIT

    return {
        "games": [DEFAULT_GAME_NAME],
        "current_game": DEFAULT_GAME_NAME,
        "global_hotkeys": False,
        "data": {DEFAULT_GAME_NAME: smo},
    }


def _remove_seeded_smo_pb(store):
    """Remove the old imported SMO PB from existing save data once."""
    old_seeded_pb = [
        128000, 490000, 1134000, 1366000, 2184000, 2575000,
        2935000, 3746000, 4222000, 4956000, 5624000, 5938000,
        6382000, 7122000,
    ]

    smo = store.get("data", {}).get(DEFAULT_GAME_NAME)

    if smo is None:
        return

    if smo.get("pb") == old_seeded_pb:
        smo["pb"] = []
        smo["best"] = []
        smo["pb_history"] = []


def save_data(data):
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    DATA_FILE.write_text(json.dumps(data, indent=2), encoding="utf-8")


# ------------------------------------------------------------- formatting --

def fmt_time(ms, force_hours=False):
    neg = ms < 0
    ms = abs(int(round(ms)))

    h, rem = divmod(ms, 3600000)
    m, rem = divmod(rem, 60000)
    s, cs = divmod(rem, 1000)

    cs //= 10

    if h > 0 or force_hours:
        out = f"{h}:{m:02d}:{s:02d}.{cs:02d}"
    else:
        out = f"{m}:{s:02d}.{cs:02d}"

    return ("-" if neg else "") + out


def fmt_delta(ms):
    if ms is None:
        return ""

    neg = ms < 0
    ms = abs(int(round(ms)))

    h, rem = divmod(ms, 3600000)
    m, rem = divmod(rem, 60000)
    s, cs = divmod(rem, 1000)

    cs //= 10

    if h:
        out = f"{h}:{m:02d}:{s:02d}.{cs:02d}"
    else:
        out = f"{m}:{s:02d}.{cs:02d}"

    return ("-" if neg else "+") + out


def parse_time(s):
    """
    Parse time strings like:
        H:MM:SS.CS
        M:SS.CS
        S.CS

    Returns milliseconds or None.
    """
    if s is None:
        return None

    s = str(s).strip()

    if not s:
        return None

    try:
        parts = s.split(":")

        if len(parts) == 3:
            h = int(parts[0])
            m = int(parts[1])
            sec_part = parts[2]
        elif len(parts) == 2:
            h = 0
            m = int(parts[0])
            sec_part = parts[1]
        else:
            h = 0
            m = 0
            sec_part = parts[0]

        if "." in sec_part:
            sec_str, frac = sec_part.split(".", 1)
            sec = int(sec_str) if sec_str else 0
            cs = int((frac + "00")[:2])
        else:
            sec = int(sec_part) if sec_part else 0
            cs = 0

        return ((h * 3600 + m * 60 + sec) * 1000) + cs * 10

    except Exception:
        return None


_NICE_KEY_NAMES = {
    "Return": "Enter",
    "space": "Space",
    "Control": "Ctrl",
    "Shift": "Shift",
    "Alt": "Alt",
    "BackSpace": "Backspace",
    "Prior": "PageUp",
    "Next": "PageDown",
    "Delete": "Del",
    "Escape": "Esc",
}


def seq_to_label(seq):
    """'<Shift-Return>' -> 'Shift+Enter'."""
    inner = seq.strip().strip("<>")
    out = []

    for p in inner.split("-"):
        if p.startswith("KP_"):
            out.append("Num " + p[3:])
        elif p in _NICE_KEY_NAMES:
            out.append(_NICE_KEY_NAMES[p])
        elif len(p) == 1:
            out.append(p.upper())
        else:
            out.append(p.capitalize())

    return "+".join(out)


# ------------------------------------------------------ global hotkey utils --

_VK_NAMES = {
    "Return": 0x0D, "KP_Enter": 0x0D, "space": 0x20, "BackSpace": 0x08,
    "Tab": 0x09, "Escape": 0x1B, "Delete": 0x2E, "Insert": 0x2D,
    "Home": 0x24, "End": 0x23, "Prior": 0x21, "Next": 0x22,
    "Left": 0x25, "Up": 0x26, "Right": 0x27, "Down": 0x28,
    "Pause": 0x13, "Scroll_Lock": 0x91,
    "KP_Add": 0x6B, "KP_Subtract": 0x6D, "KP_Multiply": 0x6A,
    "KP_Divide": 0x6F, "KP_Decimal": 0x6E,
    "semicolon": 0xBA, "equal": 0xBB, "comma": 0xBC, "minus": 0xBD,
    "period": 0xBE, "slash": 0xBF, "grave": 0xC0, "bracketleft": 0xDB,
    "backslash": 0xDC, "bracketright": 0xDD, "apostrophe": 0xDE,
}


def parse_seq(seq):
    """'<Shift-Return>' -> ({'Shift'}, 'Return')."""
    parts = seq.strip().strip("<>").split("-")
    mods = {p for p in parts[:-1] if p in ("Shift", "Control", "Alt")}
    return mods, parts[-1]


def keysym_to_vk(key):
    """Tk keysym -> Windows virtual-key code (or None if unsupported)."""
    if len(key) == 1 and key.isascii() and key.isalnum():
        return ord(key.upper())

    if key in _VK_NAMES:
        return _VK_NAMES[key]

    if key.startswith("F") and key[1:].isdigit() and 1 <= int(key[1:]) <= 24:
        return 0x70 + int(key[1:]) - 1

    if key.startswith("KP_") and key[3:].isdigit():
        return 0x60 + int(key[3:])

    return None


class KeyStamper(threading.Thread):
    """Windows only. Watches the keys you've bound on its own thread and
    records WHEN each press really happened (perf_counter time).

    If the app freezes (low memory, a stall...), the timer still gets the
    real press time afterwards, so a split lands where you pressed it.
    """

    def __init__(self):
        super().__init__(daemon=True)
        self._lock = threading.Lock()
        self._vks = set()
        self._events = []
        self._down = {}
        self._stop_flag = False
        self.ok = False

    def set_vks(self, vks):
        with self._lock:
            self._vks = set(vks)

    def drain(self):
        with self._lock:
            ev, self._events = self._events, []

        return ev

    def stop(self):
        self._stop_flag = True

    def run(self):
        begun = False

        try:
            user32 = ctypes.windll.user32
            user32.GetForegroundWindow.restype = ctypes.c_void_p
            user32.GetWindowThreadProcessId.argtypes = [
                ctypes.c_void_p, ctypes.POINTER(ctypes.c_ulong),
            ]
            gas = user32.GetAsyncKeyState
            pid = os.getpid()

            try:
                ctypes.windll.winmm.timeBeginPeriod(1)
                begun = True
            except Exception:
                pass

            self.ok = True

            while not self._stop_flag:
                with self._lock:
                    vks = tuple(self._vks)

                for vk in vks:
                    st = gas(vk) & 0xFFFF
                    down = bool(st & 0x8000)
                    was = self._down.get(vk, False)

                    # Second case: a quick tap that fell between two polls.
                    if (down and not was) or (
                        bool(st & 1) and not down and not was
                    ):
                        t = time.perf_counter()

                        mods = frozenset(
                            name
                            for name, code in (
                                ("Shift", 0x10), ("Control", 0x11),
                                ("Alt", 0x12),
                            )
                            if gas(code) & 0x8000
                        )

                        ours = False

                        try:
                            hwnd = user32.GetForegroundWindow()
                            fg_pid = ctypes.c_ulong(0)
                            user32.GetWindowThreadProcessId(
                                hwnd, ctypes.byref(fg_pid)
                            )
                            ours = fg_pid.value == pid
                        except Exception:
                            pass

                        with self._lock:
                            self._events.append((vk, t, mods, ours))
                            del self._events[:-500]

                    self._down[vk] = down

                time.sleep(0.001)
        except Exception:
            pass
        finally:
            self.ok = False

            if begun:
                try:
                    ctypes.windll.winmm.timeEndPeriod(1)
                except Exception:
                    pass


# ------------------------------------------------------------------ theme --

# Fixed palette used by the Settings / Games windows so they stay readable
# no matter what theme the main window uses.
PANEL = "#161b22"
PANEL2 = "#1c222c"
BORDER = "#2a3140"
TEXT = "#e6e9ef"
DIM = "#8b93a3"
RED = "#ff5c5c"
BLUE = "#2f6fed"

FONT_UI = ("Segoe UI", 10)

THEMES = {
    "Dark": {
        "bg": "#0e1116", "panel": "#161b22", "panel2": "#1c222c",
        "border": "#2a3140", "text": "#e6e9ef", "dim": "#8b93a3",
        "green": "#3ddc84", "red": "#ff5c5c", "gold": "#ffcc33",
        "accent": "#2f6fed",
    },
    "Light": {
        "bg": "#f3f4f6", "panel": "#ffffff", "panel2": "#e5e7eb",
        "border": "#d1d5db", "text": "#111827", "dim": "#6b7280",
        "green": "#15a34a", "red": "#dc2626", "gold": "#b7791f",
        "accent": "#2563eb",
    },
    "Neon": {
        "bg": "#05010f", "panel": "#0b0620", "panel2": "#120a30",
        "border": "#3b1d8f", "text": "#e8f7ff", "dim": "#8a7fc8",
        "green": "#00ff9c", "red": "#ff2e63", "gold": "#ffe600",
        "accent": "#7c3aed",
    },
    "OLED": {
        "bg": "#000000", "panel": "#000000", "panel2": "#0a0a0a",
        "border": "#1f1f1f", "text": "#ffffff", "dim": "#7a7a7a",
        "green": "#3ddc84", "red": "#ff5c5c", "gold": "#ffcc33",
        "accent": "#1d4ed8",
    },
}

COLOR_LABELS = (
    ("bg", "Window background"),
    ("panel", "Split list background"),
    ("panel2", "Header / timer background"),
    ("border", "Row divider lines"),
    ("text", "Text"),
    ("dim", "Secondary text"),
    ("green", "Ahead (green)"),
    ("red", "Behind (red)"),
    ("gold", "Gold / PB"),
    ("accent", "Accent / current split"),
)

DEFAULT_APPEARANCE = {
    "colors": dict(THEMES["Dark"]),
    "font_family": "Segoe UI",
    "font_size": 10,
    "big_timer_size": 34,
    "bg_image": "",
    "bg_dim": 55,          # 0 = original image, 100 = solid panel color
    "bg_fit": "cover",     # cover | stretch | fit (whole image visible)
    "bg_anchor": "center", # which part of the image stays put on resize
    "fx_fireworks": True,  # fireworks on a new PB
    "fx_gold": True,       # big GOLD splash on a gold split
    "bg_list": True,       # show image behind the split list
    "bg_info": True,       # show image behind the timer area
    "show_cols": {
        "split": True, "dsplit": True, "gold": True,
        "cum": True, "dcum": True,
        "dgold": True, "gcum": True, "dgcum": True,
    },
    "show_split_stats": True,
    "show_bpt": True,
    "topmost": False,
    "alpha": 100,
    "popout_next": 2,        # upcoming splits shown in the pop-out window
    "popout_topmost": True,
}


MAX_GOALS = 5

# Color that becomes transparent in "See-through" mode (Windows).
SEE_KEY = "#010203"

# A run shorter than this is treated as an accidental start: it is not
# counted (no resets, reach %, split times or golds).
MIN_RUN_MS = 15000

# Pool for the "random pronoun split names" option (display only).
PRONOUNS = [
    "he", "him", "his", "himself", "she", "her", "hers", "herself",
    "they", "them", "their", "theirs", "themself", "themselves",
    "it", "its", "itself", "one", "oneself",
    "xe", "xem", "xyr", "xyrs", "xemself",
    "ze", "zir", "zirs", "zirself", "zie", "hir", "hirs", "hirself",
    "ey", "em", "eir", "eirs", "emself", "e", "ae", "aer", "aers",
    "aerself", "fae", "faer", "faers", "faerself", "ve", "ver", "vis",
    "verself", "per", "pers", "perself", "thon", "thons", "thonself",
    "co", "cos", "coself", "ne", "nem", "nir", "nirs", "nemself",
    "ze/zir", "she/her", "he/him", "they/them", "it/its", "xe/xem",
    "fae/faer", "ey/em", "ve/ver", "ae/aer", "e/em",
]

BG_ANCHORS = {
    "center": (0.5, 0.5),
    "top": (0.5, 0.0),
    "bottom": (0.5, 1.0),
    "left": (0.0, 0.5),
    "right": (1.0, 0.5),
    "top left": (0.0, 0.0),
    "top right": (1.0, 0.0),
    "bottom left": (0.0, 1.0),
    "bottom right": (1.0, 1.0),
}


def goal_times_to_texts(times, n, split_mode):
    """Cumulative ms list -> entry strings (cumulative or per-split)."""
    out = []
    prev = 0

    for k in range(n):
        ms = times[k] if k < len(times) else None

        if ms is None:
            out.append("")
            prev = None
            continue

        if split_mode:
            out.append(fmt_time(ms - prev) if prev is not None else "")
        else:
            out.append(fmt_time(ms))

        prev = ms

    return out


def goal_texts_to_times(texts, split_mode):
    """Entry strings -> (cumulative ms list with None gaps, bad_text)."""
    out = []
    total = 0
    ok = True

    for tx in texts:
        tx = tx.strip()

        if not tx:
            out.append(None)
            ok = False
            continue

        ms = parse_time(tx)

        if ms is None:
            return None, tx

        if split_mode:
            if ok:
                total += ms
                out.append(total)
            else:
                out.append(None)
        else:
            out.append(ms)

    return out, None


def merge_appearance(saved):
    """Defaults + whatever the game has saved (ignores unknown keys)."""
    ap = copy.deepcopy(DEFAULT_APPEARANCE)

    if isinstance(saved, dict):
        for k, v in saved.items():
            if k in ("colors", "show_cols") and isinstance(v, dict):
                ap[k].update({kk: vv for kk, vv in v.items() if kk in ap[k]})
            elif k in ap:
                ap[k] = v

    return ap


def _hex_to_rgb(c):
    c = c.lstrip("#")
    return [int(c[i:i + 2], 16) for i in (0, 2, 4)]


def mix(c1, c2, t):
    """Blend hex color c1 toward c2 by t (0..1)."""
    try:
        a = _hex_to_rgb(c1)
        b = _hex_to_rgb(c2)
    except Exception:
        return c1
    return "#%02x%02x%02x" % tuple(
        int(a[k] * (1 - t) + b[k] * t) for k in range(3)
    )


def contrast(c):
    """Black or white, whichever reads better on color c."""
    try:
        r, g, b = _hex_to_rgb(c)
    except Exception:
        return "#ffffff"
    return "#000000" if (0.299 * r + 0.587 * g + 0.114 * b) / 255 > 0.55 else "#ffffff"


def clamp_int(v, lo, hi, default):
    try:
        v = int(v)
    except (TypeError, ValueError):
        return default
    return max(lo, min(hi, v))


# ------------------------------------------------------------------- app ---

class SplitTimerApp(tk.Tk):

    def __init__(self):
        super().__init__()

        self.title("Split Timer")
        self.geometry("520x760")
        self.minsize(280, 320)

        self.store = load_data()
        self.store.setdefault("games", [])
        self.store.setdefault("data", {})

        # Placeholder until _set_game() loads the current game's own
        # appearance.
        self.game_data = new_game_data()
        self.ap = self.game_data["appearance"]
        self.th = self.ap["colors"]

        # Older saves kept appearance / countdown / hotkey settings in one
        # global spot. Hand each existing game its own copy, then drop the
        # global ones so new games start from defaults.
        for _name in list(self.store["data"].keys()):
            self._get_game_data(_name)

        for _k in ("appearance", "countdown_mode", "countdown_target",
                   "global_hotkeys"):
            self.store.pop(_k, None)

        # Run state: idle | running | paused | finished
        self.run_state = "idle"

        self.start_time = 0.0
        self.paused_accum = 0.0
        self.pause_started_at = 0.0

        self.split_index = 0
        self.split_times = []

        self.last_delta_sign = 0

        # True once this run has reached the game's "since" split.
        self.since_reached_this_run = False

        # Countdown mode: True after the first press, until the real split.
        self.countdown_armed = False
        self.countdown_text = ""
        self.countdown_color = "green"
        self._cd_item = None
        self._gd_item = None
        self._gd_diff = 0

        # Pre-countdown: True from pressing start until the timer hits 0.
        self._pre_pending = False

        # A run only "counts" once it passes MIN_RUN_MS. Splits made before
        # that wait here and are recorded when it does.
        self._run_counted = False
        self._pending_stats = []

        # Golds as they were when this run started (for the gold deltas).
        self.run_best = None

        # Random pronoun names for this run (see PRONOUNS).
        self.run_names = None

        # Fireworks / GOLD splash state.
        self._fx_parts = []
        self._fx_rockets = []
        self._fx_spawn = []
        self._fx_gold_start = None
        self._fx_gold_fonts = None
        self._fx_job = None
        self._fx_last = 0.0

        # PB as it was when this run started. After a PB the stored PB is
        # replaced by this run, so the finished screen compares against
        # this copy to keep the +/- deltas visible.
        self.run_pb = None

        # "No Mistakes" time for the finished run (old PB + this run).
        self.no_mistakes = None

        # "See-through" mode (transparent window background).
        self.see_through = False

        # Pop-out window (current split + timer)
        self.popout = None
        self.pop_canvas = None
        self.pop_big = None
        self.pop_split = None
        self.pop_delta = None
        self._pop_cd_item = None
        self._pop_geom_key = None

        # What the timer canvas shows (colors are theme KEYS, not hex).
        self.big_text = "0:00.00"
        self.big_color = "text"
        self.split_text = "Split: 0:00.00"
        self.delta_text = ""
        self.delta_color = "dim"

        self._tick_job = None

        self.listening_for = None
        self.modal_open = False
        self.modal_win = None

        # Hotkey bookkeeping
        self._bound_sequences = []
        self._global_binds = {}
        self._prev_down = {}
        self._poll_job = None

        # Real key-press times (survive app freezes) and a heartbeat used to
        # tell a genuinely delayed press from a stale one.
        self._event_time = None
        self._stamp_buf = []
        self._last_beat = time.perf_counter()
        self._stalls = collections.deque(maxlen=30)
        self._beat_job = None
        self.stamper = None

        if IS_WINDOWS:
            try:
                self.stamper = KeyStamper()
                self.stamper.start()
            except Exception:
                self.stamper = None

        # Background image caches
        self._bg_job = None
        self._ap_job = None
        self._bg_src = None
        self._bg_src_key = None
        self._bg_cache_key = None
        self._bg_cache_img = None
        self._bg_refs = {}

        self._row_h = 40
        self.main = None

        self.current_game = None
        self.game_data = None
        self.keybinds = None

        name = self.store.get("current_game")

        if name not in self.store["games"]:
            name = self.store["games"][0] if self.store["games"] else None

        self._set_game(name)

        self.bind_all("<Button-1>", self._on_click_focus, add="+")

        self._build_ui()
        self._apply_window_attrs()
        self._render_all()

    # ---------------------------------------------------------- appearance --

    def _apply_window_attrs(self):
        try:
            self.attributes("-topmost", bool(self.ap.get("topmost")))
        except tk.TclError:
            pass

        try:
            alpha = clamp_int(self.ap.get("alpha"), 30, 100, 100)
            self.attributes("-alpha", alpha / 100)
        except tk.TclError:
            pass

        if self.popout is not None:
            try:
                self.popout.attributes(
                    "-topmost", bool(self.ap.get("popout_topmost"))
                )
            except tk.TclError:
                pass

    def _appearance_changed(self):
        """Save + redraw the main window (debounced)."""
        self._persist()
        self._apply_window_attrs()

        if self._ap_job is not None:
            try:
                self.after_cancel(self._ap_job)
            except Exception:
                pass

        self._ap_job = self.after(120, self._rebuild_ui)

    def _refresh_theme(self):
        """self.th = this game's colors, or the see-through version."""
        base = self.ap["colors"]

        if self.see_through:
            th = dict(base)

            for k in ("bg", "panel", "panel2"):
                th[k] = SEE_KEY

            self.th = th
        else:
            self.th = base

    def _apply_see_through(self):
        wins = [self]

        if self.popout is not None:
            wins.append(self.popout)

        for w in wins:
            try:
                w.attributes(
                    "-transparentcolor", SEE_KEY if self.see_through else ""
                )
            except tk.TclError:
                # Only Windows can make a color transparent; elsewhere just
                # fade the window.
                try:
                    w.attributes(
                        "-alpha", 0.45 if self.see_through else 1.0
                    )
                except tk.TclError:
                    pass

        if not self.see_through:
            self._apply_window_attrs()

    def toggle_see_through(self):
        self.see_through = not self.see_through
        self._apply_see_through()
        self._rebuild_ui()

    def _make_fonts(self):
        fam = self.ap.get("font_family") or "Segoe UI"
        s = clamp_int(self.ap.get("font_size"), 7, 24, 10)
        big = clamp_int(self.ap.get("big_timer_size"), 16, 90, 34)

        def f(size, bold=False):
            return tkfont.Font(
                family=fam, size=max(6, size),
                weight="bold" if bold else "normal",
            )

        self.f_ui = f(s)
        self.f_ui_b = f(s, True)
        self.f_header = f(s + 2, True)
        self.f_small = f(s - 1)
        self.f_small_b = f(s - 1, True)
        self.f_tiny = f(s - 2)
        self.f_tiny_b = f(s - 2, True)
        self.f_stat = f(s - 1)
        self.f_split = f(s + 4)
        self.f_delta = f(s + 4, True)
        self.f_big = f(big, True)

    # --------------------------------------------------------- data utils --

    def _get_game_data(self, name):
        if not name:
            return new_game_data()

        d = self.store["data"].setdefault(name, new_game_data())

        d.setdefault("segments", [])
        d.setdefault("pb", [])
        d.setdefault("best", [])
        d.setdefault("pb_history", [])
        d.setdefault("pb_split_mode", False)
        d.setdefault("split_stats", {})
        d.setdefault("pre_countdown", 0)
        d.setdefault("random_names", False)
        d.setdefault("goals", [])
        d.setdefault("goal_split_mode", False)

        if "since_split" not in d:
            names = [s.get("name", "") for s in d["segments"]]
            d["since_split"] = (
                DEFAULT_SINCE_SPLIT if DEFAULT_SINCE_SPLIT in names else None
            )

        # Keybinds are per game. Older saves had one global set, so use
        # that as the starting point for games that don't have their own.
        if "keybinds" not in d:
            kb = dict(DEFAULT_KEYBINDS)
            old = self.store.get("keybinds")
            if isinstance(old, dict):
                kb.update(old)
            d["keybinds"] = kb
        else:
            for k, v in DEFAULT_KEYBINDS.items():
                d["keybinds"].setdefault(k, v)

        # Per-game settings. A game without its own yet starts from the
        # old global value (older saves) or the defaults.
        saved_ap = d.get("appearance")

        if not isinstance(saved_ap, dict):
            saved_ap = self.store.get("appearance")

        d["appearance"] = merge_appearance(saved_ap)

        if "countdown_mode" not in d:
            d["countdown_mode"] = bool(self.store.get("countdown_mode", False))

        if "countdown_target" not in d:
            d["countdown_target"] = self.store.get(
                "countdown_target", "pb_split"
            )

        if "global_hotkeys" not in d:
            d["global_hotkeys"] = bool(self.store.get("global_hotkeys", False))

        return d

    def _set_game(self, name):
        self.current_game = name
        self.game_data = self._get_game_data(name)
        self.keybinds = self.game_data["keybinds"]

        # Colors, fonts, image, columns, window options, pop-out,
        # countdown and hotkey settings all come from this game.
        self.ap = self.game_data["appearance"]
        self._refresh_theme()

        self.countdown_armed = False

        self._refresh_daily_stats()
        self._apply_keybinds()

    def _switch_game(self, name):
        # Save golds from any run in progress to the OLD game first.
        self.do_reset(count_reset=False)

        self._set_game(name)
        self._apply_window_attrs()
        self._rebuild_ui()
        self._persist()

    def _delete_game(self, name):
        was_current = name == self.current_game

        if was_current:
            # Don't save the partial run anywhere; the game is going away.
            self.do_reset(count_reset=False, save=False)

        if name in self.store["games"]:
            self.store["games"].remove(name)

        self.store["data"].pop(name, None)

        if was_current:
            nxt = self.store["games"][0] if self.store["games"] else None
            self._set_game(nxt)
            self._apply_window_attrs()
            self._rebuild_ui()

        self._persist()

    def _persist(self):
        self.store["current_game"] = self.current_game

        if self.current_game:
            self.store["data"][self.current_game] = self.game_data

        save_data(self.store)

    def export_game_to_json(self):
        if not self.current_game:
            return

        file_path = filedialog.asksaveasfilename(
            title="Export game",
            defaultextension=".json",
            initialfile=f"{self.current_game}_split_export.json",
            filetypes=[("JSON files", "*.json")],
        )

        if not file_path:
            return

        export_data = {
            "game": self.current_game,
            "segments": self.game_data.get("segments", []),
            "pb": self.game_data.get("pb", []),
            "best": self.game_data.get("best", []),
            "pb_history": self.game_data.get("pb_history", []),
            "pb_split_mode": self.game_data.get("pb_split_mode", False),
            "split_stats": self.game_data.get("split_stats", {}),
            "since_split": self.game_data.get("since_split"),
        }

        Path(file_path).write_text(
            json.dumps(export_data, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )

        messagebox.showinfo("Exported", f"Game exported to:\n{file_path}")

    def import_game_from_json(self):
        if not self.current_game:
            return

        file_path = filedialog.askopenfilename(
            title="Import game",
            defaultextension=".json",
            filetypes=[("JSON files", "*.json")],
        )

        if not file_path:
            return

        try:
            imported = json.loads(
                Path(file_path).read_text(encoding="utf-8")
            )

            if not isinstance(imported, dict):
                raise ValueError("The JSON root must be an object.")

            imported_pb = imported.get("pb", [])
            imported_best = imported.get("best", [])
            imported_segments = imported.get(
                "segments", self.game_data.get("segments", [])
            )

            if not isinstance(imported_pb, list):
                raise ValueError("PB times must be an array.")

            if not isinstance(imported_best, list):
                raise ValueError("Gold times must be an array.")

            if not isinstance(imported_segments, list):
                raise ValueError("Segments must be an array.")

        except (OSError, json.JSONDecodeError, ValueError) as exc:
            messagebox.showerror("Import failed", f"Could not read file:\n{exc}")
            return

        if not all(
            isinstance(v, (int, float)) and v >= 0 for v in imported_pb
        ):
            messagebox.showerror(
                "Import failed",
                "PB times must be non-negative numbers in milliseconds."
            )
            return

        if not all(
            v is None or (isinstance(v, (int, float)) and v >= 0)
            for v in imported_best
        ):
            messagebox.showerror(
                "Import failed",
                "Gold times must be non-negative numbers in milliseconds."
            )
            return

        self.game_data["segments"] = imported_segments
        self.game_data["pb"] = [int(v) for v in imported_pb]
        self.game_data["best"] = [
            None if v is None else int(v) for v in imported_best
        ]

        # Imported PB history is kept, but this import itself
        # does not create a new PB-history entry.
        self.game_data["pb_history"] = imported.get("pb_history", [])
        self.game_data["pb_split_mode"] = bool(
            imported.get("pb_split_mode", False)
        )

        if isinstance(imported.get("split_stats"), dict):
            self.game_data["split_stats"] = imported["split_stats"]

        if "since_split" in imported:
            self.game_data["since_split"] = imported["since_split"]

        self._persist()
        self._render_header()
        self._render_segments()

        messagebox.showinfo("Imported", f"Imported times from:\n{file_path}")

    def copy_pb_to_sheet(self):
        if not self.current_game:
            return

        segments = self.game_data.get("segments", [])
        pb = self.game_data.get("pb", [])
        best = self.game_data.get("best", [])

        rows = ["#\tIcon\tSegment\tPB cumulative\tPB segment\tGold"]

        for index, segment in enumerate(segments):
            pb_cumulative = pb[index] if index < len(pb) else None

            previous_pb = (
                pb[index - 1] if index > 0 and index - 1 < len(pb) else 0
            )

            pb_segment = (
                pb_cumulative - previous_pb
                if pb_cumulative is not None
                else None
            )

            gold = best[index] if index < len(best) else None

            rows.append("\t".join([
                str(index + 1),
                str(segment.get("icon", "")),
                str(segment.get("name", "")),
                fmt_time(pb_cumulative) if pb_cumulative is not None else "",
                fmt_time(pb_segment) if pb_segment is not None else "",
                fmt_time(gold) if gold is not None else "",
            ]))

        self.clipboard_clear()
        self.clipboard_append("\n".join(rows))
        self.update()

        self._flash_header("PB rows copied for Sheets")

    # ------------------------------------------------------- split stats --

    def _seg_key(self, i):
        return self.game_data["segments"][i].get("name", "").strip().lower()

    def _seg_stats(self, i):
        """Stats for segment i, keyed by segment name (case-insensitive)."""
        st = self.game_data.setdefault("split_stats", {}).setdefault(
            self._seg_key(i),
            {"reached": 0, "resets": 0, "times": [], "stamps": []},
        )

        st.setdefault("reached", 0)
        st.setdefault("resets", 0)
        st.setdefault("times", [])
        stamps = st.setdefault("stamps", [])

        # Keep timestamps lined up with times. Runs recorded before
        # timestamps existed get 0 (= "unknown", excluded from the week).
        while len(stamps) < len(st["times"]):
            stamps.insert(0, 0)

        if len(stamps) > len(st["times"]):
            del stamps[len(st["times"]):]

        return st

    @staticmethod
    def _avg_text(vals):
        return fmt_time(sum(vals) / len(vals)) if vals else "--"

    def _row_stats_text(self, i):
        """Two short lines of stats for segment i (shown on its row)."""
        st = self._seg_stats(i)

        reached = st["reached"]
        resets = st["resets"]
        times = st["times"]

        cutoff = time.time() - WEEK_SECONDS
        week = [t for t, s in zip(times, st["stamps"]) if s >= cutoff]

        # Share of runs that made it to this split. Every run reaches the
        # first split, so its count is the total number of runs.
        total = self._seg_stats(0)["reached"]

        pct = f"{reached / total * 100:.1f}%" if total else "--"

        line1 = (
            f"Wk {self._avg_text(week)}   "
            f"L10 {self._avg_text(times[-10:])}   "
            f"L5 {self._avg_text(times[-5:])}"
        )
        line2 = f"Reach {pct} ({reached}/{total})"

        return line1, line2

    # ------------------------------------------------------------- layout --

    def _build_ui(self):
        self._refresh_theme()
        th = self.th

        self._make_fonts()
        self.configure(bg=th["bg"])

        self.main = tk.Frame(self, bg=th["bg"])
        self.main.pack(fill="both", expand=True)
        self.main.bind("<Configure>", self._on_main_configure)

        # Header
        header = tk.Frame(self.main, bg=th["panel2"])
        header.pack(fill="x")

        btnrow = tk.Frame(header, bg=th["panel2"])
        btnrow.pack(fill="x", padx=8, pady=(6, 0))

        solid = self.ap["colors"]

        for text, cmd in (("Games", self.open_games),
                          ("Pop-out", self.open_popout),
                          ("⚙ Settings", self.open_settings),
                          ("See-through", self.toggle_see_through)):
            is_toggle = text == "See-through"

            # In see-through mode only the way back stays on screen.
            if self.see_through and not is_toggle:
                continue

            tk.Button(
                btnrow,
                text=("Solid view" if self.see_through else text)
                if is_toggle else text,
                command=cmd,
                bg=solid["panel2"] if is_toggle else th["panel2"],
                fg=solid["dim"] if is_toggle else th["dim"],
                activebackground=solid["panel2"] if is_toggle
                else th["panel2"],
                activeforeground=th["text"],
                bd=1, relief="solid", highlightbackground=th["border"],
                font=self.f_ui, takefocus=0,
            ).pack(side="right", padx=2)

        self.stats_lbl = tk.Label(
            btnrow, text="", bg=th["panel2"], fg=th["dim"],
            font=self.f_tiny, anchor="e",
        )
        self.stats_lbl.pack(side="right", padx=8)

        self.game_title_lbl = tk.Label(
            header, text="No Game Selected", bg=th["panel2"], fg=th["text"],
            font=self.f_header,
        )
        self.game_title_lbl.pack(pady=(2, 0))

        self.category_lbl = tk.Label(
            header, text="", bg=th["panel2"], fg=th["dim"], font=self.f_ui,
        )
        self.category_lbl.pack(pady=(0, 2))

        self.category_lbl.pack_configure(pady=(0, 6))

        # Split list (drawn on a canvas so a background image can show
        # through behind the text)
        seg_outer = tk.Frame(self.main, bg=th["panel"])
        seg_outer.pack(fill="both", expand=True)

        self.seg_scroll = tk.Scrollbar(seg_outer, orient="vertical")

        self.seg_canvas = tk.Canvas(
            seg_outer, bg=th["panel"], highlightthickness=0,
            yscrollincrement=20, yscrollcommand=self._on_list_yscroll,
        )

        self.seg_scroll.config(command=self.seg_canvas.yview)

        self.seg_canvas.pack(side="left", fill="both", expand=True)
        if not self.see_through:
            self.seg_scroll.pack(side="right", fill="y")

        self.seg_canvas.bind("<Configure>", self._on_list_configure)

        self.seg_canvas.bind(
            "<MouseWheel>",
            lambda e: self.seg_canvas.yview_scroll(
                int(-e.delta / 120) or (-1 if e.delta > 0 else 1), "units"
            ),
        )
        self.seg_canvas.bind(
            "<Button-4>", lambda e: self.seg_canvas.yview_scroll(-1, "units")
        )
        self.seg_canvas.bind(
            "<Button-5>", lambda e: self.seg_canvas.yview_scroll(1, "units")
        )

        # Timer area (also a canvas)
        h_big = self.f_big.metrics("linespace")
        h_split = max(
            self.f_split.metrics("linespace"),
            self.f_delta.metrics("linespace"),
        )
        h_stat = self.f_stat.metrics("linespace")
        show_bpt = bool(self.ap.get("show_bpt"))

        self._info_pad = 6
        self._info_y_big = self._info_pad + h_big / 2
        self._info_y_split = self._info_pad + h_big + h_split / 2
        self._info_y_bpt = self._info_pad + h_big + h_split + 4 + h_stat / 2
        self._info_y_pace = (
            self._info_pad + h_big + h_split + 4 + h_stat + 2 + h_stat / 2
        )

        info_h = int(
            self._info_pad + h_big + h_split
            + ((4 + h_stat + 2 + h_stat) if show_bpt else 0) + 8
        )

        self.info_canvas = tk.Canvas(
            self.main, bg=th["panel2"], highlightthickness=0, height=info_h,
        )
        self.info_canvas.pack(fill="x")

        c = self.info_canvas

        self.i_big = c.create_text(
            0, 0, text="0:00.00", anchor="e", font=self.f_big, fill=th["text"]
        )
        self.i_split = c.create_text(
            0, 0, text="Split: 0:00.00", anchor="e", font=self.f_split,
            fill=th["dim"],
        )
        self.i_delta = c.create_text(
            0, 0, text="", anchor="w", font=self.f_delta, fill=th["dim"]
        )
        self.i_bpt_lbl = c.create_text(
            0, 0, text="Sum of Best", anchor="w", font=self.f_stat,
            fill=th["dim"],
            state="normal" if show_bpt else "hidden",
        )
        self.i_bpt_val = c.create_text(
            0, 0, text="--", anchor="e", font=self.f_stat, fill=th["gold"],
            state="normal" if show_bpt else "hidden",
        )

        self.i_pace_lbl = c.create_text(
            0, 0, text="On Pace For (PB splits)", anchor="w",
            font=self.f_stat, fill=th["dim"],
            state="normal" if show_bpt else "hidden",
        )
        self.i_pace_val = c.create_text(
            0, 0, text="--", anchor="e", font=self.f_stat, fill=th["dim"],
            state="normal" if show_bpt else "hidden",
        )

        c.bind("<Configure>", self._layout_info)

        # Controls
        controls = tk.Frame(self.main, bg=th["panel"])

        if not self.see_through:
            controls.pack(fill="x", padx=8, pady=(0, 8))

        on_accent = contrast(th["accent"])
        reset_bg = mix(th["panel2"], th["red"], 0.2)

        def make_btn(text, cmd, bg, fg):
            b = tk.Button(
                controls, text=text, command=cmd, bg=bg, fg=fg,
                activebackground=bg, activeforeground=fg, bd=0,
                font=self.f_ui, takefocus=0,
            )
            b.pack(side="left", expand=True, fill="x", padx=3, ipady=6)
            return b

        self.btn_split = make_btn(
            "Split", self.do_split, th["accent"], on_accent
        )
        self.btn_pause = make_btn(
            "Pause", self.do_pause_resume, th["panel2"], th["text"]
        )
        self.btn_reset = make_btn("Reset", self.do_reset, reset_bg, th["red"])
        self.btn_unsplit = make_btn(
            "Unsplit", self.do_unsplit, th["panel2"], th["text"]
        )

        self.after_idle(self._schedule_bg)

    def _rebuild_ui(self):
        """Destroy and rebuild the main window (after theme changes)."""
        self._ap_job = None
        self._fx_stop()

        if self.main is not None:
            self.main.destroy()

        self._bg_cache_key = None
        self._bg_refs = {}

        self._build_ui()
        self._render_all()
        self._paint_info()

    # ------------------------------------------------------ timer canvas --

    def _layout_info(self, event=None):
        c = self.info_canvas
        w = c.winfo_width()

        if w < 20:
            return

        c.coords(self.i_big, w - 14, self._info_y_big)
        c.coords(self.i_split, w - 14, self._info_y_split)
        c.coords(self.i_delta, 14, self._info_y_split)
        c.coords(self.i_bpt_lbl, 14, self._info_y_bpt)
        c.coords(self.i_bpt_val, w - 14, self._info_y_bpt)
        c.coords(self.i_pace_lbl, 14, self._info_y_pace)
        c.coords(self.i_pace_val, w - 14, self._info_y_pace)

        self._schedule_bg()

    def _paint_info(self):
        th = self.th
        c = self.info_canvas

        try:
            c.itemconfig(
                self.i_big, text=self.big_text,
                fill=th.get(self.big_color, th["text"]),
            )
            c.itemconfig(self.i_split, text=self.split_text, fill=th["dim"])
            c.itemconfig(
                self.i_delta, text=self.delta_text,
                fill=th.get(self.delta_color, th["dim"]),
            )
        except tk.TclError:
            pass

        self._render_pace()
        self._paint_popout()

    def _compute_on_pace(self):
        """Projected finish: time so far + the rest of your current PB.

        Finished splits count as they happened; the split you're on counts
        as the longer of your PB split and how long you've been on it; every
        later split uses its PB split time (not golds).
        """
        segs = self.game_data["segments"]
        pb = self.game_data["pb"]

        if not self.current_game or not segs or len(pb) < len(segs):
            return None

        if self.run_state == "finished" and self.split_times:
            return self.split_times[-1]

        if self.run_state not in ("running", "paused"):
            return None

        i = min(self.split_index, len(segs) - 1)
        base = self.split_times[-1] if self.split_times else 0

        pb_seg = pb[i] - (pb[i - 1] if i > 0 else 0)
        cur = self._current_split_elapsed_ms()

        return base + max(cur, pb_seg) + (pb[len(segs) - 1] - pb[i])

    def _render_pace(self):
        try:
            c = self.info_canvas
            pace = self._compute_on_pace()
            th = self.th

            if pace is None:
                c.itemconfig(self.i_pace_val, text="--", fill=th["dim"])
                return

            pbs = (
                self.run_pb
                if self.run_state == "finished" and self.run_pb
                else self.game_data["pb"]
            )

            diff = pace - pbs[-1]

            c.itemconfig(
                self.i_pace_val,
                text=fmt_time(pace),
                fill=th["green" if diff <= 0 else "red"],
            )
        except (tk.TclError, AttributeError):
            pass

    # -------------------------------------------------- background image --

    def _on_main_configure(self, event):
        if event.widget is self.main:
            self._schedule_bg()

    def _on_list_configure(self, event):
        self._render_segments()
        self._schedule_bg()

    def _on_list_yscroll(self, first, last):
        self.seg_scroll.set(first, last)

        # Keep the background image pinned to the viewport while the
        # rows scroll over it.
        try:
            self.seg_canvas.coords("bg", 0, self.seg_canvas.canvasy(0))
        except tk.TclError:
            pass

    def _schedule_bg(self):
        if self._bg_job is not None:
            try:
                self.after_cancel(self._bg_job)
            except Exception:
                pass

        self._bg_job = self.after(60, self._refresh_bg)

    def _refresh_bg(self):
        self._bg_job = None

        try:
            self._update_bg(self.seg_canvas, "bg_list")
            self._update_bg(self.info_canvas, "bg_info")
        except tk.TclError:
            pass

    def _bg_source(self):
        path = self.ap.get("bg_image") or ""

        if not (HAVE_PIL and path and Path(path).is_file()):
            return None

        try:
            key = (path, Path(path).stat().st_mtime)
        except OSError:
            return None

        if self._bg_src_key != key:
            self._bg_src_key = key

            try:
                im = Image.open(path).convert("RGB")
                im.thumbnail((1920, 1920))
                self._bg_src = im
            except Exception:
                self._bg_src = None

        return self._bg_src

    def _bg_full(self):
        """The whole-window background (scaled + dimmed), as a PIL image."""
        src = self._bg_source()

        if src is None or self.main is None:
            return None

        w = max(self.main.winfo_width(), 1)
        h = max(self.main.winfo_height(), 1)

        fit = self.ap.get("bg_fit", "cover")
        dim = clamp_int(self.ap.get("bg_dim"), 0, 100, 55)

        anchor = self.ap.get("bg_anchor", "center")
        ax, ay = BG_ANCHORS.get(anchor, (0.5, 0.5))

        key = (self._bg_src_key, w, h, fit, anchor, dim, self.th["panel"])

        if key == self._bg_cache_key:
            return self._bg_cache_img

        # The image is re-scaled every time the window size changes, so it
        # shrinks and grows with the window. The anchor decides which part
        # of it stays in place (cover: which part is kept; fit: where the
        # smaller picture sits).
        if fit == "stretch":
            img = src.resize((w, h), _RESAMPLE)
        elif fit == "fit":
            scale = min(w / src.width, h / src.height)
            nw = max(1, int(src.width * scale + 0.5))
            nh = max(1, int(src.height * scale + 0.5))
            small = src.resize((nw, nh), _RESAMPLE)
            img = Image.new("RGB", (w, h), self.th["panel"])
            img.paste(small, (int((w - nw) * ax), int((h - nh) * ay)))
        else:
            scale = max(w / src.width, h / src.height)
            nw = max(1, int(src.width * scale + 0.5))
            nh = max(1, int(src.height * scale + 0.5))
            img = src.resize((nw, nh), _RESAMPLE)
            left = int((nw - w) * ax)
            top = int((nh - h) * ay)
            img = img.crop((left, top, left + w, top + h))

        if dim > 0:
            try:
                solid = Image.new("RGB", img.size, self.th["panel"])
                img = Image.blend(img, solid, dim / 100)
            except Exception:
                pass

        self._bg_cache_key = key
        self._bg_cache_img = img

        return img

    def _update_bg(self, canvas, flag):
        canvas.delete("bg")

        if not self.ap.get(flag) or self.see_through:
            return

        full = self._bg_full()

        if full is None:
            return

        w = canvas.winfo_width()
        h = canvas.winfo_height()

        if w < 2 or h < 2:
            return

        x0 = canvas.winfo_rootx() - self.main.winfo_rootx()
        y0 = canvas.winfo_rooty() - self.main.winfo_rooty()

        photo = ImageTk.PhotoImage(full.crop((x0, y0, x0 + w, y0 + h)))

        self._bg_refs[flag] = photo

        canvas.create_image(
            0, canvas.canvasy(0), anchor="nw", image=photo, tags="bg"
        )
        canvas.tag_lower("bg")

    # --------------------------------------------------------- keybinding --

    def _action_fns(self):
        return {
            "split": self.do_split,
            "pause": self.do_pause_resume,
            "reset": self.do_reset,
            "unsplit": self.do_unsplit,
        }

    def _global_active(self):
        return IS_WINDOWS and bool(self.game_data.get("global_hotkeys"))

    def destroy(self):
        if self.stamper is not None:
            self.stamper.stop()

        super().destroy()

    # --------------------------------------------------- real press times --

    def _now(self):
        """'Now' for the timer: the real moment of the key press while a
        key handler is running, otherwise the actual current time."""
        t = self._event_time

        return t if t is not None else time.perf_counter()

    def _run_with_time(self, fn, at=None):
        prev = self._event_time

        if at is not None:
            at = min(at, time.perf_counter())

        self._event_time = at

        try:
            fn()
        finally:
            self._event_time = prev

    def _stamper_ready(self):
        st = self.stamper

        return st is not None and st.ok and st.is_alive()

    def _pull_stamps(self):
        if not self._stamper_ready():
            return

        self._stamp_buf.extend(self.stamper.drain())

        cutoff = time.perf_counter() - 300
        self._stamp_buf = [e for e in self._stamp_buf if e[1] >= cutoff]

    def _beat(self):
        """Heartbeat: a gap here means the app was frozen."""
        now = time.perf_counter()

        if now - self._last_beat > 0.3:
            self._stalls.append((self._last_beat - 0.05, now))

        self._last_beat = now
        self._beat_job = self.after(40, self._beat)

    def _stamp_valid(self, t):
        # A press the app handled promptly happens after the previous beat;
        # a delayed one falls inside a freeze window. Anything else is a
        # leftover (e.g. Enter pressed in another window).
        if t >= self._last_beat - 0.05:
            return True

        return any(a <= t <= b for a, b in self._stalls)

    def _take_stamp(self, vk):
        """Real time of the key press this Tk key event belongs to."""
        if vk is None or not self._stamper_ready():
            return None

        self._pull_stamps()

        out = None
        keep = []

        for ev in self._stamp_buf:
            if out is None and ev[0] == vk:
                if ev[3] and self._stamp_valid(ev[1]):
                    out = ev[1]

                continue

            keep.append(ev)

        self._stamp_buf = keep

        return out

    def _focus_widget(self):
        try:
            return self.focus_get()
        except Exception:
            # Tk raises KeyError for some popup widgets (e.g. menus).
            return None

    def _typing_in_modal(self, widget=None):
        """True only if keyboard focus is inside the open Settings/Games
        window."""
        win = self.modal_win

        if not self.modal_open or win is None:
            return False

        try:
            if widget is None or not hasattr(widget, "winfo_toplevel"):
                widget = self._focus_widget()

            return widget is not None and widget.winfo_toplevel() is win
        except Exception:
            return False

    def _on_click_focus(self, event):
        """Clicking the timer (or pop-out) gives it the keyboard again."""
        try:
            top = event.widget.winfo_toplevel()

            if (top is self or top is self.popout) and not isinstance(
                event.widget, (tk.Entry, tk.Text, tk.Spinbox)
            ):
                top.focus_set()
        except Exception:
            pass

    def _apply_keybinds(self):
        """(Re)bind this game's keys: Tk bindings, or global polling."""

        for seq in self._bound_sequences:
            try:
                self.unbind_all(seq)
            except Exception:
                pass

        self._bound_sequences = []
        self._global_binds = {}
        self._prev_down = {}

        def guarded(handler, vk=None):
            def wrapper(event=None):
                # Real moment of the press (matters if the app was frozen).
                at = self._take_stamp(vk)

                # Only ignore the key if you're typing in Settings/Games,
                # not just because one of those windows is open somewhere.
                if self._typing_in_modal(getattr(event, "widget", None)):
                    return

                self._run_with_time(handler, at)
                return "break"

            return wrapper

        use_global = self._global_active()
        watch = set()
        self._stamp_buf = []

        for action, fn in self._action_fns().items():
            seq = self.keybinds.get(action)

            if not seq:
                continue

            mods, key = parse_seq(seq)
            vk = keysym_to_vk(key)

            if vk is not None:
                watch.add(vk)

            if use_global and vk is not None:
                self._global_binds[action] = (mods, vk)
                continue
            # Key can't be read globally -> fall back to a normal
            # in-window binding for this action.

            try:
                self.bind_all(seq, guarded(fn, vk))
                self._bound_sequences.append(seq)
            except tk.TclError:
                pass

        if self.stamper is not None:
            self.stamper.set_vks(watch)

        if self._beat_job is None:
            self._beat()

        if self._global_binds and self._poll_job is None:
            self._poll_tick()

    def _fire_global(self, fn, at=None):
        # Don't fire while a key is being rebound or while you're typing
        # in Settings/Games. An open-but-unfocused Settings window must
        # NOT block the hotkeys.
        if self.listening_for is not None or self._typing_in_modal():
            return

        self._run_with_time(fn, at)

    def _poll_tick(self):
        """Windows-only: watch the keyboard even when we aren't focused."""
        self._poll_job = None

        if not self._global_active() or not self._global_binds:
            return

        # Preferred path: presses were already time-stamped on their own
        # thread, so even after a freeze each one fires, in order, with its
        # real time.
        if self._stamper_ready():
            try:
                self._pull_stamps()

                buf, self._stamp_buf = self._stamp_buf, []
                fns = self._action_fns()

                for vk, t, mods, ours in buf:
                    for action, (bmods, bvk) in list(
                        self._global_binds.items()
                    ):
                        if bvk == vk and set(mods) == set(bmods):
                            self._fire_global(fns[action], t)
            except Exception:
                pass

            self._poll_job = self.after(8, self._poll_tick)
            return

        try:
            get_state = ctypes.windll.user32.GetAsyncKeyState

            held = set()

            if get_state(0x10) & 0x8000:
                held.add("Shift")
            if get_state(0x11) & 0x8000:
                held.add("Control")
            if get_state(0x12) & 0x8000:
                held.add("Alt")

            fns = self._action_fns()

            for action, (mods, vk) in list(self._global_binds.items()):
                down = held == mods and bool(get_state(vk) & 0x8000)

                if down and not self._prev_down.get(action):
                    self._fire_global(fns[action])

                self._prev_down[action] = down

        except Exception:
            pass

        self._poll_job = self.after(8, self._poll_tick)

    # ---------------------------------------------------------- rendering --

    def _render_header(self):

        stats = (
            self.game_data.get("stats", {}) if self.current_game else {}
        )

        since = (
            self.game_data.get("since_split") if self.current_game else None
        )

        txt = f"Resets today: {stats.get('reset_count', 0)}"

        if since:
            txt += f"  |  Since {since}: {stats.get('runs_since_split', 0)}"

        self.stats_lbl.config(text=txt)

        if not self.current_game:
            self.game_title_lbl.config(text="No Game Selected")
            self.category_lbl.config(text="Create or pick a game to begin")
            return

        self.game_title_lbl.config(text=self.current_game)

        pb = self.game_data["pb"]

        if pb:
            self.category_lbl.config(text=f"PB: {fmt_time(pb[-1])}")
        else:
            self.category_lbl.config(text="No PB yet")

    def _refresh_daily_stats(self):

        if not self.current_game:
            return

        stats = self.game_data.setdefault("stats", {})

        today = date.today().isoformat()

        if stats.get("reset_date") != today:
            stats["reset_date"] = today
            stats["reset_count"] = 0
            self._persist()

        stats.setdefault("reset_count", 0)

        # Older saves called this counter "runs_since_metro".
        if "runs_since_split" not in stats:
            stats["runs_since_split"] = stats.get("runs_since_metro", 0)

    def _active_goals(self):
        """Goal times to show (up to MAX_GOALS), skipping empty ones."""
        out = []

        for g in (self.game_data.get("goals") or [])[:MAX_GOALS]:
            times = g.get("times") or []

            if any(t is not None for t in times):
                name = str(g.get("name") or "Goal").strip() or "Goal"
                out.append({"name": name, "short": name[:8], "times": times})

        return out

    def _row_height(self):
        cols = self.ap["show_cols"]

        # The third line is where the delta (or the live countdown) goes.
        third = bool(cols["dcum"]) or bool(self.game_data.get("countdown_mode"))

        n3 = (
            int(bool(cols.get("dgold")))
            + int(bool(cols.get("gcum")))
            + int(bool(cols.get("dgcum")))
        )

        n = max(
            1,
            int(cols["split"] or cols["dsplit"])
            + int(cols["gold"] or cols["cum"])
            + int(third),
            n3,
        )

        # Goal columns use two lines (split on top, cumulative below).
        if self._active_goals():
            n = max(n, 2)

        text_h = (
            self.f_small.metrics("linespace")
            + (n - 1) * self.f_tiny.metrics("linespace")
        )

        if self.ap.get("show_split_stats"):
            text_h = max(text_h, 2 * self.f_tiny.metrics("linespace"))

        return max(self.f_ui.metrics("linespace") + 16, 10 + text_h)

    def _render_segments(self):

        c = self.seg_canvas
        th = self.th

        c.delete("row")

        self.current_segment_row = None

        segs = self.game_data["segments"]

        w = max(c.winfo_width(), 240)

        rh = self._row_height()
        self._row_h = rh

        if not self.current_game or not segs:
            c.create_text(
                w / 2, 40, text="No segments yet. Open Settings to add some.",
                fill=th["dim"], font=self.f_ui, tags="row",
            )
            c.configure(scrollregion=(0, 0, w, 80))

            self._render_bpt()
            self._render_popout()
            return

        pb = self.game_data["pb"]

        # After a finished run the PB has already been replaced, so keep
        # showing the +/- against the PB you were racing.
        if self.run_state == "finished" and self.run_pb is not None:
            pb = self.run_pb

        best = self.game_data["best"]
        cols = self.ap["show_cols"]

        on_accent = contrast(th["accent"])

        col2_w = max(
            self.f_small_b.measure("Δ Split +00:00.00"),
            self.f_tiny.measure("Cum 00:00.00"),
            self.f_tiny_b.measure("Δ Cum +00:00.00"),
            self.f_small_b.measure("PB split -00:00.00"),
        )
        col1_w = max(
            self.f_small.measure("Split 00:00.00"),
            self.f_tiny.measure("Gold 00:00.00"),
        )

        col3_w = max(
            self.f_small_b.measure("Δ Gold +00:00.00"),
            self.f_tiny.measure("Gold Cum 00:00.00"),
            self.f_tiny_b.measure("Δ Gold Cum +00:00.00"),
        )

        has3 = bool(
            cols.get("dgold") or cols.get("gcum") or cols.get("dgcum")
            or self.game_data.get("countdown_mode")
        )

        # Golds as they were when this run started, and their running sum.
        gbest = self.run_best if self.run_best is not None else best
        gold_cum = []
        gsum = 0
        gok = True

        for k in range(len(segs)):
            if gok and k < len(gbest) and gbest[k] is not None:
                gsum += gbest[k]
                gold_cum.append(gsum)
            else:
                gok = False
                gold_cum.append(None)

        has1 = bool(cols["split"] or cols["gold"])
        has2 = bool(
            cols["dsplit"] or cols["cum"] or cols["dcum"]
            or self.game_data.get("countdown_mode")
        )

        col2_right = w - 10
        col1_right = col2_right - ((col2_w + 10) if has2 else 0)
        left_edge = col1_right - (col1_w if has1 else 0)

        col3_right = left_edge - (10 if has3 and (has1 or has2) else 0)

        if has3:
            left_edge = col3_right - col3_w

        # Per-row stats sit between the segment name and the time columns.
        # If they don't fit they shrink to "…", then disappear.
        show_stats = bool(self.ap.get("show_split_stats"))

        name_w = max(
            [
                self.f_ui.measure(self._seg_name(k, sg))
                + (
                    8 + self.f_tiny.measure(self._seg_pronoun(k))
                    if self._seg_pronoun(k) else 0
                )
                for k, sg in enumerate(segs)
            ] + [0]
        )

        # Goal columns (up to 5): split on top, cumulative below, each with
        # its +/-. Ones that don't fit next to the name are left out.
        extra_x = {}
        goal_cols = []

        left_edge0 = left_edge
        need_extra = 0
        placing = True

        for g in self._active_goals():
            short = g["short"]

            time_w = max(
                self.f_small.measure(f"{short} 00:00.00"),
                self.f_tiny.measure("Cum 00:00.00"),
            )
            delta_w = max(
                self.f_small_b.measure("+00:00.00"),
                self.f_tiny_b.measure("+00:00.00"),
            )

            need_extra += time_w + 6 + delta_w + 10

            right = left_edge - 10
            tx = right - delta_w - 6
            new_left = tx - time_w

            if not placing or new_left < 40 + name_w + 10:
                placing = False
                continue

            gi = len(goal_cols)
            extra_x[10 + 2 * gi] = tx
            extra_x[11 + 2 * gi] = right
            goal_cols.append(dict(g, gi=gi))
            left_edge = new_left

        # Window width at which every goal column would fit.
        self._goal_need_w = int(
            (w - left_edge0) + 40 + name_w + 10 + need_extra + 30
        )

        stats_x = 40 + name_w + 14

        stat_lines = []
        stat_w = 0

        if show_stats:
            stat_lines = [self._row_stats_text(k) for k in range(len(segs))]
            stat_w = max(
                max(self.f_tiny.measure(a), self.f_tiny.measure(b))
                for a, b in stat_lines
            )

        room = left_edge - stats_x - 8

        if not show_stats or room < self.f_tiny.measure("…"):
            stats_mode = "none"
        elif room >= stat_w:
            stats_mode = "full"
        else:
            stats_mode = "dots"

        self._cd_item = None
        self._gd_item = None

        for i, seg in enumerate(segs):

            y = i * rh

            done = i < self.split_index

            is_current = (
                i == self.split_index
                and self.run_state in ("running", "paused")
            )

            if is_current:
                c.create_rectangle(
                    0, y, w, y + rh, fill=th["accent"], outline="",
                    tags="row",
                )

            def col(key):
                if key == "cd":
                    return th[self.countdown_color]

                if key == "gd":
                    return th["gold" if self._gd_diff <= 0 else "red"]

                # On the accent row, plain text colors switch to whatever
                # reads best on the accent color.
                if is_current and key in ("text", "dim"):
                    return on_accent
                return th[key]

            c.create_text(
                18, y + rh / 2, text=seg.get("icon", "⛳"),
                fill=col("text"), font=self.f_ui, tags="row",
            )

            c.create_text(
                40, y + rh / 2, text=self._seg_name(i, seg), anchor="w",
                fill=col("text"), font=self.f_ui, tags="row",
            )

            pron = self._seg_pronoun(i)

            if pron:
                c.create_text(
                    40 + self.f_ui.measure(self._seg_name(i, seg)) + 8,
                    y + rh / 2, text=pron, anchor="w",
                    fill=col("dim"), font=self.f_tiny, tags="row",
                )

            if stats_mode == "full":
                sa, sb = stat_lines[i]
                sh = self.f_tiny.metrics("linespace")

                c.create_text(
                    stats_x, y + rh / 2 - sh / 2, text=sa, anchor="w",
                    fill=col("dim"), font=self.f_tiny, tags="row",
                )
                c.create_text(
                    stats_x, y + rh / 2 + sh / 2, text=sb, anchor="w",
                    fill=col("dim"), font=self.f_tiny, tags="row",
                )

            elif stats_mode == "dots":
                c.create_text(
                    stats_x, y + rh / 2, text="…", anchor="w",
                    fill=col("dim"), font=self.f_tiny, tags="row",
                )

            split_delta_text = ""
            split_delta_color = "dim"

            split_diff_text = ""
            split_diff_color = "dim"

            split_time_text = "-"
            split_time_color = "dim"

            cumulative_text = "--"
            gold_text = "--"

            dgold_text = ""
            dgold_color = "dim"
            dgcum_text = ""
            dgcum_color = "dim"

            gcum_text = (
                fmt_time(gold_cum[i]) if gold_cum[i] is not None else "--"
            )

            if done:

                t = self.split_times[i]

                seg_dur = t - (self.split_times[i - 1] if i > 0 else 0)

                split_time_text = fmt_time(seg_dur)
                split_time_color = "text"

                if i < len(pb):
                    pb_seg_dur = pb[i] - (pb[i - 1] if i > 0 else 0)

                    split_diff = seg_dur - pb_seg_dur
                    split_diff_text = fmt_delta(split_diff)
                    split_diff_color = "green" if split_diff <= 0 else "red"

                    cumulative_delta = t - pb[i]
                    split_delta_text = fmt_delta(cumulative_delta)
                    split_delta_color = (
                        "green" if cumulative_delta <= 0 else "red"
                    )

                cumulative_text = fmt_time(t)

                if i < len(gbest) and gbest[i] is not None:
                    dg = seg_dur - gbest[i]
                    dgold_text = fmt_delta(dg)
                    dgold_color = "gold" if dg <= 0 else "red"

                if gold_cum[i] is not None:
                    dgc = t - gold_cum[i]
                    dgcum_text = fmt_delta(dgc)
                    dgcum_color = "gold" if dgc <= 0 else "red"

                if i < len(best) and best[i] is not None:
                    gold_text = fmt_time(best[i])

                    if seg_dur <= best[i]:
                        split_time_color = "gold"

            elif i < len(pb):

                pb_dur = pb[i] - (pb[i - 1] if i > 0 else 0)

                split_time_text = fmt_time(pb_dur)
                cumulative_text = fmt_time(pb[i])

                if i < len(best) and best[i] is not None:
                    gold_text = fmt_time(best[i])

            # Each line is a list of (column, text, color key, font).
            if done:
                lines = [
                    [
                        (1, f"Split {split_time_text}", split_time_color,
                         self.f_small)
                        for _ in [0] if cols["split"]
                    ] + [
                        (2, f"Δ Split {split_diff_text}", split_diff_color,
                         self.f_small_b)
                        for _ in [0] if cols["dsplit"]
                    ],
                    [
                        (1, f"Gold {gold_text}", "gold", self.f_tiny)
                        for _ in [0] if cols["gold"]
                    ] + [
                        (2, f"Cum {cumulative_text}", "text", self.f_tiny)
                        for _ in [0] if cols["cum"]
                    ],
                    [
                        (2, f"Δ Cum {split_delta_text}", split_delta_color,
                         self.f_tiny_b)
                        for _ in [0] if cols["dcum"] and split_delta_text
                    ],
                ]
            else:
                lines = [
                    [
                        (1, f"Split {split_time_text}", split_time_color,
                         self.f_small)
                        for _ in [0] if cols["split"]
                    ],
                    [
                        (1, f"Gold {gold_text}", "gold", self.f_tiny)
                        for _ in [0] if cols["gold"] and gold_text != "--"
                    ] + [
                        (2, f"Cum {cumulative_text}", "dim", self.f_tiny)
                        for _ in [0] if cols["cum"]
                    ],
                ]

            # Third column: distance to gold, gold cumulative, distance to
            # gold cumulative.
            while len(lines) < 3:
                lines.append([])

            if cols.get("dgold") and dgold_text:
                lines[0].append(
                    (3, f"Δ Gold {dgold_text}", dgold_color, self.f_small_b)
                )

            if cols.get("gcum") and gcum_text != "--":
                lines[1].append(
                    (3, f"Gold Cum {gcum_text}",
                     "gold" if done else "dim", self.f_tiny)
                )

            if cols.get("dgcum") and dgcum_text:
                lines[2].append(
                    (3, f"Δ Gold Cum {dgcum_text}", dgcum_color,
                     self.f_tiny_b)
                )

            # Goal times: split on top, cumulative below, +/- next to each.
            for gcol in goal_cols:
                gi = gcol["gi"]
                gt = gcol["times"]

                gcum = gt[i] if i < len(gt) else None

                if i == 0:
                    gprev = 0
                else:
                    gprev = gt[i - 1] if i - 1 < len(gt) else None

                gseg = (
                    gcum - gprev
                    if gcum is not None and gprev is not None else None
                )

                lines[0].append((
                    10 + 2 * gi,
                    f"{gcol['short']} "
                    f"{fmt_time(gseg) if gseg is not None else '--'}",
                    "text" if done else "dim", self.f_small,
                ))
                lines[1].append((
                    10 + 2 * gi,
                    f"Cum {fmt_time(gcum) if gcum is not None else '--'}",
                    "text" if done else "dim", self.f_tiny,
                ))

                if done and gseg is not None:
                    d1 = seg_dur - gseg
                    lines[0].append((
                        11 + 2 * gi, fmt_delta(d1),
                        "green" if d1 <= 0 else "red", self.f_small_b,
                    ))

                if done and gcum is not None:
                    d2 = t - gcum
                    lines[1].append((
                        11 + 2 * gi, fmt_delta(d2),
                        "green" if d2 <= 0 else "red", self.f_tiny_b,
                    ))

            # Countdown mode: the current row's Δ Gold counts live toward
            # THIS split's gold (not the cumulative one).
            if (
                is_current
                and self.game_data.get("countdown_mode")
                and self.countdown_armed
                and i < len(gbest)
                and gbest[i] is not None
            ):
                self._gd_diff = self._current_split_elapsed_ms() - gbest[i]

                lines[0].append(
                    (3, "Δ Gold " + fmt_delta(self._gd_diff), "gd",
                     self.f_small_b)
                )

            # Live countdown (countdown mode) goes where the final +/- will
            # be once the split is done.
            if is_current and self.countdown_armed and self.countdown_text:
                lines.append(
                    [(2, self.countdown_text, "cd", self.f_small_b)]
                )

            lines = [ln for ln in lines if ln]

            total_h = sum(ln[0][3].metrics("linespace") for ln in lines)

            cy = y + (rh - total_h) / 2

            for ln in lines:

                lh = ln[0][3].metrics("linespace")

                for colno, text, ckey, font in ln:
                    item = c.create_text(
                        extra_x[colno] if colno in extra_x
                        else col1_right if colno == 1
                        else col3_right if colno == 3
                        else col2_right,
                        cy + lh / 2, text=text, anchor="e",
                        fill=col(ckey), font=font, tags="row",
                    )

                    if ckey == "cd":
                        self._cd_item = item

                    if ckey == "gd":
                        self._gd_item = item

                cy += lh

            c.create_line(
                0, y + rh - 1, w, y + rh - 1, fill=th["border"], tags="row"
            )

        c.configure(
            scrollregion=(0, 0, w, max(len(segs) * rh, c.winfo_height()))
        )

        c.tag_lower("bg")

        self._render_bpt()
        self._render_popout()

        self.after_idle(self._scroll_current_segment_into_view)

    def _scroll_current_segment_into_view(self):

        try:
            c = self.seg_canvas
            c.winfo_exists()
        except Exception:
            return

        segs = self.game_data["segments"]

        if not segs:
            return

        rh = self._row_h
        total = max(len(segs) * rh, 1)
        vh = c.winfo_height()

        if vh <= 1:
            return

        if total <= vh or self.run_state == "idle":
            c.yview_moveto(0)
            return

        if self.run_state not in ("running", "paused"):
            return

        top = self.split_index * rh
        bottom = top + rh

        view_top = c.canvasy(0)
        view_bottom = view_top + vh

        if top < view_top:
            c.yview_moveto(top / total)

        elif bottom > view_bottom:
            c.yview_moveto((bottom - vh) / total)

    def _compute_best_possible(self):

        segs = self.game_data["segments"]

        if not self.current_game or not segs:
            return None

        best = self.game_data["best"]
        pb = self.game_data["pb"]

        total = 0

        for i in range(len(segs)):

            if i < self.split_index:
                total += self.split_times[i] - (
                    self.split_times[i - 1] if i > 0 else 0
                )
                continue

            if i < len(best) and best[i] is not None:
                total += best[i]
                continue

            if i < len(pb):
                total += pb[i] - (pb[i - 1] if i > 0 else 0)
                continue

            return None

        return total

    def _compute_sum_of_best(self):

        segs = self.game_data["segments"]

        if not self.current_game or not segs:
            return None

        best = self.game_data["best"]

        if (
            len(best) < len(segs)
            or any(b is None for b in best[:len(segs)])
        ):
            return None

        return sum(best[:len(segs)])

    def _render_bpt(self):

        c = self.info_canvas

        if not self.current_game:
            c.itemconfig(self.i_bpt_val, text="--")
            return

        if self.run_state in ("running", "paused"):

            c.itemconfig(self.i_bpt_lbl, text="Best Possible Time")

            bpt = self._compute_best_possible()

            c.itemconfig(
                self.i_bpt_val, text="--" if bpt is None else fmt_time(bpt)
            )

        elif self.run_state == "finished" and self.no_mistakes is not None:

            c.itemconfig(self.i_bpt_lbl, text="No Mistakes (old PB + this run)")

            c.itemconfig(
                self.i_bpt_val,
                text=(
                    f"{fmt_time(self.no_mistakes)}  "
                    f"({fmt_delta(self.no_mistakes - self.split_times[-1])})"
                ),
            )

        else:

            c.itemconfig(self.i_bpt_lbl, text="Sum of Best")

            sob = self._compute_sum_of_best()

            c.itemconfig(
                self.i_bpt_val, text="--" if sob is None else fmt_time(sob)
            )

    def _render_all(self):

        self._render_header()
        self._render_segments()

        kb = self.keybinds

        self.btn_split.config(text=f"Split\n{seq_to_label(kb['split'])}")
        self.btn_pause.config(text=f"Pause\n{seq_to_label(kb['pause'])}")
        self.btn_reset.config(text=f"Reset\n{seq_to_label(kb['reset'])}")
        self.btn_unsplit.config(
            text=f"Unsplit\n{seq_to_label(kb['unsplit'])}"
        )

        self._paint_info()

    def _record_split_stats(self, i, seg_ms, stamp):
        st = self._seg_stats(i)
        st["times"].append(int(seg_ms))
        st["stamps"].append(int(stamp))

        if i + 1 < len(self.game_data["segments"]):
            self._seg_stats(i + 1)["reached"] += 1

    def _mark_counted(self):
        """Called often; flips the run to 'counted' at MIN_RUN_MS."""
        if self._run_counted or self.run_state not in ("running", "paused"):
            return

        if self._elapsed_ms() < MIN_RUN_MS:
            return

        self._run_counted = True

        # Every counted run reaches the first split.
        self._seg_stats(0)["reached"] += 1

        for i, seg_ms, stamp in self._pending_stats:
            self._record_split_stats(i, seg_ms, stamp)

        self._pending_stats = []
        self._persist()

    def _seg_name(self, i, seg=None):
        """The split's real name."""
        if seg is None:
            seg = self.game_data["segments"][i]

        return seg.get("name", "")

    def _seg_pronoun(self, i):
        """Random pronoun shown next to the name during a run, or ''."""
        names = self.run_names

        if (
            names
            and i < len(names)
            and self.game_data.get("random_names")
            and self.run_state != "idle"
        ):
            return names[i]

        return ""

    def _roll_names(self):
        n = len(self.game_data["segments"])

        if not self.game_data.get("random_names") or n == 0:
            self.run_names = None
        elif n <= len(PRONOUNS):
            self.run_names = random.sample(PRONOUNS, n)
        else:
            self.run_names = [random.choice(PRONOUNS) for _ in range(n)]

    # ------------------------------------------------------------ effects --
    # Fireworks and the GOLD splash are drawn straight onto the two main
    # canvases (tag "fx") using window coordinates, so they float over
    # everything without needing a transparent window.

    FX_COLORS = [
        "#ffcc33", "#ff5c5c", "#3ddc84", "#4cc9f0",
        "#f72585", "#ffffff", "#b388ff", "#ff9f1c",
    ]

    def fx_fireworks(self):
        now = time.perf_counter()

        self._fx_spawn = [
            now + i * 0.33 + random.random() * 0.2 for i in range(14)
        ]

        self._fx_start_loop()

    def fx_gold(self):
        if self.main is None:
            return

        w = max(self.main.winfo_width(), 100)
        h = max(self.main.winfo_height(), 100)

        try:
            fam = self.f_big.actual("family")
            probe = tkfont.Font(
                root=self, family=fam, size=-100, weight="bold"
            )
            tw = max(probe.measure("GOLD!!!"), 1)

            px = int(min(100 * (w * 0.92) / tw, h * 0.5))
            px = max(px, 20)

            self._fx_gold_fonts = (
                tkfont.Font(root=self, family=fam, size=-px, weight="bold"),
                tkfont.Font(
                    root=self, family=fam, size=-int(px * 0.9), weight="bold"
                ),
            )
        except tk.TclError:
            return

        self._fx_gold_start = time.perf_counter()
        self._fx_start_loop()

    def _fx_start_loop(self):
        if self._fx_job is None:
            self._fx_last = time.perf_counter()
            self._fx_job = self.after(33, self._fx_step)

    def _fx_stop(self):
        if self._fx_job is not None:
            try:
                self.after_cancel(self._fx_job)
            except Exception:
                pass

        self._fx_job = None
        self._fx_parts = []
        self._fx_rockets = []
        self._fx_spawn = []
        self._fx_gold_start = None
        self._fx_gold_fonts = None

        for name in ("seg_canvas", "info_canvas"):
            c = getattr(self, name, None)

            try:
                c.delete("fx")
            except Exception:
                pass

    def _fx_step(self):
        self._fx_job = None

        if self.main is None:
            return

        now = time.perf_counter()
        dt = min(max(now - self._fx_last, 0.001), 0.1)
        self._fx_last = now

        try:
            w = max(self.main.winfo_width(), 100)
            h = max(self.main.winfo_height(), 100)
        except tk.TclError:
            return

        # Launch rockets that are due.
        due = [t for t in self._fx_spawn if t <= now]
        self._fx_spawn = [t for t in self._fx_spawn if t > now]

        for _ in due:
            self._fx_rockets.append({
                "x": w * random.uniform(0.12, 0.88),
                "y": float(h),
                "ty": h * random.uniform(0.15, 0.5),
                "v": h * random.uniform(0.9, 1.25),
                "color": random.choice(self.FX_COLORS),
            })

        # Rockets climb, then burst.
        alive = []

        for r in self._fx_rockets:
            r["y"] -= r["v"] * dt

            if r["y"] <= r["ty"]:
                self._fx_burst(r["x"], r["y"], r["color"], min(w, h))
            else:
                alive.append(r)

        self._fx_rockets = alive

        # Sparks.
        drag = 0.35 ** dt

        for q in self._fx_parts:
            q[4] += dt
            q[2] *= drag
            q[3] = q[3] * drag + 150 * dt
            q[0] += q[2] * dt
            q[1] += q[3] * dt

        self._fx_parts = [q for q in self._fx_parts if q[4] < q[5]]

        gold_on = (
            self._fx_gold_start is not None
            and now - self._fx_gold_start < 1.7
        )

        if not gold_on:
            self._fx_gold_start = None

        try:
            self._fx_draw(now, w, h, gold_on)
        except tk.TclError:
            return

        if (
            self._fx_parts or self._fx_rockets or self._fx_spawn or gold_on
        ):
            self._fx_job = self.after(33, self._fx_step)
        else:
            self._fx_stop()

    def _fx_burst(self, x, y, color, size):
        second = random.choice(self.FX_COLORS)

        for _ in range(48):
            a = random.uniform(0, math.tau)
            sp = random.uniform(0.12, 0.5) * size

            self._fx_parts.append([
                x, y, math.cos(a) * sp, math.sin(a) * sp,
                0.0, random.uniform(0.9, 1.6),
                color if random.random() < 0.7 else second,
                random.uniform(1.5, 3.2),
            ])

        if len(self._fx_parts) > 320:
            self._fx_parts = self._fx_parts[-320:]

    @staticmethod
    def _fx_blend(c1, c2, t):
        try:
            a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
            b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
        except ValueError:
            return c1

        return "#%02x%02x%02x" % tuple(
            int(a[i] * t + b[i] * (1 - t)) for i in range(3)
        )

    def _fx_draw(self, now, w, h, gold_on):
        th = self.th
        mx = self.main.winfo_rootx()
        my = self.main.winfo_rooty()

        for c in (self.seg_canvas, self.info_canvas):
            c.delete("fx")

            ox = c.winfo_rootx() - mx
            oy = c.winfo_rooty() - my
            cw = c.winfo_width()
            ch = c.winfo_height()

            sx = c.canvasx(0)
            sy = c.canvasy(0)

            def P(x, y):
                return x - ox + sx, y - oy + sy

            def visible(x, y, m=12):
                return -m <= x - ox <= cw + m and -m <= y - oy <= ch + m

            for r in self._fx_rockets:
                if visible(r["x"], r["y"], 40):
                    x0, y0 = P(r["x"], r["y"])
                    x1, y1 = P(r["x"], r["y"] + 22)

                    c.create_line(
                        x0, y0, x1, y1, fill=r["color"], width=2,
                        tags="fx",
                    )

            for q in self._fx_parts:
                if not visible(q[0], q[1]):
                    continue

                f = max(0.0, 1 - q[4] / q[5])
                col = self._fx_blend(q[6], th["panel"], f ** 0.6)

                x1, y1 = P(q[0], q[1])
                x0, y0 = P(q[0] - q[2] * 0.05, q[1] - q[3] * 0.05)

                c.create_line(
                    x0, y0, x1, y1, fill=col,
                    width=max(1.0, q[7] * (0.5 + f)), tags="fx",
                )

            if gold_on and self._fx_gold_fonts:
                t = now - self._fx_gold_start
                fade = t > 1.35

                x0, y0 = P(0, 0)
                x1, y1 = P(w, h)

                c.create_rectangle(
                    x0, y0, x1, y1, fill="#000000", outline="",
                    stipple="gray25" if fade else "gray50", tags="fx",
                )

                flash = int(t / 0.12) % 2 == 0
                gold = th["gold"]

                bx0, by0 = P(6, 6)
                bx1, by1 = P(w - 6, h - 6)

                c.create_rectangle(
                    bx0, by0, bx1, by1,
                    outline=gold if flash else "#ffffff",
                    width=10, tags="fx",
                )

                font = self._fx_gold_fonts[0 if flash else 1]
                cx, cy = P(w / 2, h / 2)

                for dx, dy in ((5, 5), (-5, 5), (5, -5), (-5, -5)):
                    c.create_text(
                        cx + dx, cy + dy, text="GOLD!!!", font=font,
                        fill="#000000", tags="fx",
                    )

                c.create_text(
                    cx, cy, text="GOLD!!!", font=font,
                    fill=gold if flash else "#fff3b0", tags="fx",
                )

            c.tag_raise("fx")

    # ------------------------------------------------------- run control --

    def _elapsed_ms(self):

        if self.run_state == "idle":
            return 0

        if self.run_state == "paused":
            return (
                self.pause_started_at - self.start_time - self.paused_accum
            ) * 1000

        return (
            self._now() - self.start_time - self.paused_accum
        ) * 1000

    def _current_split_elapsed_ms(self):

        total = self._elapsed_ms()

        if self.split_index > 0 and self.split_times:
            total -= self.split_times[-1]

        return max(total, 0)

    def _tick(self):

        if self.run_state == "running":

            el = self._elapsed_ms()

            # Pre-countdown: the timer sits below zero and counts up to 0.
            if el < 0:
                self.big_text = fmt_time(el)
                self.big_color = "dim"
                self.split_text = "Split: 0:00.00"
                self._paint_info()
                self._tick_job = self.after(30, self._tick)
                return

            if self._pre_pending:
                self._pre_pending = False
                self.big_color = "text"

            self._mark_counted()
            self._update_gold_live()

            self.big_text = fmt_time(el)

            self.split_text = (
                "Split: " + fmt_time(self._current_split_elapsed_ms())
            )

            # Countdown mode: if you pass the target (+0, into the red)
            # without having pressed the key, pop the countdown up anyway.
            if self.game_data.get("countdown_mode") and not self.countdown_armed:
                val = self._countdown_value()
                gold = self._gold_ms()

                over_gold = (
                    gold is not None
                    and self._current_split_elapsed_ms() >= gold
                )

                if (val is not None and val[0] >= 0) or over_gold:
                    self.countdown_armed = True
                    self._update_countdown()
                    self._render_segments()

            if self.countdown_armed:
                self._update_countdown()

            self._paint_info()

            self._tick_job = self.after(30, self._tick)

    def _set_status(self, s):
        self.run_state = s

    # ------------------------------------------------- countdown (arming) --

    def _countdown_value(self):
        """(ms difference to target, label) for the current split, or None.

        Negative = still time left before you'd tie the target.
        """
        i = self.split_index

        pb = self.game_data["pb"]
        best = self.game_data["best"]

        target = self.game_data.get("countdown_target", "pb_split")

        if target == "pb_cum":
            if i >= len(pb):
                return None
            return self._elapsed_ms() - pb[i], "PB time"

        if target == "gold":
            if i >= len(best) or best[i] is None:
                return None
            return self._current_split_elapsed_ms() - best[i], "Gold"

        if i >= len(pb):
            return None

        pb_seg = pb[i] - (pb[i - 1] if i > 0 else 0)

        return self._current_split_elapsed_ms() - pb_seg, "PB split"

    def _gold_ms(self):
        """Gold for the split you're on (as of run start), or None."""
        gb = self.run_best if self.run_best is not None else (
            self.game_data["best"]
        )
        i = self.split_index

        if i < len(gb) and gb[i] is not None:
            return gb[i]

        return None

    def _update_gold_live(self):
        item = self._gd_item

        if item is None or not self.game_data.get("countdown_mode"):
            return

        gb = self.run_best if self.run_best is not None else (
            self.game_data["best"]
        )
        i = self.split_index

        if i >= len(gb) or gb[i] is None:
            return

        diff = self._current_split_elapsed_ms() - gb[i]
        self._gd_diff = diff

        try:
            self.seg_canvas.itemconfig(
                item, text="Δ Gold " + fmt_delta(diff),
                fill=self.th["gold" if diff <= 0 else "red"],
            )
        except tk.TclError:
            pass

    def _update_countdown(self):

        val = self._countdown_value()

        if val is None:
            self.countdown_text = ""

            # Only a gold to count to: the gold countdown handles itself.
            if self._gold_ms() is not None:
                return

            self.countdown_armed = False
            self._render_segments()
            return

        diff, label = val

        self.countdown_text = f"{label} {fmt_delta(diff)}"
        self.countdown_color = "green" if diff <= 0 else "red"

        if self._cd_item is not None:
            try:
                self.seg_canvas.itemconfig(
                    self._cd_item, text=self.countdown_text,
                    fill=self.th[self.countdown_color],
                )
            except tk.TclError:
                pass

        if self.popout is not None and self._pop_cd_item is not None:
            try:
                self.pop_canvas.itemconfig(
                    self._pop_cd_item, text=self.countdown_text,
                    fill=self.th[self.countdown_color],
                )
            except tk.TclError:
                pass

    def do_start(self):

        if not self.current_game:
            self._flash_header("Pick a game first")
            return

        if not self.game_data["segments"]:
            self._flash_header("Add segments in Settings first")
            return

        try:
            pre = abs(int(self.game_data.get("pre_countdown") or 0))
        except (TypeError, ValueError):
            pre = 0

        # A pre-countdown just starts the clock "pre" seconds in the
        # future, so elapsed time is negative until it reaches 0.
        self.start_time = self._now() + pre
        self._pre_pending = pre > 0
        self.paused_accum = 0.0
        self.pause_started_at = 0.0

        self._fx_stop()
        self._roll_names()

        self.split_index = 0
        self.split_times = []

        self.last_delta_sign = 0
        self.since_reached_this_run = False
        self.countdown_armed = False

        self.run_pb = list(self.game_data["pb"])
        self.run_best = list(self.game_data["best"])
        self.no_mistakes = None
        self._run_counted = False
        self._pending_stats = []

        self.delta_text = ""
        self.delta_color = "dim"

        self._set_status("running")

        self._persist()

        self.big_text = fmt_time(-pre * 1000) if pre else "0:00.00"
        self.big_color = "dim" if pre else "text"
        self.split_text = "Split: 0:00.00"

        self._tick()

        self._render_segments()
        self._paint_info()

    def do_split(self):

        # Idle -> starts run.  Running -> records split.
        # Paused/Finished -> ignored.

        if self.run_state == "idle":
            self.do_start()
            return

        if self.run_state != "running":
            return

        # Still in the pre-countdown: splitting isn't possible yet.
        if self._elapsed_ms() < 0:
            self._flash_header("Run starts when the countdown hits 0")
            return

        self._mark_counted()

        # Countdown mode: the first press only shows how far you are from
        # the target; the second press does the real split.
        if (
            self.game_data.get("countdown_mode")
            and not self.countdown_armed
            and (
                self._countdown_value() is not None
                or self._gold_ms() is not None
            )
        ):
            self.countdown_armed = True
            self._update_countdown()
            self._render_segments()
            return

        # Prevent accidental double-splits.
        # First split is always allowed.
        if (
            self.split_index > 0
            and self._current_split_elapsed_ms() < MIN_SPLIT_INTERVAL_MS
        ):
            self._flash_header("Split blocked: wait 30 seconds")
            return

        self.countdown_armed = False

        t = self._elapsed_ms()

        self.split_times.append(t)

        pb = self.game_data["pb"]
        i = self.split_index

        current_seg = t - (self.split_times[i - 1] if i > 0 else 0)

        # Finished the whole route in under MIN_RUN_MS: not a real run.
        if (
            not self._run_counted
            and i == len(self.game_data["segments"]) - 1
        ):
            self.do_reset(count_reset=False, save=False)
            self._flash_header("Under 15s - run not counted")
            return

        # A new gold (needs an existing gold to beat).
        best_now = self.game_data["best"]
        old_gold = best_now[i] if i < len(best_now) else None

        if (
            old_gold is not None
            and current_seg < old_gold
            and self._run_counted
            and self.ap.get("fx_gold", True)
        ):
            self.fx_gold()

        # Display delta against PB split.
        if i < len(pb):

            pb_seg = pb[i] - (pb[i - 1] if i > 0 else 0)

            d = current_seg - pb_seg

            self.delta_text = fmt_delta(d)
            self.delta_color = "green" if d <= 0 else "red"

            self.last_delta_sign = -1 if d <= 0 else 1

        else:
            self.delta_text = ""
            self.delta_color = "dim"
            self.last_delta_sign = 0

        self.big_color = (
            "green" if self.last_delta_sign < 0
            else "red" if self.last_delta_sign > 0
            else "text"
        )

        self.split_index += 1

        # "Runs since reaching <split>" counter.
        since = self.game_data.get("since_split")

        if since and (
            self.game_data["segments"][i].get("name", "").strip().lower()
            == since.strip().lower()
        ):
            self.since_reached_this_run = True
            self.game_data.setdefault("stats", {})["runs_since_split"] = 0

        # Per-split stats: record this split's time (with a timestamp for
        # the weekly average), and mark the next split as reached.
        if self._run_counted:
            self._record_split_stats(i, current_seg, time.time())
        else:
            self._pending_stats.append(
                (i, int(current_seg), int(time.time()))
            )

        self._persist()

        # Full run.
        if self.split_index >= len(self.game_data["segments"]):
            self._finish_run()
        else:
            self.split_text = "Split: 0:00.00"
            self._render_segments()
            self._paint_info()

    # ---------------------------------------------------- SAVE RUN RESULTS --

    def _save_run_splits(self, allow_pb=False):
        """
        Save the current run's completed segment results.

        PB RULE:
        Only a COMPLETED FULL RUN may update the PB, and it is decided
        ONLY by the final cumulative time. If the new run is faster
        overall, the ENTIRE PB array is replaced with the new run's
        cumulative split times (individual PB splits are not compared).

        GOLD RULE:
        Golds are independent. Every completed segment from the current
        run is checked against its stored gold, so a DNF/reset run can
        still produce golds.

        Returns:
            (changed_anything, overall_pb)
        """

        if not self.split_times:
            return False, False

        segments = self.game_data.get("segments", [])

        pb = self.game_data["pb"]
        best = self.game_data["best"]

        old_pb = list(pb)

        changed_pb = False
        changed_best = False

        # A full run means EXACTLY all segments were completed.
        full_run = (
            len(segments) > 0 and len(self.split_times) == len(segments)
        )

        overall_pb = False

        # allow_pb=True is only used by _finish_run().
        # do_reset() always calls this with allow_pb=False.
        if allow_pb and full_run:

            new_final = self.split_times[-1]

            if not pb:
                overall_pb = True
            elif new_final < pb[-1]:
                overall_pb = True

            if overall_pb:
                new_pb = [int(t) for t in self.split_times]

                if new_pb != pb:
                    self.game_data["pb"] = new_pb
                    pb = new_pb
                    changed_pb = True

        # Gold check happens regardless of overall PB status.
        for i, t in enumerate(self.split_times):

            duration = t - (self.split_times[i - 1] if i > 0 else 0)

            while len(best) <= i:
                best.append(None)

            old_gold = best[i]

            if old_gold is None or duration < old_gold:
                best[i] = int(duration)
                changed_best = True

        # Only actual PB changes create PB history. Store ONLY the
        # previous PB so "Delete last PB" can't delete newer golds.
        if changed_pb:
            self.game_data.setdefault("pb_history", []).append({"pb": old_pb})

        changed = changed_pb or changed_best

        if changed:
            self._persist()

        return changed, overall_pb

    # ------------------------------------------------------------- finish --

    def _finish_run(self):

        self._set_status("finished")

        self.countdown_armed = False

        if self._tick_job:
            self.after_cancel(self._tick_job)
            self._tick_job = None

        final_time = self.split_times[-1]

        # Remember the PB we were racing before it can be replaced.
        old_pb = list(self.game_data["pb"])
        self.run_pb = old_pb

        # A completed run is the ONLY place where PB may update.
        _, is_new_pb = self._save_run_splits(allow_pb=True)

        # "No Mistakes": for every split take whichever was faster, the
        # old PB's segment or this run's, and add them up.
        n = len(self.split_times)

        if len(old_pb) >= n > 0:
            total = 0

            for i in range(n):
                new_seg = self.split_times[i] - (
                    self.split_times[i - 1] if i > 0 else 0
                )
                old_seg = old_pb[i] - (old_pb[i - 1] if i > 0 else 0)
                total += min(new_seg, old_seg)

            self.no_mistakes = int(total)
        else:
            self.no_mistakes = None

        suffix = "  ★PB" if is_new_pb else ""

        self.big_text = fmt_time(final_time) + suffix
        self.big_color = "gold" if is_new_pb else "text"

        final_split = final_time - (
            self.split_times[-2] if len(self.split_times) > 1 else 0
        )

        self.split_text = f"Split: {fmt_time(final_split)}"

        self._render_header()
        self._render_segments()
        self._paint_info()

        if is_new_pb and self.ap.get("fx_fireworks", True):
            self.fx_fireworks()

    # ------------------------------------------------------------ unsplit --

    def do_unsplit(self):

        if not self.split_times:
            return

        was_finished = self.run_state == "finished"

        # Segment we're leaving (== number of segments if finished).
        left_idx = self.split_index

        self.countdown_armed = False
        self.no_mistakes = None

        if was_finished:
            self._set_status("running")

        self.split_times.pop()

        self.split_index = max(0, self.split_index - 1)

        # Take the undone split back out of the per-split stats.
        if not self._run_counted:
            if self._pending_stats:
                self._pending_stats.pop()
        else:
            st = self._seg_stats(self.split_index)

            if st["times"]:
                st["times"].pop()
                st["stamps"].pop()

            if (
                not was_finished
                and left_idx < len(self.game_data["segments"])
            ):
                cur = self._seg_stats(left_idx)
                cur["reached"] = max(0, cur["reached"] - 1)

        self._persist()

        self.last_delta_sign = 0

        self.delta_text = ""
        self.delta_color = "dim"

        if was_finished:
            self._tick()

        self.big_text = fmt_time(self._elapsed_ms())
        self.big_color = "text"

        self.split_text = (
            "Split: " + fmt_time(self._current_split_elapsed_ms())
        )

        self._render_segments()
        self._paint_info()

    # ---------------------------------------------------------- pause/resume --

    def do_pause_resume(self):

        if self.run_state == "running":

            self.pause_started_at = self._now()

            self._set_status("paused")

            if self._tick_job:
                self.after_cancel(self._tick_job)
                self._tick_job = None

            self._render_segments()

            return

        if self.run_state == "paused":

            self.paused_accum += self._now() - self.pause_started_at

            self._set_status("running")

            self._tick()

            self._render_segments()

            return

        if self.run_state == "idle":
            self.do_start()

    # --------------------------------------------------------------- reset --

    def do_reset(self, count_reset=True, save=True):

        # Cancelling during the pre-countdown isn't a real attempt.
        if self._pre_pending:
            count_reset = False
            save = False
            self._pre_pending = False

        # Neither is a run that never reached MIN_RUN_MS (accidental start).
        self._mark_counted()
        discarded = False

        if (
            self.run_state in ("running", "paused")
            and not self._run_counted
        ):
            discarded = count_reset
            count_reset = False
            save = False

        self._fx_stop()

        self._refresh_daily_stats()

        # Count reset statistics.
        if count_reset and self.current_game:

            stats = self.game_data.setdefault("stats", {})

            stats["reset_count"] = stats.get("reset_count", 0) + 1

            # Reset while on a split -> counts against that split.
            if (
                self.run_state in ("running", "paused")
                and self.split_index < len(self.game_data["segments"])
            ):
                self._seg_stats(self.split_index)["resets"] += 1

            # Run ended before reaching the "since" split.
            if (
                self.game_data.get("since_split")
                and self.run_state != "idle"
                and not self.since_reached_this_run
            ):
                stats["runs_since_split"] = (
                    stats.get("runs_since_split", 0) + 1
                )

            self._persist()

        # Save golds from the partial/DNF run, but NEVER let it be a PB.
        if save:
            self._save_run_splits(allow_pb=False)

        if self._tick_job:
            self.after_cancel(self._tick_job)
            self._tick_job = None

        self._set_status("idle")
        self.run_names = None

        self.split_index = 0
        self.split_times = []

        self.last_delta_sign = 0
        self.since_reached_this_run = False
        self.countdown_armed = False
        self.run_pb = None
        self.run_best = None
        self._run_counted = False
        self._pending_stats = []
        self.no_mistakes = None

        self.big_text = fmt_time(0)
        self.big_color = "text"
        self.split_text = "Split: 0:00.00"
        self.delta_text = ""
        self.delta_color = "dim"

        self._render_header()
        self._render_segments()
        self._paint_info()

        if discarded:
            self._flash_header("Under 15s - run not counted")

    def _flash_header(self, msg):

        self.category_lbl.config(text=msg)

        self.after(1400, self._render_header)

    # ---------------------------------------------------------- pop-out --

    def open_popout(self):
        """Small always-on-top window: timer + current (and next) splits."""

        if self.popout is not None:
            try:
                self.popout.lift()
                return
            except tk.TclError:
                self.popout = None

        win = tk.Toplevel(self)
        win.title("Split Timer - Pop-out")
        win.configure(bg=self.th["panel"])
        win.minsize(260, 110)
        win.protocol("WM_DELETE_WINDOW", self._close_popout)

        self.popout = win
        self._pop_geom_key = None

        self.pop_canvas = tk.Canvas(
            win, bg=self.th["panel"], highlightthickness=0
        )
        self.pop_canvas.pack(fill="both", expand=True)
        self.pop_canvas.bind("<Configure>", lambda e: self._render_popout())

        self._apply_window_attrs()

        if self.see_through:
            self._apply_see_through()

        self._render_popout()

    def _close_popout(self):
        win = self.popout

        self.popout = None
        self.pop_canvas = None
        self.pop_big = self.pop_split = self.pop_delta = None
        self._pop_cd_item = None

        if win is not None:
            try:
                win.destroy()
            except tk.TclError:
                pass

    def _popout_rows(self):
        """Indexes of the segments the pop-out shows."""
        segs = self.game_data["segments"]

        if not self.current_game or not segs:
            return []

        n_next = clamp_int(self.ap.get("popout_next"), 0, 999, 2)

        if self.run_state in ("running", "paused"):
            first = min(self.split_index, len(segs) - 1)
        elif self.run_state == "finished":
            first = len(segs) - 1
        else:
            first = 0

        return list(range(first, min(first + 1 + n_next, len(segs))))

    def _render_popout(self):

        if self.popout is None:
            return

        c = self.pop_canvas
        th = self.th

        try:
            c.delete("all")

            self.popout.configure(bg=th["panel"])
            c.configure(bg=th["panel"])

            w = max(c.winfo_width(), 260)

            pad = 6
            h_big = self.f_big.metrics("linespace")
            h_split = max(
                self.f_split.metrics("linespace"),
                self.f_delta.metrics("linespace"),
            )
            timer_h = pad + h_big + h_split + 8

            # Timer block
            c.create_rectangle(
                0, 0, w, timer_h, fill=th["panel2"], outline=""
            )

            self.pop_big = c.create_text(
                w - 14, pad + h_big / 2, text=self.big_text, anchor="e",
                font=self.f_big, fill=th["text"],
            )
            self.pop_split = c.create_text(
                w - 14, pad + h_big + h_split / 2, text=self.split_text,
                anchor="e", font=self.f_split, fill=th["dim"],
            )
            self.pop_delta = c.create_text(
                14, pad + h_big + h_split / 2, text=self.delta_text,
                anchor="w", font=self.f_delta, fill=th["dim"],
            )

            # Split rows
            pb = self.game_data["pb"]
            best = self.game_data["best"]

            rh = max(
                self.f_ui.metrics("linespace") + 16,
                10 + self.f_small.metrics("linespace")
                + self.f_tiny.metrics("linespace"),
            )

            col2_w = max(
                self.f_small.measure("Cum 00:00.00"),
                self.f_small_b.measure("PB split -00:00.00"),
            )
            col2_right = w - 10
            col1_right = col2_right - col2_w - 10

            on_accent = contrast(th["accent"])

            self._pop_cd_item = None

            idxs = self._popout_rows()
            segs = self.game_data["segments"]

            if not idxs:
                c.create_text(
                    w / 2, timer_h + 26, text="No segments yet",
                    fill=th["dim"], font=self.f_ui,
                )

            for n, i in enumerate(idxs):

                y = timer_h + n * rh

                is_current = (
                    i == self.split_index
                    and self.run_state in ("running", "paused")
                )

                if is_current:
                    c.create_rectangle(
                        0, y, w, y + rh, fill=th["accent"], outline=""
                    )

                def col(key, cur=is_current):
                    if key == "cd":
                        return th[self.countdown_color]
                    if cur and key in ("text", "dim"):
                        return on_accent
                    return th[key]

                if i < len(self.split_times):
                    # Already completed this run: show what you did.
                    seg_dur = self.split_times[i] - (
                        self.split_times[i - 1] if i > 0 else 0
                    )
                    split_txt = fmt_time(seg_dur)
                    cum_txt = fmt_time(self.split_times[i])
                else:
                    split_txt = (
                        fmt_time(pb[i] - (pb[i - 1] if i > 0 else 0))
                        if i < len(pb) else "--"
                    )
                    cum_txt = fmt_time(pb[i]) if i < len(pb) else "--"

                gold_txt = (
                    fmt_time(best[i])
                    if i < len(best) and best[i] is not None else "--"
                )

                seg = segs[i]

                c.create_text(
                    10, y + rh / 2,
                    text=(
                        f"{seg.get('icon', '')} {self._seg_name(i, seg)}"
                        + (
                            f"  ({self._seg_pronoun(i)})"
                            if self._seg_pronoun(i) else ""
                        )
                    ),
                    anchor="w", fill=col("text"),
                    font=self.f_ui_b if is_current else self.f_ui,
                )

                l1 = self.f_small.metrics("linespace")
                l2 = self.f_tiny.metrics("linespace")
                top = y + (rh - l1 - l2) / 2

                c.create_text(
                    col1_right, top + l1 / 2, text=f"Split {split_txt}",
                    anchor="e", fill=col("text"), font=self.f_small,
                )
                c.create_text(
                    col2_right, top + l1 / 2, text=f"Cum {cum_txt}",
                    anchor="e", fill=col("text"), font=self.f_small,
                )
                c.create_text(
                    col1_right, top + l1 + l2 / 2, text=f"Gold {gold_txt}",
                    anchor="e", fill=th["gold"], font=self.f_tiny,
                )

                if is_current and self.countdown_armed and self.countdown_text:
                    self._pop_cd_item = c.create_text(
                        col2_right, top + l1 + l2 / 2,
                        text=self.countdown_text, anchor="e",
                        fill=col("cd"), font=self.f_small_b,
                    )

                c.create_line(
                    0, y + rh - 1, w, y + rh - 1, fill=th["border"]
                )

            # Fit the window height to the rows (only when that changes,
            # so manual resizing isn't fought).
            total_h = int(timer_h + max(len(idxs), 1) * rh)

            # Never taller than the screen.
            try:
                total_h = min(
                    total_h, max(int(self.popout.winfo_screenheight()) - 80, 200)
                )
            except (TypeError, ValueError):
                pass
            key = (len(idxs), rh, timer_h)

            if key != self._pop_geom_key:
                self._pop_geom_key = key

                cur_w = self.popout.winfo_width()
                width = cur_w if cur_w > 100 else 380

                self.popout.geometry(f"{width}x{total_h}")

        except tk.TclError:
            return

        self._paint_popout()

    def _paint_popout(self):

        if self.popout is None or self.pop_big is None:
            return

        th = self.th
        c = self.pop_canvas

        try:
            c.itemconfig(
                self.pop_big, text=self.big_text,
                fill=th.get(self.big_color, th["text"]),
            )
            c.itemconfig(self.pop_split, text=self.split_text, fill=th["dim"])
            c.itemconfig(
                self.pop_delta, text=self.delta_text,
                fill=th.get(self.delta_color, th["dim"]),
            )
        except tk.TclError:
            pass

    # ------------------------------------------------------- games modal --

    def open_games(self):

        if self.modal_open:
            self._raise_modal()
            return

        self.modal_open = True

        win = tk.Toplevel(self, bg=PANEL)
        self.modal_win = win

        win.title("Games")
        win.geometry("340x420")
        win.configure(bg=PANEL)
        win.transient(self)

        win.protocol("WM_DELETE_WINDOW", lambda: self._close_modal(win))

        tk.Label(
            win, text="New game name", bg=PANEL, fg=DIM,
            font=("Segoe UI", 9),
        ).pack(anchor="w", padx=12, pady=(12, 2))

        row = tk.Frame(win, bg=PANEL)
        row.pack(fill="x", padx=12)

        name_entry = tk.Entry(
            row, bg=PANEL2, fg=TEXT, insertbackground=TEXT,
            bd=1, relief="solid",
        )
        name_entry.pack(side="left", fill="x", expand=True, ipady=4)

        def pick(name):
            self._switch_game(name)
            self._close_modal(win)

        def create_game():

            name = name_entry.get().strip()

            if not name:
                return

            if name not in self.store["games"]:
                self.store["games"].append(name)

                self.store["data"][name] = new_game_data(
                    [{"name": "Segment 1", "icon": "⛳"}]
                )

            pick(name)

        tk.Button(
            row, text="Create", command=create_game,
            bg=BLUE, fg="white", bd=0,
        ).pack(side="left", padx=(6, 0), ipady=4)

        tk.Label(
            win, text="Saved games", bg=PANEL, fg=DIM,
            font=("Segoe UI", 9),
        ).pack(anchor="w", padx=12, pady=(14, 2))

        list_frame = tk.Frame(win, bg=PANEL)
        list_frame.pack(fill="both", expand=True, padx=12)

        def delete_game(name):

            if not messagebox.askyesno(
                "Delete game", f'Delete "{name}" and all its data?',
                parent=win,
            ):
                return

            self._delete_game(name)
            refresh_list()

        def refresh_list():

            for w in list_frame.winfo_children():
                w.destroy()

            if not self.store["games"]:
                tk.Label(
                    list_frame, text="No games yet.", bg=PANEL, fg=DIM
                ).pack(pady=20)
                return

            for name in self.store["games"]:

                item = tk.Frame(
                    list_frame, bg=PANEL2, bd=1, relief="solid",
                    highlightbackground=(
                        BLUE if name == self.current_game else BORDER
                    ),
                )
                item.pack(fill="x", pady=3)

                lbl = tk.Label(
                    item, text=name, bg=PANEL2, fg=TEXT,
                    font=FONT_UI, anchor="w",
                )
                lbl.pack(side="left", fill="x", expand=True, padx=8, pady=6)

                lbl.bind("<Button-1>", lambda e, n=name: pick(n))

                del_btn = tk.Label(
                    item, text="delete", bg=PANEL2, fg=RED,
                    font=("Segoe UI", 9),
                )
                del_btn.pack(side="right", padx=8)

                del_btn.bind("<Button-1>", lambda e, n=name: delete_game(n))

        refresh_list()

    # ----------------------------------------------------- settings modal --

    def open_settings(self):

        if self.modal_open:
            self._raise_modal()
            return

        self.modal_open = True

        win = tk.Toplevel(self, bg=PANEL)
        self.modal_win = win

        win.title("Settings")
        win.geometry("420x720")
        win.configure(bg=PANEL)
        win.transient(self)

        win.protocol("WM_DELETE_WINDOW", lambda: self._close_modal(win))

        canvas = tk.Canvas(win, bg=PANEL, highlightthickness=0)

        scroll = tk.Scrollbar(win, orient="vertical", command=canvas.yview)

        body = tk.Frame(canvas, bg=PANEL)

        body.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all")),
        )

        canvas.create_window((0, 0), window=body, anchor="nw", width=390)

        canvas.configure(yscrollcommand=scroll.set)

        canvas.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        def on_wheel(e):
            canvas.yview_scroll(
                int(-e.delta / 120) or (-1 if e.delta > 0 else 1), "units"
            )

        win.bind("<MouseWheel>", on_wheel)

        cb_style = dict(
            bg=PANEL, fg=TEXT, activebackground=PANEL,
            activeforeground=TEXT, selectcolor=PANEL2,
        )

        def section(text, pady=(10, 4)):
            tk.Label(
                body, text=text, bg=PANEL, fg=DIM,
                font=("Segoe UI", 9, "bold"),
            ).pack(anchor="w", padx=12, pady=pady)

        def note(text, pady=(0, 8)):
            tk.Label(
                body, text=text, bg=PANEL, fg=DIM, font=("Segoe UI", 8),
                wraplength=350, justify="left",
            ).pack(anchor="w", padx=12, pady=pady)

        def style_menu(om):
            om.config(
                bg=PANEL2, fg=TEXT, activebackground=PANEL2,
                activeforeground=TEXT, bd=1, relief="solid",
                highlightthickness=0,
            )
            om["menu"].config(bg=PANEL2, fg=TEXT)

        # ----------------------------------------------------
        # SEGMENTS
        # ----------------------------------------------------

        note(
            f'Everything in this window belongs to "{self.current_game}" '
            "only. Other games keep their own colors, fonts, image, "
            "hotkeys and countdown settings.",
            (8, 0),
        )

        section("SEGMENTS", (4, 4))

        seg_list_frame = tk.Frame(body, bg=PANEL)
        seg_list_frame.pack(fill="x", padx=12)

        working_segments = (
            [dict(s) for s in self.game_data["segments"]]
            if self.current_game
            else []
        )

        def refresh_seg_list():

            for w in seg_list_frame.winfo_children():
                w.destroy()

            for i, seg in enumerate(working_segments):

                row = tk.Frame(seg_list_frame, bg=PANEL)
                row.pack(fill="x", pady=2)

                icon_var = tk.StringVar(value=seg.get("icon", "⛳"))
                name_var = tk.StringVar(value=seg.get("name", ""))

                def on_icon_change(*_, i=i, var=icon_var):
                    working_segments[i]["icon"] = var.get()

                def on_name_change(*_, i=i, var=name_var):
                    working_segments[i]["name"] = var.get()

                icon_var.trace_add("write", on_icon_change)
                name_var.trace_add("write", on_name_change)

                tk.Entry(
                    row, textvariable=icon_var, width=3, bg=PANEL2, fg=TEXT,
                    insertbackground=TEXT, bd=1, relief="solid",
                ).pack(side="left", padx=(0, 4), ipady=3)

                tk.Entry(
                    row, textvariable=name_var, bg=PANEL2, fg=TEXT,
                    insertbackground=TEXT, bd=1, relief="solid",
                ).pack(side="left", fill="x", expand=True, ipady=3)

                def move_up(i=i):
                    if i > 0:
                        working_segments[i - 1], working_segments[i] = (
                            working_segments[i], working_segments[i - 1]
                        )
                        refresh_seg_list()

                def move_down(i=i):
                    if i < len(working_segments) - 1:
                        working_segments[i + 1], working_segments[i] = (
                            working_segments[i], working_segments[i + 1]
                        )
                        refresh_seg_list()

                def delete_row(i=i):
                    working_segments.pop(i)
                    refresh_seg_list()

                for txt, cmd, fg in (
                    ("↑", move_up, DIM),
                    ("↓", move_down, DIM),
                    ("✕", delete_row, RED),
                ):
                    tk.Button(
                        row, text=txt, command=cmd, bg=PANEL2, fg=fg,
                        bd=1, relief="solid", width=2,
                    ).pack(side="left", padx=1)

        refresh_seg_list()

        def add_seg():
            working_segments.append({"name": "New Segment", "icon": "⛳"})
            refresh_seg_list()

        tk.Button(
            body, text="+ Add segment", command=add_seg,
            bg=PANEL2, fg=TEXT, bd=1, relief="solid",
        ).pack(fill="x", padx=12, pady=(6, 4), ipady=4)

        def save_segments():

            if not self.current_game:
                return

            self.game_data["segments"] = working_segments

            n = len(working_segments)

            self.game_data["pb"] = self.game_data["pb"][:n]
            self.game_data["best"] = self.game_data["best"][:n]

            # If the "since" split was renamed/removed, clear it.
            names_lower = [
                s.get("name", "").strip().lower() for s in working_segments
            ]
            since = self.game_data.get("since_split")

            if since and since.strip().lower() not in names_lower:
                self.game_data["since_split"] = None

            self._persist()

            self._render_header()
            self._render_segments()

            self._close_modal(win)

        tk.Button(
            body, text="Save segments", command=save_segments,
            bg=BLUE, fg="white", bd=0,
        ).pack(fill="x", padx=12, pady=(0, 10), ipady=6)

        # ----------------------------------------------------
        # SINCE COUNTER
        # ----------------------------------------------------

        section("COUNTER: RUNS SINCE REACHING (this game)")

        since_var = tk.StringVar(
            value=self.game_data.get("since_split") or "(none)"
        )

        since_names = ["(none)"] + [
            s.get("name", "") for s in self.game_data["segments"]
        ]

        def on_since_change(*_):

            if not self.current_game:
                return

            v = since_var.get()
            new = None if v == "(none)" else v

            if new != self.game_data.get("since_split"):
                self.game_data["since_split"] = new
                self.game_data.setdefault("stats", {})["runs_since_split"] = 0
                self._persist()
                self._render_header()

        since_var.trace_add("write", on_since_change)

        om = tk.OptionMenu(body, since_var, *since_names)
        style_menu(om)
        om.pack(fill="x", padx=12, pady=(0, 2))

        note(
            "Uses saved segments - click \"Save segments\" first after "
            "adding or renaming one. Changing this resets the counter to 0."
        )

        # ----------------------------------------------------
        # TIMES
        # ----------------------------------------------------

        section("EDIT TIMES (PB cumulative, Gold segment)", (8, 4))

        times_frame = tk.Frame(body, bg=PANEL)
        times_frame.pack(fill="x", padx=12)

        pb_mode_var = tk.BooleanVar(
            value=bool(self.game_data.get("pb_split_mode", False))
        )

        def on_pb_mode_toggle():
            refresh_times_entries()

        mode_row = tk.Frame(body, bg=PANEL)
        mode_row.pack(fill="x", padx=12, pady=(4, 6))

        tk.Checkbutton(
            mode_row,
            text="Enter PB as split (segment) durations",
            variable=pb_mode_var, command=on_pb_mode_toggle, **cb_style,
        ).pack(anchor="w")

        pb_entries = []
        best_entries = []

        def refresh_times_entries():

            for w in times_frame.winfo_children():
                w.destroy()

            cur_pb = list(self.game_data.get("pb", []))
            cur_best = list(self.game_data.get("best", []))

            pb_entries.clear()
            best_entries.clear()

            use_split_mode = bool(pb_mode_var.get())

            for i, seg in enumerate(working_segments):

                row = tk.Frame(times_frame, bg=PANEL)
                row.pack(fill="x", pady=2)

                tk.Label(
                    row, text=seg.get("icon", "") + " " + seg.get("name", ""),
                    bg=PANEL, fg=TEXT, font=FONT_UI,
                ).pack(side="left")

                # PB
                if use_split_mode:
                    if i < len(cur_pb):
                        prev = cur_pb[i - 1] if i > 0 else 0
                        pb_val = fmt_time(cur_pb[i] - prev)
                    else:
                        pb_val = ""
                else:
                    pb_val = fmt_time(cur_pb[i]) if i < len(cur_pb) else ""

                pb_ent = tk.Entry(
                    row, bg=PANEL2, fg=TEXT, insertbackground=TEXT,
                    bd=1, relief="solid", width=12,
                )
                pb_ent.insert(0, pb_val)
                pb_ent.pack(side="right", padx=(4, 0))

                tk.Label(
                    row, text="Split" if use_split_mode else "PB",
                    bg=PANEL, fg=DIM,
                ).pack(side="right")

                # Gold
                best_val = (
                    fmt_time(cur_best[i])
                    if i < len(cur_best) and cur_best[i] is not None
                    else ""
                )

                best_ent = tk.Entry(
                    row, bg=PANEL2, fg=TEXT, insertbackground=TEXT,
                    bd=1, relief="solid", width=12,
                )
                best_ent.insert(0, best_val)
                best_ent.pack(side="right", padx=(4, 0))

                tk.Label(row, text="Gold", bg=PANEL, fg=DIM).pack(side="right")

                pb_entries.append(pb_ent)
                best_entries.append(best_ent)

        refresh_times_entries()

        def save_times():

            use_split_mode = bool(pb_mode_var.get())

            new_pb = []

            for ent in pb_entries:

                v = ent.get().strip()

                if not v:
                    break

                ms = parse_time(v)

                if ms is None:
                    messagebox.showerror(
                        "Invalid time", f"Invalid PB time: {v}", parent=win
                    )
                    return

                new_pb.append(ms)

            # Convert segment durations to cumulative PB times.
            if use_split_mode and new_pb:
                cum = []
                total = 0

                for dur in new_pb:
                    total += dur
                    cum.append(total)

                new_pb = cum

            for j in range(1, len(new_pb)):
                if new_pb[j] < new_pb[j - 1]:
                    messagebox.showerror(
                        "Invalid PB",
                        "PB cumulative times must be non-decreasing",
                        parent=win,
                    )
                    return

            new_best = []

            for ent in best_entries:

                v = ent.get().strip()

                if not v:
                    new_best.append(None)
                    continue

                ms = parse_time(v)

                if ms is None:
                    messagebox.showerror(
                        "Invalid time", f"Invalid Gold time: {v}", parent=win
                    )
                    return

                new_best.append(ms)

            n = len(working_segments)

            self.game_data["pb"] = [int(x) for x in new_pb[:n]]
            self.game_data["pb_split_mode"] = bool(pb_mode_var.get())
            self.game_data["best"] = new_best[:n]

            # Manual time editing is not a new run,
            # so it does not create PB history.
            self._persist()

            self._render_header()
            self._render_segments()

            messagebox.showinfo("Saved", "Times saved.", parent=win)

        tk.Button(
            body, text="Save times", command=save_times,
            bg=BLUE, fg="white", bd=0,
        ).pack(fill="x", padx=12, pady=(6, 10), ipady=6)

        # ----------------------------------------------------
        # GOAL TIMES
        # ----------------------------------------------------

        section("GOAL TIMES (up to 5)", (6, 4))

        note(
            "Times you want to beat: a friend's PB, the world record... "
            "Each goal shows on every split row with the split time on top "
            "and the cumulative below. Once you've split, a +/- appears "
            "next to each so you can see how far behind you are.",
            (0, 4),
        )

        goal_mode_var = tk.BooleanVar(
            value=bool(self.game_data.get("goal_split_mode", False))
        )
        goal_prev_mode = {"v": bool(goal_mode_var.get())}
        goal_sel = {"i": 0}
        working_goals = []

        for g in (self.game_data.get("goals") or [])[:MAX_GOALS]:
            working_goals.append({
                "name": str(g.get("name") or ""),
                "vals": goal_times_to_texts(
                    g.get("times") or [], len(working_segments),
                    goal_prev_mode["v"],
                ),
            })

        def on_goal_mode_toggle():
            new_mode = bool(goal_mode_var.get())
            converted = []

            for g in working_goals:
                times, bad = goal_texts_to_times(
                    g["vals"], goal_prev_mode["v"]
                )

                if bad is not None:
                    messagebox.showerror(
                        "Invalid time", f"Invalid goal time: {bad}",
                        parent=win,
                    )
                    goal_mode_var.set(goal_prev_mode["v"])
                    return

                converted.append(times)

            for g, times in zip(working_goals, converted):
                g["vals"] = goal_times_to_texts(
                    times, len(working_segments), new_mode
                )

            goal_prev_mode["v"] = new_mode
            render_goals()

        tk.Checkbutton(
            body,
            text="Enter goal times as split (segment) durations",
            variable=goal_mode_var, command=on_goal_mode_toggle, **cb_style,
        ).pack(anchor="w", padx=12, pady=(0, 4))

        goals_frame = tk.Frame(body, bg=PANEL)
        goals_frame.pack(fill="x", padx=12)

        def select_goal(gi):
            goal_sel["i"] = gi
            render_goals()

        def remove_goal(gi):
            working_goals.pop(gi)
            goal_sel["i"] = max(0, min(goal_sel["i"], len(working_goals) - 1))
            render_goals()

        def render_goals():
            for w in goals_frame.winfo_children():
                w.destroy()

            try:
                add_goal_btn.config(
                    state="normal" if len(working_goals) < MAX_GOALS
                    else "disabled"
                )
            except Exception:
                pass

            if not working_goals:
                tk.Label(
                    goals_frame, text="No goals yet.", bg=PANEL, fg=DIM,
                    font=("Segoe UI", 9),
                ).pack(anchor="w", pady=2)
                return

            gi = min(goal_sel["i"], len(working_goals) - 1)
            goal_sel["i"] = gi
            g = working_goals[gi]

            while len(g["vals"]) < len(working_segments):
                g["vals"].append("")

            tabs = tk.Frame(goals_frame, bg=PANEL)
            tabs.pack(fill="x", pady=(0, 4))

            for k, other in enumerate(working_goals):
                on = k == gi

                tk.Button(
                    tabs,
                    text=(other["name"].strip() or f"Goal {k + 1}")[:10],
                    command=lambda k=k: select_goal(k),
                    bg=BLUE if on else PANEL2,
                    fg="white" if on else TEXT, bd=1, relief="solid",
                ).pack(side="left", padx=(0, 3))

            name_row = tk.Frame(goals_frame, bg=PANEL)
            name_row.pack(fill="x", pady=2)

            tk.Label(
                name_row, text="Goal name", bg=PANEL, fg=TEXT, font=FONT_UI
            ).pack(side="left")

            name_var = tk.StringVar(value=g["name"])

            def on_name(*_, g=g, var=name_var):
                g["name"] = var.get()

            name_var.trace_add("write", on_name)

            tk.Entry(
                name_row, textvariable=name_var, bg=PANEL2, fg=TEXT,
                insertbackground=TEXT, bd=1, relief="solid", width=18,
            ).pack(side="right", ipady=3)

            split_mode = bool(goal_mode_var.get())

            for k, seg in enumerate(working_segments):
                row = tk.Frame(goals_frame, bg=PANEL)
                row.pack(fill="x", pady=2)

                tk.Label(
                    row,
                    text=seg.get("icon", "") + " " + seg.get("name", ""),
                    bg=PANEL, fg=TEXT, font=FONT_UI,
                ).pack(side="left")

                var = tk.StringVar(value=g["vals"][k])

                def on_val(*_, g=g, k=k, var=var):
                    g["vals"][k] = var.get()

                var.trace_add("write", on_val)

                tk.Entry(
                    row, textvariable=var, bg=PANEL2, fg=TEXT,
                    insertbackground=TEXT, bd=1, relief="solid", width=12,
                ).pack(side="right", padx=(4, 0))

                tk.Label(
                    row, text="Split" if split_mode else "Cum",
                    bg=PANEL, fg=DIM,
                ).pack(side="right")

            tk.Button(
                goals_frame, text="Remove this goal",
                command=lambda gi=gi: remove_goal(gi),
                bg="#3a1f1f", fg=RED, bd=0,
            ).pack(fill="x", pady=(6, 2), ipady=3)

        def add_goal():
            if len(working_goals) >= MAX_GOALS:
                return

            working_goals.append({
                "name": f"Goal {len(working_goals) + 1}",
                "vals": [""] * len(working_segments),
            })
            goal_sel["i"] = len(working_goals) - 1
            render_goals()

        add_goal_btn = tk.Button(
            body, text="+ Add goal", command=add_goal,
            bg=PANEL2, fg=TEXT, bd=1, relief="solid",
        )
        add_goal_btn.pack(fill="x", padx=12, pady=(6, 4), ipady=4)

        def save_goals():
            split_mode = bool(goal_mode_var.get())
            new_goals = []

            for g in working_goals:
                times, bad = goal_texts_to_times(g["vals"], split_mode)

                if bad is not None:
                    messagebox.showerror(
                        "Invalid time",
                        f'Invalid time in "{g["name"] or "goal"}": {bad}',
                        parent=win,
                    )
                    return

                known = [t for t in times if t is not None]

                if any(b < a for a, b in zip(known, known[1:])):
                    messagebox.showerror(
                        "Invalid goal",
                        f'"{g["name"] or "goal"}": cumulative times must be '
                        "non-decreasing",
                        parent=win,
                    )
                    return

                n = len(working_segments)

                new_goals.append({
                    "name": g["name"].strip() or "Goal",
                    "times": [
                        None if t is None else int(t) for t in times[:n]
                    ],
                })

            self.game_data["goals"] = new_goals
            self.game_data["goal_split_mode"] = split_mode

            self._persist()
            self._render_segments()

            # Make the window wide enough to show every goal column.
            try:
                need = getattr(self, "_goal_need_w", 0)
                cur_w = self.winfo_width()
                cap = self.winfo_screenwidth() - 40

                if new_goals and need > cur_w:
                    self.geometry(f"{min(need, cap)}x{self.winfo_height()}")
            except Exception:
                pass

            messagebox.showinfo("Saved", "Goal times saved.", parent=win)

        tk.Button(
            body, text="Save goals", command=save_goals,
            bg=BLUE, fg="white", bd=0,
        ).pack(fill="x", padx=12, pady=(0, 10), ipady=6)

        render_goals()

        # ----------------------------------------------------
        # IMPORT / EXPORT
        # ----------------------------------------------------

        section("IMPORT / EXPORT", (6, 4))

        tk.Button(
            body, text="Export game to .json",
            command=self.export_game_to_json,
            bg=PANEL2, fg=TEXT, bd=1, relief="solid",
        ).pack(fill="x", padx=12, pady=3, ipady=5)

        tk.Button(
            body, text="Import game from .json",
            command=self.import_game_from_json,
            bg=PANEL2, fg=TEXT, bd=1, relief="solid",
        ).pack(fill="x", padx=12, pady=(3, 10), ipady=5)

        tk.Button(
            body, text="Copy PB rows for Google Sheets",
            command=self.copy_pb_to_sheet,
            bg=PANEL2, fg=TEXT, bd=1, relief="solid",
        ).pack(fill="x", padx=12, pady=(0, 10), ipady=5)

        # ----------------------------------------------------
        # KEYBINDS (per game)
        # ----------------------------------------------------

        section("KEYBINDS (this game only)", (6, 4))

        glob_var = tk.BooleanVar(value=bool(self.game_data.get("global_hotkeys")))

        def on_global_toggle():
            self.game_data["global_hotkeys"] = bool(glob_var.get())
            self._persist()
            self._apply_keybinds()

        tk.Checkbutton(
            body,
            text="Hotkeys work when this window is not focused",
            variable=glob_var, command=on_global_toggle,
            state="normal" if IS_WINDOWS else "disabled", **cb_style,
        ).pack(anchor="w", padx=12)

        note(
            "When on, these keys are read system-wide, so they will also "
            "fire while you type in other apps. Function keys or numpad "
            "keys are safest."
            if IS_WINDOWS
            else "Global hotkeys are only available on Windows in this "
                 "version.",
            (0, 6),
        )

        listen = {"action": None, "bind_id": None, "label": None}

        def stop_listening():
            if listen["bind_id"] is not None:
                try:
                    win.unbind("<KeyPress>", listen["bind_id"])
                except Exception:
                    pass
            listen["bind_id"] = None
            listen["action"] = None
            self.listening_for = None

        def restore_label(action, lbl):
            lbl.config(text=seq_to_label(self.keybinds[action]), fg=TEXT)

        def start_listen(action, value_lbl):

            # Cancel any other row that is waiting for a key.
            if listen["action"] is not None and listen["label"] is not None:
                restore_label(listen["action"], listen["label"])

            stop_listening()

            listen["action"] = action
            listen["label"] = value_lbl
            self.listening_for = action

            value_lbl.config(text="Press keys... (Esc cancels)", fg=BLUE)

            win.focus_set()

            def capture(event):

                if listen["action"] != action:
                    return

                keysym = event.keysym

                if keysym in (
                    "Shift_L", "Shift_R", "Control_L", "Control_R",
                    "Alt_L", "Alt_R", "Caps_Lock", "Num_Lock",
                ):
                    return

                mods = []

                if event.state & 0x0001:
                    mods.append("Shift")

                if event.state & 0x0004:
                    mods.append("Control")

                # On Windows 0x0008 is Num Lock, so only use 0x20000.
                alt_mask = 0x20000 if IS_WINDOWS else 0x0008

                if event.state & alt_mask:
                    mods.append("Alt")

                if keysym == "Escape" and not mods:
                    restore_label(action, value_lbl)
                    stop_listening()
                    return "break"

                seq = "<" + "-".join(mods + [keysym]) + ">"

                # Don't allow the same key on two actions of this game.
                for other, other_name in KEY_ACTIONS:
                    if other != action and self.keybinds.get(other) == seq:
                        messagebox.showwarning(
                            "Key already used",
                            f"{seq_to_label(seq)} is already bound to "
                            f"{other_name} for this game.",
                            parent=win,
                        )
                        restore_label(action, value_lbl)
                        stop_listening()
                        return "break"

                self.keybinds[action] = seq

                restore_label(action, value_lbl)
                stop_listening()

                self._persist()
                self._apply_keybinds()
                self._render_all()

                if (
                    self._global_active()
                    and keysym_to_vk(keysym) is None
                ):
                    messagebox.showinfo(
                        "Not available globally",
                        f"{seq_to_label(seq)} can't be read when the "
                        "window is unfocused, so it will only work while "
                        "this window is focused. Try a letter, number, "
                        "function or numpad key.",
                        parent=win,
                    )

                return "break"

            listen["bind_id"] = win.bind("<KeyPress>", capture)

        for action, label in KEY_ACTIONS:

            row = tk.Frame(body, bg=PANEL)
            row.pack(fill="x", padx=12, pady=4)

            tk.Label(
                row, text=label, bg=PANEL, fg=TEXT, font=FONT_UI
            ).pack(side="left")

            val_lbl = tk.Label(
                row, text=seq_to_label(self.keybinds[action]),
                bg=PANEL2, fg=TEXT, font=("Segoe UI", 9),
                padx=10, pady=4, bd=1, relief="solid",
            )
            val_lbl.pack(side="right")

            val_lbl.bind(
                "<Button-1>",
                lambda e, a=action, v=val_lbl: start_listen(a, v),
            )

        note("Click a keybind, then press the new key combo.", (2, 10))

        # ----------------------------------------------------
        # BEHAVIOR
        # ----------------------------------------------------

        section("BEHAVIOR", (6, 4))

        cd_var = tk.BooleanVar(value=bool(self.game_data.get("countdown_mode")))

        def on_cd_toggle():
            self.game_data["countdown_mode"] = bool(cd_var.get())
            self.countdown_armed = False
            self.countdown_text = ""
            self._persist()
            self._render_segments()

        tk.Checkbutton(
            body,
            text="Countdown mode: split key shows a live countdown first",
            variable=cd_var, command=on_cd_toggle, **cb_style,
        ).pack(anchor="w", padx=12)

        note(
            "Press the split key when you're close: it shows how far you "
            "are from the target (like -0:10.00) and keeps counting live. "
            "Press the split key again to actually split. The first split "
            "of a run still starts the timer as normal.",
            (0, 4),
        )

        tk.Label(
            body, text="Count down to", bg=PANEL, fg=TEXT, font=FONT_UI
        ).pack(anchor="w", padx=12)

        target_labels = {v: k for k, v in COUNTDOWN_TARGETS.items()}

        cd_target_var = tk.StringVar(
            value=target_labels.get(
                self.game_data.get("countdown_target"), "PB split time"
            )
        )

        def on_cd_target(*_):
            self.game_data["countdown_target"] = COUNTDOWN_TARGETS.get(
                cd_target_var.get(), "pb_split"
            )
            self._persist()

        cd_target_var.trace_add("write", on_cd_target)

        om = tk.OptionMenu(body, cd_target_var, *COUNTDOWN_TARGETS.keys())
        style_menu(om)
        om.pack(fill="x", padx=12, pady=(2, 10))

        rn_var = tk.BooleanVar(value=bool(self.game_data.get("random_names")))

        def on_rn_toggle():
            self.game_data["random_names"] = bool(rn_var.get())
            self._persist()

        tk.Checkbutton(
            body,
            text="Random pronoun next to each split name (new every run)",
            variable=rn_var, command=on_rn_toggle, **cb_style,
        ).pack(anchor="w", padx=12)

        note(
            "Each run, every split gets a random pronoun shown next to its "
            "name (he, they, xe, fae/faer...). Names, times and stats are "
            "untouched. Applies from the next run.",
            (0, 6),
        )

        pre_row = tk.Frame(body, bg=PANEL)
        pre_row.pack(fill="x", padx=12, pady=(0, 2))

        tk.Label(
            pre_row, text="Pre-countdown (seconds, 0 = off)",
            bg=PANEL, fg=TEXT, font=FONT_UI,
        ).pack(side="left")

        pre_var = tk.StringVar(
            value=str(-abs(int(self.game_data.get("pre_countdown") or 0)))
        )

        def apply_pre(*_):
            try:
                v = abs(int(pre_var.get()))
            except ValueError:
                return

            v = min(v, 600)

            if v != self.game_data.get("pre_countdown"):
                self.game_data["pre_countdown"] = v
                self._persist()

        pre_sp = tk.Spinbox(
            pre_row, from_=-600, to=0, width=5, textvariable=pre_var,
            command=apply_pre, bg=PANEL2, fg=TEXT, insertbackground=TEXT,
            buttonbackground=PANEL2, bd=1, relief="solid",
        )
        pre_sp.pack(side="right")
        pre_sp.bind("<Return>", apply_pre)
        pre_sp.bind("<FocusOut>", apply_pre)

        note(
            "Set it to -30 and the timer starts at -0:30.00 when you press "
            "start, counting up to 0 before the run begins. Splitting is "
            "disabled until it hits 0, and resetting during it doesn't "
            "count as an attempt.",
            (2, 10),
        )

        # ----------------------------------------------------
        # APPEARANCE
        # ----------------------------------------------------

        section("APPEARANCE: COLORS", (6, 4))

        current_preset = next(
            (n for n, p in THEMES.items() if p == self.ap["colors"]), "Custom"
        )

        preset_var = tk.StringVar(value=current_preset)
        swatches = {}

        def on_preset(*_):
            name = preset_var.get()

            if name in THEMES:
                self.ap["colors"].update(THEMES[name])

                for k, b in swatches.items():
                    col_hex = self.ap["colors"][k]
                    b.config(
                        bg=col_hex, fg=contrast(col_hex), text=col_hex,
                        activebackground=col_hex,
                    )

                self._appearance_changed()

        preset_var.trace_add("write", on_preset)

        prow = tk.Frame(body, bg=PANEL)
        prow.pack(fill="x", padx=12, pady=(0, 6))

        tk.Label(
            prow, text="Preset", bg=PANEL, fg=TEXT, font=FONT_UI
        ).pack(side="left")

        om = tk.OptionMenu(prow, preset_var, "Custom", *THEMES.keys())
        style_menu(om)
        om.pack(side="right")

        def pick_color(key):
            res = colorchooser.askcolor(
                color=self.ap["colors"][key], parent=win,
                title=dict(COLOR_LABELS)[key],
            )

            if res and res[1]:
                self.ap["colors"][key] = res[1]

                swatches[key].config(
                    bg=res[1], fg=contrast(res[1]), text=res[1],
                    activebackground=res[1],
                )

                preset_var.set("Custom")
                self._appearance_changed()

        for key, label in COLOR_LABELS:

            row = tk.Frame(body, bg=PANEL)
            row.pack(fill="x", padx=12, pady=2)

            tk.Label(
                row, text=label, bg=PANEL, fg=TEXT, font=FONT_UI
            ).pack(side="left")

            col_hex = self.ap["colors"][key]

            b = tk.Button(
                row, text=col_hex, width=10, bg=col_hex, fg=contrast(col_hex),
                activebackground=col_hex, bd=1, relief="solid",
                command=lambda k=key: pick_color(k),
            )
            b.pack(side="right")

            swatches[key] = b

        section("APPEARANCE: FONTS", (12, 4))

        frow = tk.Frame(body, bg=PANEL)
        frow.pack(fill="x", padx=12, pady=2)

        tk.Label(
            frow, text="Font", bg=PANEL, fg=TEXT, font=FONT_UI
        ).pack(side="left")

        families = sorted({f for f in tkfont.families() if not f.startswith("@")})

        font_var = tk.StringVar(value=self.ap.get("font_family", "Segoe UI"))

        font_box = ttk.Combobox(
            frow, textvariable=font_var, values=families,
            state="readonly", width=24,
        )
        font_box.pack(side="right")

        def on_font(_e=None):
            self.ap["font_family"] = font_var.get()
            self._appearance_changed()

        font_box.bind("<<ComboboxSelected>>", on_font)

        def spin(label, key, lo, hi):
            row = tk.Frame(body, bg=PANEL)
            row.pack(fill="x", padx=12, pady=2)

            tk.Label(
                row, text=label, bg=PANEL, fg=TEXT, font=FONT_UI
            ).pack(side="left")

            var = tk.StringVar(value=str(self.ap[key]))

            def apply(*_):
                try:
                    v = int(var.get())
                except ValueError:
                    return

                v = max(lo, min(hi, v))

                if v != self.ap[key]:
                    self.ap[key] = v
                    self._appearance_changed()

            sp = tk.Spinbox(
                row, from_=lo, to=hi, width=5, textvariable=var,
                command=apply, bg=PANEL2, fg=TEXT, insertbackground=TEXT,
                buttonbackground=PANEL2, bd=1, relief="solid",
            )
            sp.pack(side="right")
            sp.bind("<Return>", apply)
            sp.bind("<FocusOut>", apply)

        spin("Text size", "font_size", 7, 24)
        spin("Big timer size", "big_timer_size", 16, 90)

        section("APPEARANCE: BACKGROUND IMAGE", (12, 4))

        if not HAVE_PIL:
            note(
                "Background images need Pillow. Install it with:  "
                "pip install pillow  (then restart the timer).",
                (0, 4),
            )

        img_name_var = tk.StringVar(
            value=Path(self.ap["bg_image"]).name
            if self.ap.get("bg_image") else "(none)"
        )

        tk.Label(
            body, textvariable=img_name_var, bg=PANEL, fg=DIM,
            font=("Segoe UI", 9),
        ).pack(anchor="w", padx=12)

        irow = tk.Frame(body, bg=PANEL)
        irow.pack(fill="x", padx=12, pady=4)

        def choose_image():
            path = filedialog.askopenfilename(
                parent=win, title="Choose background image",
                filetypes=[
                    ("Images", "*.png *.jpg *.jpeg *.gif *.bmp *.webp"),
                    ("All files", "*.*"),
                ],
            )

            if not path:
                return

            self.ap["bg_image"] = path
            img_name_var.set(Path(path).name)
            self._appearance_changed()

        def clear_image():
            self.ap["bg_image"] = ""
            img_name_var.set("(none)")
            self._appearance_changed()

        state = "normal" if HAVE_PIL else "disabled"

        tk.Button(
            irow, text="Choose image...", command=choose_image, state=state,
            bg=PANEL2, fg=TEXT, bd=1, relief="solid",
        ).pack(side="left", expand=True, fill="x", padx=(0, 3), ipady=3)

        tk.Button(
            irow, text="Remove", command=clear_image, state=state,
            bg=PANEL2, fg=TEXT, bd=1, relief="solid",
        ).pack(side="left", expand=True, fill="x", padx=(3, 0), ipady=3)

        def scale(label, key, lo, hi):
            tk.Label(
                body, text=label, bg=PANEL, fg=TEXT, font=FONT_UI
            ).pack(anchor="w", padx=12)

            def on_scale(v):
                v = int(float(v))

                if v != self.ap[key]:
                    self.ap[key] = v
                    self._appearance_changed()

            s = tk.Scale(
                body, from_=lo, to=hi, orient="horizontal", showvalue=True,
                bg=PANEL, fg=TEXT, troughcolor=PANEL2, highlightthickness=0,
                bd=0, command=on_scale,
            )
            s.set(self.ap[key])
            s.pack(fill="x", padx=12, pady=(0, 4))

        scale("Image dimming (higher = easier to read text)", "bg_dim", 0, 100)

        fit_var = tk.StringVar(value=self.ap.get("bg_fit", "cover"))

        def on_fit(*_):
            self.ap["bg_fit"] = fit_var.get()
            self._appearance_changed()

        fit_var.trace_add("write", on_fit)

        frow2 = tk.Frame(body, bg=PANEL)
        frow2.pack(fill="x", padx=12, pady=2)

        tk.Label(
            frow2, text="Fit", bg=PANEL, fg=TEXT, font=FONT_UI
        ).pack(side="left")

        om = tk.OptionMenu(frow2, fit_var, "cover", "fit", "stretch")
        style_menu(om)
        om.pack(side="right")

        note(
            "cover = fill the window (edges cropped), fit = whole image "
            "visible, stretch = squash to the window. The image resizes "
            "with the window.",
            (0, 4),
        )

        anchor_var = tk.StringVar(value=self.ap.get("bg_anchor", "center"))

        def on_anchor(*_):
            self.ap["bg_anchor"] = anchor_var.get()
            self._appearance_changed()

        anchor_var.trace_add("write", on_anchor)

        arow = tk.Frame(body, bg=PANEL)
        arow.pack(fill="x", padx=12, pady=2)

        tk.Label(
            arow, text="Shrinks toward", bg=PANEL, fg=TEXT, font=FONT_UI
        ).pack(side="left")

        om = tk.OptionMenu(arow, anchor_var, *BG_ANCHORS.keys())
        style_menu(om)
        om.pack(side="right")

        def ap_check(text, key, sub=None):
            cur = self.ap[key] if sub is None else self.ap[key][sub]

            var = tk.BooleanVar(value=bool(cur))

            def on():
                if sub is None:
                    self.ap[key] = bool(var.get())
                else:
                    self.ap[key][sub] = bool(var.get())

                self._appearance_changed()

            tk.Checkbutton(
                body, text=text, variable=var, command=on, **cb_style,
            ).pack(anchor="w", padx=12)

        ap_check("Show image behind the split list", "bg_list")
        ap_check("Show image behind the timer area", "bg_info")

        section("APPEARANCE: EFFECTS", (12, 4))

        ap_check("Fireworks when you get a new PB", "fx_fireworks")
        ap_check("Big GOLD splash when you beat a gold", "fx_gold")

        section("APPEARANCE: WHAT TO SHOW", (12, 4))

        ap_check("Split time column", "show_cols", "split")
        ap_check("Δ split column", "show_cols", "dsplit")
        ap_check("Gold column", "show_cols", "gold")
        ap_check("Cumulative time column", "show_cols", "cum")
        ap_check("Δ cumulative column", "show_cols", "dcum")
        ap_check("Δ Gold column (distance to gold)", "show_cols", "dgold")
        ap_check("Gold cumulative column", "show_cols", "gcum")
        ap_check(
            "Δ Gold cumulative column (distance to gold cumulative)",
            "show_cols", "dgcum",
        )
        ap_check("Stats on each split row (reach %, averages)", "show_split_stats")
        ap_check("Best Possible Time / Sum of Best row", "show_bpt")

        section("APPEARANCE: WINDOW", (12, 4))

        ap_check("Always on top", "topmost")
        scale("Window opacity %", "alpha", 30, 100)

        section("POP-OUT WINDOW", (12, 4))

        note(
            "A small window with the timer and the current split's "
            "split/gold/cumulative times. It can also show the next few "
            "splits.",
            (0, 4),
        )

        spin("Upcoming splits to show", "popout_next", 0, 999)
        ap_check("Pop-out always on top", "popout_topmost")

        tk.Button(
            body, text="Open pop-out window", command=self.open_popout,
            bg=PANEL2, fg=TEXT, bd=1, relief="solid",
        ).pack(fill="x", padx=12, pady=(6, 4), ipady=5)

        def reset_appearance():
            if not messagebox.askyesno(
                "Reset appearance",
                "Reset all colors, fonts, image and display options?",
                parent=win,
            ):
                return

            self.ap = copy.deepcopy(DEFAULT_APPEARANCE)
            self.game_data["appearance"] = self.ap
            self._refresh_theme()

            self._appearance_changed()

            # Reopen so every control shows the default values again.
            self._close_modal(win)
            self.after(250, self.open_settings)

        tk.Button(
            body, text="Reset appearance to defaults",
            command=reset_appearance,
            bg=PANEL2, fg=TEXT, bd=1, relief="solid",
        ).pack(fill="x", padx=12, pady=(10, 10), ipady=5)

        # ----------------------------------------------------
        # DANGER ZONE
        # ----------------------------------------------------

        section("DANGER ZONE", (6, 4))

        def clear_pb():

            if not self.current_game:
                return

            if not messagebox.askyesno(
                "Clear PB",
                f'Clear PB and gold splits for "{self.current_game}"?',
                parent=win,
            ):
                return

            self.game_data["pb"] = []
            self.game_data["best"] = []

            # Once the PB is manually cleared, its old history
            # should not be able to resurrect it.
            self.game_data["pb_history"] = []

            self._persist()

            self._render_header()
            self._render_segments()

        def clear_split_stats():

            if not self.current_game:
                return

            if not messagebox.askyesno(
                "Reset split stats",
                "Clear reach % and split averages for this game?",
                parent=win,
            ):
                return

            self.game_data["split_stats"] = {}
            self.game_data.setdefault("stats", {})["runs_since_split"] = 0

            self._persist()

            self._render_header()
            self._render_segments()

        def delete_last_pb():

            history = self.game_data.get("pb_history", [])

            if not history:
                messagebox.showinfo(
                    "Delete last PB", "There is no previous PB to restore.",
                    parent=win,
                )
                return

            if not messagebox.askyesno(
                "Delete last PB",
                "Delete the current PB and restore the previous one?",
                parent=win,
            ):
                return

            previous = history.pop()

            # History stores only the PB. Older saves may also contain
            # "best"; it's ignored so deleting a PB can't erase golds
            # that were earned later.
            if isinstance(previous, dict):
                self.game_data["pb"] = list(previous.get("pb", []))
            elif isinstance(previous, list):
                self.game_data["pb"] = list(previous)
            else:
                self.game_data["pb"] = []

            self._persist()

            self._render_header()
            self._render_segments()

        def delete_current_game():

            if not self.current_game:
                return

            if not messagebox.askyesno(
                "Delete game",
                f'Delete "{self.current_game}" and all its data?',
                parent=win,
            ):
                return

            self._delete_game(self.current_game)
            self._close_modal(win)

        for text, cmd, pady in (
            ("Clear PB & gold splits for this game", clear_pb, 3),
            ("Reset split stats (reach % / averages)", clear_split_stats, 3),
            ("Delete last PB (restore previous)", delete_last_pb, 3),
            ("Delete this game", delete_current_game, (3, 16)),
        ):
            tk.Button(
                body, text=text, command=cmd,
                bg="#3a1f1f", fg=RED, bd=0,
            ).pack(fill="x", padx=12, pady=pady, ipady=5)

    def _raise_modal(self):
        """Bring the already-open Settings/Games window to the front."""
        win = self.modal_win

        try:
            win.deiconify()
            win.lift()
            # Briefly topmost so it also clears an always-on-top main window.
            win.attributes("-topmost", True)
            win.after(200, lambda: win.attributes("-topmost", False))
            win.focus_force()
        except Exception:
            # The window is gone; allow opening a fresh one next click.
            self.modal_open = False
            self.modal_win = None

    def _close_modal(self, win):
        self.listening_for = None
        self.modal_open = False
        self.modal_win = None
        win.destroy()


# ================================================================
# MAIN
# ================================================================

if __name__ == "__main__":
    app = SplitTimerApp()
    app.mainloop()
