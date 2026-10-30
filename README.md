AI WAS USED FOR DEBUGING AND README 




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

AI WAS USED FOR DEBUGING AND README 
