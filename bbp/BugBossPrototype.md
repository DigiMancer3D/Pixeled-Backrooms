# BugBossPrototype 
 <br></br> 
**Name:** Backrooms Bug & Boss Generator   <br></br>
**Version:** 33 <br></br>
**Language:** Python 3 + Tkinter + PIL (Pillow)   <br></br>
**Purpose:** Procedural liminal horror game testing. Generate swarms of polygonal “roach-like” bugs that pile & cluster into mimic bosses (hydra, giant skull, dragon-like shapes). Player uses aimdot to stomp bugs and bosses in a Backrooms-style octagonal arena. Live canvas editor for bugs/emojis. Full persistence, AI, faux depth, particle effects, explosion domes, smashed counter, and Souls-like combat feel. <br></br>
**NOTE:** This is to prototype to build up the bug & boss mechanics for bSIM and TOAST Engine, work on the A.I.s within and attempt to determine the effective method while staying within python3-tk (no pygame), few dependecies; locally hosted game ideology. <br></br>

 <br></br> 
## 1. Startup & Initialization Flow

1. `__init__` is called when `BugBossPrototype()` is instantiated.
2. Tk root window created (900×950, resizable).
3. Canvas created and packed.
4. `draw_backrooms()` draws beige walls, yellow lines, and 6 faux-depth height boxes.
5. All class variables initialized (see table below).
6. `load_aimdot()` loads `aimdot.png` (if present) for custom cursor.
7. `load_crumbs()` attempts 3 times to read `bbp.crumbs` (::key:value).
8. Event bindings: Motion, Button-1/3, Double-Button-1, Release-1, Escape, Configure.
9. `regenerate()` creates initial bugs/bosses and draws top UI + smashed counter.
10. `game_loop()` starts (root.after(28) ≈ 35 FPS).
11. `run()` calls `root.mainloop()`.

**Closing Procedure:**  
- Escape → toggle_pause → draw_pause_menu_on_canvas.  
- Quit button → `save_crumbs()` → `root.destroy()`.  
- Window close → implicit Tk cleanup (no explicit save on close).

 <br></br> 
## 2. All Variables 

| Variable                        | Type          | What It Tracks / Does                                                                 |
|--------------------------------|---------------|---------------------------------------------------------------------------------------|
| `bug_sides`                    | int           | Polygon sides for bugs (0=circle, 2=square, 3–24=roach)                              |
| `bug_r/g/b/a`                  | int (0-255)   | RGBA components of bug color                                                          |
| `bug_color`                    | str (#hex)    | Live hex color used for bugs & emojis                                                 |
| `bug_size`                     | int           | Base pixel size of bugs                                                               |
| `emoji_size`                   | int           | Base pixel size of emoji overlays                                                     |
| `emoji_to_bug_ratio`           | float         | Maintained ratio so emojis scale with bug size changes                                |
| `selected_emojis`              | list[str]     | Currently enabled emojis (weighted random assignment)                                 |
| `boss_overlay_path`            | str           | Path to uploaded PNG sprite for bosses                                                |
| `boss_overlay`                 | PIL Image     | Loaded RGBA image for boss overlay                                                    |
| `seen_bosses`                  | list[dict]    | History of every boss that has spawned (for E&B Index)                                |
| `bugs`                         | list[dict]    | All active ground bugs (id, x, y, size, emoji_id, lead_index, etc.)                   |
| `bug_vx / bug_vy`              | list[float]   | Velocity for each bug in bugs list                                                    |
| `free_attacking_bugs`          | list[dict]    | Summoned bugs that chase the aimdot                                                   |
| `current_bosses`               | list[dict]    | Active bosses (pinned bugs, health, ring_id, overlay_id, etc.)                        |
| `particles`                    | list[list]    | Active particle effects (id, life, vx, vy)                                            |
| `mimic_serial`                 | int           | Global difficulty counter (increases after each boss kill)                            |
| `height_boxes`                 | list[tuple]   | Faux-depth collision boxes (x,y,w,h,height) – bugs avoid, bosses climb               |
| `lead_indices`                 | list[int]     | Indices of “lead” bugs that other bugs gather around                                  |
| `lead_targets`                 | list[tuple]   | Target (x,y) each lead bug is moving toward                                           |
| `throw_timers`                 | dict          | Per-lead bug timer for throwing mechanic                                              |
| `bug_count_var / poly_var / mimic_serial_var` | int | Live UI counters                                                                      |
| `current_threshold`            | int           | Calculated boss spawn threshold = sides*3.14 + mimic_serial*(sides+1)                |
| `emoji_dial_values`            | dict          | Per-emoji corner index (0-3) for directional facing                                   |
| `is_paused`                    | bool          | Global pause flag                                                                     |
| `editor_open / emoji_editor_mode` | bool       | Canvas editor state flags                                                             |
| `smashed_count`                | int           | Total bugs squashed (shown in bottom UI)                                              |

 <br></br> 
## 3. Core Loops & States

- **game_loop()** (root.after(28)):  
  - If paused → early return.  
  - Mouse position & faux-depth aimdot shadow/scale.  
  - Search-and-find protocol (if aimdot over UI >1.3s).  
  - Pile throwing (5+ bugs, 33% chance every 90s).  
  - Faux-depth avoidance for bugs.  
  - Emoji directional facing (atan2 offset).  
  - Bug & boss movement + jitter/push separation.  
  - Particle decay.  
  - tag_raise("aim") for z-order.

- **regenerate()**: Full redraw of bugs/bosses + UI after any change.

- **States:** Tutorial → normal bug piles → mimic boss → terrain reset on death.

 <br></br> 
## 4. Bug AI Table

| Behavior                        | Trigger / Condition                  | Action / Math                                                                 |
|--------------------------------|--------------------------------------|-------------------------------------------------------------------------------|
| Lead bugs                      | One per pile                         | Move to unique target near aimdot (30% range)                                 |
| Non-lead gathering             | After 0.3s scatter or spawn         | Steer toward current lead bug                                                 |
| Scatter                        | 13% chance when gathered on lead     | Run away for 9 seconds, then re-gather                                        |
| Non-lead flee when attacked    | 22% chance when lead is stomped      | Switch to different lead bug                                                  |
| Pile throwing                  | Pile ≥5 bugs, every 90s              | 33% chance, 39% accuracy, stronger on misses                                 |
| Faux-depth avoidance           | Inside height_box                    | Push vector away from box center                                              |
| Speed ramp                     | Alive >180s                          | +3 speed per 180s (last bug +0.1 per 3s for 9s)                              |

 <br></br> 
## 5. Boss AI Table

| Behavior                        | Condition                            | Action / Math                                                                 |
|--------------------------------|--------------------------------------|-------------------------------------------------------------------------------|
| Base movement                  | Always                               | Steer to aimdot with base_speed = 1.6*1.22                                   |
| Flanking / orbit               | Random 1.5%                          | Add offset angle + sudden lunge                                               |
| Speed boost                    | Mimic serial ≥50                     | +22% speed, curves sharply after 100                                          |
| Low-health boost               | Health ≤15%                          | +40% speed                                                                    |
| Kick smaller bugs              | Every 140s                           | 15% chance to kick bugs within 140px                                          |
| Summoner mode                  | sides >25                            | Spawn extra bugs every 3.5-6.5s                                               |
| Self-heal on summon            | Random 2% per hit                    | +1% health + new bug at hit location                                          |
| Self-kill minion for heal      | Health ≤25%                          | 15% chance to kill own minion for 15% health return                          |

 <br></br> 
## 6. Mimic AI Table

Mimic bosses use the same base AI as normal bosses but with these extras:
- Pinned bugs jitter + push separation on backer polygon while boss moves.
- Backer polygon fades red → black as health drops.
- Extra ground bugs spawn with every mimic boss (non-summoner).
- Threshold locked until boss is killed (no mid-wave change).

 <br></br> 
## 7. Menus & Editors Breakdown

**Pause Menu (Escape):**  
Canvas overlay with RESUME, RESTART (keep serial), REBOOT (full reset), QUIT, E&B INDEX buttons. Game fully paused.

**Live Bug Editor (Right-click):**  
Full canvas panel matching your screenshot:
- Sides ↑↓ (0–24, live update)
- R/G/B/A ↑↓ (10-step, live color box + bug recolor)
- Bug Size ↑↓ (live ratio recalc for emojis)
- Emoji Size ↑↓ (live ratio recalc)
- “Edit Emoji Overlay” button → switches panel
- CLOSE EDITOR (saves crumbs + regenerate)

**Emoji Overlay Editor:**  
4-column grid of toggle buttons (click to enable/disable).  
Each has a directional dial (↖ ↗ ↘ ↙) – click dial to cycle corner that faces movement direction.  
BACK TO BUG EDITOR returns to main panel.

 <br></br> 
## 8. Emojis List (Importance Order = Weighted %)

| Emoji | Name          | Show % | Importance (higher = more likely when multiple enabled) |
|-------|---------------|--------|---------------------------------------------------------|
| 🪳    | Roach         | 77%    | 1 (most common)                                         |
| 🕷️    | Spider        | 55%    | 2                                                       |
| 🪰    | Fly           | 31%    | 3                                                       |
| ⚫️    | Black Dot     | 13%    | 4                                                       |
| 🪲    | Beetle        | 9%     | 5                                                       |
| 🩸    | Blood         | 6%     | 6                                                       |
| 🐜    | Ant           | 3%     | 7                                                       |
| ☢️    | Radioactive   | 1%     | 8                                                       |
| 💀    | Skull         | 1%     | 9                                                       |
| 💣    | Bomb          | 0.5%   | 10 (rarest)                                             |

Weighted random selection when multiple toggles are on. Bomb explodes on smash (ring flash + 💥 + 15% chance to chain-kill nearby bugs).

 <br></br> 
## 9. bbp.crumbs Persistence

- **Format:** Plain text, one line per variable: `Human Readable::variable_name:value`
- **Load:** On startup, tries 3 times (0.1s delay) to read file. Falls back to defaults on failure.
- **Save:** Called on editor close, quit, and reboot. Overwrites entire file.
- **Auto-save:** Only on explicit editor close or quit. No live auto-save during gameplay.
- **Stored values:** sides, RGBA, sizes, ratio, selected_emojis list, boss PNG path, bug_color.

 <br></br> 
## 10. Known Issues

| Category                  | Issue                                                                 | Additional Notes     |
|---------------------------|-----------------------------------------------------------------------|------------|
| Emoji Editor              | Directional dials are clickable but do not yet rotate the emoji live | Buttons unresponsive, completely not-working but visuals exist only but collide with some data |
| Aimdot over UI            | Sometimes clicks mess up or aimdot freezes when over UI | Seems like something else is colliding with aimdot when clicking single clicks continually but not fast enough to be double clicks where one click is disregarded or used as a double click instead of a single click |

**Functions / Features Not Present:**  
- Full height collision for bosses climbing walls/boxes (current: bosses ignore height_boxes).
- Advanced per-emoji corner dial in emoji editor is present but dial click only cycles value (no live visual rotation yet).
- Terrain reset on 0.1% normal bug squash is not present.
- Summoner self-kill minion heal is not present.
- Mimic Bosses do not seem to be implemented nor do they seem to have a chance of showing.

**Not Properly Working:**  
- Emoji directional facing uses atan2 offset but does not yet use the per-emoji corner index for different “front” corners (default top-left only).
- Double-click smash on single-bug cluster had a safeguard but can still edge-case on size 1.
- `load_crumbs()` attempts 3 times to read `bbp.crumbs` (::key:value format) but does not perfrom this in a series where the data (plain text::key:value) is attempted to load in the following manner: (check 1) key === varaiable, value === varaiable_value; (check 2) plain text (spaces removed) === variable, value === variable_value; (check 3) plain text (spaces removed) === variable, key === variable_value.
- bbp.crumbs file saves too often. The bbp.crumbs file should only save after the user has had the bug or emoji editor menu(s) up upon closing either menu. Closing emoji editor should save only changed emoji data, closing bug editor should save only changed bug data.

 <br></br> 
###### This is a prototype program to determine TOAST-BOSS-SIM (bosssim aka bSIM) eventual boss and bug AI mechanics.

<br></br><br></br>
