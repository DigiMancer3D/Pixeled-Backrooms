**Bug AI Algorithms — Full Breakdown**

The bug AI runs **every frame** inside `game_loop()` (≈35 FPS) for every bug in the `self.bugs` list (and `free_attacking_bugs`). It uses velocity-based movement (`bug_vx`, `bug_vy`), a lead/follower system, timers, and layered behaviors. There is no separate AI class — everything is computed directly on the bug dicts and lists.

### 1. Core Structure: Lead Bugs vs Non-Lead Bugs
- **Lead bugs**: Special “anchor” bugs (one per pile). They decide where the pile moves.
- **Non-lead bugs**: Regular bugs that try to gather on their assigned lead.
- Number of leads ≈ number of piles (minimum 2, increases over time based on bug count and mimic_serial).

**Lead assignment** happens in `regenerate()`:
- Leads get a `lead_targets` entry — a unique random point near the aimdot (within ~30% screen range).
- When a lead reaches its target, it gets a new random target.

### 2. Lead Bug Movement (Every Frame)
```pseudocode
for each lead_bug:
    dx = lead_target_x - lead_bug.x
    dy = lead_target_y - lead_bug.y
    dist = hypot(dx, dy) or 1
    lead_bug.vx += (dx / dist) * 2.8   # strong steering
    lead_bug.vy += (dy / dist) * 2.8
    # Clamp to playable area
    lead_bug.x = clamp(40, 860)
    lead_bug.y = clamp(140, 820)
```

### 3. Non-Lead Gathering AI
- Every non-lead bug stores `lead_index` pointing to its lead bug.
- Steering force toward the lead bug’s current position.
- **0.3-second delay** after scattering before re-gathering (prevents instant re-clumping).

### 4. Scatter Mechanics
- When a non-lead bug is gathered on a lead: **13% chance per frame** to scatter.
- Scattered bugs run away in a random direction for **at least 9 seconds**.
- After the timer expires, the bug looks for any lead bug to re-gather on.

### 5. Flee When Lead Is Attacked
- When a lead bug is stomped/attacked: **22% chance** for each non-lead bug on that lead to flee to a **different** lead bug.
- Prevents the entire pile from being wiped out instantly.

### 6. Pile Throwing Mechanic (Aggressive Behavior)
- If a pile has **5 or more bugs**:
  - Every **90 seconds**, **33% chance** to trigger a throw.
  - A random bug from the pile is selected and thrown toward the aimdot.
  - Base accuracy: **39%**.
  - Accuracy increases with consecutive misses (stronger throws on miss streak).
  - Thrown bug gets high velocity: `(3.5 + 0.3 * bug_size)` in the direction of the aimdot.

### 7. Faux-Depth Avoidance (Height Boxes)
- For every bug inside a height_box:
  ```pseudocode
  push_x = (bug.x - box_center_x) * 0.8
  push_y = (bug.y - box_center_y) * 0.8
  bug.vx += push_x
  bug.vy += push_y
  ```
- Bugs actively steer around the elevated “boxes” while bosses ignore them.

### 8. Speed Ramp Over Time
- Every bug alive longer than **180 seconds**: +3 speed.
- **Last remaining bug**: +0.1 speed every 3 seconds for 9 seconds (makes the final bug-hunt feel frantic).

### 9. Search-and-Find Protocol (When Aimdot Is Hidden)
- If aimdot is over UI or editor for > **1.3 seconds**:
  - Each bug has **30% chance per frame** to steer toward the aimdot.
- Helps bugs “find” the player when menus are open.

### 10. Jitter & Separation (Natural Crawling Look)
- Bugs on the same pile apply a small **separation force** (push away if too close).
- Adds organic “crawling pile” animation even when gathered.

### 11. Emoji Directional Facing
- For any bug with an emoji overlay:
  ```pseudocode
  angle = atan2(vy, vx)
  offset_x = cos(angle) * 5
  offset_y = sin(angle) * 5
  canvas.coords(emoji_id, bug.x + offset_x, bug.y + offset_y)
  ```
- Uses the per-emoji `emoji_corner` (0–3) set by the directional dial in the Emoji Editor (↖ ↗ ↘ ↙). The corner that is considered “front” rotates with the dial.

### 12. Visual & Cleanup
- All movement is clamped to the playable area.
- `cleanup_lead_indices()` removes invalid lead references after bugs die.
- Emojis are moved and rotated with their bug.

**Summary of Feel**  
The bugs feel alive: they form natural piles, scatter when disturbed, throw bugs at you when grouped, avoid obstacles, speed up over time, and actively hunt you when you hide behind menus. The lead/follower system + scatter/flee creates dynamic, unpredictable swarms that become more dangerous as the game progresses.

<br></br>
