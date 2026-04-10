**Boss AI Algorithms**

The boss AI is implemented entirely inside **`game_loop()`** (the 35 FPS main loop) and uses a combination of **steering behaviors**, **state modifiers**, **pinned-bug jitter**, and **special abilities**. There is **no separate AI class** — everything runs on the `current_bosses` list of dicts.

### 1. Core Movement Algorithm (Every Frame)

```pseudocode
for each boss in current_bosses:
    # 1. Basic steering toward aimdot
    dx = aim_x - boss.x
    dy = aim_y - boss.y
    dist = hypot(dx, dy) or 1
    angle = atan2(dy, dx)

    # 2. Base speed with multiple multipliers
    speed = 1.6 * 1.22
    if mimic_serial >= 50:      speed *= 1.22
    if mimic_serial >= 100:     speed *= (1.0 + (mimic_serial-100)*0.022)   # curved ramp
    if health <= 15% of max:    speed *= 1.4

    # 3. Apply movement with small random jitter
    boss.x += cos(angle + 1.7) * speed + random(-0.8, 0.8)
    boss.y += sin(angle + 1.7) * speed + random(-0.8, 0.8)

    # 4. Occasional flanking/lunge (1.5% chance per frame)
    if random() < 0.015:
        boss.x += (dx / dist) * 18
        boss.y += (dy / dist) * 18

    # 5. Clamp to playable area
    boss.x = clamp(80, 820)
    boss.y = clamp(100, 750)
```

**Visual result:** Bosses feel alive — they orbit, evade/defend, and flank the aimdot while slowly accelerating as difficulty rises.

### 2. Pinned-Bug Jitter & Separation (on the boss backer polygon)

While the boss moves:
- Every pinned bug gets **independent jitter** (`random(-2.2, 2.2)` on both axes).
- **Separation push** is applied between every pair of pinned bugs (if distance < 28 pixels, they push away from each other).
- The entire pinned group is moved by the same delta as the boss body so they stay attached.

This creates the “crawling on the boss” effect you asked for.

### 3. Special Abilities by Boss Type

| Boss Type          | Condition                  | Ability / Algorithm                                                                 |
|--------------------|----------------------------|-------------------------------------------------------------------------------------|
| **Tutorial Boss**  | First boss only            | Fixed 13 health, 4 pinned bugs, simple sphere shape, no special attacks            |
| **Normal Mimic**   | Standard boss              | Same core movement + pinned jitter + kick (see below)                              |
| **Summoner**       | `sides > 25`               | Spawn 1–3 free-attacking bugs every 3.5–6.5 seconds                               |
| **Greater Mimic**  | High sides / serial        | All above + stronger speed ramp + more pinned bugs                                 |

### 4. Kick Ability (All Bosses)

```pseudocode
if time > boss.kick_timer:
    boss.kick_timer = now + 140
    if random() < 0.15:
        for every bug within 140px of boss:
            kick_vector = normalize(bug - boss) * 35
            bug.x += kick_vector.x
            bug.y += kick_vector.y
            create_particles(bug, yellow, 12)
```

### 5. Summoner-Only Heal / Self-Kill Mechanics

- **Per-hit chance (2%)**: When player hits the summoner, 2% chance to spawn an extra bug at the hit location **and** give the boss +1% health.
- **Low-health desperation (health ≤ 25%)**: 15% chance per frame to kill one of its own summoned minions and gain 15% health back.

### 6. Health & Visual Feedback

- Health ring arc shrinks in real time (`extent = 360 * (health / max_health)`).
- Backing polygon color fades from bright red → dark red as health drops.
- Boss becomes un-clickable the instant health reaches 0.
- Explosion dome starts immediately on death and fades the boss sprite within 0.3s.

### 7. Spawn & Placement Rules

- Bosses always spawn in one of four rotating quadrants (top-left, top-right, bottom-left, bottom-right) with small random offset.
- After tutorial boss is killed, poly count starts at 3 and increases by +1 after **every** boss kill.
- Threshold is locked until the current boss is defeated (no mid-wave change).

### 8. Difficulty Scaling Summary

- Speed increases with mimic_serial (22% at 50, then accelerating curve after 100).
- More pinned bugs and larger radius as bug_count and sides grow.
- Low-health survival AI (extra speed + lunge frequency) kicks in at 40% and again at 15%.

<br></br>
