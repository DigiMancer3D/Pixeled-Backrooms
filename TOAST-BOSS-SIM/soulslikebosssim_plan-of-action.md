# Plan of action

### Visual Enhancements and 3D Extrapolation
- **3D Boss Models**: Use filled/shaded polys (canvas polygon with fill for simple shading—gradient based on light dir). Extrude 2D verts to 3D (add height, create sides/top/bottom for cube-like polys). For sphere, use more verts/tessellation.
  - Splitting: Animate explosion (particles from boss pos, fade old model, spawn twins with scale-up anim).
- **Animations**:
  - Player/Boss: In 3D views, scale/rotate polys for jump (bounce), dodge (stretch), attack (pulse red), defend (glow cyan).
  - In 2D: Keep color/size changes; add particle bursts.
- **Pickups**: Glimmer with light blooms (yellow particles rising/fading). Eye looks at nearest pickup > boss (calc dist, adjust eye pos).
- **World Objects**: Procedural generation per boss kill (clear/rebuild arena). Backrooms-inspired: random walls (yellow carpet texture sim via colors), rocks/hills (poly mounds), skyscrapers (tall rects), furniture (small rects). Affect physics (add collision shapes, jumping on them updates pos/y).
  - In 2D: Flat shapes with outlines.
  - In 3D: Extruded polys.
- **Test**: Switch views; ensure 1st/3rd/helicopter show 3D bosses/objects; no lag (limit objects to 20-30).

### World Building and Procedural Arenas
- **Procedural Arenas**: On boss kill/level up, regenerate: random layout of objects (e.g., 5-10 walls/rocks, themed per lore—volcano: red rocks, office: desks). Use simple proc gen (grid placement with randomness).
  - Physics: Add GJK collision for objects (treat as polys/spheres).
- **Backrooms Lore Integration**: Themes cycle (office, volcano, corn field, etc.)—change colors/particles (e.g., yellow carpet = yellow floor rects).
- **Test**: Ensure collisions work in all views; no clipping; arenas feel varied.

### Additional Features (Elementals, Boss Variety, Sounds)
- **Boss Variety**: Dynamic per level—add attacks: melee (charge), range (projectiles), run (flee/heal). Styles: aggressive (close fast), defensive (shield), summoner (spawn minis). Randomize per boss.
  - New: Backrooms Creatures Integration—For bosses with sides % 3 == 0, mimic lore entities (e.g., Smiler: dark poly with glowing eyes/smile; Hound: quadruped shape). Use summoner style: stay back, spawn 2-5 minor creatures (smaller polys mimicking entities like Smilers/Hounds; basic AI: pursue/attack player, lower health/damage). Minors despawn on boss death or after time.
- **Elemental Skills**: Implement effects (cold slow/freeze, heat burn/sun burn, etc., as detailed). Apply on hits; track stacks per boss.
- **Raw Damage/Charge Scaling**: Raw +1% per 10 levels (physical bonus), charge max +1% per 10 levels (defense charge bonus).
- **Sounds**: Use simple lib (e.g., playsound—auto-install via subprocess if missing). Add for attack (beep high), dodge (whoosh low), jump (boing), collect (ding).
  - Cross-platform: Check os, use winsound on Windows, aplay on Linux.
- **Test**: Balance elementals; variety makes bosses unique; sounds trigger correctly.

### Polish, Optimization, and Final Touches
- **Robustness**: Add save/load (JSON file on exit/reset; use *.crumbs json file extension). View transitions smooth (fade).
- **Performance**: Cap entities (e.g., max 100 particles). Profile views for lag; optimize proj_func (vector math).
- **Additions**: Add boss health bars in 3D (3D ring proj). Tutorial popup on start (controls). Difficulty curve: bosses faster/stronger per level.
- **Full Testing**: All views/controls stable; no crashes; fun loop with variety.

---

# PreDetermined Bosses & Stuff

### Backrooms Creatures as Polygons for Game Representation
Based on Backrooms lore from various wikis and communities, I'll detail key creatures, their descriptions, behaviors, and how to represent them as polygons in your boss simulator. Polygons are ideal for the game's style (simple verts/edges/fills). For bosses with sides % 3 == 0, they can mimic these (e.g., adjust color/verts to resemble), and summon minors as attacks (small polys with basic AI: pursue/player collision damage). Minors: 50% boss health/damage, 2-5 spawned, despawn after 30s or boss death.

1. Smiler (Entity 3)

Description: Pitch-black entities with glowing white smiles/eyes, aggressive in darkness. Hunt by sound/light, slash/bite.
Behavior in Game: Stealthy; invisible in low-light (alpha=0), appear when close. Attack: lunge (trail anim).
Polygon Representation: Base: irregular decagon (10 verts) for shadowy blob. Glowing features: 2 triangles (eyes), curved pentagon (smile, approx arc). Color: black fill, white outline for glow. Minor summon: scale 0.5, spawn in dark areas.

2. Hound (Entity 5)

Description: Hairless, quadrupedal humanoids with sharp teeth/claws. Feral, charge/infect victims (turn into hounds).
Behavior in Game: Fast pursuit; bite melee. If hit player 3x, temp "infect" (slow player 10s).
Polygon Representation: Body: elongated octagon (8 verts). Legs: 4 triangles attached. Head: pentagon with spikes (triangles for teeth). Color: gray fill, red eyes (dots). Minor: scale 0.7, pack of 3.

3. Partygoer (Entity 67)

Description: Yellow, balloon-like humanoids with smiley faces. Lure with "fun," convert via cake. Group threats.
Behavior in Game: Taunt (text popup "= )"), ranged "cake" proj (poison dot). Summon minors as "party."
Polygon Representation: Round dodecagon (12 verts) for balloon. Face: circle approx (octagon), triangles for eyes/mouth. Color: yellow fill, black features. Minor: scale 0.6, bouncy anim (oscillate pos).

4. Skin-Stealer (Entity 10)

Description: Mimic humans by wearing skin. Ambush, pose as wanderers.
Behavior in Game: Disguise as player poly (copy verts/color), reveal on attack. Melee slash.
Polygon Representation: Humanoid hex (6 verts body), attached limbs (rects). "Skin": outer irregular poly layer (peeling anim: fade parts). Color: flesh pink, reveal dark under. Minor: scale 0.8.

5. Deathmoth (Entity 4)

Description: Giant moths; males aggressive with acid spit, females passive/large.
Behavior in Game: Fly (sin wave pos[1]), ranged spit (proj slow/poison).
Polygon Representation: Wings: 2 large triangles. Body: cylinder approx (hex prism). Antennae: lines. Color: brown fill, glow eyes. Minor: scale 0.5, swarm.

6. Clumps (Entity 50)
Clumps are grotesque, fleshy masses of fused human limbs and torsos, often resembling tangled clusters of arms and legs. They're slow-moving but highly durable, found in moist or decaying levels like Level 5 down to level -50. They attack by grabbing and pulling victims into their mass, "assimilating" them. Survival: Use fire or explosives to break them apart; avoid close range.
In the boss sim: Polygon as irregular 12-vert blob with protruding triangles (limbs). For summoning: Scale 0.6, slow pursuit AI, "grab" on collision (temp slow player).

7. Dullers (Entity 66)
Dullers are shadowy, humanoid figures with elongated limbs and no facial features, emitting a "dulling" aura that drains wanderers' energy and motivation. Common in monotonous levels like Level 66, they stalk silently and induce apathy, making escape harder. Attacks: Psychic drain (slow/weaken over time).
In the boss sim: Polygon as tall hex prism (body) with stretched rect limbs. Black fill, no eyes. Summon: Scale 0.7, aura effect (reduce player speed if near).


8. Jerry "JE" (Entity 17)
Jerry aka "JE" is a unique, parrot-like entity that's semi-sentient and often friendly/neutral, mimicking speech and behaviors. Found in levels with colonies, it can be tamed with food but turns hostile if provoked. Attacks: Peck/swarm if angered. Look Mogs if not angered.
In the boss sim: Polygon as bird-shaped (triangle body, lines for wings/beak). Blue fill, yellow eyes. Summon: Scale 0.5, fly AI (sin wave height), mimic player attacks.

9. Facelings (Entity 9)
Facelings are humanoid entities with distorted, mask-like faces, ranging from child-like to adult forms. They mimic humans but are predatory, often ambushing in groups. In levels like Level 9, adults are hostile while juveniles can be neutral.
In the boss sim: Polygon as humanoid octagon (body) with circle head, irregular verts for distorted face. Flesh tones. Summon: Scale 0.8, group rush AI.


10. Wretches (Entity 28)
Wretches are mutated former humans, twisted by almond water overuse or infection, with elongated limbs and erratic behavior. Found in unstable levels, they charge wildly and self-harm. Attacks: Frenzied melee, potential "infection" spread.
In the boss sim: Polygon as stretched humanoid (long rect limbs, warped hex body). Red/purple fill. Summon: Scale 0.6, erratic movement (random dir changes).


---


### Office Stuff as Interactive Elements (Chests, Boats, etc.)

In Backrooms lore, mundane office items often gain surreal, functional twists due to the liminal space's anomalies. Here's how they could be repurposed creatively as "chests" (storage/loot), vehicles, or tools—fitting for the boss simulator game, where arenas include office-themed procedural elements.

- Filing Cabinets as Boats/Rafts: In flooded levels (e.g., waterlogged offices), tip a cabinet sideways to float on almond water pools. Use as a "boat" to cross hazards—polygon: tall rect (cabinet), rotate 90 deg for raft mode. In game: Player interacts to "ride" (temp speed boost over water, avoid drowning entities).

- Desks as Chests/Barricades: Desks act as storage "chests" holding supplies (e.g., almond water, weapons). Flip for cover against entities. Polygon: simple rect with drawers (small inner rects). In game: Open for loot (random item), push for physics barrier (block projectiles/minors).

- Chairs as Weapons/Seats: Stack chairs for improvised clubs or throwable objects. In safe zones, sit to "rest" (regen health/stamina). Polygon: cross rects (legs/seat). In game: Pick up/throw (projectile damage), or use for climb (stack to reach ledges).

- Cubical Walls as Mazes/Shields: Partition walls create mini-mazes for hiding/ambushing. Dismantle for portable shields. Polygon: thin rect panels. In game: Procedural placement for cover; breakable (health bar, destroy for paths).

- Computers/Printers as Traps/Portals: Hack computers for "noclip" portals to escape attacks. Printers spit "ink blobs" as hazards or ammo. Polygon: box with screen (rect + glow dot). In game: Interact for teleport (random safe spot), or trap trigger (spawn minor entity).

These add interactivity—e.g., in boss fights, use a filing cabinet "boat" to dodge water-based summons, or desk as loot chest post-kill. For polygons, keep simple (4-8 verts) to avoid lag.


