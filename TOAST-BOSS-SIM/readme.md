
# 🍞 TOAST - Backroom Game Engine

> Part of the **Pixeled-Backrooms** project ecosystem

TOAST is a **souls-like boss combat simulator** and game engine built with Python and Tkinter. It's designed as the third component of a three-tier architecture alongside **PB** (map maker) and **JAM** (world generator), enabling a fully generatable pixelated backroom crawler experience.

## 📋 Project Overview

This repository contains the **Pixeled-Backrooms** project, which consists of three interconnected tools:

- **PB** (Pixeled-Backrooms Map Maker) - Create custom arena layouts and environments
- **JAM** (Procedural World Generator) - Generate procedural world data and creature encounters
- **TOAST** (This Game Engine) - Real-time souls-like combat and exploration engine

## 🎮 Features

### Core Gameplay
- **Souls-like Combat System**: Multi-action control scheme (attack, dodge, defense, charged abilities)
- **Dynamic Boss Encounters**: Procedurally generated and predefined boss creatures
- **Progression System**: Level-up mechanics with element customization
- **Inventory & Loot**: Pickup collection, equipment management, stat upgrades

### Rendering & Visuals
- **Multiple View Modes**:
  - First-person 3D perspective
  - Third-person 3D view
  - Helicopter overview
  - 2D top-down view
  - 2D side view
  - Faux-3D isometric projections
- **Dynamic Lighting**: Surface shading based on light direction
- **Particle Effects**: Combat feedback, damage indicators, loot spawning
- **Trail Effects**: Boss attack visualization

### Physics & Collision
- **GJK Collision Detection**: Accurate sphere-to-polygon collision testing
- **Physics Simulation**: 
  - Gravity and jump mechanics
  - Movement acceleration and friction
  - Arena boundary constraints
  - Boss-player interaction

### AI & Bosses
- **Procedural Boss Generation**: Randomized geometry and stats based on level
- **Multiple Behaviors**: 
  - Stealth mechanics
  - Melee, ranged, and summoner attack types
  - Frenzy states with lunge attacks
  - Run-away tactics
- **Boss Splitting** aka ***Hydra Effect***: Mid-combat boss splitting mechanics
- **Element System**: Cold, hot, poison, dry, humid, and physical effects

### Customization
- **Settings Menu**: FOV, mouse sensitivity, camera smoothing, inversion options
- **Color Customization**: Choose player color in real-time
- **Screen Modes**: Normal, double resolution, fullscreen support
- **Weapon System**: Multiple weapon types with varied attack ranges

## 🎮 Controls

### Movement
- **WASD** - Move (directional based on camera)
- **Space** - Jump
- **Escape** - Pause/Resume

### Combat
- **Left Click** - Single: Attack | Double: Strong Attack | Hold: Charge Attack
- **Right Click** - Single: Dodge | Double: Jump | Hold: Defense Stance
- **E** - Interact with objects

### Pause Menu
- Adjust FOV and mouse sensitivity
- Toggle camera inversion
- Change player color
- Switch view modes and weapons
- Save/load progress
- Reset game state

## 📊 Game Mechanics

### Progression
- **Experience System**: Defeat bosses to gain experience
- **Leveling**: Unlock stat upgrades and progression choices
- **Stat Gains**: Increase health, stamina, or element affinities
- **Equipment**: Armor, weapons, and gear collection

### Combat Stats
- **Health/Stamina/Magic**: Resource management for different actions
- **Attack Level**: Scales damage output
- **Defense Level**: Reduces incoming damage
- **Skill Level**: Affects overall capability
- **Armor**: Passive damage reduction
- **Life Steal**: Heal from dealt damage

### Element System
- Each boss has an element affinity
- Players can customize element resistance
- Elemental damage creates status effects:
  - Cold: Speed reduction
  - Hot: Continuous damage
  - Poison: Damage over time
  - Dry: Damage reduction
  - Humid: Speed slow

### Arena System
- **Octagonal arenas** with dynamic scaling
- **Interactive objects**: Desks, walls, rocks, furniture
- **Theme-based generation**: Office, volcano, cornfield, skyscraper, furniture themes
- **Progressive difficulty**: Increased complexity at higher levels

## 🔧 Technical Details

### Architecture
- **Language**: Python 3.x
- **GUI Framework**: Tkinter
- **Collision Detection**: GJK (Gilbert-Johnson-Keerthi) algorithm
- **Rendering**: Canvas-based 2D/3D projection

### Key Systems

#### Collision Detection
```python
gjk_intersect(shape1, shape2)  # Returns boolean collision status
```

#### Projection System
- Perspective projection for 3D views
- Isometric projection for faux-3D
- Multiple camera positions and angles

#### Save System
- JSON-based game state persistence (`game.crumbs`)
- Automatic save on exit
- Load game progress on startup

## 📈 Integration Points

### With PB (Map Maker)
- TOAST can load custom arena layouts created in PB
- Supports dynamic object placement and theming

### With JAM (World Generator)
- Receives procedurally generated boss configurations
- Creature pool populated from JAM output
- Dynamic arena theming based on world generation

## 🚀 Getting Started

### Requirements
- Python 3.7+
- Tkinter (usually included with Python)

### Running
```bash
python soulslikebosssim_17.py
```

### First Time
- Tutorial overlay will appear on first run
- Can be toggled in pause menu
- Press Start to begin

## 📁 Project Structure

```
TOAST-BOSS-SIM/
└── soulslikebosssim_17.py    # Main game engine (this file)
```

## 🎨 Creature Types

TOAST includes predefined creatures that spawn at milestones:
- **Smiler** - Stealth-focused creature with distinctive features
- **Hound** - Aggressive melee attacker
- Plus procedurally generated variants

## 🔮 Future Development

- [ ] Networking/multiplayer support
- [ ] Advanced shader system
- [ ] Enhanced particle effects
- [ ] More creature types and behaviors
- [ ] Expanded weapon/ability system
- [ ] Audio integration
- [ ] Mobile port

## 🛠️ Development Notes

### Game Loop
- Fixed 60 FPS (16ms per frame)
- Delta-time based physics
- Smooth camera interpolation

### Performance
- Recursion limit set to 2000
- Particle pooling with max cap
- Efficient collision checks with spatial awareness

## 📝 Save Data

Game progress is saved to `game.crumbs` in JSON format, including:
- Player stats and level
- Element affinities
- Weapon and equipment state
- Camera settings
- View preferences
- Tutorial completion status

## 🎯 Vibecoded (VBCD)

This project was VBCD (vibecoded) because the creator uses JS not Python. I (3Douglas) wanted a game that was faster to tell Grok what I wanted since I do not know pyhon but I have been using multiple VBCD pyhon projects to learn more about python and have been editing VBCD work to learn how python work. That and w3schools.com have been helping me learn through vibecoding. 

## 📖 Related Documentation

For more context on the broader Pixeled-Backrooms project:
- See PB documentation for map creation
- See JAM documentation for world generation
- This README focuses on TOAST's gameplay and engine details

## 🙏 Credits

Created by DigiMancer3D as part of the Pixeled-Backrooms project.

Coded by Grok.

---

**Status**: Early Development 

*TOAST: The game engine that's crisp & fresh from the toaster! 🍞*
