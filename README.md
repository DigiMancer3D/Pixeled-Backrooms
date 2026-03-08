# Pixeled Backrooms
**A retro-style pixelated exploration game inspired by the Backrooms lore.**
<br></br>
Pixeled Backrooms is an open-world procedural horror/exploration project built around two powerful companion tools, an asset manager, game engine test bed (for players & development), & a soon to be game engine:
- **PB (Pixeled Backrooms [Map Maker])**: A full-featured graphical editor for precise, hand-crafted maps and narrative arcs. (*Mostly Complete **Testing Phase has begun***)
- **JAM (Justified Auto Mapper [World Generator])**: A live procedural world generator that creates vast, interconnected map networks on the fly. (*Still In-Progress*)
- **TOST (Tkinter Original Amalgamated System Terminal [Game Engine])**: The future pixel based game engine, play the things you built or generate on the fly. (*concept only thus far **Early Development Phase has begun***)
- **ALT (Automated Loader Tester [Asset Manager])**: The asset manager for TOAST & bSIM (Toast Boss Simulator & Game Engine Development testing bed). Helps show your assets & files for the Pixeled Backrooms system without showing all your computer's systems. Makes finding mistakes and files easy within the system directory. (*Complete*)
- **BSIM (Boss Simulator [Player & Development Test-Bed])**: The official testing program for both players to learn how TOAST game engine works and reacts while also allowing development for the game engine and file integrations to be tested in a live environment. (*In-Progress*)
Together they allow creators to design detailed levels manually while rapidly prototyping and expanding entire worlds procedurally and test in a live environment.
<br></br><br></br>
---
## Features
### PB Map Maker (Manual Editing)
- Grid-based canvas (up to 1080×1080 cells) with zoom, pan, and multi-select
- Rich symbol system (walls, doors, enemies, objects, water, etc.)
- Per-cell properties: name, color, texture, height, depth, value, 3D, range, earmarks, title cards
- **New in latest update**:
  - Multiple view modes: Side (Z=Z), Isometric (Y=Z), Helicopter (XY=Z), Top-down (XYZ=Z)
  - Enhanced height-difference visualization using flood-fill for cleaner borders
  - Improved map blending with automatic pin-based alignment
  - Paint tool for background tints with named color storage
  - Performance optimizations (image caching)
- Arc Builder with scripting phrases, AI sequences, and map attachment
- Mini-map connectivity editor (7 opening slots, compatibility rules)
- Export: PNG, separated .txt, full dictionary ZIP, CSV
<br></br>
![PB Map Maker Screenshot](https://raw.githubusercontent.com/DigiMancer3D/Pixeled-Backrooms/refs/heads/main/pics/Screenshot_20260210_110255.png)
###### *PB Map Maker: Advanced grid editor with blending, view modes, and property system*
<br></br>
### JAM (Procedural Generation)
- Seed-based world generation
- Dynamic map expansion and connectivity
- Live canvas with panning/zooming
- Integration with PB maps and arcs
- Export generated worlds for use in the game engine
<br></br>
### ALT (Asset Manager)
- Dynamic directory scanning with treeview display of files and folders
- Advanced filtering: by rarity, name, type, category, direction, loot category, extension, and folder
- PNG-specific metadata extraction: name, type, rarity, direction, loot category, with descriptive tooltips
- Image previews, file descriptions, and related/similar asset lists
- Context menus for opening files in explorer or externally
- Toggle options for hidden files and .py/.txt visibility
- Integrated launchers for latest versions of TOAST, PB, and JAM scripts
- Duplicate detection, unknown file tagging, and auto-open for folder-only views
<br></br>
### BSIM (Boss Simulator Test-Bed)
- Procedural octagonal arena generation with obstacles, windows, safes, and interactive objects (e.g., nukes, keys, locked safes)
- Player character selection: witch, necromancer, elemental, or custom PNG with directional variants (_L/_R)
- Movement modes: third-person follow/inspect/pin, first-person view with mouse locking and pitch/yaw controls
- Inventory system: hotbar, backpack, equipment slots, loot rows (weapons/armor/usables/skills) with dragging and auto-placement
- Radial menus for player actions (follow, inspect, FPV, inventory, skill tree) and safe interactions (open, take, break, trap)
- Skill tree with body/combat/aura upgrades using earned points
- HUD elements: dynamic drawers for inventory/safe, groups for entity management, stamina/health bars
- Procedural spawning during movement: safes with inventories/traps, assist safes at milestones
- Cross-platform mouse warping/clipping for immersive controls
<br></br>
### Shared Features
- Persistent user data and themes
- Comprehensive in-app help system
- Robust undo/redo, copy/paste, and safety checks
- Integration across tools: shared sprite directories, map/dict/arc file compatibility, crumbs saves for state persistence
<br></br>
## Installation
1. **Clone the repository**
   ```bash
   git clone https://github.com/DigiMancer3D/Pixeled-Backrooms.git
   apt install python3
   apt install python3-tk
   cd Pixeled-Backrooms
   ```
2. **Install Dependencies**
   ```bash
   pip install numpy pillow networkx
   ```
###### &nbsp;&nbsp;(Tkinter is usually included with Python. On Linux you may need sudo apt install python3-tk)
<br></br>
### Run the tools
- PB Map Maker: python PB.py
- JAM World Mapper: python JAM.D.1b.py
- ALT Asset Manager: python TOAST-BOSS-SIM/ALT.py
- BSIM Boss Simulator: python TOAST-BOSS-SIM/bSIM_50.py
<br></br>
## Using PB
<br></br>
### Quick Start
- Using PB Map Maker
<br></br>
### Launch PB.py
- Create or load a map
- Use the symbol list to place objects
- Edit properties in the right drawer
- Build narrative arcs in the bottom panel
- Connect maps using the Mini-Map tool
- Export as PNG or dictionary for JAM/engine use
<br></br>
## Using JAM
<br></br>
### Launch JAM.D.1b.py
- Generate a new world or load existing maps
- Adjust parameters and expand the world
- Export the generated structure back to PB format
<br></br>
## Using ALT
<br></br>
### Quick Start
- Launch ALT.py from the TOAST-BOSS-SIM folder
- Browse the project directory tree on the left
- Apply filters (e.g., rarity, type) from the top bars for targeted searches
- Select items to view previews, descriptions, and related assets on the right
- Right-click for context options: open in explorer or externally
- Use bottom buttons to launch TOAST, PB, or JAM
- Toggle hidden files or .py/.txt visibility as needed
<br></br>
## Using BSIM
<br></br>
### Quick Start
- Launch bSIM_50.py from the TOAST-BOSS-SIM folder
- Select character type and damage affinity on title screen
- Explore procedural arena: move with WASD or mouse-follow
- Interact with safes/objects via clicks or radial menus (right-click)
- Manage inventory: drag items between hotbar, backpack, equip, and loot rows
- Access skill tree (Q in menu) to spend points on body/combat/aura
- Toggle FPV mode for immersive view (E in menu)
- Pause with ESC for reset/repick/exit
<br></br>
### Help & Documentation
#### Detailed guides are included in the /help folder:
- **map.help** Map editing basics
- **arc.help / arc.guide** Arc scripting and narrative
- **door.guide** Openings and connectivity
- **Mmap.guide** Mini-map and connections
- *Symbol, phrase, and data lists (full and quick-reference versions)*
###### Press the Help menu in PB for in-app access.
<br></br>
## Screenshots
<br></br>
### PB Map Maker
![PB screenshot](https://raw.githubusercontent.com/DigiMancer3D/Pixeled-Backrooms/refs/heads/main/pics/Screenshot_20260210_110205.png)
###### *Help System Built In*
<br></br>
![PB screenshot](https://raw.githubusercontent.com/DigiMancer3D/Pixeled-Backrooms/refs/heads/main/pics/Screenshot_20260210_110222.png)
###### *More then one help file to read from*
<br></br>
![PB screenshot](https://raw.githubusercontent.com/DigiMancer3D/Pixeled-Backrooms/refs/heads/main/pics/Screenshot_20260210_110255.png)
###### *Edit your map with full options at your mouse click*
<br></br>
## Credits
- Design & Development: 3Douglas [@DigiMancer3D aka @Z0M8I3D](https://x.com/z0m8i3d)
- VibeCodeD assistance from [@Grok and xAI](https://grok.com)
## License
### This project is open-source. See LICENSE for details (or contact the author for specific usage rights).
###### Made with passion for the Backrooms aesthetic and procedural creativity.
<br></br>
<br></br>
<br></br>
