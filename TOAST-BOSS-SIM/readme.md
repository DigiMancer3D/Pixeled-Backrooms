# 🍞 TOAST Boss Sim - Boss Simulator Engine
> Part of the **Pixeled-Backrooms** project ecosystem

TOAST 🍞 is a **souls-like looped game-rounds real-time iso crawler boss simulator** game engine built with Python and Tkinter. TOST is made up of two key programs: 
  - #### **Toast ALT** [Functional] (Automated Loader Tester, `ALT.py`) for asset management and browsing
  - #### **Boss Sim** [Work-in-progress] (`bSIM_50.py`) for real-time combat simulation. 

These tools will be used along with **PB** 🥜 (map maker), **JAM** 🫙 (world generator), and **GRILLS** 🔥 (animation sequencer) to create procedurally generated pixelated backroom experiences in due time.

## 📋 Project Overview
This sub-repository under **Pixeled-Backrooms** contains:
- **Toast ALT (`ALT.py`)**: A finished GUI tool for browsing, filtering, and managing project assets like sprites, maps, and scripts. It serves as a development aid for loading, testing, and organizing resources, with previews and metadata extraction.
- **Boss Sim (`bSIM_50.py`)**: A work-in-progress simulator for boss fights in a backrooms-style arena. Features include player movement, inventory management, first-person view (FPV), skill trees, procedural generation, and interactive elements like safes and objects.
- Integration with the broader ecosystem:
  - Loads maps and data from PB (e.g., `.tmap`, `.mapd`) and JAM (e.g., `.arcs`).
  - Supports custom sprites from `Sprites/Characters` and procedural enemy/mini-boss generation.
  - Supports GIF animations from GRILLS for dynamic elements like character movements, effects, and boss behaviors.
  - Shared asset directories for seamless resource sharing.

## 🔧 Technical Details
- **Language**: Python 3.x
- **GUI Framework**: Tkinter (with Canvas for rendering in bSIM, Treeview for asset browsing in ALT)
- **Key Features**:
  - **Asset Management (ALT.py)**: Directory tree with filters (rarity, name, type, category, direction, loot category, extension, folder). PNG metadata parsing for game-specific fields. Image previews, related asset lists, context menus for opening files externally.
  - **Game Simulation (bSIM_50.py)**: Procedural octagonal arena with obstacles, windows, safes, and interactives. Player controls with collision detection, camera smoothing, FPV mode with mouse locking. HUD with dynamic inventory drawers, hotbar, dragging mechanics, and group management.
  - **Cross-Platform Support**: Mouse cursor warping and clipping for immersive controls (Windows/Linux).
  - **Procedural Elements**: Random generation of arenas, safes (with traps/inventory), and interactives (e.g., nukes, keys, locked safes).
  - **Save System**: JSON-based `.crumbs` files for player state, history, and map samples.
- **Dependencies**: Standard Python libraries (os, tkinter, json, random, math, subprocess, webbrowser, collections, re, datetime, platform, ctypes, time). No external installs required beyond Tkinter. (Note: Integration with GRILLS may require Pillow for advanced animation handling.)

## 📈 Integration Points
### Internal System Integration
- **Shared Asset Loading**: Both programs scan the `Sprites/` directory and subfolders (e.g., `enemies/`, `aimdot/`, `Characters/`) for PNG sprites. ALT.py provides metadata and previews, while bSIM_50.py loads them dynamically for game objects (e.g., items, aim dots, characters).
- **File Type Handling**: Common support for custom formats like `.livemap` (live maps), `.tmap` (text-maps), `.mapd` (map dictionaries), `.arcs` (arc saves), and `.cumbs` (crumbs saves). ALT.py categorizes and describes them; bSIM_50.py uses them for saving/loading game states.
- **Launcher Integration**: ALT.py includes buttons to launch related scripts (e.g., latest TOAST, PB, JAM) via subprocess, using pattern matching to find the most recent versions.
- **Data Flow**: bSIM_50.py generates and saves game data (e.g., player coords, skills) to `.cumbs`, which can be browsed/analyzed in ALT.py. Procedural outputs from JAM/PB can be loaded into bSIM for testing.

### With PB (Map Maker)
- Loads custom .tmap and .mapd files for arena layouts via dictionary parsing.
- Uses cutmaps and dict files for generation assistance.

### With JAM (World Generator)
- Imports procedural enemy pools and world data from .arcs and .guide files.
- Supports .lore and .help files for in-game narrative, browsable in ALT.py.

### With GRILLS (Animation Sequencer)
- Loads GIF animations created and optimized in GRILLS for real-time use in boss simulations, including character animations, effects, and dynamic sprites.
- Utilizes benchmarks from GRILLS to ensure animations meet TOAST's performance requirements for smooth integration.
- Shares asset directories like `Sprites/animations/` for exporting and loading sequenced GIFs and PNGs.
- Supports the C.L.E.R.E. workflow: Craft PNG layers, Load into GRILLS, Export as GIF, Reload and refine, then integrate into TOAST for testing.

## 🚀 Getting Started
### Requirements
- Python 3.8+ (tested up to 3.12)
- Tkinter (included with most Python installs; install via package manager if needed):
  - **Ubuntu/Debian**: `sudo apt-get install python3-tk`
  - **Fedora**: `sudo dnf install python3-tkinter`
  - **Arch**: `sudo pacman -S tk`
- For GRILLS integration: Pillow (`pip install pillow`)

### Running
- For asset browsing:  
  ```bash
  python3 ALT.py
  ```
  - Launches a Tkinter window with a file tree, filters, previews, and launch buttons.
- For boss simulator (WIP):  
  ```bash
  python3 bSIM_50.py
  ```
  - Starts at title screen; select character and start game.

Controls (bSIM_50.py):
- WASD/Keys: Movement/menu actions
- Mouse: Camera/Aim/Drag items
- 1-9: Hotbar activation
- Right-click: Context menus/Interact
- ESC: Pause/Settings
- Double right-click: Cancel selections

## 📁 Project Structure
```
TOAST-BOSS-SIM/             # Main Boss Simulator folder
├── ALT.py                  # Automated Loader Tester (finished)
├── bSIM_50.py              # Boss Simulator (WIP)
├── Sprites/                # Sprite assets
│   ├── enemies/            # Enemy sprites
│   ├── random-mini-boss/   # Mini-boss variants
│   ├── boss/               # Boss sprites
│   ├── miniboss/           # Mini-boss sprites
│   ├── aimdot/             # Aim dot variants
│   ├── unused/             # Unused/development sprites
│   ├── old/                # Outdated sprites
│   ├── Characters/         # Premade playable characters
│   ├── animations/         # GIF and PNG animation sequences from GRILLS
│   └── ...                 # UI/icons (bpack.png, equip.png, etc.)
├── cutmaps/                # Map cutouts for generation
├── dict/                   # Dictionary files (.mapd)
├── myenv/                  # Python environment
├── arc/                    # Arc storage
├── help/                   # Help files
├── RAWS/                   # Raw sprite data
├── page/                   # Page data
└── bSIM.crumbs             # Save data (auto-generated)
```

## 🔍 Program Details: ALT.py (Automated Loader Tester)
### How It Works
ALT.py is a standalone Tkinter application that scans the current directory and subfolders, building a treeview of files and folders with game-specific metadata. It focuses on PNG sprites, extracting fields like name, type, rarity, and category using custom parsing logic. Users can filter by various criteria, view image previews, descriptions, and related files. Context menus allow opening files externally, and buttons launch related scripts. After a splash screen, it displays the asset tree with dynamic updates on filter changes.

- **Startup**: Scans directory for duplicates, related files, and unique filters (rarities, names, etc.).
- **UI**: Treeview (left), preview/description/related list (right), filter bars (top).
- **Interactivity**: Selection updates preview; double-click related jumps in tree; filters auto-refresh.
- **Integration**: Launches TOAST/PB/JAM via pattern-matched file names; describes file types based on extensions.

### Function Briefs
- `get_png_fields(filename, dir_path)`: Extracts metadata (name, type, rarity, etc.) from PNG filenames using splitting logic.
- `parse_png(filename, dir_path)`: Generates human-readable descriptions for PNG assets based on fields.
- `insert_dir(parent, path, filters)`: Recursively builds treeview, applying filters and tags (duplicate, hidden, unknown).
- `update_tree(event=None, force_open=False)`: Refreshes tree based on current filters, auto-opens if needed.
- `on_select(event)`: Updates preview, description, and related list on item selection.
- `show_menu(event, is_tree=True, iid=None, idx=None)`: Displays context menu for open/explore/view actions.
- `find_latest_toast()` (and similar for PB/JAM): Uses regex patterns to find the latest version of related scripts.
- `start_main()`: Hides splash after delay and initializes main UI.

## 🔍 Program Details: bSIM_50.py (Boss Simulator)
### How It Works
bSIM_50.py is a full Tkinter Canvas-based game loop simulating boss combat in a procedural arena. It starts with a title screen for character selection (witch, necromancer, elemental, or custom PNG). In-game, it generates an octagonal arena with obstacles, windows, safes, and interactives. Player movement uses WASD or mouse-follow; FPV mode locks mouse for immersion. HUD includes dynamic loot rows (weapons/armor/usables/skills), inventory/safe drawers with dragging, hotbar, and groups. Menus (radial) handle actions like inspect, pin, inventory. Game state saves to `.crumbs`; procedural elements spawn during movement.

- **Startup**: Loads sprites, initializes states, binds events.
- **Game Loop (`game_update`)**: Handles movement, collisions, camera, spawning, UI updates every 30ms.
- **Rendering (`draw`)**: Clears canvas, draws world/player/HUD/menus based on state.
- **Interactivity**: Dragging items between HUD sections; radial menus for player/safe actions; key/hotbar activations.
- **Integration**: Loads custom characters from `Sprites/Characters`; uses shared sprites for items/aimdots; saves integrate with PB/JAM formats.

### Function Briefs
- `__init__()`: Sets up Tkinter, loads sprites, initializes states/variables, binds events.
- `generate_arena()`: Procedurally creates obstacles, windows, safes, world_safe, and interactives with random positions/inventories.
- `start_new_game()`: Creates player dict, resets variables, generates arena, enables mouse lock.
- `on_motion(event)`: Handles mouse hover, edge scrolling, FPV yaw/pitch, HUD hover detection.
- `handle_hud_left_click(x, y)`: Processes clicks on hotbar, loot rows, drawers, groups.
- `on_left_release(event)`: Handles item drops with auto-placement logic, returns to source if invalid.
- `handle_menu_button(idx)`: Executes radial menu actions (follow/inspect/pin, FPV, inventory, etc.).
- `draw_world()`: Renders arena, obstacles, windows, safes, interactives (FPV or top-down).
- `draw_hud()`: Draws dynamic loot rows, drawers (inventory/safe), hotbar, groups, dragging items.
- `game_update()`: Main loop for updates (movement, collisions, spawning, stamina, drawing).

## 📝 Save Data
- `bSIM.crumbs`: JSON with header (player ID/coords/data), map samples, details, history (scores/kills/levels/timestamps).

- ###### ALT.py uses no persistent save but dynamically scans files.

## 🎯 Vibecoded (VBCD)
This project was VBCD (vibecoded) because the creator primarily uses JS, not Python. I (DigiMancer3D) wanted a fast way to prototype a game engine by describing ideas to Grok, while learning Python through editing VBCD outputs. Resources like w3schools.com and other VBCD Python projects have been invaluable for understanding syntax and structure.

## 📖 Related Documentation
For the full Pixeled-Backrooms ecosystem:
- [PB Repository](https://github.com/DigiMancer3D/Pixeled-Backrooms) - Map creation tools
- [JAM Documentation](https://github.com/DigiMancer3D/Pixeled-Backrooms/tree/main/JAM) - World generation
- [GRILLS Documentation](https://github.com/DigiMancer3D/Pixeled-Backrooms/tree/main/GRILLS) - Animation sequencing tools

## Sprites
There are some sprites data that are preloaded and each sprite has default sizings (check png.guide in /help/ for full sprite sizing list).

### Defaults
All sprites are allowed a range between 1-1042 pixels but some have predetermined defaults that work within the bounds of the UI.
- **Splash Screen**: 1200x930
- **DIY Character**: 128x128
- **Interactive Objects**: 256x256
- **Directional Arrows**: 48x48
- **Tabbed-Loot-Array Row Identifiers**: 64x64
- **Inventory & Safe Tab Icons**: 42x42
- **BackPack & Equip Icons**: 42x42
- **Usables/Findables**: 128x128 
- **AimDot**: 68x68

### Pre-Loaded
Some sprites come already installed or pre-made & ready for use.
- **AimDot**: 238 Pre-Loaded AimDots [avg 19.83~ per category [12] || avg 19.75 per material [8]]
- **Characters**: 13 Pre-Loaded [DIY] Characters [avg 2 varients per character]
- **Random-Mini-Boss**: 1 Pre-Loaded RMB 
- **Usables/Findables**: 37 Pre-Loaded Usables/Findables
- **Directional Arrows**: 13 Pre-Loaded DArrows
- **Tabbed-Loot-Array Row Identifiers**: 6 Pre-Loaded TLA Row IDs [1 unused swappable option]
- **Safe(s)**: 3 Pre-Loaded Touchable Safes (Including the world safe)
- **Inventory & Safe Tab Icons**: 4 Pre-Loaded Inventory & Safe Tab Icons
- **BackPack & Equip Icons**: 3 Pre-Loaded BPack & Equip Icons

## 🙏 Credits
Created by DigiMancer3D as part of the Pixeled-Backrooms project.  
Coded with assistance from Grok.

---
**Status**: Active Development (ALT.py complete; bSIM_50.py WIP)  
*TOAST: The engine that's crisp, fresh, and ready to battle bosses! 🍞*
