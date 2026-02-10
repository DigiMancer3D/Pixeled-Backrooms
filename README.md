# Pixeled Backrooms (PB) Project

## Overview
**Pixeled Backrooms (PB)** is a retro-style pixelated game project inspired by Backrooms lore. It is being developed in three interconnected components:

1. **Pixel-Game Engine** — Core rendering, physics, AI, and gameplay systems.
2. **Map & Arc Generator** — Procedural generation tools for levels and narrative arcs.
3. **Map Maker** — A powerful graphical editor (the most mature component).

The **Map Maker** (PB.17.py) is now fully functional and serves as the primary creative tool for designing maps, properties, and story arcs. The engine and generator remain in early conceptual stages.


### Project Progress
- **Pixel-Game Engine** (Progress: 0% — conceptual only)  
  Basic rendering pipeline ideas tested. Have found issues with map-view switching, looking at new method of handling the visual-display for multiple forms. Future work includes entity movement, collision, lighting, and integration with exported maps/arcs.

- **Map & Arc Generator** (Progress: 0% — early testing)  
  Procedural algorithms planned but not yet implemented. Will eventually integrate with the Map Maker's output.

- **Map Maker** (Progress: ~95% — stable and feature-rich)  
  A complete Tkinter-based editor for manual map and arc creation. Includes grid editing, property management, arc scripting, minimap connectivity, blending, paint/tint tools, and multiple export formats.  
  **Current version:** `PB.17.py`


## Map Maker (PB.17.py)

The **Map Maker** is a standalone Python tool for designing maps and narrative arcs for Pixeled Backrooms. It features a responsive GUI with advanced editing capabilities, export options, and quality-of-life tools.


### Installation

**Requirements:**
- Python 3.12+
- Tkinter (usually included; on Ubuntu/Debian: `sudo apt update && sudo apt install python3-tk`)
- Additional packages:
  ```bash
  pip install numpy pillow networkx
  ```
  
Run the Map Maker:   
 ```Bash
 git clone https://github.com/yourusername/pixeled-backrooms.git
 cd pixeled-backrooms
 python PB.17.py
 ```
 
## Usage Quick Start

1. **Launch** → PB.17.py opens the main window.
2. **Create/Edit Maps** → Use the left Symbols panel. Click to place, right-click to remove or inspect.
3. **Properties** → Click a cell → edit in the right drawer (or use multi-select).
4. **Arcs** → Create in the bottom panel, attach to current map via the Arcs list.
5. **Mini-Map** → Open drawer to visualize and connect maps.
6. **Export** → Use the File or Map menu (PNG, CSV, ZIP dictionary).

###### Detailed help is available in the Help menu.

---

### Key Features

#### Map Editing
- Grid-based canvas (resizable, up to 1080×1080 cells).
- Rich symbol system (walls, doors, water, enemies, chests, teleporters, etc.).
- **Multi-select** (up to 9 regions) with Shift-click support.
- **Copy / Cut / Paste / Replace** operations.
- **Undo / Redo** (per-map history, delta-based for efficiency).
- Zoom slider + scroll/pan.
- View modes (Side, Iso, Heli, Top).
- **Paint Tool** — Apply background tints/colors with opacity and named color storage.
- **Title Cards** — Toggleable floating name labels.
- Sun rise/set placement and height-difference visualization (colored borders indicating jumpability/injury risk).

#### Property System
- Per-cell properties: name, color, texture, height, depth, value, 3D flag, range, earmark, title card, sun position.
- **Lock Apply** mode for consistent property stamping.
- **Mass editing** on multi-selected regions.
- **Pin At / Pin To** system for map-to-map alignment.

#### Arc Builder
- Full arc creation and editing (name, estimated time picker, zone type, start/confirm messages, map reference, data field).
- **Script Generator** — Quick forms for enemies, bosses, mini-bosses, NPCs, groups, map locations, and key bindings.
- **Phrase injector** buttons for common events (exit, enter, kill, touch, etc.).
- Undo/redo for arc fields.
- Attach arcs to maps (visual dots on canvas).

#### Mini-Map & Connectivity
- Visual minimap showing all maps as nodes.
- Drag-to-connect openings (7 possible per map: top, right, bottom, left, +3 internal).
- Compatibility rules and colored connections (black/gold/green/red/blue).
- Randomize connections option.
- Click maps to switch tabs.

#### Blending System
- Sliders to blend adjacent maps (useful for stacked or connected levels).
- Automatic alignment using **Pin At / Pin To** markers.

#### User & Customization
- New-user onboarding form (name, tag, text color theme).
- Persistent user data (`PB.udata`) including UUID, colors, and named tints.
- Text color themes (Classic, Ink, Rusty, etc.).
- Epoch timestamp in menu bar.

#### File Management & Export
- Auto-organizes files into `map/`, `arc/`, `dict/`, `help/` folders.
- **.tmap** — Single map (grid + metadata).
- **.mapd** — Dictionary (multiple maps + arcs + connections).
- **PNG export** — High-quality map images with footer (title, date code, arc count).
- **CSV export** — Arcs (selected or all).
- **Full Dictionary ZIP** — All maps (PNG + TXT) + arcs CSV.
- Separated TXT export (grid symbols + header/footer).

#### Help & Safety
- In-app help viewer with guides (symbols, arcs, doors, minimap, full lists).
- Input validation and length limits.
- Right-click tooltips and info popups throughout the UI.

---

### Screenshots
//<-- add screenshots here -->


- Main editor with map canvas, symbols, and properties
- Arc builder + script generator
- Mini-map with connections
- Paint tint drawer and blending sliders

---

### Happy mapping! 🚀

###### For questions, open an issue on GitHub or reach out to the maintainers (@Z0M8I3D and contributors).

###### Last updated: February 2026 — Map Maker v17 stable.
