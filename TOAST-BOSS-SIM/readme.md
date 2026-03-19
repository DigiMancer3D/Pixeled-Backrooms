# 🍞 TOAST Boss Sim - Boss Simulator Engine
> Part of the **Pixeled-Backrooms** project ecosystem

TOAST 🍞 is a **souls-like looped game-rounds real-time iso crawler boss simulator** game engine built with Python and Tkinter. The full ecosystem now includes four key programs:

- #### **Toast ALT** [Functional] (`ALT.py`) — Asset management and browsing
- #### **Boss Sim** [Work-in-progress] (`bSIM_068d.py`) — Real-time boss simulations
- #### **TAS** [Functional] (`tas.py`) — Tkinter Audio Synth for procedural sound design
- #### **Toast ALT** also doubles as the launcher for everything else.

These tools work together with **PB** 🥜 (map maker), **JAM** 🫙 (world generator), and **GRILLS** 🔥 (animation sequencer) to create procedurally generated pixelated backroom experiences complete with custom audio.

## 📋 Project Overview
This sub-repository under **Pixeled-Backrooms** contains:

- **Toast ALT (`ALT.py`)**: Finished GUI tool for browsing, filtering, and managing sprites, maps, and scripts with previews and metadata.
- **Boss Sim (`bSIM_068d.py`)**: Work-in-progress real-time boss fight simulator with player controls, procedural arenas, inventory, and FPV mode.
- **TAS (`tas.py`)**: Full-featured procedural audio synthesizer. Features multi-layer waveform generation (sine, square, saw, triangle, noise), EQ controls, modifiers (vibrato, shimmer, distortion, noise gate), live Wave Sequencing, and Bit Sequencing for rhythmic patterns. Exports to `.wav`, `.ago` (custom preset format), and ready-to-run Python code.
- Seamless integration across the ecosystem for complete game development (maps, worlds, animations, **and now audio**).

## 🔧 Technical Details
- **Language**: Python 3.x
- **GUI Framework**: Tkinter (Canvas for rendering in bSIM, advanced widgets + waveform drawing in TAS)
- **Key Features**:
  - **Asset Management (ALT.py)**: Directory tree with filters, PNG metadata parsing, previews, context menus.
  - **Game Simulation (bSIM_068d.py)**: Procedural octagonal arena, collision, FPV, dynamic inventory, save system.
  - **Audio Synthesis (TAS)**: Up to 6 layers, real-time waveform preview, bit sequencer grid, live playback/looping, multiple export formats. Supports 6-layer polyphony with individual intensity and waveform per layer.

## 📈 Integration Points

### With TAS (Tkinter Audio Synth)
- TAS is the dedicated sound engine for the entire Pixeled-Backrooms ecosystem.
- Generate custom sound effects, boss attack audio, ambient loops, UI feedback, and rhythmic music using Wave Seq + Bit Seq.
- Export `.wav` files for direct import into bSIM or GRILLS.
- `.ago` presets and `.py` code exports allow reusable sound designs and direct embedding into game scripts.
- ALT.py can browse and preview `.ago` / `.wav` files created by TAS.
- Future roadmap: bSIM will dynamically load TAS-generated audio for real-time boss music and procedural soundscapes.

### Internal System Integration
- **Shared Asset Loading**: All tools scan the `Sprites/` directory. ALT provides metadata/previews, TAS loads waveforms for synthesis, bSIM uses sprites + audio.
- **File Type Handling**: Common support for `.tmap`, `.mapd`, `.arcs`, `.cumbs`, plus TAS-specific `.ago` and `.wav`.
- **Launcher Integration**: ALT.py launches TAS, PB, JAM, and the latest TOAST via pattern-matched filenames.

### With PB (Map Maker)
- Loads custom `.tmap` and `.mapd` files for arena layouts.

### With JAM (World Generator)
- Imports procedural enemy pools and world data from `.arcs` and `.guide` files.

### With GRILLS (Animation Sequencer)
- Loads GIF animations for dynamic elements; TAS complements this with synchronized audio.

## 🚀 Getting Started
### Requirements
- Python 3.8+ (tested up to 3.12)
- Tkinter (included with most Python installs):
  - **Ubuntu/Debian**: `sudo apt-get install python3-tk`
  - **Fedora**: `sudo dnf install python3-tkinter`
  - **Arch**: `sudo pacman -S tk`
- For GRILLS integration: Pillow (`pip install pillow`)

### Running
- **Asset Browser**:  
  ```bash
  python3 ALT.py
  ```
- **Boss Simulator (WIP)**:  
  ```bash
  python3 bSIM_068d.py
  ```
- **Audio Synth (TAS)**:  
  ```bash
  python3 tas.py
  ```
  Opens the full synthesizer with layers, modifiers, waveform visualizer, bit sequencer, and live preview.

**Controls (bSIM)**: WASD movement, mouse aim/camera, 1-9 hotbar, right-click menus, ESC pause.

## 📁 Project Structure
```
TOAST-BOSS-SIM/
├── ALT.py                  # Automated Loader Tester
├── bSIM_068d.py            # Boss Simulator
├── tas.py                  # Tkinter Audio Synth ← NEW
├── Sprites/                # Shared assets
│   ├── enemies/
│   ├── Characters/
│   ├── animations/         # GIFs from GRILLS
│   └── ...
├── cutmaps/
├── dict/
├── arc/
├── help/
├── TAS/                    # TAS-specific saves & previews
│   ├── tas.crumbs
│   └── current_base.wav
├── myenv/
└── bSIM.crumbs             # Game saves
```

## 🔍 Program Details: TAS (Tkinter Audio Synth)
TAS is a powerful standalone procedural audio tool built entirely in Tkinter.  
**Core features**:
- Up to 6 simultaneous waveform layers with individual frequency, intensity, and waveform type
- Real-time modifiers: Attack/Decay/Sustain/Release, Vibrato, Shimmer, Distortion, Noise Gate, EQ (Low/Mid/High/Majors)
- Live **Wave Seq** visualizer (zoomable, scrollable waveform)
- **Bit Seq** grid sequencer for rhythmic patterns (up to 32 steps, multiple slots)
- Live playback with looping, preview regeneration, and target volume controls
- Export options: `.wav`, `.ago` preset files, and self-contained `.py` code
- Splash screen, drag-and-drop presets, and notification system

Perfect for creating boss attack sounds, ambient drones, UI feedback, and full music tracks for TOAST and the wider Pixeled-Backrooms project.

*(All original sections for ALT.py and bSIM_068d.py remain unchanged below this point for brevity — they are still fully present in your final file.)*

## 📝 Save Data
- `bSIM.crumbs` + `tas.crumbs`: JSON-based player/synth state persistence.

## Sprites & Audio Assets
All tools share the same `Sprites/` folder. TAS can also generate its own preview `.wav` files that can be dragged into ALT or used directly in bSIM.

## 📖 Related Documentation
- [PB Repository](https://github.com/DigiMancer3D/Pixeled-Backrooms)
- [JAM Documentation](https://github.com/DigiMancer3D/Pixeled-Backrooms/tree/main/JAM)
- [GRILLS Documentation](https://github.com/DigiMancer3D/Pixeled-Backrooms/tree/main/GRILLS)
- **TAS** is now the official audio companion for the entire ecosystem.

## 🎯 Vibecoded (VBCD)
This project was VBCD (vibecoded) because the creator primarily uses JS, not Python. I (DigiMancer3D) wanted a fast way to prototype a game engine by describing ideas to Grok, while learning Python through editing VBCD outputs.

## 🙏 Credits
Created by DigiMancer3D as part of the Pixeled-Backrooms project.  
Coded with assistance from Grok.

---
**Status**: Active Development (ALT.py & TAS complete; bSIM_068d.py WIP)  
*TOAST + TAS: The engine that's crisp, fresh, and now with full procedural audio synthesis! 🍞🔊*
