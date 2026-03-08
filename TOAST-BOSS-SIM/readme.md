
# 🍞 TOAST - Backroom Game Engine

> Part of the **Pixeled-Backrooms** project ecosystem

TOAST is a **souls-like boss combat simulator** and game engine built with Python and Tkinter. It's designed as the third component of a three-tier architecture alongside **PB** (map maker) and **JAM** (world generator), enabling a fully generatable pixelated backroom crawler experience.

## 📋 Project Overview

This repository contains the **Pixeled-Backrooms** project, which consists of three interconnected tools:

- **PB** (Pixeled-Backrooms Map Maker) - Create custom arena layouts and environments
- **JAM** (Procedural World Generator) - Generate procedural world data and creature encounters
- **TOAST** (This Game Engine) - Real-time souls-like combat and exploration engine

---

## 🔧 Technical Details

### Architecture
- **Language**: Python 3.x
- **GUI Framework**: Tkinter
- **Collision Detection**: GJK (Gilbert-Johnson-Keerthi) algorithm

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
  - Some times you need to get tk specific python3
      #### Unbuntu Flavors
      ```bash
      sudo apt-get python3-tk  
      ```
      #### Fedora Flavors
      ```bash
      sudo dnf install python3-tkinter  
      ```
      #### Arch Flavors
      ```bash
      sudo pacman -S tk  
      ```

### Running
  ```bash
  python3 soulslikebosssim_17.py
  ```


## 📁 Project Structure

```
Pixeled Backrooms (PB)   # Main poject folder
└── bosssim/             # Main Tast-Boss-Sim folder
    └── bSIM_50.py       # Boss Simulator
    └── ALT.py           # Automated Loader Tester
    └── Sprites          # Sprite Data
        └── Enemies      # Enemy Sprites
        └── aimdot       # Aimdot Sprites
        └── Characters   # Premade Character Sprites
```

## 📝 Save Data

Game progress is saved to `game.crumbs` in JSON format, including:
- Player stats and level
- Element affinities
- Weapon and equipment state
- Settings

## 🎯 Vibecoded (VBCD)

This project was VBCD (vibecoded) because the creator uses JS not Python. I (3Douglas) wanted a game that was faster to tell Grok what I wanted since I do not know pyhon but I have been using multiple VBCD pyhon projects to learn more about python and have been editing VBCD work to learn how python work. That and w3schools.com have been helping me learn through vibecoding. 

## 📖 Related Documentation

For more context on the broader Pixeled-Backrooms project:
- See PB documentation for map creation
- See JAM documentation for world generation

## 🙏 Credits

Created by DigiMancer3D as part of the Pixeled-Backrooms project.

Coded by Grok. 

---

**Status**: Early Development 

*TOAST: The game engine that's crisp & fresh from the toaster! 🍞*
