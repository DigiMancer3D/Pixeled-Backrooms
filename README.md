# Pixeled Backrooms (PB) Project

## Overview

Pixeled Backrooms (PB) is an ambitious project aimed at creating a retro-style pixelated game inspired by backrooms lore. The project is divided into three main components:

1. **Pixel-Game Engine**: The core rendering and logic engine for handling game mechanics, physics, and interactions in a pixelated environment.
2. **Map & Arc Generator**: A tool for generating maps and narrative arcs, including procedural generation of levels and story elements.
3. **Map Maker**: A graphical editor for manually designing and editing maps, arcs, and properties, built using Python and Tkinter.

This README provides an overview of the project's progress across these components and a detailed guide to the Map Maker tool, which is the most developed part to date.

### Project Progress

- **Pixel-Game Engine** (Progress: 0% [only-tested concept]):
  - Basic rendering pipeline implemented using Pygame or similar libraries.
  - Support for pixelated graphics, entity movement, and basic collision detection.
  - Todo: Advanced features like AI pathfinding, lighting effects, and multiplayer integration.
  - Challenges: Optimizing for low-resolution pixel art while maintaining performance.

- **Map & Arc Generator** (Progress: 0% [had problems with inital testing]):
  - Procedural generation algorithms for creating backrooms-style maps (e.g., maze-like structures with random rooms).
  - Arc generation for narrative elements, including events, enemies, and items.
  - Todo: Integration with the game engine, more varied generation rules, and user-customizable parameters.
  - Challenges: Ensuring generated content is balanced and engaging.

- **Map Maker** (Progress: 80% [working on bugs & mini-map]):
  - Fully functional GUI for creating and editing maps.
  - Supports symbol placement, property editing, arc building, and export options.
  - Detailed below in the dedicated section.
  - Challenges: Handling large maps efficiently and improving user interface responsiveness.

The project is open-source and welcomes contributions. See the [Contributing](#contributing) section for details.

## Map Maker for Pixeled Backrooms

The Map Maker is a Python-based tool for designing maps and arcs for the Pixeled Backrooms game. It provides a user-friendly interface for placing symbols, editing properties, and managing narrative arcs. The tool is built with Tkinter and supports various export formats for integration with the game engine.

### Features

- **Map Editing**:
  - Grid-based canvas for placing symbols (walls, doors, enemies, etc.).
  - Multi-select, copy, cut, paste, and replace tools.
  - Undo/redo support for edits.
  - Zoom and scroll functionality.

- **Property Editing**:
  - Edit cell properties like name, color, texture, height, depth, value, 3D, range, and sun position.
  - Lock apply feature for consistent properties across symbols.

- **Arc Builder**:
  - Create and edit narrative arcs with fields for name, estimated time, zone type, start/confirm messages, map, and data.
  - Script generator for injecting common elements like enemies, bosses, NPCs.
  - Data phrases for quick insertion of common terms.

- **Export Options**:
  - Export maps as .png with accompanying .txt for metadata.
  - Export arcs as .csv.
  - Full dictionary export as .zip containing maps and arcs.

- **User Customization**:
  - Text color themes.
  - User name, tag, and UUID management.
  - Epoch time display in menu bar.

- **Safety and Validation**:
  - Input validation for numerical fields.
  - Cheating detection for invalid map interactions.

### Installation

1. Ensure Python 3.12+ is installed.
2. Install Tkinter if not present: `sudo apt update && sudo apt install python3-tk` (on Ubuntu/Debian).
3. Clone the repository:
   ```
   git clone https://github.com/yourusername/pixeled-backrooms.git
   cd pixeled-backrooms
   ```
4. Run the Map Maker:
   ```
   python pb.11a.py
   ```

No additional dependencies are required beyond the standard library and Tkinter.

### Usage

1. **Launch the Tool**:
   - Run the script to open the GUI.

2. **Create a Map**:
   - Use the Symbols list to select and place items on the canvas.
   - Right-click to remove or select properties.
   - Use multi-select for bulk operations.

3. **Edit Properties**:
   - Select a cell to view/edit properties in the right panel.
   - Apply changes or lock for consistent application.

4. **Build Arcs**:
   - Use the Arcs list to create/edit arcs.
   - Fill fields and use the script generator for quick input.

5. **Export**:
   - Use menu options to export maps, arcs, or the full dictionary.

For detailed help, use the "Help" menu in the tool.

### Screenshots

![Map Editor Interface](https://placeholder.com/screenshot-map-editor.png)  
*The main interface showing the map canvas, symbols, and properties.*

![Arc Builder](https://placeholder.com/screenshot-arc-builder.png)  
*The arc builder section for creating narrative elements.*

### Contributing

Contributions are welcome! Please follow these steps:
1. Fork the repository.
2. Create a feature branch (`git checkout -b feature/AmazingFeature`).
3. Commit your changes (`git commit -m 'Add some AmazingFeature'`).
4. Push to the branch (`git push origin feature/AmazingFeature`).
5. Open a Pull Request.

### License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

---

For questions or issues, open an issue on GitHub or contact the maintainer. Happy mapping! 🚀
