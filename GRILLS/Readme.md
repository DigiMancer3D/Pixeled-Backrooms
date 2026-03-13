# General Real-time Integration Lateral Limited Sequencer [GRILLS]

> Part of the Pixeled-Backrooms project ecosystem  

GRILLS is a real-time animation sequencer and benchmark tool built with Python and Tkinter. It features a dual-panel interface for GIF (left) and PNG sequences (right), enabling loading, manipulation, benchmarking, and exporting animations. Integrates with Pixeled Backrooms tools like PB (map maker), JAM (world generator), and TOAST Boss Sim for performance testing and asset optimization.

## Project Overview

- **GRILLS.py**: Core app for sequencing, blending, adjusting, and benchmarking animations.  
- Supports GIF/PNG with controls for speed, layering, opacity, sizing, rotation, color/hue/sat adjustments.  
- Benchmarks FPS, render time, memory for TOAST compatibility.  
- Exports to GIF/PNG sequences in Sprites/animations/.

## Technical Details

- **Language**: Python 3.x  
- **GUI**: Tkinter  
- **Libraries**: Pillow (PIL), glob, json, re, platform, ctypes, subprocess, gc, math, collections.  
- **Features**:  
  - Playback: Speed (±0.01-13.0), reverse, overlap, loops.  
  - Robin Mode: Layering with gaps, alignments (C/B/T/R/L), extras.  
  - Blending: Opacity (0-1), scale (0.01-4x), offsets, rotation, locking.  
  - Adjustments: Color boosts, hue (brightness/temp/tint), sat (tints, reductions, concentration).  
  - Benchmark: FPS, render ms, mem (PIL/resized), CPU/RAM.  
  - Export: GIF (durations/loops) or PNG sequences.  
  - Cross-platform memory monitoring; .crumbs for temps.  

## Integration Points

- **With TOAST Boss Sim**: Test boss animations for FPS/mem, layer effects, export optimized assets.  
- **With PB/JAM**: Benchmark procedural animations, adjust aesthetics, export for maps/generation.  

## Getting Started

### Requirements

- Python 3.8+  
- Tkinter (bundled; install if needed, e.g., `sudo apt-get install python3-tk`).  
- Pillow: `pip install pillow`  

### Installation

1. Clone: `git clone https://github.com/DigiMancer3D/Pixeled-Backrooms.git`  
2. Navigate: `cd Pixeled-Backrooms/GRILLS` (or create if needed)  
3. Run: `python3 GRILLS.py`  

## Usage Instructions

1. **Load**: Click "Load .gif" (left) or ".png" (right); multi-select PNGs.  
2. **Controls**: +/- speed (hold), Reverse, Overlap +/-, Loop +/-. Pause: canvas click.  
3. **Benchmark**: View FPS/mem during play.  
4. **Robin**: Toggle for layers; adjust count/gap/align. Add extras. Reorder: << / <- / -> / >>.  
5. **Blending/Adjust**: Target (Initial/Robin/Stack), opacity/size +/-, lock. Color/Hue/Sat with ● options. Long-press tabs for position/rotate/align/lock popup.  
6. **Export**: Button; name, .gif/.png to Sprites/animations/.  
7. **Advanced**: Double-left: reload; double-right: cancel. Long-click: properties. Resize window scales.  

## Examples

- **Boss Benchmark**: Load GIF, speed test, monitor FPS, adjust hue, export.  
- **Layered Effect**: Robin 3, add extras, gap/align, benchmark, export PNG.  
- **Procedural Tune**: Load PNG seq, sat reduce, loop 5x, export GIF.  


## Why GRILLS?

GRILLS prototypes animations live for smooth TOAST/PB/JAM integration. Test, tweak, export—grill hot assets! Fork/star/contribute to pixelated adventures. 🚀
