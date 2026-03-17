# General Real-time Integration Lateral Limited Sequencer [GRILLS]

> Part of the Pixeled-Backrooms project ecosystem  

GRILLS is a real-time animation sequencer and benchmark tool built with Python and Tkinter. It features a dual-panel interface for GIF (left) and PNG sequences (right), enabling loading, manipulation, benchmarking, and exporting animations. Integrates with Pixeled Backrooms tools like PB (map maker), JAM (world generator), and TOAST Boss Sim for performance testing and asset optimization.

<br></br>

## Intended Use Case

GRILLS is intended to be used alongside TOAST Engine for campign builders to form custom animations to be used with TOAST. The basic concept of usage goes as follows: 

### ***C.L.E.R.E.***

 - ***C*raft** your own .png based layers to form a sequenced animation 
 - ***L*oad** your custom png sequenced animation files in to GRILLS (right side) to manipulate with the soft 
 - ***E*xport** your setup animation that is seen in GRILLS soft as a .gif, when you feel the animation works how you want.
 - ***R*eload** in your newly saved .gif animations into GRILLS (left side) to manipulate with the soft 
 - ***E*xport** as a new .gif when you feel you have finished elevating or configuring you custom animations.

 
<br></br>
  

## Why GRILLS?

GRILLS prototypes animations in-real-time for smooth integration to your choice of game engine by being able to run alongside your favorite game engine. Test, tweak, export & grill your assets! 

<br></br>

## Project Overview

- **GRILLS.py**: Core app for sequencing, blending, adjusting, and benchmarking animations.  
- Supports GIF/PNG with controls for speed, layering, opacity, sizing, rotation, color/hue/sat adjustments.  
- Benchmarks FPS, render time, memory for TOAST compatibility.  
- Exports to GIF/PNG sequences in Sprites/animations/.

<br></br>

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

---

<br></br>

## Getting Started


### Requirements

- Python 3.8+  
- Tkinter (bundled; install if needed, e.g., `sudo apt-get install python3-tk`).  
- Pillow: `pip install pillow`
  
<br></br>

### Installation

1. Clone: `git clone https://github.com/DigiMancer3D/Pixeled-Backrooms.git`  
2. Navigate: `cd Pixeled-Backrooms/GRILLS` (or create if needed)  
3. Run: `python3 GRILLS.py`  

<br></br>

## Usage & Example

### ***L.E.D. L.E.E.C.***
1. **Load**: Click "Load .gif" (left) or ".png" (right); multi-select PNGs.  
2. **Edit**: +/- speed (hold), Reverse, Overlap +/-, Loop +/-. Pause: canvas click.  
3. **Determine**: View banchmark data FPS/mem during play to detemine best play points.  
4. **Loop**: Toggle for layers; adjust count/gap/align. Add extras. Reorder: << / <- / -> / >>.  
5. **Edit**: Target (Initial/Robin/Stack), opacity/size +/-, lock. Color/Hue/Sat with ● options. Long-press tabs for position/rotate/align/lock holding pop-in options.  
6. **Export**: Button; name, .gif/.png to Sprites/animations/.  
7. **Control**: single-left: play/pause; Double-left: reload; double-right: cancel. Long-click: properties. Resize window scales.  

<br></br>

## Examples of usages

- **Boss Benchmark**: Load GIF, speed test, monitor FPS, adjust hue, export.  
- **Layered Effect**: Robin 3, add extras, gap/align, benchmark, export PNG.  
- **Procedural Tune**: Load PNG seq, sat reduce, loop 5x, export GIF.
- **Create & Export**: Make the PNGs to export as GIF then reload the GIF to finalize to make how you want them.
- **Edit Your Old Gifs**: Take your old gifs to new levels with layering and adjustments in-real-time.

<br></br>
<br></br>
<br></br>
