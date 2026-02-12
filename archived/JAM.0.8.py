import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import json
import random
import os
from typing import Dict, List, Tuple, Optional

# ====================== JAM.0.8.py - Journey-Action-Mapper ======================
# Pixeled Backrooms World Builder - Version 0.8
# Interactive click-to-place for .tmap + full .mapd dictionary import with connections

class MapChunk:
    def __init__(self, map_id: str, openings: str = "0000000", width: int = 48, height: int = 24):
        self.id = map_id
        self.name = "Generated Room"
        self.openings = openings
        self.width = width
        self.height = height
        self.z_level = 0
        self.grid: List[List[str]] = [[' ' for _ in range(width)] for _ in range(height)]
        self.props: List[Dict] = []
        self.spawners: List[Dict] = []
        self.arc_ids: List[str] = []
        self.type = "Mixed"
        self.waypoint_kind = "none"

    def set_opening(self, slot: int, value: int):
        if 0 <= slot < 7:
            openings_list = list(self.openings)
            openings_list[slot] = str(value)
            self.openings = ''.join(openings_list)
            if value == 5:
                if self.waypoint_kind == "none":
                    self.waypoint_kind = random.choice(["home", "instance"])
                elif self.waypoint_kind != "both":
                    self.waypoint_kind = "both"

    def to_dict(self) -> Dict:
        return {
            "id": self.id,
            "name": self.name,
            "openings": self.openings,
            "width": self.width,
            "height": self.height,
            "z_level": self.z_level,
            "grid": [''.join(row) for row in self.grid],
            "props": self.props,
            "spawners": self.spawners,
            "arc_ids": self.arc_ids,
            "type": self.type,
            "waypoint_kind": self.waypoint_kind
        }

    @staticmethod
    def from_dict(data: Dict) -> 'MapChunk':
        chunk = MapChunk(data["id"], data.get("openings", "0000000"),
                         data.get("width", 48), data.get("height", 24))
        chunk.name = data.get("name", "Loaded Room")
        chunk.type = data.get("type", "Mixed")
        chunk.arc_ids = data.get("arc_ids", [])
        chunk.props = data.get("props", [])
        chunk.spawners = data.get("spawners", [])
        chunk.waypoint_kind = data.get("waypoint_kind", "none")
        chunk.z_level = data.get("z_level", 0)
        grid_strs = data.get("grid", [])
        if grid_strs and isinstance(grid_strs[0], str):
            chunk.grid = [list(row) for row in grid_strs]
        return chunk


class World:
    def __init__(self, seed: int = 42, world_name: str = "The Yellow Halls", world_lvl: str = "0"):
        random.seed(seed)
        self.seed = seed
        self.world_name = world_name
        self.world_lvl = world_lvl
        self.params = {"spawn_enemy_rate": 0.35, "boss_chance": 0.05}
        self.maps: Dict[str, MapChunk] = {}
        self.connections: List[Dict] = []
        self.arcs: Dict[str, Dict] = {}
        self.next_id = 1
        self.map_positions: Dict[str, Tuple[float, float]] = {}
        self.used_slots: Dict[str, set] = {}
        self.generation_mode = "bsp"
        self.last_placed = None

    def new_map_id(self) -> str:
        mid = f"m{self.next_id:03d}"
        self.next_id += 1
        return mid

    def rebuild_positions(self):
        self.map_positions.clear()
        if not self.maps:
            return
        mids = list(self.maps.keys())
        cx, cy = 0.0, 0.0
        self.map_positions[mids[0]] = (cx, cy)
        directions = [(1,0), (0,1), (-1,0), (0,-1)]
        step = 1
        idx = 1
        while idx < len(mids):
            for _ in range(2):
                dx, dy = directions[(step-1) % 4]
                for _ in range(step):
                    if idx >= len(mids):
                        break
                    cx += dx * 210
                    cy += dy * 150
                    self.map_positions[mids[idx]] = (cx, cy)
                    idx += 1
            step += 1

    def add_connection(self, from_map: str, from_slot: int, to_map: str, to_slot: int):
        self.connections.append({
            "from_map": from_map, "from_slot": from_slot,
            "to_map": to_map, "to_slot": to_slot
        })
        self.used_slots.setdefault(from_map, set()).add(from_slot)
        self.used_slots.setdefault(to_map, set()).add(to_slot)

    def is_slot_available(self, map_id: str, slot: int) -> bool:
        chunk = self.maps.get(map_id)
        if not chunk: return False
        slot_type = int(chunk.openings[slot])
        used = self.used_slots.get(map_id, set())
        if slot_type in (5, 4):
            return True
        return slot not in used

    def is_compatible(self, slot1: int, type1: int, slot2: int, type2: int) -> bool:
        allowed = {0: [0,4,5], 1: [0,1,3,4,5], 2: [1,2,4,5],
                   3: [0,1,3,4,5], 4: [0,1,2,3,4,5], 5: [0,1,2,3,4,5]}
        if type2 not in allowed.get(type1, []):
            return False
        opposites = {0: 2, 2: 0, 1: 3, 3: 1}
        if slot1 < 4 and slot2 < 4:
            return opposites.get(slot1) == slot2
        return True

    def get_free_slot_maps(self) -> List[str]:
        return [mid for mid in self.maps if any(self.is_slot_available(mid, s) for s in range(7))]

    def calculate_adjacent_position(self, parent_pos: Tuple[float, float], slot: int, is_vertical: bool) -> Tuple[float, float]:
        px, py = parent_pos
        if is_vertical:
            return (px + random.randint(-80, 80), py + random.randint(-60, 60))
        offsets = {
            0: (0, -180), 1: (230, 0), 2: (0, 180), 3: (-230, 0),
            4: (-100, -80), 5: (0, -80), 6: (100, -80)
        }
        dx, dy = offsets.get(slot, (random.randint(-140,140), random.randint(-120,120)))
        return (px + dx, py + dy)

    def try_connect(self, new_chunk: MapChunk, parent_id: str) -> bool:
        if parent_id not in self.maps:
            return False
        parent = self.maps[parent_id]
        slot_order = [0,1,2,3,4,5,6]
        if random.random() < 0.08:
            slot_order = slot_order[::-1]
        for s1 in slot_order:
            if not self.is_slot_available(parent_id, s1):
                continue
            t1 = int(parent.openings[s1])
            for s2 in slot_order:
                if not self.is_slot_available(new_chunk.id, s2):
                    continue
                t2 = int(new_chunk.openings[s2])
                if self.is_compatible(s1, t1, s2, t2):
                    is_vertical = (t1 == 3 or t2 == 3)
                    parent_pos = self.map_positions.get(parent_id, (0,0))
                    new_pos = self.calculate_adjacent_position(parent_pos, s1, is_vertical)
                    self.map_positions[new_chunk.id] = new_pos
                    if is_vertical:
                        new_chunk.z_level = parent.z_level + (1 if t1 == 3 or t2 == 3 else -1)
                    self.add_connection(parent_id, s1, new_chunk.id, s2)
                    self.last_placed = new_chunk.id
                    return True
        return False

    def generate_new_map(self, entry_slot: Optional[int] = None) -> MapChunk:
        is_horizontal = entry_slot in (1, 3) if entry_slot is not None else random.random() < 0.5
        base_w = 76 if is_horizontal else 38
        base_h = 38 if is_horizontal else 76
        width = random.randint(base_w-14, base_w+22)
        height = random.randint(base_h-14, base_h+22)

        chunk = MapChunk(self.new_map_id(), width=width, height=height)
        chunk.name = f"Yellow Hall {len(self.maps)+1}"

        if self.generation_mode == "bsp":
            chunk.grid = [['#' for _ in range(width)] for _ in range(height)]
            ow = max(24, width - 16)
            oh = max(24, height - 16)
            ox = (width - ow) // 2
            oy = (height - oh) // 2
            for y in range(oy, oy + oh):
                for x in range(ox, ox + ow):
                    chunk.grid[y][x] = ' '
            for _ in range(10):
                rw = random.randint(5, min(10, ow - 14))
                rh = random.randint(5, min(9, oh - 14))
                if rw < 5 or rh < 5: continue
                max_rx = max(ox + 8, ox + ow - rw - 8)
                max_ry = max(oy + 8, oy + oh - rh - 8)
                rx = random.randint(ox + 8, max_rx)
                ry = random.randint(oy + 8, max_ry)
                for y in range(ry, ry + rh):
                    for x in range(rx, rx + rw):
                        if 0 <= y < height and 0 <= x < width:
                            chunk.grid[y][x] = ' '
        else:
            chunk.grid = [['#' if random.random() < 0.37 else ' ' for _ in range(width)] for _ in range(height)]
            for _ in range(10):
                new_grid = [row[:] for row in chunk.grid]
                for y in range(1, height-1):
                    for x in range(1, width-1):
                        walls = sum(1 for dy in [-1,0,1] for dx in [-1,0,1] if (dy or dx) and chunk.grid[y+dy][x+dx] == '#')
                        new_grid[y][x] = '#' if walls >= 5 else ' '
                chunk.grid = new_grid
            if is_horizontal:
                cy = height // 2
                for x in range(8, width-8):
                    for dy in range(-3, 4):
                        if 0 <= cy+dy < height:
                            chunk.grid[cy+dy][x] = ' '
                for _ in range(6):
                    jx = random.randint(15, width-15)
                    chunk.grid[cy-4][jx] = ' '
                    chunk.grid[cy+4][jx] = ' '
            else:
                cx = width // 2
                for y in range(8, height-8):
                    for dx in range(-3, 4):
                        if 0 <= cx+dx < width:
                            chunk.grid[y][cx+dx] = ' '
                for _ in range(6):
                    jy = random.randint(15, height-15)
                    chunk.grid[jy][cx-4] = ' '
                    chunk.grid[jy][cx+4] = ' '

        for s in range(7):
            if random.random() < 0.88:
                val = random.choices([1,2,3,4,5], weights=[27,33,21,11,8])[0]
                chunk.set_opening(s, val)

        for _ in range(17):
            x = random.randint(5, width-6)
            y = random.randint(5, height-6)
            if chunk.grid[y][x] == ' ':
                sym = random.choice(['!', '@', '?', 'E', 'T'])
                chunk.props.append({"x": x, "y": y, "symbol": sym, "color": "yellow"})

        if random.random() < self.params["spawn_enemy_rate"]:
            chunk.spawners.append({"type": "E", "x": width//2, "y": height//2, "rate": 0.6, "variants": ["basic", "fast"]})

        return chunk

    def parse_tmap(self, filepath: str) -> Optional[MapChunk]:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            if not lines:
                return None
            header = lines[0].strip()
            parts = header.split()
            openings = parts[0] if len(parts) > 0 else "0000000"
            width, height = 48, 24
            for p in parts:
                if 'x' in p:
                    try:
                        w, h = map(int, p.split('x'))
                        width, height = w, h
                        break
                    except:
                        pass
            chunk = MapChunk(self.new_map_id(), openings, width, height)
            chunk.name = os.path.basename(filepath)[:-5]
            for i, line in enumerate(lines[1:]):
                line = line.rstrip('\n')
                if line.strip() and not line.startswith(('type;', 'mapc', ';arcs')):
                    if i < height:
                        row = list(line[:width].ljust(width))
                        chunk.grid[i] = row
                else:
                    break
            return chunk
        except Exception as e:
            messagebox.showerror("Import Error", f"Failed to parse .tmap\n{str(e)}")
            return None

    def parse_mapd(self, filepath: str) -> Tuple[List[MapChunk], List[Dict]]:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            imports = []
            connections = []
            in_import = False
            in_connections = False
            for line in lines:
                line = line.strip()
                if line.startswith("import {"):
                    in_import = True
                    continue
                if in_import:
                    if line.endswith("}"):
                        in_import = False
                    imports.extend([x.strip('"') for x in line.replace('"', '').split(',') if x.strip()])
                if line.startswith(";connections::"):
                    in_connections = True
                    continue
                if in_connections and line:
                    connections.append(line)
            # For this version we return the list of map names and raw connection lines
            return imports, connections
        except Exception as e:
            messagebox.showerror("Import Error", f"Failed to parse .mapd\n{str(e)}")
            return [], []

    def expand(self, steps: int = 5):
        for _ in range(steps):
            free_maps = self.get_free_slot_maps()
            if not free_maps:
                break
            parent = self.last_placed if self.last_placed and self.last_placed in free_maps and random.random() < 0.67 else random.choice(free_maps)
            new_chunk = self.generate_new_map()
            self.add_map(new_chunk)
            if not self.try_connect(new_chunk, parent):
                for alt in free_maps:
                    if self.try_connect(new_chunk, alt):
                        break

    def add_map(self, chunk: MapChunk):
        self.maps[chunk.id] = chunk
        self.used_slots.setdefault(chunk.id, set())
        self.rebuild_positions()
        self.last_placed = chunk.id

    def to_dict(self) -> Dict:
        return {
            "version": "1.0",
            "seed": self.seed,
            "world_name": self.world_name,
            "world_lvl": self.world_lvl,
            "params": self.params,
            "maps": {mid: m.to_dict() for mid, m in self.maps.items()},
            "connections": self.connections,
            "arcs": self.arcs
        }

    @staticmethod
    def from_dict(data: Dict) -> 'World':
        w = World(data.get("seed", 42), data.get("world_name", "Loaded World"), data.get("world_lvl", "0"))
        w.params = data.get("params", w.params)
        w.connections = data.get("connections", [])
        w.arcs = data.get("arcs", {})
        for mdata in data.get("maps", {}).values():
            chunk = MapChunk.from_dict(mdata)
            w.maps[chunk.id] = chunk
            try:
                nid = int(chunk.id[1:])
                w.next_id = max(w.next_id, nid + 1)
            except:
                pass
        w.used_slots.clear()
        for conn in w.connections:
            w.used_slots.setdefault(conn["from_map"], set()).add(conn["from_slot"])
            w.used_slots.setdefault(conn["to_map"], set()).add(conn["to_slot"])
        w.rebuild_positions()
        if w.maps:
            w.last_placed = list(w.maps.keys())[-1]
        return w


class WorldBuilderApp:
    def __init__(self, root):
        self.root = root
        self.root.title("JAM.0.8 - Journey-Action-Mapper (Pixeled Backrooms)")
        self.world = World(seed=12345)
        self.zoom = 1.0
        self.pan_x = 0
        self.pan_y = 0
        self.selected_map = None
        self.current_z = 0
        self.pending_map = None   # For click-to-place mode
        self.setup_ui()
        self.new_world()

    def setup_ui(self):
        main_pane = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_pane.pack(fill=tk.BOTH, expand=True)

        left = ttk.Frame(main_pane, width=280)
        main_pane.add(left, weight=1)
        ttk.Label(left, text="JAM.0.8", font=("Arial", 16, "bold")).pack(pady=12)

        ttk.Button(left, text="New World", command=self.new_world).pack(fill=tk.X, padx=12, pady=6)
        ttk.Button(left, text="Add Random Map", command=self.add_random_map).pack(fill=tk.X, padx=12, pady=4)
        ttk.Button(left, text="Expand World (+5)", command=lambda: self.expand_world(5)).pack(fill=tk.X, padx=12, pady=4)
        ttk.Button(left, text="Insert .tmap", command=self.insert_tmap).pack(fill=tk.X, padx=12, pady=4)
        ttk.Button(left, text="Insert .mapd", command=self.insert_mapd).pack(fill=tk.X, padx=12, pady=4)
        ttk.Button(left, text="Force Adjacent Connect", command=self.force_adjacent_connect).pack(fill=tk.X, padx=12, pady=4)

        # Z Layer Tabs
        ttk.Separator(left).pack(fill=tk.X, padx=12, pady=12)
        ttk.Label(left, text="Z Layers (Tabs)", font=("Arial", 10, "bold")).pack(anchor="w", padx=12)
        self.z_tab_frame = ttk.Frame(left)
        self.z_tab_frame.pack(fill=tk.X, padx=12, pady=8)
        self.z_buttons = {}
        self.update_z_tabs()

        # View Controls
        ttk.Separator(left).pack(fill=tk.X, padx=12, pady=12)
        ttk.Label(left, text="View Controls", font=("Arial", 10, "bold")).pack(anchor="w", padx=12)
        ctrl_frame = ttk.Frame(left)
        ctrl_frame.pack(pady=8)
        ttk.Button(ctrl_frame, text="↑", width=3, command=lambda: self.pan_view(0, -80)).grid(row=0, column=1)
        ttk.Button(ctrl_frame, text="←", width=3, command=lambda: self.pan_view(-80, 0)).grid(row=1, column=0)
        ttk.Button(ctrl_frame, text="→", width=3, command=lambda: self.pan_view(80, 0)).grid(row=1, column=2)
        ttk.Button(ctrl_frame, text="↓", width=3, command=lambda: self.pan_view(0, 80)).grid(row=2, column=1)

        zoom_frame = ttk.Frame(left)
        zoom_frame.pack(pady=8)
        ttk.Button(zoom_frame, text="Zoom +", command=self.zoom_in).pack(side=tk.LEFT, padx=4)
        ttk.Button(zoom_frame, text="Zoom -", command=self.zoom_out).pack(side=tk.LEFT, padx=4)
        ttk.Button(zoom_frame, text="Reset View", command=self.reset_view).pack(side=tk.LEFT, padx=4)

        ttk.Separator(left).pack(fill=tk.X, padx=12, pady=12)

        ttk.Label(left, text="Generation Mode:").pack(anchor="w", padx=12)
        self.mode_var = tk.StringVar(value="bsp")
        ttk.Radiobutton(left, text="BSP - Halls + Cubicles", variable=self.mode_var, value="bsp", command=self.update_mode).pack(anchor="w", padx=24)
        ttk.Radiobutton(left, text="CA - Long Corridors", variable=self.mode_var, value="ca", command=self.update_mode).pack(anchor="w", padx=24)

        ttk.Separator(left).pack(fill=tk.X, padx=12, pady=12)
        ttk.Button(left, text="Save .livemap", command=self.save_livemap).pack(fill=tk.X, padx=12, pady=4)
        ttk.Button(left, text="Load .livemap", command=self.load_livemap).pack(fill=tk.X, padx=12, pady=4)

        canvas_frame = ttk.Frame(main_pane)
        main_pane.add(canvas_frame, weight=4)
        self.canvas = tk.Canvas(canvas_frame, bg="#0a0a0a", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<MouseWheel>", self.on_zoom)

        right = ttk.Frame(main_pane, width=300)
        main_pane.add(right, weight=1)
        ttk.Label(right, text="Inspector", font=("Arial", 12, "bold")).pack(pady=10)
        self.info_text = tk.Text(right, height=36, bg="#1a1a1a", fg="#eeeeee", font=("Consolas", 9))
        self.info_text.pack(fill=tk.BOTH, expand=True, padx=12, pady=12)

        self.status = ttk.Label(self.root, text="JAM.0.8 - Click to place imported maps • .mapd supported", relief=tk.SUNKEN, anchor=tk.W)
        self.status.pack(fill=tk.X)

    def update_mode(self):
        self.world.generation_mode = self.mode_var.get()

    def update_z_tabs(self):
        for widget in self.z_tab_frame.winfo_children():
            widget.destroy()
        self.z_buttons.clear()
        z_levels = sorted({chunk.z_level for chunk in self.world.maps.values()})
        for z in z_levels:
            btn = ttk.Button(self.z_tab_frame, text=f"Z{z}", command=lambda zz=z: self.switch_z(zz))
            btn.pack(side=tk.LEFT, padx=2)
            self.z_buttons[z] = btn
        if self.current_z in self.z_buttons:
            self.z_buttons[self.current_z].state(['pressed'])

    def switch_z(self, z: int):
        self.current_z = z
        self.update_z_tabs()
        self.redraw()

    def pan_view(self, dx: int, dy: int):
        self.pan_x += dx
        self.pan_y += dy
        self.redraw()

    def zoom_in(self):
        self.zoom *= 1.22
        self.redraw()

    def zoom_out(self):
        self.zoom *= 0.82
        self.redraw()

    def reset_view(self):
        self.pan_x = 0
        self.pan_y = 0
        self.zoom = 1.0
        self.redraw()

    def new_world(self):
        self.world = World(seed=random.randint(10000, 99999))
        self.world.world_name = "The Yellow Halls"
        self.world.world_lvl = "0"
        central = self.world.generate_new_map()
        self.world.add_map(central)
        self.pan_x = self.pan_y = 0
        self.zoom = 1.0
        self.current_z = 0
        self.pending_map = None
        self.update_z_tabs()
        self.redraw()

    def add_random_map(self):
        self.world.generation_mode = self.mode_var.get()
        chunk = self.world.generate_new_map()
        self.world.add_map(chunk)
        if self.world.maps:
            parent = list(self.world.maps.keys())[-1]
            self.world.try_connect(chunk, parent)
        self.update_z_tabs()
        self.redraw()

    def expand_world(self, steps: int):
        self.world.generation_mode = self.mode_var.get()
        self.world.expand(steps)
        self.update_z_tabs()
        self.redraw()

    def insert_tmap(self):
        path = filedialog.askopenfilename(filetypes=[("Pixeled Backrooms Map", "*.tmap")])
        if not path:
            return
        chunk = self.world.parse_tmap(path)
        if not chunk:
            return
        self.pending_map = chunk
        self.status.config(text="Click on canvas or existing map to place the imported .tmap")
        self.redraw()

    def insert_mapd(self):
        path = filedialog.askopenfilename(filetypes=[("Pixeled Backrooms Dictionary", "*.mapd")])
        if not path:
            return
        map_names, conn_lines = self.world.parse_mapd(path)
        if not map_names:
            return
        folder = filedialog.askdirectory(title="Select folder containing the .tmap files")
        if not folder:
            return
        loaded_maps = {}
        for name in map_names:
            tmap_path = os.path.join(folder, name + ".tmap")
            if os.path.exists(tmap_path):
                chunk = self.world.parse_tmap(tmap_path)
                if chunk:
                    loaded_maps[name] = chunk
            else:
                # Fallback prompt
                tmap_path = filedialog.askopenfilename(title=f"Select {name}.tmap", filetypes=[("tmap", "*.tmap")])
                if tmap_path:
                    chunk = self.world.parse_tmap(tmap_path)
                    if chunk:
                        loaded_maps[name] = chunk
        if not loaded_maps:
            return
        # Add all maps
        for chunk in loaded_maps.values():
            self.world.add_map(chunk)
        # Apply connections from .mapd (simple parsing)
        for line in conn_lines:
            # Very basic parsing - "mapA (slot) -> mapB (slot)"
            if "->" in line or "{" in line:
                try:
                    parts = line.replace("{", "").replace("}", "").split()
                    from_map = parts[0].strip('"')
                    to_map = parts[3].strip('"') if len(parts) > 3 else None
                    if from_map in loaded_maps and to_map in loaded_maps:
                        # Try to connect them
                        self.world.try_connect(loaded_maps[to_map], loaded_maps[from_map].id)
                except:
                    pass
        self.update_z_tabs()
        self.redraw()
        self.status.config(text=f"Imported {len(loaded_maps)} maps from .mapd")

    def force_adjacent_connect(self):
        if not self.world.last_placed or len(self.world.maps) < 2:
            return
        free = self.world.get_free_slot_maps()
        if not free:
            return
        new_id = random.choice(free)
        parent = self.world.last_placed
        chunk = self.world.maps[new_id]
        self.world.try_connect(chunk, parent)
        self.redraw()

    def on_canvas_click(self, event):
        # Handle pending map placement
        if self.pending_map:
            scale = 0.65 * self.zoom
            clicked_map = None
            for mid, (x, y) in self.world.map_positions.items():
                chunk = self.world.maps[mid]
                if chunk.z_level != self.current_z:
                    continue
                sx = self.pan_x + self.offset_x + x * scale
                sy = self.pan_y + self.offset_y + y * scale
                if sx <= event.x <= sx+122 and sy <= event.y <= sy+78:
                    clicked_map = mid
                    break
            if clicked_map:
                self.world.try_connect(self.pending_map, clicked_map)
            else:
                # Place at click position
                self.world.map_positions[self.pending_map.id] = (
                    (event.x - self.pan_x - self.offset_x) / scale,
                    (event.y - self.pan_y - self.offset_y) / scale
                )
            self.world.add_map(self.pending_map)
            self.pending_map = None
            self.update_z_tabs()
            self.redraw()
            self.status.config(text="Map placed")
            return

        # Normal selection
        scale = 0.65 * self.zoom
        for mid, (x, y) in self.world.map_positions.items():
            chunk = self.world.maps[mid]
            if chunk.z_level != self.current_z:
                continue
            sx = self.pan_x + self.offset_x + x * scale
            sy = self.pan_y + self.offset_y + y * scale
            if sx <= event.x <= sx+122 and sy <= event.y <= sy+78:
                self.selected_map = mid
                self.redraw()
                return
        self.selected_map = None
        self.redraw()

    def save_livemap(self):
        path = filedialog.asksaveasfilename(defaultextension=".livemap", filetypes=[("Live Map", "*.livemap")])
        if path:
            try:
                with open(path, 'w', encoding='utf-8') as f:
                    json.dump(self.world.to_dict(), f, indent=2)
                self.status.config(text=f"Saved → {path}")
            except Exception as e:
                messagebox.showerror("Save Error", str(e))

    def load_livemap(self):
        path = filedialog.askopenfilename(filetypes=[("Live Map", "*.livemap")])
        if path:
            try:
                with open(path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                self.world = World.from_dict(data)
                self.pan_x = self.pan_y = 0
                self.zoom = 1.0
                self.current_z = 0
                self.pending_map = None
                self.update_z_tabs()
                self.redraw()
                self.status.config(text=f"Loaded → {path}")
            except Exception as e:
                messagebox.showerror("Load Error", str(e))

    def redraw(self):
        self.canvas.delete("all")
        scale = 0.65 * self.zoom
        visible_maps = {mid: chunk for mid, chunk in self.world.maps.items() if chunk.z_level == self.current_z}

        for conn in self.world.connections:
            fm = conn["from_map"]
            tm = conn["to_map"]
            if fm in visible_maps and tm in visible_maps:
                x1, y1 = self.world.map_positions.get(fm, (0,0))
                x2, y2 = self.world.map_positions.get(tm, (0,0))
                sx1 = self.pan_x + self.offset_x + x1 * scale + 60
                sy1 = self.pan_y + self.offset_y + y1 * scale + 37
                sx2 = self.pan_x + self.offset_x + x2 * scale + 60
                sy2 = self.pan_y + self.offset_y + y2 * scale + 37
                is_wp = (int(self.world.maps[fm].openings[conn["from_slot"]]) == 5 or
                         int(self.world.maps[tm].openings[conn["to_slot"]]) == 5)
                color = "#ffaa00" if is_wp else "#88ccff"
                self.canvas.create_line(sx1, sy1, sx2, sy2, fill=color, width=5, arrow=tk.LAST)

        for mid, chunk in visible_maps.items():
            if mid not in self.world.map_positions:
                continue
            x, y = self.world.map_positions[mid]
            sx = self.pan_x + self.offset_x + x * scale
            sy = self.pan_y + self.offset_y + y * scale
            color = "#ffdd44" if mid == self.selected_map else "#3366dd"
            self.canvas.create_rectangle(sx, sy, sx+122, sy+78, fill=color, outline="#ffffff", width=3, tags=mid)
            self.canvas.create_text(sx+61, sy+26, text=chunk.name[:22], fill="black", font=("Arial", 9, "bold"))
            self.canvas.create_text(sx+61, sy+54, text=chunk.openings, fill="#111111", font=("Courier", 10))
            if chunk.waypoint_kind != "none":
                self.canvas.create_text(sx+61, sy+70, text=f"Z{chunk.z_level} {chunk.waypoint_kind.upper()}",
                                        fill="#00ffaa", font=("Arial", 8, "bold"))

        self.update_inspector()

    def on_zoom(self, event):
        factor = 1.22 if event.delta > 0 else 0.82
        self.zoom *= factor
        self.redraw()

    def update_inspector(self):
        self.info_text.delete(1.0, tk.END)
        if self.selected_map and self.selected_map in self.world.maps:
            c = self.world.maps[self.selected_map]
            info = f"Map: {c.id}\nName: {c.name}\nOpenings: {c.openings}\n"
            info += f"Size: {c.width}×{c.height}\nZ-Level: {c.z_level}\nWaypoint: {c.waypoint_kind}\n"
            info += f"Type: {c.type}\nProps: {len(c.props)} | Spawners: {len(c.spawners)}\n"
            used = len(self.world.used_slots.get(self.selected_map, set()))
            info += f"Used Slots: {used}/7\n"
            self.info_text.insert(tk.END, info)
        else:
            self.info_text.insert(tk.END, "JAM.0.8 Features:\n"
                                         "• Click on canvas or map to place imported .tmap\n"
                                         "• Insert .mapd dictionaries with connections\n"
                                         "• Z-layer tabs\n"
                                         "• Pan / Zoom controls\n\n"
                                         "Click maps to inspect.")

    @property
    def offset_x(self):
        return 90

    @property
    def offset_y(self):
        return 90


if __name__ == "__main__":
    root = tk.Tk()
    root.geometry("1620x940")
    root.minsize(1300, 800)
    app = WorldBuilderApp(root)
    root.mainloop()
