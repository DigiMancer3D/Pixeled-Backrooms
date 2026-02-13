import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import copy
import os
import re
import random
import json
from datetime import datetime
import numpy as np
import math
from collections import deque
import time

class WorldBuilder:
    def __init__(self, root):
        self.root = root
        self.root.title("Pixeled Backrooms - World Builder (Live Map Generator)")
        self.root.geometry("1400x900")
        # .udata
        self.udata_file = "JAM.udata"
        self.settings = self.load_udata()
        # Core data
        self.world = {
            "version": "1.0",
            "seed": random.randint(100000, 999999),
            "world_level": "0",
            "world_name": "The Yellow Halls",
            "params": {"spawn_enemy_rate": 0.35, "boss_chance": 0.05, "premade_percent": 0.3},
            "map_base_height": "1.0",
            "maps": {},
            "connections": [],
            "arcs": {}
        }
        self.map_counter = 1
        self.base_radius = 120
        self.zoom_level = 1.0
        self.center_distance = 2 * self.base_radius * math.cos(math.radians(22.5))
        self.direction_angles_deg = {1:270, 2:0, 3:90, 4:180, 5:225, 6:315, 7:45, 8:135}
        self.opposite_dir = {1:3, 3:1, 2:4, 4:2, 5:7, 7:5, 6:8, 8:6}
        self.z_priority = {7:0, 8:0, 1:1, 3:1, 5:2, 6:2, 0:3, 2:4, 4:4}

        # Diagonal unlock rules (7 slots)
        self.allow_map = {
            0: [4, 5],   # Top -> TL, TR
            1: [5, 6],   # Right -> TR, BR
            2: [6, 7],   # Bottom -> BR, BL
            3: [4, 7],   # Left -> TL, BL
            4: [4, 7],   # Inner-Left
            5: [4, 5, 6, 7],  # Inner-Center (all 4 diagonals)
            6: [5, 6],   # Inner-Right
        }

        self.map_positions = {}
        self.current_selected_map_id = None
        self.selected_center = None
        self.pan_offset_x = 0
        self.pan_offset_y = 0
        self.is_panning = False
        self.pan_start_x = 0
        self.pan_start_y = 0
        # UI
        self.main_vertical_paned = tk.PanedWindow(self.root, orient=tk.VERTICAL)
        self.main_vertical_paned.pack(fill=tk.BOTH, expand=True)
        upper_frame = tk.Frame(self.main_vertical_paned)
        self.main_vertical_paned.add(upper_frame)
        self.upper_paned = tk.PanedWindow(upper_frame, orient=tk.HORIZONTAL)
        self.upper_paned.pack(fill=tk.BOTH, expand=True)
        left_controls = tk.Frame(self.upper_paned, width=220)
        self.upper_paned.add(left_controls, minsize=220)
        tk.Label(left_controls, text="Generation Controls", font=("Arial", 12, "bold")).pack(pady=5)
        tk.Button(left_controls, text="New World", command=self.new_world).pack(fill=tk.X, padx=5, pady=2)
        tk.Button(left_controls, text="Auto-Expand (10)", command=lambda: self.auto_expand(10)).pack(fill=tk.X, padx=5, pady=2)
        tk.Button(left_controls, text="Generate Single", command=self.generate_single_map).pack(fill=tk.X, padx=5, pady=2)
        tk.Button(left_controls, text="Load Premade", command=self.load_premade_dict).pack(fill=tk.X, padx=5, pady=2)
        tk.Button(left_controls, text="Save .livemap", command=self.save_livemap).pack(fill=tk.X, padx=5, pady=2)
        tk.Button(left_controls, text="Load .livemap", command=self.load_livemap).pack(fill=tk.X, padx=5, pady=2)
        world_frame = tk.Frame(self.upper_paned)
        self.upper_paned.add(world_frame, minsize=700)
        self.world_canvas = tk.Canvas(world_frame, bg="#0a0a0a", highlightthickness=0)
        self.world_canvas.pack(fill=tk.BOTH, expand=True)
        self.world_canvas.bind("<ButtonPress-3>", self.start_pan)
        self.world_canvas.bind("<B3-Motion>", self.do_pan)
        self.world_canvas.bind("<ButtonRelease-3>", self.end_pan)
        self.world_canvas.bind("<Button-1>", self.on_world_click)
        self.world_canvas.bind("<Configure>", self.on_canvas_configure)
        self.zoom_frame = tk.Frame(world_frame)
        self.zoom_frame.place(relx=0.02, rely=0.85, anchor="sw")
        tk.Button(self.zoom_frame, text="0", width=3, command=self.zoom_fit).pack(side=tk.BOTTOM, pady=2)
        tk.Button(self.zoom_frame, text="-", width=3, command=self.zoom_out).pack(side=tk.BOTTOM, pady=2)
        tk.Button(self.zoom_frame, text="+", width=3, command=self.zoom_in).pack(side=tk.BOTTOM, pady=2)
        right_frame = tk.Frame(self.upper_paned, width=280)
        self.upper_paned.add(right_frame, minsize=280)
        tk.Label(right_frame, text="Selected Map Info", font=("Arial", 11, "bold")).pack(pady=5)
        tk.Label(right_frame, text="Name:").pack(anchor="w", padx=5)
        self.name_var = tk.StringVar()
        tk.Entry(right_frame, textvariable=self.name_var).pack(fill=tk.X, padx=5)
        tk.Label(right_frame, text="Openings (7 chars):").pack(anchor="w", padx=5)
        self.openings_var = tk.StringVar()
        tk.Entry(right_frame, textvariable=self.openings_var).pack(fill=tk.X, padx=5)
        tk.Button(right_frame, text="Apply Changes", command=self.apply_map_changes).pack(pady=8)
        self.map_info_text = tk.Text(right_frame, height=8)
        self.map_info_text.pack(fill=tk.X, padx=5, pady=5)
        tk.Label(right_frame, text="Arcs", font=("Arial", 11, "bold")).pack(pady=5)
        self.arc_listbox = tk.Listbox(right_frame)
        self.arc_listbox.pack(fill=tk.BOTH, expand=True, padx=5)
        self.arc_listbox.bind("<<ListboxSelect>>", self.edit_selected_arc)
        bottom_frame = tk.Frame(self.main_vertical_paned)
        self.main_vertical_paned.add(bottom_frame, minsize=280)
        self.bottom_paned = tk.PanedWindow(bottom_frame, orient=tk.HORIZONTAL)
        self.bottom_paned.pack(fill=tk.BOTH, expand=True)
        arc_frame = tk.Frame(self.bottom_paned)
        self.bottom_paned.add(arc_frame, minsize=500)
        tk.Label(arc_frame, text="Arc Builder").pack()
        self.arc_data_entry = tk.Text(arc_frame, height=12)
        self.arc_data_entry.pack(fill=tk.BOTH, expand=True)
        status_frame = tk.Frame(self.bottom_paned)
        self.bottom_paned.add(status_frame, minsize=200)
        self.status_label = tk.Label(status_frame, text="Ready")
        self.status_label.pack()
        self.root.after(150, self.load_pane_positions)
        self.new_world()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    # ==================== .udata ====================
    def load_udata(self):
        settings = {}
        if os.path.exists(self.udata_file):
            with open(self.udata_file, 'r') as f:
                lines = f.readlines()
            current_section = None
            for line in lines:
                line = line.strip()
                if line.startswith(':') and line.endswith(':'):
                    current_section = line[1:-1]
                    continue
                if current_section == 'JAM' and '=' in line:
                    key, value = line.split('=', 1)
                    settings[key.strip()] = value.strip()
        return settings

    def save_udata(self):
        try:
            lines = []
            if os.path.exists(self.udata_file):
                with open(self.udata_file, 'r') as f:
                    lines = f.readlines()
            with open(self.udata_file, 'w') as f:
                in_jam = False
                for line in lines:
                    if line.strip() == ':JAM:':
                        in_jam = True
                        continue
                    if in_jam and line.strip().startswith(':'):
                        in_jam = False
                    if not in_jam:
                        f.write(line)
                f.write(":JAM:\n")
                try:
                    pos = self.main_vertical_paned.sash_coord(0)[1] if len(self.main_vertical_paned.sash_coord(0)) > 0 else 600
                    f.write(f"JAM:pane_main_vertical_pos={pos}\n")
                except:
                    f.write("JAM:pane_main_vertical_pos=600\n")
                try:
                    pos = self.upper_paned.sash_coord(0)[0] if len(self.upper_paned.sash_coord(0)) > 0 else 220
                    f.write(f"JAM:pane_upper_horizontal_pos1={pos}\n")
                except:
                    f.write("JAM:pane_upper_horizontal_pos1=220\n")
                try:
                    pos = self.upper_paned.sash_coord(1)[0] if len(self.upper_paned.sash_coord(1)) > 0 else 1000
                    f.write(f"JAM:pane_upper_horizontal_pos2={pos}\n")
                except:
                    f.write("JAM:pane_upper_horizontal_pos2=1000\n")
                try:
                    pos = self.bottom_paned.sash_coord(0)[0] if len(self.bottom_paned.sash_coord(0)) > 0 else 500
                    f.write(f"JAM:pane_bottom_horizontal_pos1={pos}\n")
                except:
                    f.write("JAM:pane_bottom_horizontal_pos1=500\n")
                try:
                    pos = self.bottom_paned.sash_coord(1)[0] if len(self.bottom_paned.sash_coord(1)) > 0 else 900
                    f.write(f"JAM:pane_bottom_horizontal_pos2={pos}\n")
                except:
                    f.write("JAM:pane_bottom_horizontal_pos2=900\n")
        except Exception as e:
            print("udata save warning:", e)

    def load_pane_positions(self):
        try:
            if 'JAM:pane_main_vertical_pos' in self.settings:
                pos = int(self.settings['JAM:pane_main_vertical_pos'])
                self.main_vertical_paned.sash_place(0, 0, pos)
            if 'JAM:pane_upper_horizontal_pos1' in self.settings:
                pos = int(self.settings['JAM:pane_upper_horizontal_pos1'])
                self.upper_paned.sash_place(0, pos, 0)
            if 'JAM:pane_upper_horizontal_pos2' in self.settings:
                pos = int(self.settings['JAM:pane_upper_horizontal_pos2'])
                self.upper_paned.sash_place(1, pos, 0)
            if 'JAM:pane_bottom_horizontal_pos1' in self.settings:
                pos = int(self.settings['JAM:pane_bottom_horizontal_pos1'])
                self.bottom_paned.sash_place(0, pos, 0)
            if 'JAM:pane_bottom_horizontal_pos2' in self.settings:
                pos = int(self.settings['JAM:pane_bottom_horizontal_pos2'])
                self.bottom_paned.sash_place(1, pos, 0)
        except:
            pass

    # ==================== CENTERING & ZOOM ====================
    def on_canvas_configure(self, event):
        self.center_view()

    def center_view(self):
        if not self.map_positions:
            return
        xs = [p[0] for p in self.map_positions.values()]
        ys = [p[1] for p in self.map_positions.values()]
        minx, maxx = min(xs), max(xs)
        miny, maxy = min(ys), max(ys)
        content_w = (maxx - minx) * self.zoom_level + self.base_radius * 4 * self.zoom_level
        content_h = (maxy - miny) * self.zoom_level + self.base_radius * 4 * self.zoom_level
        canvas_w = self.world_canvas.winfo_width()
        canvas_h = self.world_canvas.winfo_height()
        self.pan_offset_x = (canvas_w - content_w) / 2 - minx * self.zoom_level
        self.pan_offset_y = (canvas_h - content_h) / 2 - miny * self.zoom_level
        self.draw_world_view()

    def apply_zoom(self, new_zoom):
        if not self.map_positions:
            self.zoom_level = new_zoom
            self.draw_world_view()
            return
        xs = [p[0] for p in self.map_positions.values()]
        ys = [p[1] for p in self.map_positions.values()]
        center_x = sum(xs) / len(xs)
        center_y = sum(ys) / len(ys)
        scale_factor = new_zoom / self.zoom_level
        for map_id in list(self.map_positions.keys()):
            cx, cy = self.map_positions[map_id]
            self.map_positions[map_id] = (
                center_x + (cx - center_x) * scale_factor,
                center_y + (cy - center_y) * scale_factor
            )
        self.zoom_level = new_zoom
        self.draw_world_view()
        if self.current_selected_map_id and self.current_selected_map_id in self.map_positions:
            self.selected_center = self.map_positions[self.current_selected_map_id]
        self.draw_world_view()

    def zoom_in(self):
        self.apply_zoom(self.zoom_level * 1.15)

    def zoom_out(self):
        self.apply_zoom(max(0.2, self.zoom_level / 1.15))

    def zoom_fit(self):
        if not self.map_positions:
            return
        xs = [p[0] for p in self.map_positions.values()]
        ys = [p[1] for p in self.map_positions.values()]
        minx, maxx = min(xs), max(xs)
        miny, maxy = min(ys), max(ys)
        w = maxx - minx + self.base_radius * 4
        h = maxy - miny + self.base_radius * 4
        canvas_w = self.world_canvas.winfo_width()
        canvas_h = self.world_canvas.winfo_height()
        scale_x = canvas_w / w
        scale_y = canvas_h / h
        self.apply_zoom(min(scale_x, scale_y) * 0.85)

    # ==================== PANNING ====================
    def start_pan(self, event):
        self.is_panning = True
        self.pan_start_x = event.x
        self.pan_start_y = event.y

    def do_pan(self, event):
        if self.is_panning:
            dx = event.x - self.pan_start_x
            dy = event.y - self.pan_start_y
            self.pan_offset_x += dx
            self.pan_offset_y += dy
            self.pan_start_x = event.x
            self.pan_start_y = event.y
            self.draw_world_view()

    def end_pan(self, event):
        self.is_panning = False

    # ==================== OCTAGON & DRAW ====================
    def get_octagon_points(self, cx, cy):
        points = []
        for i in range(8):
            angle_deg = 22.5 + i * 45
            angle_rad = math.radians(angle_deg)
            px = cx + self.base_radius * self.zoom_level * math.cos(angle_rad)
            py = cy + self.base_radius * self.zoom_level * math.sin(angle_rad)
            points.append((px, py))
        return points

    def point_in_polygon(self, x, y, poly):
        n = len(poly)
        inside = False
        p1x, p1y = poly[0]
        for i in range(n + 1):
            p2x, p2y = poly[i % n]
            if y > min(p1y, p2y):
                if y <= max(p1y, p2y):
                    if x <= max(p1x, p2x):
                        if p1y != p2y:
                            xinters = (y - p1y) * (p2x - p1x) / (p2y - p1y) + p1x
                        if p1x == p2x or x <= xinters:
                            inside = not inside
            p1x, p1y = p2x, p2y
        return inside

    def is_side_connected(self, map_id, side):
        for conn in self.world.get("connections", []):
            if (conn.get("from_id") == map_id and conn.get("from_side") == side) or \
               (conn.get("to_id") == map_id and conn.get("to_side") == side):
                return True
        return False

    def is_diagonal_allowed(self, map_id, side):
        if side < 4 or side > 7:
            return False
        openings_str = self.world["maps"][map_id].get("openings", "0000000").ljust(7, '0')
        if '5' in openings_str:
            return True
        allowed = set()
        for s in range(7):
            if openings_str[s] in ('3', '5'):
                allowed.update(self.allow_map.get(s, []))
        return side in allowed

    def draw_world_view(self):
        self.world_canvas.delete("all")
        sorted_maps = sorted(self.map_positions.items(), key=lambda item: self.z_priority.get(int(item[0].split('-')[-1]), 2))
        for map_id, (cx, cy) in sorted_maps:
            drawn_cx = cx + self.pan_offset_x
            drawn_cy = cy + self.pan_offset_y
            poly = self.get_octagon_points(drawn_cx, drawn_cy)
            base_z = float(self.world.get("map_base_height", 1.0))
            z_level = self.world["maps"][map_id].get("z_level", base_z)
            delta = z_level - base_z
            brightness = int(26 + delta * 35)
            r = g = b = max(0, min(255, brightness))
            if delta < 0:
                darkness = int(abs(delta) * 40)
                b = max(0, min(255, 26 - darkness))
                if b == 0:
                    r = max(0, min(255, 26 - darkness))
            if any(o == '5' for o in self.world["maps"][map_id].get("openings", "0000000")):
                r = min(255, r + 115)
            fill_color = f"#{r:02x}{g:02x}{b:02x}"
            color = "#00ff00" if map_id == self.current_selected_map_id else "#00aaaa"
            width = 7 if map_id == self.current_selected_map_id else 4
            self.world_canvas.create_polygon(poly, fill=fill_color, outline=color, width=width)

            openings = self.world["maps"][map_id].get("openings", "0000000").ljust(7, '0')
            inset = self.base_radius * self.zoom_level * 0.12
            for i in range(8):
                p1 = poly[i]
                p2 = poly[(i + 1) % 8]
                mx = (p1[0] + p2[0]) / 2
                my = (p1[1] + p2[1]) / 2
                dx = p2[0] - p1[0]
                dy = p2[1] - p1[1]
                length = math.hypot(dx, dy)
                ux = dx / length
                uy = dy / length
                sx = mx - ux * (length / 2 - inset)
                sy = my - uy * (length / 2 - inset)
                ex = mx + ux * (length / 2 - inset)
                ey = my + uy * (length / 2 - inset)

                if self.is_side_connected(map_id, i):
                    col = "dimgray"
                elif i < 4:  # cardinal sides use direct slot
                    val = openings[i]
                    if val == '0':
                        col = "red"
                    elif val == '4':
                        col = "#222222"
                    else:
                        col = "white"
                else:  # diagonal sides (no direct slot, only unlock rule)
                    if self.is_diagonal_allowed(map_id, i):
                        col = "white"
                    else:
                        col = "#222222"

                self.world_canvas.create_line(sx, sy, ex, ey, fill=col, width=5)

            z_val = self.world["maps"][map_id].get("z_level", 0.0)
            label_text = f"{map_id}\nZ:{z_val:.1f}\n{openings}"
            self.world_canvas.create_rectangle(
                drawn_cx - 62 * self.zoom_level, drawn_cy - 48 * self.zoom_level,
                drawn_cx + 62 * self.zoom_level, drawn_cy + 48 * self.zoom_level,
                fill="#000000", stipple="gray25")
            self.world_canvas.create_text(drawn_cx, drawn_cy, text=label_text, fill="#ffff00",
                                          font=("Arial", int(10 * self.zoom_level), "bold"), justify="center")

        # Ghost dashed - only allowed directions
        if self.current_selected_map_id and self.selected_center:
            sel_cx, sel_cy = self.selected_center
            openings_sel = self.world["maps"][self.current_selected_map_id].get("openings", "0000000").ljust(7, '0')
            for dir_num in range(1, 9):
                rad = math.radians(self.direction_angles_deg[dir_num])
                dx = self.center_distance * self.zoom_level * math.cos(rad)
                dy = self.center_distance * self.zoom_level * math.sin(rad)
                prop_cx = sel_cx + dx
                prop_cy = sel_cy + dy

                occupied = any(math.hypot(prop_cx - ecx, prop_cy - ecy) < self.base_radius * self.zoom_level * 1.3
                               for ecx, ecy in self.map_positions.values())
                if occupied:
                    continue

                from_side = dir_num - 1
                if dir_num <= 4:  # cardinal
                    val = openings_sel[from_side] if from_side < 7 else '0'
                    if val in ('0', '4'):
                        continue
                else:  # diagonal
                    if not self.is_diagonal_allowed(self.current_selected_map_id, from_side):
                        continue

                drawn_pc_x = prop_cx + self.pan_offset_x
                drawn_pc_y = prop_cy + self.pan_offset_y
                poly = self.get_octagon_points(drawn_pc_x, drawn_pc_y)
                self.world_canvas.create_polygon(poly, fill="", outline="#666666", width=3, dash=(12, 8))

    # ==================== CLICK & PLACEMENT ====================
    def on_world_click(self, event):
        for map_id, (cx, cy) in self.map_positions.items():
            drawn_cx = cx + self.pan_offset_x
            drawn_cy = cy + self.pan_offset_y
            poly = self.get_octagon_points(drawn_cx, drawn_cy)
            if self.point_in_polygon(event.x, event.y, poly):
                self.current_selected_map_id = map_id
                self.selected_center = (cx, cy)
                self.update_map_info()
                self.draw_world_view()
                return

        if self.current_selected_map_id and self.selected_center:
            sel_cx, sel_cy = self.selected_center
            openings = self.world["maps"][self.current_selected_map_id].get("openings", "0000000").ljust(7, '0')

            for dir_num in range(1, 9):
                rad = math.radians(self.direction_angles_deg[dir_num])
                dx = self.center_distance * self.zoom_level * math.cos(rad)
                dy = self.center_distance * self.zoom_level * math.sin(rad)
                prop_cx = sel_cx + dx
                prop_cy = sel_cy + dy
                drawn_pc_x = prop_cx + self.pan_offset_x
                drawn_pc_y = prop_cy + self.pan_offset_y
                poly = self.get_octagon_points(drawn_pc_x, drawn_pc_y)

                if self.point_in_polygon(event.x, event.y, poly):
                    from_side = dir_num - 1

                    if dir_num <= 4:  # cardinal
                        exit_val = openings[from_side] if from_side < 7 else '0'
                        if exit_val in ('0', '4'):
                            self.show_invalid_flash(drawn_pc_x, drawn_pc_y)
                            return
                    else:  # diagonal
                        if not self.is_diagonal_allowed(self.current_selected_map_id, from_side):
                            self.show_invalid_flash(drawn_pc_x, drawn_pc_y)
                            return

                    occupied = any(math.hypot(prop_cx - ecx, prop_cy - ecy) < self.base_radius * self.zoom_level * 1.3
                                   for ecx, ecy in self.map_positions.values())
                    if occupied:
                        return

                    new_id = f"m{self.map_counter:03d}-{dir_num}"
                    self.map_counter += 1

                    from_side = dir_num - 1
                    to_side = self.opposite_dir[dir_num] - 1
                    self.world["connections"].append({
                        "from_id": self.current_selected_map_id,
                        "from_side": from_side,
                        "to_id": new_id,
                        "to_side": to_side
                    })

                    origin_z = self.world["maps"][self.current_selected_map_id].get("z_level", float(self.world["map_base_height"]))
                    if dir_num in [5, 6]:
                        new_z = origin_z + 1
                    elif dir_num in [7, 8]:
                        new_z = origin_z - 1
                    else:
                        new_z = origin_z

                    # Entry on new map (7 slots)
                    arrival_dir = self.opposite_dir[dir_num]
                    entry_openings = list("2120100")
                    if arrival_dir <= 4:
                        entry_side = [2, 3, 0, 1][arrival_dir-1]
                        entry_openings[entry_side] = random.choice("124")
                    else:
                        entry_side = 5  # inside-center for Z connections
                        entry_openings[entry_side] = "3"

                    self.generate_single_map(map_id=new_id, cx=prop_cx, cy=prop_cy, openings="".join(entry_openings), z_level=new_z)
                    self.current_selected_map_id = new_id
                    self.selected_center = (prop_cx, prop_cy)
                    self.update_map_info()
                    self.draw_world_view()
                    self.show_success_flash(drawn_pc_x, drawn_pc_y)
                    return

    def show_invalid_flash(self, cx, cy):
        poly = self.get_octagon_points(cx, cy)
        flash = self.world_canvas.create_polygon(poly, fill="#ff0000", stipple="gray50", outline="")
        self.root.after(200, lambda: self.world_canvas.delete(flash))

    def show_success_flash(self, cx, cy):
        poly = self.get_octagon_points(cx, cy)
        flash = self.world_canvas.create_polygon(poly, fill="#00ff00", stipple="gray50", outline="")
        self.root.after(200, lambda: self.world_canvas.delete(flash))

    # ==================== GENERATION ====================
    def generate_single_map(self, openings="2120100", map_id=None, cx=None, cy=None, z_level=None):
        width, height = 48, 24
        grid = np.full((height, width), ' ', dtype='<U1')
        for y in range(height):
            for x in range(width):
                if random.random() < 0.44:
                    grid[y, x] = '#'
        for _ in range(5):
            new_grid = grid.copy()
            for y in range(1, height-1):
                for x in range(1, width-1):
                    walls = sum(1 for dy in [-1,0,1] for dx in [-1,0,1] if grid[y+dy, x+dx] == '#')
                    new_grid[y, x] = '#' if walls >= 5 else ' '
            grid = new_grid
        props = []
        for _ in range(random.randint(8, 18)):
            x = random.randint(4, width-5)
            y = random.randint(4, height-5)
            if grid[y, x] == ' ':
                sym = random.choice(['!', '?', 'E', 'W', 'L', 'H', 'R', '@'])
                grid[y, x] = sym
                props.append({"x": x, "y": y, "symbol": sym})
        if map_id is None:
            map_id = f"m{self.map_counter:03d}-0"
            self.map_counter += 1
        cx = 800 if cx is None else cx
        cy = 500 if cy is None else cy
        if z_level is None:
            z_level = float(self.world.get("map_base_height", 1.0))
        self.world["maps"][map_id] = {
            "id": map_id,
            "name": f"Level {self.map_counter-1}",
            "openings": openings,
            "width": width,
            "height": height,
            "grid": [list(row) for row in grid],
            "props": props,
            "spawners": [{"type": "E", "rate": 0.35}],
            "arc_ids": [],
            "z_level": z_level
        }
        self.map_positions[map_id] = (cx, cy)
        self.status_label.config(text=f"Generated {map_id}")
        self.draw_world_view()

    def auto_expand(self, steps=10):
        for _ in range(steps):
            if not self.current_selected_map_id:
                self.generate_single_map()
                continue
            openings = self.world["maps"][self.current_selected_map_id].get("openings", "0000000").ljust(7, '0')
            possible_dirs = []
            for d in range(1,9):
                rad = math.radians(self.direction_angles_deg[d])
                prop_cx = self.selected_center[0] + self.center_distance * self.zoom_level * math.cos(rad)
                prop_cy = self.selected_center[1] + self.center_distance * self.zoom_level * math.sin(rad)
                occupied = any(math.hypot(prop_cx - ecx, prop_cy - ecy) < self.base_radius * self.zoom_level * 1.3
                               for ecx, ecy in self.map_positions.values())
                if occupied:
                    continue
                from_side = d - 1
                if d <= 4:
                    val = openings[from_side] if from_side < 7 else '0'
                    if val in ('0', '4'):
                        continue
                else:
                    if not self.is_diagonal_allowed(self.current_selected_map_id, from_side):
                        continue
                possible_dirs.append(d)

            if possible_dirs:
                dir_num = random.choice(possible_dirs)
                rad = math.radians(self.direction_angles_deg[dir_num])
                prop_cx = self.selected_center[0] + self.center_distance * self.zoom_level * math.cos(rad)
                prop_cy = self.selected_center[1] + self.center_distance * self.zoom_level * math.sin(rad)
                new_id = f"m{self.map_counter:03d}-{dir_num}"
                self.map_counter += 1

                from_side = dir_num - 1
                to_side = self.opposite_dir[dir_num] - 1
                self.world["connections"].append({
                    "from_id": self.current_selected_map_id,
                    "from_side": from_side,
                    "to_id": new_id,
                    "to_side": to_side
                })

                origin_z = self.world["maps"][self.current_selected_map_id].get("z_level", float(self.world["map_base_height"]))
                if dir_num in [5, 6]:
                    new_z = origin_z + 1
                elif dir_num in [7, 8]:
                    new_z = origin_z - 1
                else:
                    new_z = origin_z

                arrival_dir = self.opposite_dir[dir_num]
                entry_openings = list("2120100")
                if arrival_dir <= 4:
                    entry_side = [2, 3, 0, 1][arrival_dir-1]
                    entry_openings[entry_side] = random.choice("124")
                else:
                    entry_side = 5
                    entry_openings[entry_side] = "3"

                self.generate_single_map(map_id=new_id, cx=prop_cx, cy=prop_cy, openings="".join(entry_openings), z_level=new_z)
                self.current_selected_map_id = new_id
                self.selected_center = (prop_cx, prop_cy)
                self.draw_world_view()

    def apply_map_changes(self):
        if not self.current_selected_map_id:
            return
        name = self.name_var.get().strip()
        openings = self.openings_var.get().strip().ljust(7, '0')[:7]
        if name:
            self.world["maps"][self.current_selected_map_id]["name"] = name
        self.world["maps"][self.current_selected_map_id]["openings"] = openings
        self.draw_world_view()
        self.update_map_info()
        self.status_label.config(text="Map data updated")

    def update_map_info(self):
        self.map_info_text.delete("1.0", tk.END)
        if self.current_selected_map_id:
            data = self.world["maps"][self.current_selected_map_id]
            self.name_var.set(data.get("name", ""))
            self.openings_var.set(data.get("openings", "0000000"))
            info = f"ID: {data['id']}\nSize: {data['width']}x{data['height']}\nProps: {len(data.get('props',[]))}\nZ: {data.get('z_level', 0.0)}"
            self.map_info_text.insert("1.0", info)

    def save_livemap(self):
        file = filedialog.asksaveasfilename(defaultextension=".livemap", filetypes=[("Live Map", "*.livemap")])
        if file:
            save_data = self.world.copy()
            save_data["map_positions"] = self.map_positions
            with open(file, 'w') as f:
                json.dump(save_data, f, indent=2)
            messagebox.showinfo("Saved", f"Saved to {file}")

    def load_livemap(self):
        file = filedialog.askopenfilename(filetypes=[("Live Map", "*.livemap")])
        if file:
            with open(file, 'r') as f:
                loaded = json.load(f)
            self.world = {k: v for k, v in loaded.items() if k != "map_positions"}
            self.map_positions = loaded.get("map_positions", {})

            if isinstance(self.world.get("connections"), list) and self.world["connections"] and isinstance(self.world["connections"][0], str):
                self.world["connections"] = []

            if self.map_positions:
                first = next(iter(self.map_positions))
                self.current_selected_map_id = first
                self.selected_center = self.map_positions[first]
            self.draw_world_view()
            self.update_map_info()

    def load_premade_dict(self):
        messagebox.showinfo("Premade", "Coming soon")

    def new_world(self):
        self.world = {
            "version": "1.0",
            "seed": random.randint(100000, 999999),
            "world_level": "0",
            "world_name": "The Yellow Halls",
            "params": {"spawn_enemy_rate": 0.35, "boss_chance": 0.05, "premade_percent": 0.3},
            "map_base_height": "1.0",
            "maps": {}, "connections": [], "arcs": {}
        }
        self.map_counter = 1
        self.map_positions = {}
        self.pan_offset_x = 0
        self.pan_offset_y = 0
        self.zoom_level = 1.0
        self.generate_single_map(openings="2120100", map_id="m001-0", cx=800, cy=500, z_level=float(self.world["map_base_height"]))
        self.current_selected_map_id = "m001-0"
        self.selected_center = (800, 500)
        self.update_map_info()
        self.status_label.config(text=f"New world - Seed: {self.world['seed']}")

    def edit_selected_arc(self, event=None):
        messagebox.showinfo("Arc", "Editor coming soon")

    def on_close(self):
        self.save_udata()
        if messagebox.askyesno("Exit", "Save .livemap before closing?"):
            self.save_livemap()
        self.root.destroy()

if __name__ == "__main__":
    root = tk.Tk()
    app = WorldBuilder(root)
    root.mainloop()
