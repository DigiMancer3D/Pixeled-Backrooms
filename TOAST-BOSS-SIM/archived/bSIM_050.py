# bSIM_049.py
# Full working Python3-tkinter game
# Version 049 - New updates after this line with newest updates at top -
# • All previous fixes preserved
# Run with: python3 bSIM_049.py

import tkinter as tk
from tkinter import filedialog
import json
import random
import math
import os
import platform
import ctypes
from datetime import datetime
import time

class bSIM:  # bSIM === Boss Simulator (base of program)
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Boss Sim - TOAST Engine")
        self.canvas = tk.Canvas(self.root, width=1200, height=800, bg="#1a1a1a", highlightthickness=0)
        self.canvas.pack()

        # Platform detection + Linux X11 setup
        self.platform = platform.system()
        self.clip_supported = (self.platform == "Windows")
        self.x11_lib = None
        self.x11_display = None
        if self.platform == "Linux":
            try:
                self.x11_lib = ctypes.CDLL("libX11.so.6")
            except:
                self.x11_lib = None

        # Safe sprite (failsafe needed)
        self.safe_img = None
        try:
            if os.path.exists("sprites/safe.png"):
                self.safe_img = tk.PhotoImage(file="sprites/safe.png").subsample(2)
        except:
            pass # failsafe needed to draw square with bordered square inside to resemble a safe

        # Arrow sprites (with failsafe)
        self.arrow_imgs = {}
        directions = ['top', 'topright', 'right', 'bottomright', 'bottom', 'bottomleft', 'left', 'topleft']
        for d in directions:
            path = f"sprites/{d}_arrow.png"
            if os.path.exists(path):
                self.arrow_imgs[d] = tk.PhotoImage(file=path)
            else:
                self.arrow_imgs[d] = None

        # TLA row title images (Sprites/)
        self.tla_imgs = {}
        tla_files = ["weapons_tla.png", "armor_tla.png", "usables_tla.png", "skills_tla.png"]
        for i, fname in enumerate(tla_files):
            path = f"Sprites/{fname}"
            if os.path.exists(path):
                self.tla_imgs[i] = tk.PhotoImage(file=path)
            else:
                self.tla_imgs[i] = None

        # UI PNGs (Sprites/)
        self.bpack_img = None
        if os.path.exists("Sprites/bpack.png"):
            self.bpack_img = tk.PhotoImage(file="Sprites/bpack.png")
        self.equip_img = None
        if os.path.exists("Sprites/equip.png"):
            self.equip_img = tk.PhotoImage(file="Sprites/equip.png")
        self.i_tab_img = None
        if os.path.exists("Sprites/i_tab.png"):
            self.i_tab_img = tk.PhotoImage(file="Sprites/i_tab.png")
        self.s_tab_img = None
        if os.path.exists("Sprites/s_tab.png"):
            self.s_tab_img = tk.PhotoImage(file="Sprites/s_tab.png")
        self.i_tab_open_img = None
        if os.path.exists("Sprites/i_tab_open.png"):
            self.i_tab_open_img = tk.PhotoImage(file="Sprites/i_tab_open.png")
        self.s_tab_open_img = None
        if os.path.exists("Sprites/s_tab_open.png"):
            self.s_tab_open_img = tk.PhotoImage(file="Sprites/s_tab_open.png")

        # Game state
        self.state = "TITLE"
        self.selected_char_type = None
        self.selected_char_color = None
        self.selected_damage_type = None
        self.custom_preview = None
        self.custom_image = None
        self.player = None
        self.obstacles = []
        self.safes = []
        self.windows = []
        self.arena_radius = 5000
        self.arena_points = self.calculate_octagon(0, 0, self.arena_radius)
        self.camera_x = 0.0
        self.camera_y = 0.0
        self.camera_target_x = 0.0
        self.camera_target_y = 0.0
        self.scale = 1.0
        self.camera_yaw = 0.0
        self.camera_pitch = 0.0
        self.target_yaw = 0.0
        self.target_pitch = 0.0
        self.bob = 0.0
        self.time = 0.0
        self.skill_points = 0.0
        self.history = []
        self.mouse_screen_x = 600
        self.mouse_screen_y = 400
        self.last_mouse_x = 600
        self.last_mouse_y = 400
        self.right_drag_start = None
        self.target_x = None
        self.target_y = None
        self.current_mode = None
        self.inspect_center_x = 0.0
        self.inspect_center_y = 0.0
        self.inspect_timer = 0
        self.menu_open = False
        self.safe_menu_open = False
        self.settings_open = False
        self.skilltree_open = False
        self.fpv_mode = False
        self.pause_open = False
        self.selected = True
        self.keys = set()
        self.mouse_warped = False
        self.is_dragging = False
        self.right_hold_start = None
        self.menu_type = "normal"  # or "directional"
        self.persistent_scroll = None
        self.edge_scroll_dir = None
        self.tla_open = [True] * 4
        self.safe_offset = 0

        # HUD state
        self.groups = [["Player"]]
        self.group_names = ["0"]
        self.current_group_index = 0
        self.group_scroll_offset = 0
        self.hotbar = [None] * 9
        self.loot_rows = [
            ["Sword", "Fireball", "Ice Blast"],
            ["Leather Armor", "Mage Robe", "Ancient Spellbook"],
            ["Health", "Mana", "Key"],
            ["Dash", "Aura Heal", "Summon Minion"]
        ]
        self.loot_offsets = [0] * 4
        self.inventory_drawer_open = False
        self.safe_drawer_open = False
        self.dragging_item = None
        self.dragging_from_tla = None
        self.backpack_offset = 0
        self.hud_hover = False
        self.last_right_click = 0.0
        self.selected_safe = None
        self.highlighted_slot = None

        # Arrow positions – ! PERFECTLY ALIGNED !
        self.arrow_positions = {
            'top': (600, 25),
            'topright': (1175, 25),
            'right': (1175, 400),
            'bottomright': (1175, 775),
            'bottom': (600, 775),
            'bottomleft': (25, 775),
            'left': (25, 400),
            'topleft': (25, 25)
        }
        self.arrow_size = 25
        self.dxdy = {
            'top': (0, -8),
            'topright': (8, -8),
            'right': (8, 0),
            'bottomright': (8, 8),
            'bottom': (0, 8),
            'bottomleft': (-8, 8),
            'left': (-8, 0),
            'topleft': (-8, -8)
        }

        # Bindings
        self.canvas.bind("<Button-1>", self.on_left_click)
        self.canvas.bind("<ButtonRelease-1>", self.on_left_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        self.canvas.bind("<B3-Motion>", self.on_right_drag)
        self.canvas.bind("<ButtonRelease-3>", self.on_right_release)
        self.canvas.bind("<Motion>", self.on_motion)
        self.root.bind("<KeyPress>", self.key_down)
        self.root.bind("<KeyRelease>", self.key_up)
        self.root.bind("<Escape>", self.handle_escape)
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

        self.load_crumbs()
        self.game_update()
        self.root.mainloop()

    def calculate_octagon(self, cx, cy, r):
        points = []
        for i in range(8):
            ang = i * (2 * math.pi / 8)
            points.append((cx + r * math.cos(ang), cy + r * math.sin(ang)))
        return points

    def screen_to_world(self, sx, sy):
        wx = self.camera_x + (sx - 600) / self.scale
        wy = self.camera_y + (sy - 400) / self.scale
        return wx, wy

    def world_to_screen(self, wx, wy, wz=0):
        dx = wx - self.camera_x
        dy = wy - self.camera_y
        if self.fpv_mode:
            cos_y = math.cos(-self.camera_yaw)
            sin_y = math.sin(-self.camera_yaw)
            rx = dx * cos_y - dy * sin_y
            ry = dx * sin_y + dy * cos_y
            cos_p = math.cos(self.camera_pitch)
            sin_p = math.sin(self.camera_pitch)
            final_depth = ry * cos_p - (wz - 80) * sin_p
            final_height = ry * sin_p + (wz - 80) * cos_p
            if final_depth < 30: final_depth = 30
            scale_p = 920 / final_depth
            sx = 600 + rx * scale_p
            sy = 400 - final_height * scale_p + self.bob
        else:
            sx = 600 + dx * self.scale
            sy = 400 + dy * self.scale
        return sx, sy

    def is_near_player(self, wx, wy):
        if not self.player: return False
        return math.hypot(wx - self.player["x"], wy - self.player["y"]) < 35

    def get_safe_at(self, sx, sy):
        if not self.safes: return None
        wx, wy = self.screen_to_world(sx, sy)
        for safe in self.safes:
            if math.hypot(wx - safe["x"], wy - safe["y"]) < 35:
                return safe
        return None

    def clamp_to_arena(self, x, y):
        r = math.hypot(x, y)
        max_r = self.arena_radius * 0.93
        if r > max_r:
            return x * max_r / r, y * max_r / r
        return x, y

    def collides(self, x, y):
        r = 22
        for obs in self.obstacles:
            left = obs["x"] - obs["w"]/2 - r
            right = obs["x"] + obs["w"]/2 + r
            top = obs["y"] - obs["h"]/2 - r
            bottom = obs["y"] + obs["h"]/2 + r
            if left < x < right and top < y < bottom:
                return True
        return False

    def load_crumbs(self):
        if os.path.exists("bSIM.crumbs"):
            try:
                with open("bSIM.crumbs", "r") as f:
                    data = json.load(f)
                    self.history = data.get("history", [])[-3:]
            except:
                self.history = []

    def save_crumbs(self):
        if not self.player: return
        header = {"user_id": "player", "char_unique_ID": self.player["id"],
                  "coord": [round(self.player["x"], 1), round(self.player["y"], 1)],
                  "data_array": [self.player.get("level", 1), self.player.get("kills", 0), round(self.skill_points, 1)]}
        map_sample = [{"x": round(o["x"]), "y": round(o["y"]), "type": "cubicle"} for o in self.obstacles[:8]]
        details = {"report": f"Backrooms run {datetime.now().strftime('%Y-%m-%d %H:%M')}"}
        new_entry = {"score": int(self.skill_points * 10) + self.player.get("kills", 0),
                     "kills": self.player.get("kills", 0), "level": self.player.get("level", 1),
                     "timestamp": datetime.now().strftime("%Y-%m-%d")}
        new_history = (self.history + [new_entry])[-3:]
        data = {"header": header, "map": map_sample, "details": details, "history": new_history}
        with open("bSIM.crumbs", "w") as f:
            json.dump(data, f, indent=2)

    def start_new_game(self):
        if not self.selected_char_type: return
        self.state = "GAME"
        self.player = {
            "id": "p001",
            "type": self.selected_char_type,
            "color": self.selected_char_color or "#ff0000",
            "damage_type": self.selected_damage_type or "Physical/Bleeding",
            "name": "Explorer",
            "x": 0.0,
            "y": 0.0,
            "level": 1,
            "kills": 0,
            "body": 0,
            "combat": 0,
            "aura": 0,
            "health": 100.0,
            "max_health": 100.0,
            "stamina": 100.0,
            "max_stamina": 100.0,
            "custom_image": self.custom_image,
            "custom_preview": self.custom_preview,
            "ownership": "User_Owned",
            "backpack": ["Health Potion", "Mana Potion"],
            "equip": [None] * 6,
            "chest": []
        }
        self.reset_game_variables()
        self.generate_arena()
        self.root.config(cursor="none")
        if self.clip_supported:
            self.clip_cursor(True)
        self.scale = 1200 / 1200
        self.camera_target_x = self.camera_x
        self.camera_target_y = self.camera_y

    def reset_game_variables(self):
        self.target_x = None
        self.target_y = None
        self.current_mode = None
        self.inspect_center_x = 0.0
        self.inspect_center_y = 0.0
        self.inspect_timer = 0
        self.menu_open = False
        self.safe_menu_open = False
        self.settings_open = False
        self.skilltree_open = False
        self.fpv_mode = False
        self.pause_open = False
        self.skill_points = 0.0
        self.camera_yaw = 0.0
        self.camera_pitch = 0.0
        self.target_yaw = 0.0
        self.target_pitch = 0.0
        self.bob = 0.0
        self.last_mouse_x = 600
        self.last_mouse_y = 400
        self.mouse_warped = False
        self.selected = True
        self.camera_target_x = 0.0
        self.camera_target_y = 0.0
        self.custom_image = None
        self.custom_preview = None
        self.group_scroll_offset = 0
        self.inventory_drawer_open = False
        self.safe_drawer_open = False
        self.dragging_item = None
        self.dragging_from_tla = None
        self.backpack_offset = 0
        self.hotbar = [None] * 9
        self.hud_hover = False
        self.selected_safe = None
        self.last_right_click = 0.0
        self.is_dragging = False
        self.right_hold_start = None
        self.menu_type = "normal"
        self.persistent_scroll = None
        self.edge_scroll_dir = None
        self.tla_open = [True] * 4
        self.safe_offset = 0

    def generate_arena(self):
        self.obstacles = []
        self.windows = []
        self.safes = []
        for _ in range(20):
            ox = random.uniform(-self.arena_radius * 0.85, self.arena_radius * 0.85)
            oy = random.uniform(-self.arena_radius * 0.85, self.arena_radius * 0.85)
            ow = random.uniform(60, 240)
            oh = random.uniform(60, 200)
            height = random.randint(80, 240) if random.random() < 0.5 else 55
            self.obstacles.append({"x": ox, "y": oy, "w": ow, "h": oh, "height": height, "color": "#555555"})
        for _ in range(12):
            ox = random.uniform(-self.arena_radius * 0.8, self.arena_radius * 0.8)
            oy = random.uniform(-self.arena_radius * 0.8, self.arena_radius * 0.8)
            self.obstacles.append({"x": ox, "y": oy, "w": 40, "h": 40, "height": 30, "color": "#444444"})
        for _ in range(6):
            hx = random.uniform(-self.arena_radius * 0.7, self.arena_radius * 0.7)
            hy = random.uniform(-self.arena_radius * 0.7, self.arena_radius * 0.7)
            self.obstacles.append({"x": hx, "y": hy, "w": 90, "h": 90, "height": 0, "color": "#1a1a1a"})
        for _ in range(30):
            wx = random.choice([-self.arena_radius*0.92, self.arena_radius*0.92])
            wy = random.uniform(-self.arena_radius*0.85, self.arena_radius*0.85)
            self.windows.append((wx, wy))
        for _ in range(4):
            sx = random.uniform(-self.arena_radius * 0.6, self.arena_radius * 0.6)
            sy = random.uniform(-self.arena_radius * 0.6, self.arena_radius * 0.6)
            self.safes.append({"x": sx, "y": sy, "inventory": [], "owner": "System_Owned", "hits_left": 9, "trapped": False})

    # ==================== CROSS-PLATFORM MOUSE LOCK ====================
    def warp_cursor_to_center(self):
        cx = self.canvas.winfo_rootx() + 600
        cy = self.canvas.winfo_rooty() + 400
        if self.platform == "Windows":
            try:
                ctypes.windll.user32.SetCursorPos(cx, cy)
            except:
                pass
        elif self.platform == "Linux" and self.x11_lib:
            try:
                if not self.x11_display:
                    self.x11_display = self.x11_lib.XOpenDisplay(None)
                if self.x11_display:
                    root = self.x11_lib.XDefaultRootWindow(self.x11_display)
                    self.x11_lib.XWarpPointer(self.x11_display, 0, root, 0, 0, 0, 0, cx, cy)
                    self.x11_lib.XFlush(self.x11_display)
            except:
                pass
        else:
            self.root.after(1, lambda: self.canvas.event_generate("<Motion>", x=600, y=400))

    def clip_cursor(self, enable=True):
        if not self.clip_supported:
            return
        try:
            if enable:
                left = self.canvas.winfo_rootx()
                top = self.canvas.winfo_rooty()
                right = left + 1200
                bottom = top + 800
                rect = ctypes.wintypes.RECT(left, top, right, bottom)
                ctypes.windll.user32.ClipCursor(ctypes.byref(rect))
            else:
                ctypes.windll.user32.ClipCursor(None)
        except:
            pass
    # =================================================================

    def is_mouse_in_hud(self, x, y):
        if 40 <= x <= 340 and 30 <= y <= 580: return True
        if self.inventory_drawer_open and 30 <= x <= 300 and 350 <= y <= 520: return True
        if self.safe_drawer_open and 30 <= x <= 300 and 350 <= y <= 520: return True
        if 650 <= y <= 740 and 180 <= x <= 1020: return True
        if 900 <= x <= 1180 and 30 <= y <= 390: return True
        if 20 <= x <= 220 and 560 <= y <= 760: return True
        if 950 <= x <= 1150 and 580 <= y <= 780: return True
        return False

    def is_near_hud(self, x, y):
        if self.is_mouse_in_hud(x, y): return True
        if (x < 64 or x > 1136) or (y < 30 or y > 770): return True
        return False

    def on_motion(self, event):
        self.hud_hover = self.is_mouse_in_hud(event.x, event.y)
        if self.state == "GAME" and self.fpv_mode and not self.pause_open:
            if self.mouse_warped:
                self.mouse_warped = False
                return
            delta_x = event.x - 600
            delta_y = event.y - 400
            if abs(delta_x) > 4:
                self.target_yaw -= delta_x * 0.000015
            if abs(delta_y) > 4:
                self.target_pitch += delta_y * 0.00000095
            self.target_pitch = max(-33, min(53, self.target_pitch))
            self.mouse_warped = True
            self.root.after(0, self.warp_cursor_to_center)
            return
        self.mouse_screen_x = event.x
        self.mouse_screen_y = event.y

        # EDGE ARROW HOVER
        self.edge_scroll_dir = None
        for d, pos in self.arrow_positions.items():
            if (pos[0] - self.arrow_size < event.x < pos[0] + self.arrow_size and
                pos[1] - self.arrow_size < event.y < pos[1] + self.arrow_size):
                self.edge_scroll_dir = d
                break

        if self.is_dragging:
            if not self.fpv_mode and not self.menu_open and not self.safe_menu_open and not self.pause_open and not self.hud_hover and not self.is_near_hud(event.x, event.y):
                edge = 36
                if event.x < edge: self.camera_target_x -= 8
                elif event.x > 1200 - edge: self.camera_target_x += 8
                if event.y < edge: self.camera_target_y -= 8
                elif event.y > 800 - edge: self.camera_target_y += 8
            return
        if not self.fpv_mode and not self.menu_open and not self.safe_menu_open and not self.pause_open and not self.hud_hover and not self.is_near_hud(event.x, event.y):
            edge = 36
            if event.x < edge: self.camera_target_x -= 8
            elif event.x > 1200 - edge: self.camera_target_x += 8
            if event.y < edge: self.camera_target_y -= 8
            elif event.y > 800 - edge: self.camera_target_y += 8
        if self.current_mode == "follow" and self.player and not self.menu_open and not self.safe_menu_open and not self.hud_hover:
            self.target_x, self.target_y = self.screen_to_world(event.x, event.y)

    def key_down(self, event):
        k = event.keysym.lower()
        if self.state == "GAME" and k in "123456789":
            slot = int(k) - 1
            if 0 <= slot < 9 and self.hotbar[slot]:
                self.skill_points = min(15.0, self.skill_points + 0.5)
            return
        if self.selected_safe and self.safe_menu_open:
            if k == "w": self.handle_safe_menu(0); return
            if k == "e": self.handle_safe_menu(1); return
            if k == "s": self.handle_safe_menu(4); return
            if k == "z": self.handle_safe_menu(5); return
            if k == "q": self.handle_safe_menu(7); return
        if self.selected_safe:
            if k == "w":
                self.handle_safe_menu(0)
                return
            if k == "d":
                self.handle_safe_menu(4)
                return
        self.keys.add(k)

    def key_up(self, event):
        k = event.keysym.lower()
        if k in self.keys: self.keys.remove(k)

    def handle_hud_left_click(self, x, y):
        if self.fpv_mode: return False
        hb_y = 683
        hb_start_x = 600 - (9 * 58 / 2)
        if hb_y <= y <= hb_y + 54 and hb_start_x - 10 <= x <= hb_start_x + 9 * 58 + 10:
            slot = max(0, min(8, int((x - hb_start_x) / 58)))
            if hb_start_x + slot * 58 + 45 <= x <= hb_start_x + slot * 58 + 54 and hb_y + 2 <= y <= hb_y + 18:
                if self.hotbar[slot]:
                    item = self.hotbar[slot]
                    self.hotbar[slot] = None
                    if self.player and "backpack" in self.player:
                        self.player["backpack"].append(item)
            return True
        loot_x, loot_y = 78, 50
        row_h = 72
        col_w = 72
        for row in range(4):
            ry = loot_y + row * row_h
            # Toggle row on title click
            if loot_x - 70 < x < loot_x and ry <= y <= ry + row_h:
                self.tla_open[row] = not self.tla_open[row]
                return True
            if self.tla_open[row]:
                if loot_x + 3 * col_w + 10 < x < loot_x + 3 * col_w + 25 and ry + 12 < y < ry + 32:
                    self.loot_offsets[row] = (self.loot_offsets[row] + 1) % 3
                    return True
                for col in range(3):
                    cx = loot_x + col * col_w
                    if cx <= x <= cx + col_w - 4 and ry <= y <= ry + row_h - 4:
                        idx = (self.loot_offsets[row] + col) % 3
                        item = self.loot_rows[row][idx]
                        if item:
                            self.dragging_item = item
                            self.dragging_from_tla = (row, idx)
                            self.loot_rows[row][idx] = None  # Remove on grab
                            return True
        drawer_y = loot_y + 4 * row_h + 8
        # Inventory tab
        if 78 <= x <= 300 and drawer_y <= y <= drawer_y + 26:
            self.inventory_drawer_open = not self.inventory_drawer_open
            return True
        # Safe tab
        if 78 <= x <= 300 and drawer_y + 36 <= y <= drawer_y + 62:
            if self.selected_safe:
                self.safe_drawer_open = not self.safe_drawer_open
            return True
        g_x, g_y = 926, 40
        g_w = 220
        if g_x - 10 <= x <= g_x + g_w + 10 and g_y <= y <= g_y + 340:
            num_tabs = len(self.groups)
            tab_h = max(24, 265 // max(4, num_tabs))
            for i in range(num_tabs):
                ty = g_y + 45 + i * tab_h
                if g_x - 8 <= x <= g_x + 38 and ty <= y <= ty + tab_h:
                    self.current_group_index = i
                    self.group_scroll_offset = 0
                    return True
            list_x = g_x + 48
            list_y = g_y + 45
            block_h = 41
            vis = 5
            blocks = self.groups[self.current_group_index]
            for v in range(vis):
                b_idx = self.group_scroll_offset + v
                if b_idx >= len(blocks): break
                by = list_y + v * block_h
                if list_x <= x <= list_x + 155 and by <= y <= by + block_h:
                    if blocks[b_idx] == "Player" and self.player:
                        self.camera_target_x = self.player["x"]
                        self.camera_target_y = self.player["y"]
                        self.selected = True
                    return True
            plus_y = g_y + 45 + num_tabs * tab_h + 8
            if g_x - 8 <= x <= g_x + 38 and plus_y <= y <= plus_y + 28:
                self.groups.append([])
                self.group_names.append(f" {len(self.groups) - 1} ")
                self.current_group_index = len(self.groups) - 1
                return True
        return False

    def on_left_click(self, event):
        if self.state == "TITLE":
            if self.selected_char_type:
                dot_y = 480
                if self.selected_char_type == "witch":
                    centers = [118, 188, 258]
                    damages = ["Heat/Burn", "Cold/Freeze", "Physical/Bleeding"]
                    fills = ["#ff0000", "#4488ff", "#ffffff"]
                elif self.selected_char_type == "necromancer":
                    centers = [378, 448, 518]
                    damages = ["Poison/Poison", "Decay/Rot", "Physical/Bleeding"]
                    fills = ["#00aa00", "#222222", "#ffffff"]
                elif self.selected_char_type == "elemental":
                    centers = [638, 708, 778]
                    damages = ["Cold/Freeze", "Electric/Burn", "Physical/Bleeding"]
                    fills = ["#88ccff", "#ffff00", "#ffffff"]
                else:
                    centers = [898, 968, 1038]
                    damages = ["Hot/Burn", "Decay/Poison", "Physical/Bleeding"]
                    fills = ["#aa0000", "#222222", "#ffffff"]
                for i, cx in enumerate(centers):
                    if math.hypot(event.x - cx, event.y - dot_y) < 28:
                        self.selected_damage_type = damages[i]
                        self.selected_char_color = fills[i]
                        return

            if 70 <= event.x <= 290 and 310 <= event.y <= 560:
                self.selected_char_type = "witch"
                self.selected_char_color = "#ff4444"
                self.selected_damage_type = "Heat/Burn"
                return
            if 330 <= event.x <= 550 and 310 <= event.y <= 560:
                self.selected_char_type = "necromancer"
                self.selected_char_color = "#00aa00"
                self.selected_damage_type = "Poison/Poison"
                return
            if 590 <= event.x <= 810 and 310 <= event.y <= 560:
                self.selected_char_type = "elemental"
                self.selected_char_color = "#4488ff"
                self.selected_damage_type = "Cold/Freeze"
                return
            if 850 <= event.x <= 1070 and 310 <= event.y <= 560:
                if event.y < 430:
                    characters_path = "Sprites/Characters"
                    sprites_path = "Sprites"
                    initialdir = characters_path if os.path.exists(characters_path) else sprites_path
                    path = filedialog.askopenfilename(initialdir=initialdir, title="Select 64x64 PNG", filetypes=[("PNG files", "*.png")])
                    if path:
                        try:
                            original = tk.PhotoImage(file=path)
                            self.custom_preview = original.subsample(4)
                            self.custom_image = original.subsample(2)
                            self.selected_char_type = "diy"
                            self.selected_char_color = "#ffffff"
                            self.selected_damage_type = "Physical/Bleeding"
                        except:
                            pass
                return

            if self.selected_char_type and 490 <= event.x <= 710 and 620 <= event.y <= 670:
                self.start_new_game()
            return

        if self.state != "GAME": return

        if self.handle_hud_left_click(event.x, event.y):
            return

        if self.is_near_hud(event.x, event.y):
            return

        if 250 < event.x < 950 and 100 < event.y < 700:
            safe = self.get_safe_at(event.x, event.y)
            if safe:
                self.inventory_drawer_open = True
                self.safe_drawer_open = True
                self.selected_safe = safe
                return

        if self.pause_open:
            if 420 <= event.x <= 780:
                if 270 <= event.y <= 310: self.pause_open = False
                elif 330 <= event.y <= 370:
                    if self.player:
                        self.generate_arena()
                        self.player["x"] = self.player["y"] = 0.0
                        self.camera_x = self.camera_y = 0.0
                        self.reset_game_variables()
                        self.pause_open = False
                elif 390 <= event.y <= 430:
                    self.state = "TITLE"
                    self.player = None
                    self.pause_open = False
                    self.root.config(cursor="arrow")
                    if self.clip_supported:
                        self.clip_cursor(False)
                elif 450 <= event.y <= 490: self.on_close()
            return

        if self.settings_open:
            if 540 <= event.x <= 660 and 480 <= event.y <= 510: self.settings_open = True
            return
        if self.skilltree_open:
            if 390 <= event.x <= 490 and 310 <= event.y <= 350 and self.skill_points >= 1:
                self.skill_points -= 1; self.player["body"] += 1
            elif 530 <= event.x <= 630 and 310 <= event.y <= 350 and self.skill_points >= 1:
                self.skill_points -= 1; self.player["combat"] += 1
            elif 670 <= event.x <= 770 and 310 <= event.y <= 350 and self.skill_points >= 1:
                self.skill_points -= 1; self.player["aura"] += 1
            if 540 <= event.x <= 660 and 520 <= event.y <= 550: self.skilltree_open = False
            return

        if self.menu_open:
            sx, sy = self.world_to_screen(self.player["x"], self.player["y"])
            ring_r = 102
            for i in range(8):
                ang = i * (2 * math.pi / 8) - math.pi / 2
                bx = sx + ring_r * math.cos(ang)
                by = sy + ring_r * math.sin(ang)
                if math.hypot(event.x - bx, event.y - by) < 30:
                    if self.menu_type == "directional":
                        self.persistent_scroll = i
                        self.menu_open = False
                    else:
                        self.handle_menu_button(i)
                    return
            return
# bSIM_050.py
# Full working Python3-tkinter game
# Version 050 - Updates based on requests
# • All previous fixes preserved
# Run with: python3 bSIM_050.py
import tkinter as tk
from tkinter import filedialog
import json
import random
import math
import os
import platform
import ctypes
from datetime import datetime
import time

class bSIM: # bSIM === Boss Simulator (base of program)
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Boss Sim - TOAST Engine")
        self.canvas = tk.Canvas(self.root, width=1200, height=800, bg="#1a1a1a", highlightthickness=0)
        self.canvas.pack()
        # Platform detection + Linux X11 setup
        self.platform = platform.system()
        self.clip_supported = (self.platform == "Windows")
        self.x11_lib = None
        self.x11_display = None
        if self.platform == "Linux":
            try:
                self.x11_lib = ctypes.CDLL("libX11.so.6")
            except:
                self.x11_lib = None
        # Safe sprites
        self.safe_img = None
        try:
            if os.path.exists("sprites/safe.png"):
                self.safe_img = tk.PhotoImage(file="sprites/safe.png").subsample(2)
        except:
            pass
        self.safe1_img = None
        try:
            if os.path.exists("Sprites/safe_1.png"):
                self.safe1_img = tk.PhotoImage(file="Sprites/safe_1.png").subsample(2)
        except:
            pass
        self.safe_icon_img = None
        try:
            if os.path.exists("Sprites/safe_icon.png"):
                self.safe_icon_img = tk.PhotoImage(file="Sprites/safe_icon.png")
        except:
            pass
        # Arrow sprites (with failsafe)
        self.arrow_imgs = {}
        directions = ['top', 'topright', 'right', 'bottomright', 'bottom', 'bottomleft', 'left', 'topleft']
        for d in directions:
            path = f"sprites/{d}_arrow.png"
            if os.path.exists(path):
                self.arrow_imgs[d] = tk.PhotoImage(file=path)
            else:
                self.arrow_imgs[d] = None
        # TLA row title images (Sprites/)
        self.tla_imgs = {}
        tla_files = ["weapons_tla.png", "armor_tla.png", "usables_tla.png", "skills_tla.png"]
        for i, fname in enumerate(tla_files):
            path = f"Sprites/{fname}"
            if os.path.exists(path):
                self.tla_imgs[i] = tk.PhotoImage(file=path)
            else:
                self.tla_imgs[i] = None
        # UI PNGs (Sprites/)
        self.bpack_img = None
        if os.path.exists("Sprites/bpack.png"):
            self.bpack_img = tk.PhotoImage(file="Sprites/bpack.png")
        self.equip_img = None
        if os.path.exists("Sprites/equip.png"):
            self.equip_img = tk.PhotoImage(file="Sprites/equip.png")
        self.i_tab_img = None
        if os.path.exists("Sprites/i_tab.png"):
            self.i_tab_img = tk.PhotoImage(file="Sprites/i_tab.png")
        self.s_tab_img = None
        if os.path.exists("Sprites/s_tab.png"):
            self.s_tab_img = tk.PhotoImage(file="Sprites/s_tab.png")
        self.i_tab_open_img = None
        if os.path.exists("Sprites/i_tab_open.png"):
            self.i_tab_open_img = tk.PhotoImage(file="Sprites/i_tab_open.png")
        self.s_tab_open_img = None
        if os.path.exists("Sprites/s_tab_open.png"):
            self.s_tab_open_img = tk.PhotoImage(file="Sprites/s_tab_open.png")
        # Item sprites
        self.item_imgs = {}
        self.starter_items = [
            "Sword", "Fireball", "Ice Blast", "Leather Armor", "Mage Robe", "Ancient Spellbook",
            "Health", "Mana", "Key", "Dash", "Aura Heal", "Summon Minion"
        ]
        item_sprites = [
            "sword-sword_-1.png", "fireball-magic_0.png", "ice-blast-magic_0.png",
            "leather-armor_0.png", "mage-armor_-1.png", "acspells-magic_0.png",
            "health-usable_0.png", "mana-usable_0.png", "key_0.png",
            "dash-skill_0.png", "aura-heal-skill_1.png", "minion-summon_0.png"
        ]
        for item, sprite in zip(self.starter_items, item_sprites):
            path = f"Sprites/{sprite}"
            if os.path.exists(path):
                self.item_imgs[item] = tk.PhotoImage(file=path).subsample(2)
        # Aim dots
        self.aimdots = ["Default"]
        aimdot_dir = "Sprites/aimdot/"
        if os.path.exists(aimdot_dir):
            for f in os.listdir(aimdot_dir):
                if f.endswith(".png"):
                    self.aimdots.append(f[:-4])
                    path = aimdot_dir + f
                    self.item_imgs[f"aimdot_{f[:-4]}"] = tk.PhotoImage(file=path)
        self.aimdot_selected = 0
        # Game state
        self.state = "TITLE"
        self.selected_char_type = None
        self.selected_char_color = None
        self.selected_damage_type = None
        self.custom_preview = None
        self.custom_image = None
        self.custom_image_L = None
        self.custom_image_R = None
        self.player = None
        self.obstacles = []
        self.safes = []
        self.world_safe = None
        self.interactives = []
        self.windows = []
        self.arena_radius = 5000
        self.arena_points = self.calculate_octagon(0, 0, self.arena_radius)
        self.camera_x = 0.0
        self.camera_y = 0.0
        self.camera_target_x = 0.0
        self.camera_target_y = 0.0
        self.scale = 1.0
        self.camera_yaw = 0.0
        self.camera_pitch = 0.0
        self.target_yaw = 0.0
        self.target_pitch = 0.0
        self.bob = 0.0
        self.time = 0.0
        self.skill_points = 0.0
        self.inspect_sp = 0.0
        self.assist_given = False
        self.history = []
        self.mouse_screen_x = 600
        self.mouse_screen_y = 400
        self.last_mouse_x = 600
        self.last_mouse_y = 400
        self.right_drag_start = None
        self.target_x = None
        self.target_y = None
        self.current_mode = None
        self.inspect_center_x = 0.0
        self.inspect_center_y = 0.0
        self.inspect_timer = 0
        self.menu_open = False
        self.safe_menu_open = False
        self.settings_open = False
        self.skilltree_open = False
        self.fpv_mode = False
        self.pause_open = False
        self.pause_hover = -1
        self.selected = True
        self.keys = set()
        self.mouse_warped = False
        self.is_dragging = False
        self.right_hold_start = None
        self.menu_type = "normal" # or "directional"
        self.persistent_scroll = None
        self.edge_scroll_dir = None
        self.tla_open = 15  # bitmask: bit 0 row0, bit1 row1, etc. 15=all open
        # tla_open bitmask:
        # 0 = all closed
        # 1 = only weapons open
        # 2 = only armor open
        # 3 = weapons and armor open
        # 4 = only usables open
        # 5 = weapons and usables open (mixed)
        # 6 = armor and usables open (mixed)
        # 7 = weapons, armor, usables open
        # 8 = only skills open
        # 9 = weapons and skills open (mixed)
        # 10 = armor and skills open (mixed)
        # 11 = weapons, armor, skills open
        # 12 = usables and skills open (mixed)
        # 13 = weapons, usables, skills open
        # 14 = armor, usables, skills open
        # 15 = all open
        self.safe_offset = 0
        # HUD state
        self.groups = [["Player"]]
        self.group_names = ["0"]
        self.current_group_index = 0
        self.group_scroll_offset = 0
        self.hotbar = [None] * 9
        self.loot_rows = [
            ["Sword", "Fireball", "Ice Blast"],
            ["Leather Armor", "Mage Robe", "Ancient Spellbook"],
            ["Health", "Mana", "Key"],
            ["Dash", "Aura Heal", "Summon Minion"]
        ]
        self.loot_offsets = [0] * 4
        self.inventory_drawer_open = False
        self.safe_drawer_open = False
        self.dragging_item = None
        self.dragging_from = None  # ("type", data)
        self.dragging_start_time = None
        self.dragging_start_x = None
        self.dragging_start_y = None
        self.backpack_offset = 0
        self.hud_hover = False
        self.last_right_click = 0.0
        self.selected_safe = None
        self.highlighted_slot = None
        # Arrow positions – ! PERFECTLY ALIGNED !
        self.arrow_positions = {
            'top': (600, 25),
            'topright': (1175, 25),
            'right': (1175, 400),
            'bottomright': (1175, 775),
            'bottom': (600, 775),
            'bottomleft': (25, 775),
            'left': (25, 400),
            'topleft': (25, 25)
        }
        self.arrow_size = 25
        self.dxdy = {
            'top': (0, -8),
            'topright': (8, -8),
            'right': (8, 0),
            'bottomright': (8, 8),
            'bottom': (0, 8),
            'bottomleft': (-8, 8),
            'left': (-8, 0),
            'topleft': (-8, -8)
        }
        # Bindings
        self.canvas.bind("<Button-1>", self.on_left_click)
        self.canvas.bind("<ButtonRelease-1>", self.on_left_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        self.canvas.bind("<B3-Motion>", self.on_right_drag)
        self.canvas.bind("<ButtonRelease-3>", self.on_right_release)
        self.canvas.bind("<Motion>", self.on_motion)
        self.root.bind("<KeyPress>", self.key_down)
        self.root.bind("<KeyRelease>", self.key_up)
        self.root.bind("<Escape>", self.handle_escape)
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.load_crumbs()
        self.game_update()
        self.root.mainloop()

    def calculate_octagon(self, cx, cy, r):
        points = []
        for i in range(8):
            ang = i * (2 * math.pi / 8)
            points.append((cx + r * math.cos(ang), cy + r * math.sin(ang)))
        return points

    def screen_to_world(self, sx, sy):
        wx = self.camera_x + (sx - 600) / self.scale
        wy = self.camera_y + (sy - 400) / self.scale
        return wx, wy

    def world_to_screen(self, wx, wy, wz=0):
        dx = wx - self.camera_x
        dy = wy - self.camera_y
        if self.fpv_mode:
            cos_y = math.cos(-self.camera_yaw)
            sin_y = math.sin(-self.camera_yaw)
            rx = dx * cos_y - dy * sin_y
            ry = dx * sin_y + dy * cos_y
            cos_p = math.cos(self.camera_pitch)
            sin_p = math.sin(self.camera_pitch)
            final_depth = ry * cos_p - (wz - 80) * sin_p
            final_height = ry * sin_p + (wz - 80) * cos_p
            if final_depth < 30: final_depth = 30
            scale_p = 920 / final_depth
            sx = 600 + rx * scale_p
            sy = 400 - final_height * scale_p + self.bob
        else:
            sx = 600 + dx * self.scale
            sy = 400 + dy * self.scale
        return sx, sy

    def is_near_player(self, wx, wy):
        if not self.player: return False
        return math.hypot(wx - self.player["x"], wy - self.player["y"]) < 35

    def get_safe_at(self, sx, sy):
        if not self.safes: return None
        wx, wy = self.screen_to_world(sx, sy)
        for safe in self.safes:
            if math.hypot(wx - safe["x"], wy - safe["y"]) < 35:
                return safe
        return None

    def get_interactive_at(self, sx, sy):
        wx, wy = self.screen_to_world(sx, sy)
        for inter in self.interactives:
            if math.hypot(wx - inter["x"], wy - inter["y"]) < 35:
                return inter
        return None

    def clamp_to_arena(self, x, y):
        r = math.hypot(x, y)
        max_r = self.arena_radius * 0.93
        if r > max_r:
            return x * max_r / r, y * max_r / r
        return x, y

    def collides(self, x, y):
        r = 22
        for obs in self.obstacles:
            left = obs["x"] - obs["w"]/2 - r
            right = obs["x"] + obs["w"]/2 + r
            top = obs["y"] - obs["h"]/2 - r
            bottom = obs["y"] + obs["h"]/2 + r
            if left < x < right and top < y < bottom:
                return True
        return False

    def load_crumbs(self):
        if os.path.exists("bSIM.crumbs"):
            try:
                with open("bSIM.crumbs", "r") as f:
                    data = json.load(f)
                    self.history = data.get("history", [])[-3:]
            except:
                self.history = []

    def save_crumbs(self):
        if not self.player: return
        header = {"user_id": "player", "char_unique_ID": self.player["id"],
                  "coord": [round(self.player["x"], 1), round(self.player["y"], 1)],
                  "data_array": [self.player.get("level", 1), self.player.get("kills", 0), round(self.skill_points, 1),
                                 self.player["type"], self.player["damage_type"]]}
        map_sample = [{"x": round(o["x"]), "y": round(o["y"]), "type": "cubicle"} for o in self.obstacles[:8]]
        details = {"report": f"Backrooms run {datetime.now().strftime('%Y-%m-%d %H:%M')}"}
        new_entry = {"score": int(self.skill_points * 10) + self.player.get("kills", 0),
                     "kills": self.player.get("kills", 0), "level": self.player.get("level", 1),
                     "timestamp": datetime.now().strftime("%Y-%m-%d")}
        new_history = (self.history + [new_entry])[-3:]
        data = {"header": header, "map": map_sample, "details": details, "history": new_history}
        with open("bSIM.crumbs", "w") as f:
            json.dump(data, f, indent=2)

    def start_new_game(self):
        if not self.selected_char_type: return
        self.state = "GAME"
        self.player = {
            "id": "p001",
            "type": self.selected_char_type,
            "color": self.selected_char_color or "#ff0000",
            "damage_type": self.selected_damage_type or "Physical/Bleeding",
            "name": "Explorer",
            "x": 0.0,
            "y": 0.0,
            "vx": 0.0,
            "vy": 0.0,
            "facing": "right",
            "level": 1,
            "kills": 0,
            "body": 0,
            "combat": 0,
            "aura": 0,
            "health": 100.0,
            "max_health": 100.0,
            "stamina": 100.0,
            "max_stamina": 100.0,
            "custom_image": self.custom_image,
            "custom_image_L": self.custom_image_L,
            "custom_image_R": self.custom_image_R,
            "custom_preview": self.custom_preview,
            "ownership": "User_Owned",
            "backpack": ["Health Potion", "Mana Potion"],
            "equip": [None] * 6,
            "chest": []
        }
        self.reset_game_variables()
        self.generate_arena()
        self.root.config(cursor="none")
        if self.clip_supported:
            self.clip_cursor(True)
        self.scale = 1200 / 1200
        self.camera_target_x = self.camera_x
        self.camera_target_y = self.camera_y

    def reset_game_variables(self):
        self.target_x = None
        self.target_y = None
        self.current_mode = None
        self.inspect_center_x = 0.0
        self.inspect_center_y = 0.0
        self.inspect_timer = 0
        self.menu_open = False
        self.safe_menu_open = False
        self.settings_open = False
        self.skilltree_open = False
        self.fpv_mode = False
        self.pause_open = False
        self.skill_points = 0.0
        self.inspect_sp = 0.0
        self.assist_given = False
        self.camera_yaw = 0.0
        self.camera_pitch = 0.0
        self.target_yaw = 0.0
        self.target_pitch = 0.0
        self.bob = 0.0
        self.last_mouse_x = 600
        self.last_mouse_y = 400
        self.mouse_warped = False
        self.selected = True
        self.camera_target_x = 0.0
        self.camera_target_y = 0.0
        self.custom_image = None
        self.custom_image_L = None
        self.custom_image_R = None
        self.custom_preview = None
        self.group_scroll_offset = 0
        self.inventory_drawer_open = False
        self.safe_drawer_open = False
        self.dragging_item = None
        self.dragging_from = None
        self.dragging_start_time = None
        self.dragging_start_x = None
        self.dragging_start_y = None
        self.backpack_offset = 0
        self.hotbar = [None] * 9
        self.hud_hover = False
        self.selected_safe = None
        self.world_safe = None
        self.last_right_click = 0.0
        self.is_dragging = False
        self.right_hold_start = None
        self.menu_type = "normal"
        self.persistent_scroll = None
        self.edge_scroll_dir = None
        self.tla_open = 15
        self.safe_offset = 0
        self.pause_hover = -1

    def generate_arena(self):
        self.obstacles = []
        self.windows = []
        self.safes = []
        self.interactives = []
        for _ in range(20):
            ox = random.uniform(-self.arena_radius * 0.85, self.arena_radius * 0.85)
            oy = random.uniform(-self.arena_radius * 0.85, self.arena_radius * 0.85)
            ow = random.uniform(60, 240)
            oh = random.uniform(60, 200)
            height = random.randint(80, 240) if random.random() < 0.5 else 55
            self.obstacles.append({"x": ox, "y": oy, "w": ow, "h": oh, "height": height, "color": "#555555"})
        for _ in range(12):
            ox = random.uniform(-self.arena_radius * 0.8, self.arena_radius * 0.8)
            oy = random.uniform(-self.arena_radius * 0.8, self.arena_radius * 0.8)
            self.obstacles.append({"x": ox, "y": oy, "w": 40, "h": 40, "height": 30, "color": "#444444"})
        for _ in range(6):
            hx = random.uniform(-self.arena_radius * 0.7, self.arena_radius * 0.7)
            hy = random.uniform(-self.arena_radius * 0.7, self.arena_radius * 0.7)
            self.obstacles.append({"x": hx, "y": hy, "w": 90, "h": 90, "height": 0, "color": "#1a1a1a"})
        for _ in range(30):
            wx = random.choice([-self.arena_radius*0.92, self.arena_radius*0.92])
            wy = random.uniform(-self.arena_radius*0.85, self.arena_radius*0.85)
            self.windows.append((wx, wy))
        for _ in range(4):
            sx = random.uniform(-self.arena_radius * 0.6, self.arena_radius * 0.6)
            sy = random.uniform(-self.arena_radius * 0.6, self.arena_radius * 0.6)
            inv = []
            if random.random() < 0.5:
                inv.append(random.choice(self.starter_items))
            self.safes.append({"x": sx, "y": sy, "inventory": inv, "owner": "System_Owned", "hits_left": 9, "trapped": False, "type": "safe"})
        # Hidden world safe
        ang = random.uniform(0, 2*math.pi)
        dist = self.arena_radius * 0.85
        wx = dist * math.cos(ang)
        wy = dist * math.sin(ang)
        self.world_safe = {"x": wx, "y": wy, "inventory": [], "owner": "World", "quality": 1, "trapped": False, "type": "safe_1"}
        # New interactives
        new_objs = [
            ("Big Daddy", "nuke_big.png", "nuke_big"),
            ("Smol Boi", "nuke_small.png", "nuke_small"),
            ("Key", "key_0.png", "key_0"),
            ("Vortex Key", "key_1.png", "key_1"),
            ("Locked Safe", "safe_0.png", "safe_0")
        ]
        for _ in range(random.randint(1,5)):
            obj = random.choice(new_objs)
            ox = random.uniform(-self.arena_radius * 0.8, self.arena_radius * 0.8)
            oy = random.uniform(-self.arena_radius * 0.8, self.arena_radius * 0.8)
            img = None
            path = f"Sprites/{obj[1]}"
            if os.path.exists(path):
                img = tk.PhotoImage(file=path).subsample(2)
            self.interactives.append({"x": ox, "y": oy, "type": obj[2], "img": img, "name": obj[0]})

    # ==================== CROSS-PLATFORM MOUSE LOCK ====================
    def warp_cursor_to_center(self):
        cx = self.canvas.winfo_rootx() + 600
        cy = self.canvas.winfo_rooty() + 400
        if self.platform == "Windows":
            try:
                ctypes.windll.user32.SetCursorPos(cx, cy)
            except:
                pass
        elif self.platform == "Linux" and self.x11_lib:
            try:
                if not self.x11_display:
                    self.x11_display = self.x11_lib.XOpenDisplay(None)
                if self.x11_display:
                    root = self.x11_lib.XDefaultRootWindow(self.x11_display)
                    self.x11_lib.XWarpPointer(self.x11_display, 0, root, 0, 0, 0, 0, cx, cy)
                    self.x11_lib.XFlush(self.x11_display)
            except:
                pass
        else:
            self.root.after(1, lambda: self.canvas.event_generate("<Motion>", x=600, y=400))

    def clip_cursor(self, enable=True):
        if not self.clip_supported:
            return
        try:
            if enable:
                left = self.canvas.winfo_rootx()
                top = self.canvas.winfo_rooty()
                right = left + 1200
                bottom = top + 800
                rect = ctypes.wintypes.RECT(left, top, right, bottom)
                ctypes.windll.user32.ClipCursor(ctypes.byref(rect))
            else:
                ctypes.windll.user32.ClipCursor(None)
        except:
            pass
    # =================================================================

    def is_tla_row_open(self, row):
        return (self.tla_open & (1 << row)) != 0

    def toggle_tla_row(self, row):
        self.tla_open ^= (1 << row)

    def is_mouse_in_hud(self, x, y):
        loot_x, loot_y = 78, 50
        row_h = 72
        # TLA deadzones dynamic per row
        for row in range(4):
            ry = loot_y + row * row_h
            # Title always
            if loot_x - 70 < x < loot_x + 3*72 + 30 and ry <= y <= ry + row_h:
                return True
            # Content if open
            if self.is_tla_row_open(row):
                if loot_x <= x <= loot_x + 3*72 + 30 and ry <= y <= ry + row_h:
                    return True
        drawer_y = loot_y + 4 * row_h + 8
        # Inventory tab
        if 78 <= x <= 300 and drawer_y <= y <= drawer_y + 26:
            return True
        # Safe tab dynamic
        safe_tab_y = drawer_y + 36 if not self.inventory_drawer_open else drawer_y + 200  # approx inventory height
        if 78 <= x <= 300 and safe_tab_y <= y <= safe_tab_y + 26:
            return True
        if self.inventory_drawer_open and 30 <= x <= 300 and drawer_y + 30 <= y <= drawer_y + 200:
            return True
        if self.safe_drawer_open and 30 <= x <= 300 and safe_tab_y + 30 <= y <= safe_tab_y + 200:
            return True
        if 650 <= y <= 740 and 180 <= x <= 1020: return True
        if 900 <= x <= 1180 and 30 <= y <= 390: return True
        if 20 <= x <= 220 and 560 <= y <= 760: return True
        if 950 <= x <= 1150 and 580 <= y <= 780: return True
        return False

    def is_near_hud(self, x, y):
        if self.is_mouse_in_hud(x, y): return True
        if (x < 64 or x > 1136) or (y < 30 or y > 770): return True
        return False

    def on_motion(self, event):
        self.hud_hover = self.is_mouse_in_hud(event.x, event.y)
        if self.state == "GAME" and self.fpv_mode and not self.pause_open:
            if self.mouse_warped:
                self.mouse_warped = False
                return
            delta_x = event.x - 600
            delta_y = event.y - 400
            if abs(delta_x) > 4:
                self.target_yaw -= delta_x * 0.000015
            if abs(delta_y) > 4:
                self.target_pitch += delta_y * 0.00000095
            self.target_pitch = max(-33, min(53, self.target_pitch))
            self.mouse_warped = True
            self.root.after(0, self.warp_cursor_to_center)
            return
        self.mouse_screen_x = event.x
        self.mouse_screen_y = event.y
        # EDGE ARROW HOVER
        self.edge_scroll_dir = None
        for d, pos in self.arrow_positions.items():
            if (pos[0] - self.arrow_size < event.x < pos[0] + self.arrow_size and
                pos[1] - self.arrow_size < event.y < pos[1] + self.arrow_size):
                self.edge_scroll_dir = d
                break
        if self.is_dragging:
            if not self.fpv_mode and not self.menu_open and not self.safe_menu_open and not self.pause_open and not self.hud_hover and not self.is_near_hud(event.x, event.y):
                edge = 36
                if event.x < edge: self.camera_target_x -= 8
                elif event.x > 1200 - edge: self.camera_target_x += 8
                if event.y < edge: self.camera_target_y -= 8
                elif event.y > 800 - edge: self.camera_target_y += 8
            return
        if not self.fpv_mode and not self.menu_open and not self.safe_menu_open and not self.pause_open and not self.hud_hover and not self.is_near_hud(event.x, event.y):
            edge = 36
            if event.x < edge: self.camera_target_x -= 8
            elif event.x > 1200 - edge: self.camera_target_x += 8
            if event.y < edge: self.camera_target_y -= 8
            elif event.y > 800 - edge: self.camera_target_y += 8
        if self.current_mode == "follow" and self.player and not self.menu_open and not self.safe_menu_open and not self.hud_hover:
            self.target_x, self.target_y = self.screen_to_world(event.x, event.y)
        if self.pause_open:
            btns_y = [270, 330, 390, 450, 510]  # added for aimdot
            self.pause_hover = -1
            if 420 <= event.x <= 780:
                for i, by in enumerate(btns_y):
                    if by <= event.y <= by + 40:
                        self.pause_hover = i
                        break

    def key_down(self, event):
        k = event.keysym.lower()
        if self.state == "GAME" and k in "123456789":
            slot = int(k) - 1
            if 0 <= slot < 9 and self.hotbar[slot]:
                self.skill_points = min(15.0, self.skill_points + 0.5)
            return
        if self.selected_safe and self.safe_menu_open:
            if k == "w": self.handle_safe_menu(0); return
            if k == "e": self.handle_safe_menu(1); return
            if k == "s": self.handle_safe_menu(4); return
            if k == "z": self.handle_safe_menu(5); return
            if k == "q": self.handle_safe_menu(7); return
        if self.selected_safe:
            if k == "w":
                self.handle_safe_menu(0)
                return
            if k == "d":
                self.handle_safe_menu(4)
                return
        self.keys.add(k)

    def key_up(self, event):
        k = event.keysym.lower()
        if k in self.keys: self.keys.remove(k)

    def handle_hud_left_click(self, x, y):
        if self.fpv_mode: return False
        hb_y = 683
        hb_start_x = 600 - (9 * 58 / 2)
        if hb_y <= y <= hb_y + 54 and hb_start_x - 10 <= x <= hb_start_x + 9 * 58 + 10:
            slot = max(0, min(8, int((x - hb_start_x) / 58)))
            if hb_start_x + slot * 58 + 45 <= x <= hb_start_x + slot * 58 + 54 and hb_y + 2 <= y <= hb_y + 18:
                if self.hotbar[slot]:
                    item = self.hotbar[slot]
                    self.hotbar[slot] = None
                    if self.player and "backpack" in self.player:
                        self.player["backpack"].append(item)
            else:
                # Grab from hotbar
                if self.hotbar[slot]:
                    self.dragging_item = self.hotbar[slot]
                    self.dragging_from = ("hotbar", slot)
                    self.hotbar[slot] = None
                    self.dragging_start_time = time.time()
                    self.dragging_start_x = x
                    self.dragging_start_y = y
            return True
        loot_x, loot_y = 78, 50
        row_h = 72
        col_w = 72
        for row in range(4):
            ry = loot_y + row * row_h
            # Toggle row on title click
            if loot_x - 70 < x < loot_x and ry <= y <= ry + row_h:
                self.toggle_tla_row(row)
                return True
            if self.is_tla_row_open(row):
                if loot_x + 3 * col_w + 10 < x < loot_x + 3 * col_w + 25 and ry + 12 < y < ry + 32:
                    self.loot_offsets[row] = (self.loot_offsets[row] + 1) % 3
                    return True
                for col in range(3):
                    cx = loot_x + col * col_w
                    if cx <= x <= cx + col_w - 4 and ry <= y <= ry + row_h - 4:
                        idx = (self.loot_offsets[row] + col) % 3
                        item = self.loot_rows[row][idx]
                        if item:
                            self.dragging_item = item
                            self.dragging_from = ("tla", (row, idx))
                            self.loot_rows[row][idx] = None
                            self.dragging_start_time = time.time()
                            self.dragging_start_x = x
                            self.dragging_start_y = y
                            return True
        drawer_y = loot_y + 4 * row_h + 8
        # Inventory tab
        if 78 <= x <= 300 and drawer_y <= y <= drawer_y + 26:
            self.inventory_drawer_open = not self.inventory_drawer_open
            return True
        # Safe tab dynamic y
        safe_tab_y = drawer_y + 36 if not self.inventory_drawer_open else drawer_y + 200
        if 78 <= x <= 300 and safe_tab_y <= y <= safe_tab_y + 26:
            if self.selected_safe or self.world_safe:
                self.safe_drawer_open = not self.safe_drawer_open
            return True
        # Inventory content clicks
        if self.inventory_drawer_open:
            d_y = drawer_y + 32
            bp_x = 133
            bp_y = d_y + 10
            # Backpack title auto-drop
            if bp_x - 50 < x < bp_x + 50 and bp_y - 30 < y < bp_y - 10:
                return True  # handled in release
            # Backpack arrows
            # Upper left pointing
            if bp_x + 155 < x < bp_x + 170 and bp_y + 14 < y < bp_y + 34:
                self.backpack_offset = max(0, self.backpack_offset - 3)
                return True
            # Lower right pointing
            if bp_x + 155 < x < bp_x + 170 and bp_y + 56 < y < bp_y + 76:
                self.backpack_offset += 3
                return True
            # Backpack boxes
            for row in range(2):
                ry = bp_y + row * 48
                for col in range(3):
                    cx = bp_x + col * 48
                    if cx <= x <= cx + 44 and ry <= y <= ry + 42:
                        idx = self.backpack_offset + row * 3 + col
                        if idx < len(self.player["backpack"]):
                            self.dragging_item = self.player["backpack"][idx]
                            self.dragging_from = ("backpack", idx)
                            self.player["backpack"][idx] = None
                        self.dragging_start_time = time.time()
                        self.dragging_start_x = x
                        self.dragging_start_y = y
                        return True
            # Equip title auto-equip
            eq_y = bp_y + 110
            if bp_x - 50 < x < bp_x + 50 and eq_y - 30 < y < eq_y - 10:
                return True  # handled in release
            # Equip boxes
            labels = ['Head', 'Chest', 'Legs', 'Feet', 'Left', 'Right']
            for row in range(2):
                ry = eq_y + row * 38
                for col in range(3):
                    cx = 133 + col * 38
                    if cx <= x <= cx + 34 and ry <= y <= ry + 34:
                        slot = row * 3 + col
                        if self.player["equip"][slot]:
                            self.dragging_item = self.player["equip"][slot]
                            self.dragging_from = ("equip", slot)
                            self.player["equip"][slot] = None
                        self.dragging_start_time = time.time()
                        self.dragging_start_x = x
                        self.dragging_start_y = y
                        return True
        # Safe content clicks
        if self.safe_drawer_open:
            safe_d_y = safe_tab_y + 28
            for row in range(2):
                ry = safe_d_y + 45 + row * 48
                for col in range(3):
                    cx = 45 + col * 48
                    if cx <= x <= cx + 44 and ry <= y <= ry + 36:
                        idx = self.safe_offset + row * 3 + col
                        safe = self.selected_safe or self.world_safe
                        if idx < len(safe["inventory"]):
                            self.dragging_item = safe["inventory"][idx]
                            self.dragging_from = ("safe", idx)
                            safe["inventory"][idx] = None
                        self.dragging_start_time = time.time()
                        self.dragging_start_x = x
                        self.dragging_start_y = y
                        return True
            # Safe arrows (assuming similar to backpack)
            if 45 + 155 < x < 45 + 170 and safe_d_y + 52 < y < safe_d_y + 72:
                self.safe_offset = max(0, self.safe_offset - 3)
                return True
            if 45 + 155 < x < 45 + 170 and safe_d_y + 144 < y < safe_d_y + 174:
                self.safe_offset += 3
                return True
        g_x, g_y = 926, 40
        g_w = 220
        if g_x - 10 <= x <= g_x + g_w + 10 and g_y <= y <= g_y + 340:
            num_tabs = len(self.groups)
            tab_h = max(24, 265 // max(4, num_tabs))
            for i in range(num_tabs):
                ty = g_y + 45 + i * tab_h
                if g_x - 8 <= x <= g_x + 38 and ty <= y <= ty + tab_h:
                    self.current_group_index = i
                    self.group_scroll_offset = 0
                    return True
            list_x = g_x + 48
            list_y = g_y + 45
            block_h = 41
            vis = 5
            blocks = self.groups[self.current_group_index]
            for v in range(vis):
                b_idx = self.group_scroll_offset + v
                if b_idx >= len(blocks): break
                by = list_y + v * block_h
                if list_x <= x <= list_x + 155 and by <= y <= by + block_h:
                    if blocks[b_idx] == "Player" and self.player:
                        self.camera_target_x = self.player["x"]
                        self.camera_target_y = self.player["y"]
                        self.selected = True
                    return True
            plus_y = g_y + 45 + num_tabs * tab_h + 8
            if g_x - 8 <= x <= g_x + 38 and plus_y <= y <= plus_y + 28:
                self.groups.append([])
                self.group_names.append(f" {len(self.groups) - 1} ")
                self.current_group_index = len(self.groups) - 1
                return True
        return False

    def on_left_click(self, event):
        if self.state == "TITLE":
            if self.selected_char_type:
                dot_y = 480
                if self.selected_char_type == "witch":
                    centers = [118, 188, 258]
                    damages = ["Heat/Burn", "Cold/Freeze", "Physical/Bleeding"]
                    fills = ["#ff0000", "#4488ff", "#ffffff"]
                elif self.selected_char_type == "necromancer":
                    centers = [378, 448, 518]
                    damages = ["Poison/Poison", "Decay/Rot", "Physical/Bleeding"]
                    fills = ["#00aa00", "#222222", "#ffffff"]
                elif self.selected_char_type == "elemental":
                    centers = [638, 708, 778]
                    damages = ["Cold/Freeze", "Electric/Burn", "Physical/Bleeding"]
                    fills = ["#88ccff", "#ffff00", "#ffffff"]
                else:
                    centers = [898, 968, 1038]
                    damages = ["Hot/Burn", "Decay/Poison", "Physical/Bleeding"]
                    fills = ["#aa0000", "#222222", "#ffffff"]
                for i, cx in enumerate(centers):
                    if math.hypot(event.x - cx, event.y - dot_y) < 28:
                        self.selected_damage_type = damages[i]
                        self.selected_char_color = fills[i]
                        return
            if 70 <= event.x <= 290 and 310 <= event.y <= 560:
                self.selected_char_type = "witch"
                self.selected_char_color = "#ff4444"
                self.selected_damage_type = "Heat/Burn"
                return
            if 330 <= event.x <= 550 and 310 <= event.y <= 560:
                self.selected_char_type = "necromancer"
                self.selected_char_color = "#00aa00"
                self.selected_damage_type = "Poison/Poison"
                return
            if 590 <= event.x <= 810 and 310 <= event.y <= 560:
                self.selected_char_type = "elemental"
                self.selected_char_color = "#4488ff"
                self.selected_damage_type = "Cold/Freeze"
                return
            if 850 <= event.x <= 1070 and 310 <= event.y <= 560:
                if event.y < 430:
                    characters_path = "Sprites/Characters"
                    sprites_path = "Sprites"
                    initialdir = characters_path if os.path.exists(characters_path) else sprites_path
                    path = filedialog.askopenfilename(initialdir=initialdir, title="Select 64x64 PNG", filetypes=[("PNG files", "*.png")])
                    if path:
                        try:
                            original = tk.PhotoImage(file=path)
                            self.custom_preview = original.subsample(4)
                            self.custom_image = original.subsample(2)
                            name = os.path.basename(path)[:-4]
                            l_path = path.replace(".png", "_L.png")
                            r_path = path.replace(".png", "_R.png")
                            if os.path.exists(l_path):
                                self.custom_image_L = tk.PhotoImage(file=l_path).subsample(2)
                            if os.path.exists(r_path):
                                self.custom_image_R = tk.PhotoImage(file=r_path).subsample(2)
                            self.selected_char_type = "diy"
                            self.selected_char_color = "#ffffff"
                            self.selected_damage_type = "Physical/Bleeding"
                        except:
                            pass
                return
            if self.selected_char_type and 490 <= event.x <= 710 and 620 <= event.y <= 670:
                self.start_new_game()
            return
        if self.state != "GAME": return
        if self.handle_hud_left_click(event.x, event.y):
            return
        if self.is_near_hud(event.x, event.y):
            return
        if 250 < event.x < 950 and 100 < event.y < 700:
            safe = self.get_safe_at(event.x, event.y)
            if safe:
                self.inventory_drawer_open = True
                self.safe_drawer_open = True
                self.selected_safe = safe
                return
            inter = self.get_interactive_at(event.x, event.y)
            if inter:
                self.handle_interactive_left(inter)
                return
        if self.pause_open:
            if 420 <= event.x <= 780:
                if 270 <= event.y <= 310: self.pause_open = False
                elif 330 <= event.y <= 370:
                    if self.player:
                        self.generate_arena()
                        self.player["x"] = self.player["y"] = 0.0
                        self.camera_x = self.camera_y = 0.0
                        self.reset_game_variables()
                        self.pause_open = False
                elif 390 <= event.y <= 430:
                    self.state = "TITLE"
                    self.player = None
                    self.pause_open = False
                    self.root.config(cursor="arrow")
                    if self.clip_supported:
                        self.clip_cursor(False)
                elif 450 <= event.y <= 490: self.on_close()
                elif 510 <= event.y <= 550:
                    # Aim dot cycle
                    self.aimdot_selected = (self.aimdot_selected + 1) % len(self.aimdots)
            return
        if self.settings_open:
            if 540 <= event.x <= 660 and 480 <= event.y <= 510: self.settings_open = False
            return
        if self.skilltree_open:
            if 390 <= event.x <= 490 and 310 <= event.y <= 350 and self.skill_points >= 1:
                self.skill_points -= 1; self.player["body"] += 1
            elif 530 <= event.x <= 630 and 310 <= event.y <= 350 and self.skill_points >= 1:
                self.skill_points -= 1; self.player["combat"] += 1
            elif 670 <= event.x <= 770 and 310 <= event.y <= 350 and self.skill_points >= 1:
                self.skill_points -= 1; self.player["aura"] += 1
            if 540 <= event.x <= 660 and 520 <= event.y <= 550: self.skilltree_open = False
            return
        if self.menu_open:
            sx, sy = self.world_to_screen(self.player["x"], self.player["y"])
            ring_r = 102
            for i in range(8):
                ang = i * (2 * math.pi / 8) - math.pi / 2
                bx = sx + ring_r * math.cos(ang)
                by = sy + ring_r * math.sin(ang)
                if math.hypot(event.x - bx, event.y - by) < 30:
                    if self.menu_type == "directional":
                        self.persistent_scroll = i
                        self.menu_open = False
                    else:
                        self.handle_menu_button(i)
                    return
            return
        if self.safe_menu_open and self.selected_safe:
            sx, sy = self.world_to_screen(self.selected_safe["x"], self.selected_safe["y"])
            ring_r = 102
            for i in range(8):
                ang = i * (2 * math.pi / 8) - math.pi / 2
                bx = sx + ring_r * math.cos(ang)
                by = sy + ring_r * math.sin(ang)
                if math.hypot(event.x - bx, event.y - by) < 24:
                    self.handle_safe_menu(i)
                    return
            return
        wx, wy = self.screen_to_world(event.x, event.y)
        if self.is_near_player(wx, wy):
            self.selected = True
        else:
            if self.selected and not self.menu_open and not self.safe_menu_open and not self.fpv_mode:
                self.target_x = wx
                self.target_y = wy
                self.current_mode = None

    def on_left_release(self, event):
        if self.dragging_item is None or self.state != "GAME":
            return
        dropped = False
        # Hotbar drop
        hb_y = 683
        hb_start_x = 600 - (9 * 58 / 2)
        if hb_y - 10 <= event.y <= hb_y + 64 and hb_start_x - 10 <= event.x <= hb_start_x + 9 * 58 + 10:
            slot = max(0, min(8, int((event.x - hb_start_x) / 58)))
            if self.hotbar[slot] is None:
                self.hotbar[slot] = self.dragging_item
                dropped = True
            else:
                old = self.hotbar[slot]
                self.hotbar[slot] = self.dragging_item
                self.player["backpack"].append(old)
                dropped = True
        # Inventory/safe drop
        drawer_y = 50 + 4*72 + 8
        if self.inventory_drawer_open or self.safe_drawer_open:
            d_y = drawer_y + 32
            bp_x = 133
            bp_y = d_y + 10
            eq_y = bp_y + 110
            # Backpack title auto-drop
            if bp_x - 50 < event.x < bp_x + 50 and bp_y - 30 < event.y < bp_y - 10:
                self.player["backpack"].append(self.dragging_item)
                dropped = True
            # Backpack boxes manual drop
            for row in range(2):
                ry = bp_y + row * 48
                for col in range(3):
                    cx = bp_x + col * 48
                    if cx - 5 <= event.x <= cx + 49 and ry - 5 <= event.y <= ry + 47:  # slight tolerance
                        idx = self.backpack_offset + row * 3 + col
                        if idx < len(self.player["backpack"]):
                            old = self.player["backpack"][idx]
                            self.player["backpack"][idx] = self.dragging_item
                            if old:
                                self.player["backpack"].append(old)
                        else:
                            self.player["backpack"].append(self.dragging_item)
                        dropped = True
                        break
            # Auto-box-finder for backpack
            if not dropped and bp_x - 20 < event.x < bp_x + 170 and bp_y - 20 < event.y < bp_y + 100:
                self.player["backpack"].append(self.dragging_item)
                dropped = True
            # Equip title auto-equip
            if bp_x - 50 < event.x < bp_x + 50 and eq_y - 30 < event.y < eq_y - 10:
                for slot in range(6):
                    if self.player["equip"][slot] is None:
                        self.player["equip"][slot] = self.dragging_item
                        dropped = True
                        break
                if not dropped:
                    old = self.player["equip"][5]
                    self.player["equip"][5] = self.dragging_item
                    self.player["backpack"].append(old)
                    dropped = True
            # Equip boxes manual drop
            for row in range(2):
                ry = eq_y + row * 38
                for col in range(3):
                    cx = 133 + col * 38
                    if cx - 5 <= event.x <= cx + 39 and ry - 5 <= event.y <= ry + 39:
                        slot = row * 3 + col
                        old = self.player["equip"][slot]
                        self.player["equip"][slot] = self.dragging_item
                        if old:
                            self.player["backpack"].append(old)
                        dropped = True
                        break
            # Auto-box-finder for equip
            if not dropped and bp_x - 20 < event.x < bp_x + 170 and eq_y - 20 < event.y < eq_y + 100:
                for slot in range(6):
                    if self.player["equip"][slot] is None:
                        self.player["equip"][slot] = self.dragging_item
                        dropped = True
                        break
                if not dropped:
                    old = self.player["equip"][5]
                    self.player["equip"][5] = self.dragging_item
                    self.player["backpack"].append(old)
                    dropped = True
        # Safe drop similar
        if self.safe_drawer_open:
            safe = self.selected_safe or self.world_safe
            safe_tab_y = drawer_y + 36 if not self.inventory_drawer_open else drawer_y + 200
            safe_d_y = safe_tab_y + 28
            for row in range(2):
                ry = safe_d_y + 45 + row * 48
                for col in range(3):
                    cx = 45 + col * 48
                    if cx - 5 <= event.x <= cx + 49 and ry - 5 <= event.y <= ry + 41:
                        idx = self.safe_offset + row * 3 + col
                        if idx < len(safe["inventory"]):
                            old = safe["inventory"][idx]
                            safe["inventory"][idx] = self.dragging_item
                            if old:
                                safe["inventory"].append(old)
                        else:
                            safe["inventory"].append(self.dragging_item)
                        dropped = True
                        break
            if not dropped and 30 < event.x < 250 and safe_d_y < event.y < safe_d_y + 125:
                safe["inventory"].append(self.dragging_item)
                dropped = True
        # TLA drop
        loot_x, loot_y = 78, 50
        row_h = 72
        col_w = 72
        for row in range(4):
            if self.is_tla_row_open(row):
                ry = loot_y + row * row_h
                for col in range(3):
                    cx = loot_x + col * col_w
                    if cx - 5 <= event.x <= cx + col_w + 1 and ry - 5 <= event.y <= ry + row_h + 1:
                        idx = (self.loot_offsets[row] + col) % 3
                        if self.loot_rows[row][idx] is None:
                            self.loot_rows[row][idx] = self.dragging_item
                            dropped = True
                        break
        # If not dropped, return to source or to TLA/backpack
        if not dropped:
            duration = time.time() - self.dragging_start_time
            dist = math.hypot(event.x - self.dragging_start_x, event.y - self.dragging_start_y)
            if duration < 1.1 or dist < 10 or not self.is_mouse_in_hud(event.x, event.y):
                # Put back
                if self.dragging_from[0] == "tla":
                    row, idx = self.dragging_from[1]
                    if self.loot_rows[row][idx] is None:
                        self.loot_rows[row][idx] = self.dragging_item
                    else:
                        # Try TLA other spot
                        for r in range(4):
                            for c in range(3):
                                i = (self.loot_offsets[r] + c) % 3
                                if self.loot_rows[r][i] is None:
                                    self.loot_rows[r][i] = self.dragging_item
                                    dropped = True
                                    break
                            if dropped: break
                        if not dropped:
                            self.player["backpack"].append(self.dragging_item)
                elif self.dragging_from[0] == "hotbar":
                    slot = self.dragging_from[1]
                    if self.hotbar[slot] is None:
                        self.hotbar[slot] = self.dragging_item
                    else:
                        self.player["backpack"].append(self.dragging_item)
                elif self.dragging_from[0] == "backpack":
                    idx = self.dragging_from[1]
                    if idx < len(self.player["backpack"]) and self.player["backpack"][idx] is None:
                        self.player["backpack"][idx] = self.dragging_item
                    else:
                        # To TLA if spot taken
                        dropped = False
                        for r in range(4):
                            for c in range(3):
                                i = (self.loot_offsets[r] + c) % 3
                                if self.loot_rows[r][i] is None:
                                    self.loot_rows[r][i] = self.dragging_item
                                    dropped = True
                                    break
                            if dropped: break
                        if not dropped:
                            self.player["backpack"].append(self.dragging_item)
                elif self.dragging_from[0] == "equip":
                    slot = self.dragging_from[1]
                    if self.player["equip"][slot] is None:
                        self.player["equip"][slot] = self.dragging_item
                    else:
                        self.player["backpack"].append(self.dragging_item)
                elif self.dragging_from[0] == "safe":
                    idx = self.dragging_from[1]
                    safe = self.selected_safe or self.world_safe
                    if idx < len(safe["inventory"]) and safe["inventory"][idx] is None:
                        safe["inventory"][idx] = self.dragging_item
                    else:
                        safe["inventory"].append(self.dragging_item)
            else:
                # Drop to world? But no world drop, so put back to backpack
                self.player["backpack"].append(self.dragging_item)
        self.dragging_item = None
        self.dragging_from = None
        self.dragging_start_time = None
        self.dragging_start_x = None
        self.dragging_start_y = None

    def handle_menu_button(self, idx):
        self.menu_open = False
        action_map = {0: "follow", 1: "inspect", 2: "pin"}
        action = action_map.get(idx)
        if action in ("follow", "inspect", "pin"):
            if self.current_mode == action:
                self.current_mode = None
            else:
                self.current_mode = action
                if action == "inspect":
                    self.inspect_center_x = self.player["x"]
                    self.inspect_center_y = self.player["y"]
                    self.inspect_timer = 0
                if action == "pin":
                    self.target_x = self.player["x"]
                    self.target_y = self.player["y"]
        elif idx == 3:
            self.target_x = 0.0
            self.target_y = 0.0
            self.current_mode = None
        elif idx == 4:
            self.fpv_mode = not self.fpv_mode
            if self.fpv_mode:
                self.target_yaw = self.camera_yaw
                self.target_pitch = self.camera_pitch
                self.camera_pitch = 0.0
                self.canvas.config(cursor="none")
                self.root.grab_set()
                self.root.focus_force()
                if self.clip_supported:
                    self.clip_cursor(True)
                self.root.after(10, self.warp_cursor_to_center)
            else:
                self.canvas.config(cursor="")
                self.root.grab_release()
        elif idx == 5:
            self.group_mode = True
        elif idx == 6:
            if self.selected and self.player:
                self.inventory_drawer_open = True
                self.safe_drawer_open = False
        elif idx == 7:
            self.skilltree_open = True

    def handle_safe_menu(self, idx):
        safe = self.selected_safe or self.world_safe
        is_locked = safe.get("type", "safe") == "safe_0"
        has_key = any("Key" in item for item in self.player["backpack"] + self.player["equip"] if item)
        if is_locked and idx in [0,1,7] and not has_key:
            return  # cannot
        if idx == 0: # Open (w)
            if safe.get("trapped", False):
                if safe["inventory"]:
                    item = safe["inventory"].pop()
                    self.player["backpack"].append(item)
                if safe in self.safes:
                    self.safes.remove(safe)
            else:
                self.safe_drawer_open = True
                self.inventory_drawer_open = True
        elif idx == 1: # Take Top (e)
            if safe["inventory"]:
                item = safe["inventory"].pop(0)
                self.player["backpack"].append(item)
        elif idx == 4: # Break (s)
            if safe["inventory"]:
                item = safe["inventory"].pop()
                self.player["backpack"].append(item)
            if safe in self.safes:
                self.safes.remove(safe)
        elif idx == 5: # Trap (z)
            safe["trapped"] = True
        elif idx == 7: # Take All (q)
            for item in safe["inventory"][:]:
                self.player["backpack"].append(item)
            safe["inventory"] = []
        self.safe_menu_open = False

    def handle_interactive_left(self, inter):
        if inter["type"] == "nuke_big":
            # explode 65x damage in camera range +35%
            pass  # no enemies
            self.interactives.remove(inter)
        elif inter["type"] == "nuke_small":
            # explode 25x damage in camera -35%
            pass
            self.interactives.remove(inter)
        elif inter["type"] == "key_0":
            self.player["backpack"].append("Key")
            self.interactives.remove(inter)
        elif inter["type"] == "key_1":
            if self.player["equip"][4] is None:
                self.player["equip"][4] = "Vortex Key"
            else:
                self.player["backpack"].append("Vortex Key")
            self.interactives.remove(inter)
        elif inter["type"] == "safe_0":
            self.selected_safe = inter
            self.safe_menu_open = True

    def on_right_click(self, event):
        now = time.time()
        if now - self.last_right_click < 0.4:
            self.selected = False
            self.current_mode = None
            self.menu_open = False
            self.safe_menu_open = False
            self.selected_safe = None
            self.last_right_click = now
            self.persistent_scroll = None
            return
        self.last_right_click = now
        if self.state != "GAME": return
        if self.fpv_mode:
            self.fpv_mode = False
            self.bob = 0.0
            self.camera_pitch = 0.0
            self.canvas.config(cursor="")
            self.root.grab_release()
            return
        self.canvas.bind("<Leave>", self.on_right_release)
        wx, wy = self.screen_to_world(event.x, event.y)
        if self.menu_open and self.is_near_player(wx, wy) and self.player["ownership"] == "User_Owned":
            self.menu_open = False
            self.settings_open = True
            return
        if self.selected and self.player and math.hypot(event.x - 1050, event.y - 650) < 88 + 20:
            self.menu_open = True
            self.menu_type = "normal"
            self.right_hold_start = time.time()
            return
        safe = self.get_safe_at(event.x, event.y)
        if safe:
            if not safe["inventory"]:
                if safe in self.safes:
                    self.safes.remove(safe)
                return
            self.safe_menu_open = True
            self.selected_safe = safe
            self.menu_open = False
            return
        inter = self.get_interactive_at(event.x, event.y)
        if inter:
            # right click N/A for new objs
            return
        if self.menu_open:
            self.menu_open = False
            return
        if self.is_near_player(wx, wy):
            self.selected = True
            self.menu_open = True
            self.menu_type = "normal"
            self.right_hold_start = time.time()

    def on_right_release(self, event=None):
        self.canvas.unbind("<Leave>")
        self.camera_target_x = self.camera_x
        self.camera_target_y = self.camera_y
        self.is_dragging = False
        if self.right_hold_start is not None:
            duration = time.time() - self.right_hold_start
            if duration > 0.9 and self.menu_open and self.player:
                self.menu_type = "directional" if self.menu_type == "normal" else "normal"
            self.right_hold_start = None

    def on_right_drag(self, event):
        if self.right_drag_start is None:
            self.right_drag_start = (event.x, event.y)
            self.is_dragging = True
            return
        dx = event.x - self.right_drag_start[0]
        dy = event.y - self.right_drag_start[1]
        self.camera_target_x -= dx / self.scale
        self.camera_target_y -= dy / self.scale
        self.right_drag_start = (event.x, event.y)

    def handle_escape(self, event=None):
        self.persistent_scroll = None
        self.edge_scroll_dir = None
        if self.pause_open:
            self.pause_open = False
        elif self.menu_open or self.safe_menu_open or self.settings_open or self.skilltree_open:
            self.menu_open = self.safe_menu_open = self.settings_open = self.skilltree_open = False
        elif self.state == "GAME":
            self.pause_open = True

    def open_safe(self, safe):
        if not self.player: return
        for item in safe["inventory"][:]:
            self.player["backpack"].append(item)
        safe["inventory"] = []
        if not safe["inventory"] and safe in self.safes:
            self.safes.remove(safe)

    # ==================== TITLE SCREEN ====================
    def draw_title_screen(self):
        self.canvas.create_text(600, 120, text="TOAST Engine", font=("Courier", 72, "bold"), fill="#ffcc00")
        self.canvas.create_text(600, 210, text=":Select a Character:", font=("Arial", 18), fill="#aaaaaa")
        sections = [
            (70, 310, 290, 560, "witch", "#ff4444", "Witch", self.selected_damage_type),
            (330, 310, 550, 560, "necromancer", "#00aa00", "Necromancer", self.selected_damage_type),
            (590, 310, 810, 560, "elemental", "#4488ff", "Elemental", self.selected_damage_type),
            (850, 310, 1070, 560, "diy", "#ffffff", "PNG", self.selected_damage_type)
        ]
        for sx, sy, ex, ey, ctype, base_col, name, damage_type in sections:
            if self.selected_char_type == ctype:
                for thick in range(8, 2, -2):
                    self.canvas.create_rectangle(sx - thick//2, sy - thick//2, ex + thick//2, ey + thick//2,
                                                 outline="#ffff00", width=thick//2)
            cx = (sx + ex) // 2
            if ctype == "witch":
                self.canvas.create_polygon([cx-22,sy+80+22, cx,sy+45+22, cx+22,sy+80+22], fill=self.selected_char_color if self.selected_char_type == ctype else base_col, outline="#660000", width=4)
            elif ctype == "necromancer":
                pts = []
                for i in range(6):
                    a = i * math.pi * 2 / 6
                    pts.extend([cx + 22 * math.cos(a), sy + 80 + 22 * math.sin(a)])
                self.canvas.create_polygon(pts, fill=self.selected_char_color if self.selected_char_type == ctype else base_col, outline="#003300", width=4)
            elif ctype == "elemental":
                pts = []
                for i in range(10):
                    a = i * math.pi * 2 / 10
                    pts.extend([cx + 22 * math.cos(a), sy + 80 + 22 * math.sin(a)])
                self.canvas.create_polygon(pts, fill=self.selected_char_color if self.selected_char_type == ctype else base_col, outline="#002266", width=4)
            else:
                if self.custom_preview:
                    self.canvas.create_image(cx, sy + 80, image=self.custom_preview)
                else:
                    self.canvas.create_rectangle(cx-35, sy+55, cx+35, sy+105, fill="#290D37", outline="#200A2C", width=4)
                    self.canvas.create_text(cx, sy+80, text="DIY", font=("Arial", 14, "bold"), fill="#9B00B5")
            self.canvas.create_text(cx, ey + 25, text=name, font=("Arial", 14), fill="white")
        if self.selected_char_type:
            dot_y = 480
            if self.selected_char_type == "witch":
                centers = [118, 188, 258]
                fills = ["#ff0000", "#4488ff", "#ffffff"]
                damages = ["Heat/Burn", "Cold/Freeze", "Physical/Bleeding"]
            elif self.selected_char_type == "necromancer":
                centers = [378, 448, 518]
                fills = ["#00aa00", "#222222", "#ffffff"]
                damages = ["Poison/Poison", "Decay/Rot", "Physical/Bleeding"]
            elif self.selected_char_type == "elemental":
                centers = [638, 708, 778]
                fills = ["#88ccff", "#ffff00", "#ffffff"]
                damages = ["Cold/Freeze", "Electric/Burn", "Physical/Bleeding"]
            else:
                centers = [898, 968, 1038]
                fills = ["#aa0000", "#222222", "#ffffff"]
                damages = ["Hot/Burn", "Decay/Poison", "Physical/Bleeding"]
            for i, cx in enumerate(centers):
                dot_color = fills[i]
                self.canvas.create_oval(cx-13, dot_y-13, cx+13, dot_y+13, fill=dot_color, outline="#660000", width=3)
                if self.selected_damage_type == damages[i]:
                    self.canvas.create_oval(cx-17, dot_y-17, cx+17, dot_y+17, outline="#c0c0c0", width=4)
        if self.selected_char_type:
            self.canvas.create_rectangle(490, 620, 710, 670, fill="#00ff00", outline="#ffff00")
            cx = 600  # adjust
            ey = 560  # adjust
            self.canvas.create_text(cx - 79, ey - 21, text=self.selected_damage_type, font=("Arial", 14), fill=self.selected_char_color if self.selected_char_color != "#222222" else "#00aa00" if self.selected_damage_type != "Decay/Rot" else "#aa0000")
            self.canvas.create_text(600, 645, text="START GAME", font=("Arial", 18, "bold"), fill="#111111")

    def draw_world(self):
        floor_pts = []
        for wx, wy in self.arena_points:
            sx, sy = self.world_to_screen(wx, wy, 0)
            floor_pts.extend([sx, sy])
        self.canvas.create_polygon(floor_pts, fill="#c9b38a", outline="")
        self.canvas.create_polygon(floor_pts, fill="", outline="#664422", width=28)
        if self.fpv_mode:
            cos = math.cos(-self.camera_yaw)
            sin = math.sin(-self.camera_yaw)
            visible = []
            for obs in self.obstacles:
                dx = obs["x"] - self.camera_x
                dy = obs["y"] - self.camera_y
                rx = dx * cos - dy * sin
                ry = dx * sin + dy * cos
                if ry > 20 and abs(rx) < ry * 1.25:
                    visible.append((ry, obs))
            visible.sort(reverse=True)
            for _, obs in visible:
                bx1, by1 = self.world_to_screen(obs["x"] - obs["w"]/2, obs["y"] - obs["h"]/2, 0)
                bx2, by2 = self.world_to_screen(obs["x"] + obs["w"]/2, obs["y"] - obs["h"]/2, 0)
                bx3, by3 = self.world_to_screen(obs["x"] + obs["w"]/2, obs["y"] + obs["h"]/2, 0)
                bx4, by4 = self.world_to_screen(obs["x"] - obs["w"]/2, obs["y"] + obs["h"]/2, 0)
                self.canvas.create_polygon([bx1,by1,bx2,by2,bx3,by3,bx4,by4], fill=obs["color"], outline="#333333", width=2)
                h = obs.get("height", 120)
                tx1, ty1 = self.world_to_screen(obs["x"] - obs["w"]/2, obs["y"] - obs["h"]/2, h)
                tx2, ty2 = self.world_to_screen(obs["x"] + obs["w"]/2, obs["y"] - obs["h"]/2, h)
                tx3, ty3 = self.world_to_screen(obs["x"] + obs["w"]/2, obs["y"] + obs["h"]/2, h)
                tx4, ty4 = self.world_to_screen(obs["x"] - obs["w"]/2, obs["y"] + obs["h"]/2, h)
                self.canvas.create_polygon([tx1,ty1,tx2,ty2,tx3,ty3,tx4,ty4], fill="#666666", outline="#333333")
                for px,py,tx,ty in [(bx1,by1,tx1,ty1),(bx2,by2,tx2,ty2),(bx3,by3,tx3,ty3),(bx4,by4,tx4,ty4)]:
                    self.canvas.create_line(px, py, tx, ty, fill="#444444", width=3)
        else:
            for obs in self.obstacles:
                if self.player and obs["x"] - obs["w"]/2 < self.player["x"] < obs["x"] + obs["w"]/2 and obs["y"] - obs["h"]/2 < self.player["y"] < obs["y"] + obs["h"]/2:
                    continue
                bx1, by1 = self.world_to_screen(obs["x"] - obs["w"]/2, obs["y"] - obs["h"]/2, 0)
                bx2, by2 = self.world_to_screen(obs["x"] + obs["w"]/2, obs["y"] - obs["h"]/2, 0)
                bx3, by3 = self.world_to_screen(obs["x"] + obs["w"]/2, obs["y"] + obs["h"]/2, 0)
                bx4, by4 = self.world_to_screen(obs["x"] - obs["w"]/2, obs["y"] + obs["h"]/2, 0)
                self.canvas.create_polygon([bx1,by1,bx2,by2,bx3,by3,bx4,by4], fill=obs["color"], outline="#333333", width=2)
                h = obs.get("height", 55)
                tx1, ty1 = bx1, by1 - h
                tx2, ty2 = bx2, by2 - h
                tx3, ty3 = bx3, by3 - h
                tx4, ty4 = bx4, by4 - h
                self.canvas.create_polygon([tx1,ty1,tx2,ty2,tx3,ty3,tx4,ty4], fill="#666666", outline="#333333")
                for px,py,tx,ty in [(bx1,by1,tx1,ty1),(bx2,by2,tx2,ty2),(bx3,by3,tx3,ty3),(bx4,by4,tx4,ty4)]:
                    self.canvas.create_line(px, py, tx, ty, fill="#444444", width=2)
        for wx, wy in self.windows:
            sx, sy = self.world_to_screen(wx, wy, 40)
            self.canvas.create_rectangle(sx-12, sy-28, sx+12, sy+28, fill="#88ccff")
            self.canvas.create_text(sx, sy-5, text="☀", font=("Arial", 14), fill="#ffee99")
        for safe in self.safes + [self.world_safe]:
            if safe is None: continue
            sx, sy = self.world_to_screen(safe["x"], safe["y"], 0)
            img = self.safe_img if safe["type"] == "safe" else self.safe1_img if safe["type"] == "safe_1" else None
            if img:
                self.canvas.create_image(sx, sy, image=img)
            else:
                self.canvas.create_rectangle(sx-25, sy-25, sx+25, sy+25, fill="#8B4513", outline="#ffff00", width=3)
                self.canvas.create_text(sx, sy, text="SAFE", font=("Arial", 10, "bold"), fill="#ffff00")
        for inter in self.interactives:
            sx, sy = self.world_to_screen(inter["x"], inter["y"], 0)
            if inter["img"]:
                self.canvas.create_image(sx, sy, image=inter["img"])
            else:
                self.canvas.create_rectangle(sx-20, sy-20, sx+20, sy+20, fill="#ff0000", outline="#ffffff")
                self.canvas.create_text(sx, sy, text=inter["name"], font=("Arial", 8), fill="#ffffff")

    def draw_player(self):
        if not self.player or self.fpv_mode: return
        sx, sy = self.world_to_screen(self.player["x"], self.player["y"], 0)
        facing = self.player["facing"]
        if self.player.get("custom_image"):
            img = self.custom_image_R if facing == "right" else self.custom_image_L if self.custom_image_L else self.custom_image
            if img:
                self.canvas.create_image(sx, sy, image=img)
            else:
                self.canvas.create_image(sx, sy, image=self.player["custom_image"])
        elif self.player["type"] == "witch":
            pts = [-22,0, 0,-35, 22,0]
            if facing == "left":
                pts = [p * -1 if i % 2 == 0 else p for i, p in enumerate(pts)]
            self.canvas.create_polygon([sx + pts[0], sy + pts[1], sx + pts[2], sy + pts[3], sx + pts[4], sy + pts[5]], fill=self.player["color"], outline="#660000", width=4)
        elif self.player["type"] == "necromancer":
            pts = []
            for i in range(6):
                a = i * math.pi * 2 / 6
                px = 22 * math.cos(a)
                py = 22 * math.sin(a)
                if facing == "left":
                    px *= -1
                pts.extend([sx + px, sy + py])
            self.canvas.create_polygon(pts, fill=self.player["color"], outline="#003300", width=4)
        elif self.player["type"] == "elemental":
            pts = []
            for i in range(10):
                a = i * math.pi * 2 / 10
                px = 22 * math.cos(a)
                py = 22 * math.sin(a)
                if facing == "left":
                    px *= -1
                pts.extend([sx + px, sy + py])
            self.canvas.create_polygon(pts, fill=self.player["color"], outline="#002266", width=4)
        else:
            self.canvas.create_oval(sx-22, sy-22, sx+22, sy+22, fill=self.player["color"], outline="#ffffff", width=4)
        self.canvas.create_text(sx, sy - 45, text=self.player["name"], font=("Arial", 11), fill="#ffffff")

    def draw_menu_ring(self):
        if not self.player or not self.menu_open: return
        sx, sy = self.world_to_screen(self.player["x"], self.player["y"])
        ring_r = 102
        if self.menu_type == "directional":
            short = ["↑", "↗", "→", "↘", "↓", "↙", "←", "↖"]
            full = ["Up", "Up-Right", "Right", "Down-Right", "Down", "Down-Left", "Left", "Up-Left"]
        else:
            short = ["W", "E", "D", "X", "S", "Z", "A", "Q"]
            full = [
                "Stop Follow" if self.current_mode == "follow" else "Follow cursor",
                "Stop Inspect" if self.current_mode == "inspect" else "Inspect area",
                "Unpin" if self.current_mode == "pin" else "Pin here",
                "Go Home",
                "Exit 1st-Person" if self.fpv_mode else "1st-Person-View",
                "Group",
                "Inventory",
                "Skill Tree"
            ]
        for i in range(8):
            ang = i * (2 * math.pi / 8) - math.pi / 2
            bx = sx + ring_r * math.cos(ang)
            by = sy + ring_r * math.sin(ang)
            self.canvas.create_oval(bx-20, by-20, bx+20, by+20, fill="#222222", outline="#666666", width=4)
            self.canvas.create_text(bx, by, text=short[i], font=("Arial", 14, "bold"), fill="#ffaa00")
            self.canvas.create_text(bx, by + 32, text=full[i], font=("Arial", 9), fill="#f0f4f0")

    def draw_safe_menu_ring(self):
        if not self.selected_safe or not self.safe_menu_open: return
        sx, sy = self.world_to_screen(self.selected_safe["x"], self.selected_safe["y"])
        ring_r = 102
        short = ["O", "T", "", "", "B", "P", "", "A"]
        full = ["Open", "Take Top", "", "", "Break", "Trap", "", "Take All"]
        for i in range(8):
            if full[i] == "": continue
            ang = i * (2 * math.pi / 8) - math.pi / 2
            bx = sx + ring_r * math.cos(ang)
            by = sy + ring_r * math.sin(ang)
            self.canvas.create_oval(bx-20, by-20, bx+20, by+20, fill="#222222", outline="#666666", width=4)
            self.canvas.create_text(bx, by, text=short[i], font=("Arial", 14, "bold"), fill="#ffaa00")
            self.canvas.create_text(bx, by + 32, text=full[i], font=("Arial", 9), fill="#f0f4f0")

    def draw_settings_overlay(self):
        cx, cy = 600, 380
        self.canvas.create_rectangle(cx-210, cy-160, cx+210, cy+160, fill="#222222", outline="#333300", width=4)
        self.canvas.create_text(cx, cy-110, text=f"SETTINGS - {self.player['name']}", font=("Arial", 16, "bold"), fill="#ffff00")
        self.canvas.create_text(cx, cy-80, text=f"Type: {self.player['type']}", font=("Arial", 12), fill="#aaaaaa")
        self.canvas.create_text(cx, cy-60, text=f"Damage Type: {self.player['damage_type']}", font=("Arial", 12), fill="#aaaaaa")
        self.canvas.create_text(cx, cy-40, text=f"Color: {self.player['color'].upper()}", font=("Arial", 12), fill="#aaaaaa")
        self.canvas.create_text(cx, cy-20, text=f"Level: {self.player['level']} Kills: {self.player['kills']}", font=("Arial", 12), fill="#aaaaaa")
        self.canvas.create_text(cx, cy+30, text=f"Skill Points: {round(self.skill_points,1)}", font=("Arial", 12), fill="#00ff00")
        self.canvas.create_rectangle(540, 480, 660, 510, fill="#ff2222", outline="#ffffff")
        self.canvas.create_text(600, 495, text="CLOSE", font=("Arial", 12, "bold"), fill="#ffffff")

    def draw_skilltree(self):
        cx, cy = 600, 380
        self.canvas.create_rectangle(cx-210, cy-160, cx+210, cy+160, fill="#222222", outline="#ffcc00", width=4)
        self.canvas.create_text(cx, cy-120, text="SKILL TREE", font=("Arial", 18, "bold"), fill="#ffcc00")
        self.canvas.create_text(cx-140, cy-50, text=f"Body lvl {self.player['body']}", font=("Arial", 12), fill="#00ff88")
        self.canvas.create_text(cx, cy-50, text=f"Combat lvl {self.player['combat']}", font=("Arial", 12), fill="#ff4444")
        self.canvas.create_text(cx+140, cy-50, text=f"Aura lvl {self.player['aura']}", font=("Arial", 12), fill="#4488ff")
        self.canvas.create_text(cx, cy+20, text=f"Points: {round(self.skill_points,1)}", fill="#ffff00")
        self.canvas.create_rectangle(390, 310, 490, 350, fill="#00ff88")
        self.canvas.create_text(440, 330, text="BODY", fill="#111")
        self.canvas.create_rectangle(530, 310, 630, 350, fill="#ff4444")
        self.canvas.create_text(580, 330, text="COMBAT", fill="#111")
        self.canvas.create_rectangle(670, 310, 770, 350, fill="#4488ff")
        self.canvas.create_text(720, 330, text="AURA", fill="#111")
        self.canvas.create_rectangle(540, 520, 660, 550, fill="#ff2222")
        self.canvas.create_text(600, 535, text="CLOSE", fill="#ffffff")

    def draw_pause_menu(self):
        self.canvas.create_rectangle(300, 200, 900, 600, fill="#111111", outline="#333300", width=8)
        self.canvas.create_text(600, 240, text="PAUSED", font=("Courier", 42, "bold"), fill="#ffff00")
        btns = [("Return to Game", 270), ("Reset (Same Character)", 330), ("Repick Character", 390), ("Exit Game", 450), ("Aim Dot: " + self.aimdots[self.aimdot_selected], 510)]
        for i, (text, y) in enumerate(btns):
            outline = "#ffff00" if self.pause_hover == i else "#333300"
            width = 5 if self.pause_hover == i else 3
            self.canvas.create_rectangle(420, y, 780, y+40, fill="#333333", outline=outline, width=width)
            self.canvas.create_text(600, y+20, text=text, font=("Arial", 16, "bold"), fill="#ffffff")

    def draw_hud(self):
        if self.state != "GAME" or not self.player: return
        mm_x = 40
        mm_y = 600
        mm_size = 160
        center_x = mm_x + mm_size / 2
        center_y = mm_y + mm_size / 2
        outer_r = mm_size / 2 * 1.35
        outer_pts = []
        for i in range(8):
            ang = i * (2 * math.pi / 8)
            px = center_x + outer_r * math.cos(ang)
            py = center_y + outer_r * math.sin(ang)
            outer_pts.extend([px, py])
        self.canvas.create_polygon(outer_pts, fill="#3a2a1a", outline="#664422", width=4)
        inner_r = mm_size / 2 * 0.92
        inner_pts = []
        for i in range(8):
            ang = i * (2 * math.pi / 8)
            px = center_x + inner_r * math.cos(ang)
            py = center_y + inner_r * math.sin(ang)
            inner_pts.extend([px, py])
        self.canvas.create_polygon(inner_pts, fill="#664422", outline="#c9b38a", width=4)
        rel_scale = inner_r / (self.arena_radius * 0.75)
        for obs in self.obstacles[:8]:
            o_rx = (obs["x"] - self.camera_x) * rel_scale
            o_ry = (obs["y"] - self.camera_y) * rel_scale
            if abs(o_rx) < inner_r and abs(o_ry) < inner_r:
                self.canvas.create_rectangle(center_x + o_rx - 2, center_y + o_ry - 2,
                                             center_x + o_rx + 2, center_y + o_ry + 2, fill="#555555")
        p_rx = (self.player["x"] - self.camera_x) * rel_scale
        p_ry = (self.player["y"] - self.camera_y) * rel_scale
        arrow_ang = math.atan2(self.player["vy"], self.player["vx"]) if self.player["vx"] or self.player["vy"] else self.camera_yaw
        ax = center_x + p_rx
        ay = center_y + p_ry
        a1x = ax + 18 * math.cos(arrow_ang)
        a1y = ay + 18 * math.sin(arrow_ang)
        a2x = ax + 8 * math.cos(arrow_ang + 2.3)
        a2y = ay + 8 * math.sin(arrow_ang + 2.3)
        a3x = ax + 8 * math.cos(arrow_ang - 2.3)
        a3y = ay + 8 * math.sin(arrow_ang - 2.3)
        self.canvas.create_polygon([a1x, a1y, a2x, a2y, a3x, a3y], fill="#00ff00", outline="#000000", width=2)
        loot_x = 78
        loot_y = 50
        row_h = 72
        col_w = 72
        cats = ["Weapons", "Armor", "Usables", "Skills"]
        for row in range(4):
            ry = loot_y + row * row_h
            # TLA row title image or fallback text with backer
            tla_x = loot_x - 45
            tla_y = ry + row_h // 2
            if row in self.tla_imgs and self.tla_imgs[row]:
                self.canvas.create_image(tla_x + 4, tla_y, image=self.tla_imgs[row])
            else:
                self.canvas.create_rectangle(tla_x - 5, ry + 4, loot_x - 10, ry + row_h - 6, fill="#222222", outline="#00ffcc", width=1)
                self.canvas.create_text(loot_x - 8, ry + 8, text=cats[row], font=("Arial", 9), fill="#aaaaaa", anchor="e")
            if self.is_tla_row_open(row):
                for col in range(3):
                    cx = loot_x + col * col_w
                    idx = (self.loot_offsets[row] + col) % 3
                    item = self.loot_rows[row][idx] or "—"
                    self.canvas.create_rectangle(cx, ry, cx + col_w - 5, ry + row_h - 5, fill="#222222", outline="#5f6810", width=2)
                    if item in self.item_imgs and self.item_imgs[item]:
                        self.canvas.create_image(cx + col_w / 2, ry + row_h / 2, image=self.item_imgs[item])
                    else:
                        self.canvas.create_text(cx + col_w / 2, ry + row_h / 2 - 4, text=str(item)[:9], font=("Arial", 9), fill="#ffffff")
                self.canvas.create_polygon([loot_x+3*col_w+25, ry+27, loot_x+3*col_w+10, ry+17, loot_x+3*col_w+10, ry+37], fill="#5f6810", outline="")
            else:
                self.canvas.create_polygon([loot_x+3*col_w-205, ry+27, loot_x+3*col_w-190, ry+17, loot_x+3*col_w-190, ry+37], fill="#5f6810", outline="")
        drawer_y = loot_y + 4 * row_h + 8
        # Inventory tab (reduced width)
        inv_tab_x = 190
        inv_tab_w = 110
        drawer_active = self.inventory_drawer_open
        tab_color = "#4b520d" if drawer_active else "#222222"
        self.canvas.create_rectangle(inv_tab_x, drawer_y, inv_tab_x + inv_tab_w, drawer_y + 26, fill=tab_color, outline="#4b520d", width=3)
        if self.i_tab_img:
            img = self.i_tab_open_img if drawer_active else self.i_tab_img
            self.canvas.create_image(inv_tab_x + inv_tab_w // 2, drawer_y + 13, image=img)
        else:
            self.canvas.create_text(inv_tab_x + inv_tab_w // 2, drawer_y + 13, text="INVENTORY", font=("Arial", 11, "bold"), fill="#111111")
        # Safe tab (reduced width, left, dynamic y)
        safe_tab_x = 78
        safe_tab_w = 110
        safe_tab_y = drawer_y + 36 if not self.inventory_drawer_open else drawer_y + 200
        safe_active = self.safe_drawer_open
        safe_tab_color = "#ffaa00" if safe_active else "#222222"
        self.canvas.create_rectangle(safe_tab_x, safe_tab_y, safe_tab_x + safe_tab_w, safe_tab_y + 26, fill=safe_tab_color, outline="#ffaa00", width=3)
        if self.safe_icon_img:
            img = self.s_tab_open_img if safe_active else self.s_tab_img
            self.canvas.create_image(safe_tab_x + safe_tab_w // 2, safe_tab_y + 13, image=img)
        else:
            self.canvas.create_text(safe_tab_x + safe_tab_w // 2, safe_tab_y + 13, text="SAFE", font=("Arial", 11, "bold"), fill="#111111")
        # Inventory drawer content
        if self.inventory_drawer_open and self.player:
            d_y = drawer_y + 32
            bp_x = 133
            bp_y = d_y + 10
            if self.bpack_img:
                self.canvas.create_image(bp_x - 28, bp_y + 49, image=self.bpack_img)
            else:
                self.canvas.create_text(bp_x - 5, bp_y - 20, text="BACKPACK", font=("Arial", 11, "bold"), fill="#00ffcc", anchor="w")
            # Left arrow for upper
            self.canvas.create_polygon([bp_x+155, bp_y+24, bp_x+170, bp_y+14, bp_x+170, bp_y+34], fill="#4b520d")
            # Right arrow for lower
            self.canvas.create_polygon([bp_x+170, bp_y+66, bp_x+155, bp_y+56, bp_x+155, bp_y+76], fill="#4b520d")
            for row in range(2):
                ry = bp_y + row * 48
                for col in range(3):
                    cx = bp_x + col * 48
                    idx = self.backpack_offset + row * 3 + col
                    item = self.player["backpack"][idx] if idx < len(self.player["backpack"]) else "—"
                    self.canvas.create_rectangle(cx, ry, cx + 44, ry + 42, fill="#333333", outline="#4b520d", width=2)
                    if item in self.item_imgs and self.item_imgs[item]:
                        self.canvas.create_image(cx + 22, ry + 21, image=self.item_imgs[item])
                    else:
                        self.canvas.create_text(cx + 22, ry + 21, text=str(item)[:6], font=("Arial", 8), fill="#ffb31a")
            eq_y = bp_y + 110
            if self.equip_img:
                self.canvas.create_image(bp_x + 142, eq_y + 37, image=self.equip_img)
            else:
                self.canvas.create_text(bp_x - 5, eq_y - 20, text="EQUIP", font=("Arial", 11, "bold"), fill="#00ffcc", anchor="w")
            labels = ['Head', 'Chest', 'Legs', 'Feet', 'Left', 'Right']
            for row in range(2):
                ry = eq_y + row * 38
                for col in range(3):
                    i = row * 3 + col
                    fill = "#ff0000" if i == self.highlighted_slot else "#222222"
                    cx = 133 + col * 38
                    self.canvas.create_rectangle(cx, ry, cx + 34, ry + 34, fill=fill, outline="#13737e", width=2)
                    item = self.player["equip"][i] or "—"
                    if item in self.item_imgs and self.item_imgs[item]:
                        self.canvas.create_image(cx + 17, ry + 17, image=self.item_imgs[item])
                    else:
                        self.canvas.create_text(cx + 17, ry + 17, text=str(item)[:4], font=("Arial", 8), fill="#ffffff")
                    self.canvas.create_text(cx + 17, ry - 8, text=labels[i], font=("Arial", 6), fill="#aaaaaa")
        # Safe drawer content
        if self.safe_drawer_open and (self.selected_safe or self.world_safe):
            safe = self.selected_safe or self.world_safe
            safe_d_y = safe_tab_y + 28
            self.canvas.create_rectangle(30, safe_d_y, 250, safe_d_y + 125, fill="#222222", outline="#ffaa00", width=3)
            if self.safe_icon_img:
                self.canvas.create_image(140, safe_d_y + 18, image=self.safe_icon_img)
            else:
                self.canvas.create_text(140, safe_d_y + 18, text="SAFE", font=("Arial", 11, "bold"), fill="#ffaa00")
            # Arrows
            self.canvas.create_polygon([45+155, safe_d_y + 62, 45+170, safe_d_y + 52, 45+170, safe_d_y + 72], fill="#4b520d")  # left upper
            self.canvas.create_polygon([45+170, safe_d_y + 134, 45+155, safe_d_y + 144, 45+155, safe_d_y + 174], fill="#4b520d")  # right lower
            for row in range(2):
                ry = safe_d_y + 45 + row * 48
                for col in range(3):
                    cx = 45 + col * 48
                    idx = self.safe_offset + row * 3 + col
                    item = safe["inventory"][idx] if idx < len(safe["inventory"]) else "—"
                    self.canvas.create_rectangle(cx, ry, cx + 44, ry + 36, fill="#333333", outline="#4b520d", width=2)
                    if item in self.item_imgs and self.item_imgs[item]:
                        self.canvas.create_image(cx + 22, ry + 21, image=self.item_imgs[item])
                    else:
                        self.canvas.create_text(cx + 22, ry + 21, text=str(item)[:6], font=("Arial", 8), fill="#4b520d")
        # Hotbar
        hb_y = 683
        hb_start = 600 - (9 * 58 // 2)
        for i in range(9):
            hx = hb_start + i * 58
            item = self.hotbar[i]
            col = "#333333" if item else "#1a1a1a"
            self.canvas.create_rectangle(hx, hb_y, hx + 54, hb_y + 54, fill=col, outline="#7a7a7a", width=3)
            if item:
                if item in self.item_imgs and self.item_imgs[item]:
                    self.canvas.create_image(hx + 27, hb_y + 27, image=self.item_imgs[item])
                else:
                    self.canvas.create_text(hx + 27, hb_y + 27, text=str(item)[:7], font=("Arial", 10), fill="#ffffff")
            self.canvas.create_text(hx + 46, hb_y + 6, text="x", font=("Arial", 13, "bold"), fill="#ff0000")
            self.canvas.create_text(hx + 7, hb_y + 47, text=str(i + 1), font=("Arial", 9), fill="#aaaaaa")
        # Groups
        g_x = 926
        g_y = 40
        g_w = 220
        g_h = 325
        self.canvas.create_rectangle(g_x, g_y, g_x + g_w, g_y + g_h, fill="#222222", outline="#7a7a7a", width=4)
        self.canvas.create_text(g_x + g_w / 2, g_y + 16, text="GROUPS", font=("Arial", 14, "bold"), fill="#ffff00")
        num_tabs = len(self.groups)
        tab_h = max(24, 265 // max(4, num_tabs))
        for i in range(num_tabs):
            ty = g_y + 45 + i * tab_h
            fill = "#00ff88" if i == self.current_group_index else "#444444"
            self.canvas.create_rectangle(g_x - 8, ty, g_x + 38, ty + tab_h - 3, fill=fill, outline="#7a7a7a", width=2)
            short = self.group_names[i][:5]
            self.canvas.create_text(g_x + 15, ty + tab_h / 2, text=short, font=("Arial", 10, "bold"),
                                    fill="#111111" if i == self.current_group_index else "#ffffff")
        plus_y = g_y + 45 + num_tabs * tab_h + 8
        self.canvas.create_rectangle(g_x - 8, plus_y, g_x + 38, plus_y + 28, fill="#00ff00", outline="#666666")
        self.canvas.create_text(g_x + 15, plus_y + 14, text="+", font=("Arial", 18, "bold"), fill="#111111")
        list_x = g_x + 48
        list_y = g_y + 45
        list_h = 235
        block_h = 41
        vis = 5
        blocks = self.groups[self.current_group_index]
        for v in range(vis):
            b_idx = self.group_scroll_offset + v
            if b_idx >= len(blocks): break
            by = list_y + v * block_h
            self.canvas.create_rectangle(list_x, by, list_x + 155, by + block_h - 3, fill="#333333", outline="#7a7a7a", width=2)
            self.canvas.create_text(list_x + 12, by + block_h / 2, text=blocks[b_idx], font=("Arial", 11), fill="#ffffff", anchor="w")
            self.canvas.create_text(list_x + 165, by + block_h / 2 - 2, text="x", font=("Arial", 15, "bold"), fill="#ff2222")
        if len(blocks) > vis:
            self.canvas.create_polygon([list_x + 165, list_y - 8, list_x + 180, list_y + 8, list_x + 150, list_y + 8], fill="#ffff00")
            self.canvas.create_polygon([list_x + 165, list_y + list_h + 5, list_x + 180, list_y + list_h - 8, list_x + 150, list_y + list_h - 8], fill="#ffff00")
        # Circular selected
        if self.selected and self.player:
            circ_x = 1050
            circ_y = 650
            r = 88
            self.canvas.create_oval(circ_x - r, circ_y - r, circ_x + r, circ_y + r, fill="#1a1a1a", outline="#7a7a7a", width=6)
            if self.player.get("custom_preview"):
                self.canvas.create_image(circ_x, circ_y - 5, image=self.player["custom_preview"])
            elif self.player["type"] == "witch":
                self.canvas.create_polygon([circ_x-22, circ_y, circ_x, circ_y-28, circ_x+22, circ_y], fill=self.player["color"], outline="#7a7a7a")
            elif self.player["type"] == "necromancer":
                pts = []
                for i in range(6):
                    a = i * math.pi * 2 / 6
                    pts.extend([circ_x + 22 * math.cos(a), circ_y + 22 * math.sin(a)])
                self.canvas.create_polygon(pts, fill=self.player["color"], outline="#003300")
            else:
                self.canvas.create_oval(circ_x-26, circ_y-26, circ_x+26, circ_y+26, fill=self.player["color"], outline="#e1e9e1", width=3)
            h_pct = self.player["health"] / self.player["max_health"]
            bar_x = circ_x + r + 12
            bar_top = circ_y - r + 12
            bar_hh = r * 2 - 24
            self.canvas.create_rectangle(bar_x, bar_top, bar_x + 14, bar_top + bar_hh, fill="#222222")
            self.canvas.create_rectangle(bar_x, bar_top + bar_hh * (1 - h_pct), bar_x + 14, bar_top + bar_hh, fill="#ff4444")
            self.canvas.create_text(bar_x + 7, bar_top - 12, text="HP", font=("Arial", 9, "bold"), fill="#ff4444")
            s_pct = self.player["stamina"] / self.player["max_stamina"]
            bar_y = circ_y + r + 10
            bar_left = circ_x - r + 12
            bar_ww = r * 2 - 24
            self.canvas.create_rectangle(bar_left, bar_y, bar_left + bar_ww, bar_y + 14, fill="#222222")
            self.canvas.create_rectangle(bar_left, bar_y, bar_left + bar_ww * s_pct, bar_y + 14, fill="#00ff88")
            self.canvas.create_text(bar_left - 5, bar_y + 7, text="STA", font=("Arial", 9, "bold"), fill="#00ff88", anchor="e")
        if self.safe_menu_open:
            self.draw_safe_menu_ring()
        if self.dragging_item:
            self.canvas.create_rectangle(self.mouse_screen_x - 25, self.mouse_screen_y - 20,
                                         self.mouse_screen_x + 35, self.mouse_screen_y + 18,
                                         fill="#ffff00", outline="#000000", width=2)
            item = self.dragging_item
            if item in self.item_imgs and self.item_imgs[item]:
                self.canvas.create_image(self.mouse_screen_x + 5, self.mouse_screen_y, image=self.item_imgs[item])
            else:
                self.canvas.create_text(self.mouse_screen_x + 5, self.mouse_screen_y, text=str(item)[:8],
                                        font=("Arial", 10, "bold"), fill="#111111")

    def draw_arrows(self):
        for d, pos in self.arrow_positions.items():
            if self.arrow_imgs.get(d):
                self.canvas.create_image(pos[0], pos[1], image=self.arrow_imgs[d], tags=('arrow', f'arrow_{d}'))
            else:
                size = 22
                ang_base = {'top': -math.pi/2, 'topright': -math.pi/4, 'right': 0, 'bottomright': math.pi/4,
                            'bottom': math.pi/2, 'bottomleft': 3*math.pi/4, 'left': math.pi, 'topleft': -3*math.pi/4}[d]
                points = []
                for j in [0, 2*math.pi/3, 4*math.pi/3]:
                    ang = ang_base + j
                    px = pos[0] + size * math.cos(ang)
                    py = pos[1] + size * math.sin(ang)
                    points.extend([px, py])
                self.canvas.create_polygon(points, fill="#ffff00", outline="#000000", width=2, tags=('arrow', f'arrow_{d}'))

    def draw(self):
        self.canvas.delete("all")
        if self.state == "TITLE":
            self.draw_title_screen()
        elif self.state == "GAME" or self.pause_open:
            self.draw_world()
            self.draw_arrows()
            self.draw_player()
            if self.menu_open: self.draw_menu_ring()
            if self.safe_menu_open: self.draw_safe_menu_ring()
            self.draw_hud()
            if self.settings_open: self.draw_settings_overlay()
            if self.skilltree_open: self.draw_skilltree()
            if self.fpv_mode:
                self.canvas.create_rectangle(200, 30, 1000, 80, fill="#111111")
                self.canvas.create_text(600, 55, text="1ST-PERSON VIEW: W/A/S/D + Mouse • Right-click Exit", font=("Arial", 14), fill="#ffff00")
            if self.pause_open:
                self.draw_pause_menu()
            # Aim dot
            if self.aimdots[self.aimdot_selected] == "Default":
                self.canvas.create_oval(self.mouse_screen_x-6, self.mouse_screen_y-6, self.mouse_screen_x+6, self.mouse_screen_y+6, outline="#ffffff", width=2)
                self.canvas.create_oval(self.mouse_screen_x-2, self.mouse_screen_y-2, self.mouse_screen_x+2, self.mouse_screen_y+2, fill="#ffffff")
            else:
                key = f"aimdot_{self.aimdots[self.aimdot_selected]}"
                if key in self.item_imgs:
                    self.canvas.create_image(self.mouse_screen_x, self.mouse_screen_y, image=self.item_imgs[key])

    def spawn_safe(self):
        if not self.player: return
        nx = self.player["x"] + random.uniform(-150, 150)
        ny = self.player["y"] + random.uniform(-150, 150)
        self.safes.append({"x": nx, "y": ny, "inventory": [], "owner": "System_Owned", "hits_left": 9, "trapped": False, "type": "safe"})

    def spawn_assist_safe(self):
        if not self.player: return
        ang = random.uniform(0, 2*math.pi)
        dist = 200
        nx = self.player["x"] + dist * math.cos(ang)
        ny = self.player["y"] + dist * math.sin(ang)
        inv = ["Health", "Coin", "Coin", "Spliff", "Spliff", "Spliff", "Zip Light"]
        self.safes.append({"x": nx, "y": ny, "inventory": inv, "owner": "System_Owned", "hits_left": 9, "trapped": False, "type": "safe_1"})

    def game_update(self):
        self.time += 0.1
        if self.state == "GAME" and self.player and not self.menu_open and not self.safe_menu_open and not self.pause_open:
            old_x = self.player["x"]
            old_y = self.player["y"]
            if not self.fpv_mode:
                self.camera_x = self.camera_x * 0.82 + self.camera_target_x * 0.18
                self.camera_y = self.camera_y * 0.82 + self.camera_target_y * 0.18
            if self.fpv_mode:
                self.camera_yaw = self.camera_yaw * 0.94 + self.target_yaw * 0.7
                self.camera_pitch = self.camera_pitch * 0.99 + self.target_pitch * 0.99
                self.camera_pitch = max(-48, min(48, self.camera_pitch))
                speed = 6.0
                dx = dy = 0.0
                if 'w' in self.keys: dx += math.cos(self.camera_yaw) * speed; dy += math.sin(self.camera_yaw) * speed
                if 's' in self.keys: dx -= math.cos(self.camera_yaw) * speed; dy -= math.sin(self.camera_yaw) * speed
                if 'a' in self.keys: dx -= math.sin(self.camera_yaw) * speed; dy += math.cos(self.camera_yaw) * speed
                if 'd' in self.keys: dx += math.sin(self.camera_yaw) * speed; dy -= math.cos(self.camera_yaw) * speed
                new_x = self.player["x"] + dx
                new_y = self.player["y"] + dy
                if not self.collides(new_x, new_y):
                    self.player["x"], self.player["y"] = new_x, new_y
                else:
                    if not self.collides(self.player["x"] + dx, self.player["y"]): self.player["x"] += dx
                    if not self.collides(self.player["x"], self.player["y"] + dy): self.player["y"] += dy
                self.player["x"], self.player["y"] = self.clamp_to_arena(self.player["x"], self.player["y"])
                self.player["vx"] = self.player["x"] - old_x
                self.player["vy"] = self.player["y"] - old_y
                if self.player["vx"] > 0:
                    self.player["facing"] = "right"
                elif self.player["vx"] < 0:
                    self.player["facing"] = "left"
                moving = abs(dx) + abs(dy) > 0.1
                self.bob = math.sin(self.time * 9) * 4.5 if moving else 0.0
                if moving:
                    self.player["stamina"] = max(0.0, self.player["stamina"] - 0.09)
                else:
                    self.player["stamina"] = min(self.player["max_stamina"], self.player["stamina"] + 0.18)
                self.camera_x = self.player["x"]
                self.camera_y = self.player["y"]
            else:
                if self.current_mode == "follow" and not self.hud_hover:
                    self.target_x, self.target_y = self.screen_to_world(self.mouse_screen_x, self.mouse_screen_y)
                elif self.current_mode == "inspect":
                    self.inspect_timer = (self.inspect_timer + 1) % 30
                    if self.inspect_timer == 0:
                        self.target_x = self.inspect_center_x + random.uniform(-300, 300)
                        self.target_y = self.inspect_center_y + random.uniform(-300, 300)
                if self.current_mode != "pin" and self.target_x is not None and not self.hud_hover:
                    dx = self.target_x - self.player["x"]
                    dy = self.target_y - self.player["y"]
                    dist = math.hypot(dx, dy)
                    if dist > 7:
                        speed = 4.5 if self.current_mode == "inspect" else 9.5
                        new_x = self.player["x"] + (dx / dist) * speed
                        new_y = self.player["y"] + (dy / dist) * speed
                        if not self.collides(new_x, new_y):
                            self.player["x"], self.player["y"] = new_x, new_y
                        self.player["x"], self.player["y"] = self.clamp_to_arena(self.player["x"], self.player["y"])
                        self.player["vx"] = self.player["x"] - old_x
                        self.player["vy"] = self.player["y"] - old_y
                        if self.player["vx"] > 0:
                            self.player["facing"] = "right"
                        elif self.player["vx"] < 0:
                            self.player["facing"] = "left"
                        if random.random() < 0.014:
                            if random.random() < 0.04:
                                self.spawn_safe()
                            else:
                                add_sp = 0.1
                                self.skill_points = min(15.0, self.skill_points + add_sp)
                                if self.current_mode == "inspect":
                                    self.inspect_sp += add_sp
                                    if self.inspect_sp >= 3.4 and not self.assist_given:
                                        self.assist_given = True
                                        self.spawn_assist_safe()
                    elif self.current_mode != "inspect":
                        self.target_x = None
            # Empty safe fade on collision
            for safe in self.safes[:]:
                if math.hypot(self.player["x"] - safe["x"], self.player["y"] - safe["y"]) < 40 and not safe["inventory"]:
                    self.safes.remove(safe)
                    break
            # Interactive collision
            for inter in self.interactives[:]:
                if math.hypot(self.player["x"] - inter["x"], self.player["y"] - inter["y"]) < 40:
                    self.handle_interactive_left(inter)
            # Edge arrows (hover only) — camera scroll only
            if self.edge_scroll_dir is not None:
                dx, dy = self.dxdy[self.edge_scroll_dir]
                self.camera_target_x += dx
                self.camera_target_y += dy
            # Interactive directional menu (persistent only)
            if self.persistent_scroll is not None:
                d = self.persistent_scroll
                if isinstance(d, int):
                    ang = d * (2 * math.pi / 8) - math.pi / 2
                    dx = 8 * math.cos(ang)
                    dy = 8 * math.sin(ang)
                else:
                    dx, dy = self.dxdy.get(d, (0, 0))
                self.camera_target_x += dx
                self.camera_target_y += dy
                if self.player:
                    self.player["x"] += dx
                    self.player["y"] += dy
        self.draw()
        self.root.after(30, self.game_update)

    def on_close(self):
        if self.clip_supported:
            self.clip_cursor(False)
        if self.platform == "Linux" and self.x11_display and self.x11_lib:
            try:
                self.x11_lib.XCloseDisplay(self.x11_display)
            except:
                pass
        if self.player: self.save_crumbs()
        self.root.destroy()

if __name__ == "__main__":
    bSIM()
