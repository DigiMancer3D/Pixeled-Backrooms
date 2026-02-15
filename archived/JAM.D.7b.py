import tkinter as tk
from tkinter import filedialog, messagebox, ttk, simpledialog
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

# ==================== TOOLTIP CLASS ====================
class Tooltip:
    def __init__(self, widget, text):
        self.widget = widget
        self.text = text
        self.tip_window = None
        widget.bind("<Enter>", self.show_tip)
        widget.bind("<Leave>", self.hide_tip)

    def show_tip(self, event=None):
        x = self.widget.winfo_rootx() + 25
        y = self.widget.winfo_rooty() + 25
        self.tip_window = tk.Toplevel(self.widget)
        self.tip_window.wm_overrideredirect(True)
        self.tip_window.wm_geometry(f"+{x}+{y}")
        label = tk.Label(self.tip_window, text=self.text, justify=tk.LEFT,
                         background="#ffffe0", relief=tk.SOLID, borderwidth=1,
                         font=("Arial", 9), padx=6, pady=4)
        label.pack()

    def hide_tip(self, event=None):
        if self.tip_window:
            self.tip_window.destroy()
            self.tip_window = None

# ==================== SCROLLABLE FRAME ====================
class ScrolledFrame(tk.Frame):
    def __init__(self, parent, *args, **kwargs):
        tk.Frame.__init__(self, parent, *args, **kwargs)
        self.canvas = tk.Canvas(self, bg=parent['bg'], highlightthickness=0)
        self.scrollbar = tk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.scrollable_frame = tk.Frame(self.canvas, bg=parent['bg'])
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        )
        self.canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        self.scrollbar.pack(side="right", fill="y")

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
            "arcs": []
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
            0: [4, 5], # Top -> TL, TR
            1: [5, 6], # Right -> TR, BR
            2: [6, 7], # Bottom -> BR, BL
            3: [4, 7], # Left -> TL, BL
            4: [4, 7], # Inner-Left
            5: [4, 5, 6, 7], # Inner-Center (all 4 diagonals)
            6: [5, 6], # Inner-Right
        }
        self.map_positions = {}
        self.current_selected_map_id = None
        self.selected_center = None
        self.pan_offset_x = 0
        self.pan_offset_y = 0
        self.is_panning = False
        self.pan_start_x = 0
        self.pan_start_y = 0
        # Arc system (PB-compatible)
        self.arcs = []
        self.current_arc_index = None
        self.arc_undo_stack = []
        self.arc_redo_stack = []
        self.last_arc_state = None
        self.arc_name_var = tk.StringVar(value="Title the Arc")
        self.arc_estimated_type_var = tk.StringVar(value="2-Finish (E2F)")
        self.arc_zone_type_var = tk.StringVar(value="Safe")
        self.arc_start_msg_var = tk.StringVar(value="Start Message")
        self.arc_map_var = tk.StringVar(value="")
        self.arc_map_type_var = tk.StringVar(value="Import")
        self.arc_confirm_msg_var = tk.StringVar(value="Confirm Message")
        # Script injector state
        self.current_script_type = None
        self.current_form_widgets = {}
        self.bind_var = None
        self.key_field1_label = None
        self.key_field2_label = None
        self.key_field1_entry = None
        self.key_field2_entry = None
        self.ai_listbox = None
        # Data Phrases
        self.data_phrases = ["exit", "enter", "kill", "death", "squash", "XYZ", "pick", "acts", "touch", "user", "jim", "sarah", "bob", "obj", "weap", "armed", "arm", "speed", "faster", "slower", "slow", "glue", "hot", "cold", "froze", "flame", "drop", "xplode", "burp", "burpee", "slothee", "plop", "wrap", "parw", "par"]
        self.tooltips = {
            "exit": "activates when user exits said map/zone type",
            "enter": "activates when the user loads in, wraps in, enters or first interacts with said map/zone type",
            "kill": "when a non-player enemy, mini-boss, boss is killed",
            "death": "when a non-player NPC is killed",
            "squash": "when a non-player user is killed",
            "XYZ": "when a player user is killed",
            "pick": "when a user picks up something or activates an enemy, mini-boss, boss",
            "acts": "when a user activates something (normally by touch) or activates the following without touch: an enemy, mini-boss, boss",
            "touch": "when anything before this touches anything after this; if events are before/after -> activator",
            "user": "any non-player user and active user",
            "jim": "only any non-player non-active user",
            "sarah": "only the active user",
            "bob": "non-enemy; [NPCs, non-player user, active user]",
            "obj": "any non-weapon objects",
            "weap": "weapons",
            "armed": "armor",
            "arm": "human arm or limb",
            "speed": "increase speed",
            "faster": "increase attack speed",
            "slower": "decrease attack speed",
            "slow": "decrease speed",
            "glue": "locks creature/object in place for a limited amount of time",
            "hot": "burns creature/object for a limited amount of time; no-spread",
            "cold": "creature/object frost damage for limited time; slows target more over time; no-spread",
            "froze": "creature/object ice damage for limited time; locks target during effect, damage multiples over time; spreads",
            "flame": "creature/object fire damage & burn damage for limited time; burn damage multiples over time; spreads",
            "drop": "anything before this is droppable; if event before/after this -> activator on drop",
            "xplode": "corpse, live-enemy, object is exploadable; if event before/after -> activator",
            "burp": "exploads target; if event before/after -> activator",
            "burpee": "user gains fitness",
            "slothee": "user looses fitness",
            "plop": "user drops something, if paired with *plop* -> force object to drop; can pair with user",
            "wrap": "user enter wraps/portals or enters a map/zone without the use of a door or opening and didn't die",
            "parw": "user exit wraps/portals or exits a map/zone without the use of a door or opening and didn't die",
            "par": "completes goal within last 5 seconds"
        }
        # Corridor mode
        self.corridor_pending = False
        self.corridor_dir = None
        # Map Editor state
        self.current_symbol = ' '
        self.map_canvas = None
        self.symbol_listbox = None
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
        tk.Button(left_controls, text="Generate Corridor", command=self.generate_corridor).pack(fill=tk.X, padx=5, pady=2)
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
        self.arc_listbox.bind("<<ListboxSelect>>", self.select_arc)
        bottom_frame = tk.Frame(self.main_vertical_paned)
        self.main_vertical_paned.add(bottom_frame, minsize=280)
        self.bottom_paned = tk.PanedWindow(bottom_frame, orient=tk.HORIZONTAL)
        self.bottom_paned.pack(fill=tk.BOTH, expand=True)
        # ==================== ARC BUILDER SECTION ====================
        arc_frame = tk.Frame(self.bottom_paned)
        self.bottom_paned.add(arc_frame, minsize=700)
        tk.Label(arc_frame, text="Arc Builder", font=("Arial", 11, "bold")).pack(pady=5)
        self.arc_scroll = ScrolledFrame(arc_frame)
        self.arc_scroll.pack(fill=tk.BOTH, expand=True)
        arc_content = self.arc_scroll.scrollable_frame
        # Script + Data Phrases
        script_section = tk.Frame(arc_content)
        script_section.pack(fill=tk.X, padx=8, pady=8)
        tk.Label(script_section, text="Script Selector & Forum", font=("Arial", 11, "bold")).pack(anchor="w")
        script_paned = tk.PanedWindow(script_section, orient=tk.HORIZONTAL)
        script_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        selector_frame = tk.Frame(script_paned, width=140)
        script_paned.add(selector_frame, minsize=140)
        tk.Label(selector_frame, text="Select Type", font=("Arial", 10, "bold")).pack(pady=4)
        selector_scroll = tk.Scrollbar(selector_frame)
        selector_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.input_gen_list = tk.Listbox(selector_frame, height=8, yscrollcommand=selector_scroll.set, exportselection=False)
        for opt in ["Enemy", "Boss", "Mini-Boss", "NPC", "Group", "Map Location", "Keys"]:
            self.input_gen_list.insert(tk.END, opt)
        self.input_gen_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        selector_scroll.config(command=self.input_gen_list.yview)
        self.input_gen_list.bind("<<ListboxSelect>>", self.select_input_gen_type)
        self.script_form_outer = ScrolledFrame(script_paned)
        script_paned.add(self.script_form_outer, minsize=420)
        self.form_frame = self.script_form_outer.scrollable_frame
        tk.Label(self.form_frame, text="← Select a script type on the left to open the forum", fg="gray", wraplength=380).pack(expand=True, pady=60)
        phrases_frame = tk.Frame(script_paned, width=240)
        script_paned.add(phrases_frame, minsize=240)
        tk.Label(phrases_frame, text="Data Phrases", font=("Arial", 10, "bold")).pack(pady=4)
        phrases_inner = tk.Frame(phrases_frame)
        phrases_inner.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)
        row = 0
        col = 0
        for phrase in self.data_phrases:
            btn = tk.Button(phrases_inner, text=phrase, width=10, height=1, font=("Arial", 8))
            btn.grid(row=row, column=col, padx=3, pady=3)
            Tooltip(btn, self.tooltips.get(phrase, ""))
            btn.config(command=lambda p=phrase: self.inject_phrase(p))
            col += 1
            if col > 4:
                col = 0
                row += 1
        # Arc Forum + Data
        arc_section = tk.Frame(arc_content)
        arc_section.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        buttons_frame = tk.Frame(arc_section, width=130)
        buttons_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 8))
        for text, cmd in [
            ("New Arc", self.new_arc),
            ("Save Arc", self.save_selected_arc),
            ("Load Arc", self.load_arc),
            ("Save .arcs", self.save_arc_to_file),
            ("Attach to Map", self.attach_to_map),
            ("Delete Arc", self.delete_arc),
            ("Clear Forum", self.clear_arc_forum),
            ("Reset Forum", self.reset_arc_forum),
            ("Undo", self.undo_arc)
        ]:
            tk.Button(buttons_frame, text=text, command=cmd, width=14).pack(pady=6, padx=5)
        arc_content_paned = tk.PanedWindow(arc_section, orient=tk.HORIZONTAL)
        arc_content_paned.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.arc_forum_outer = ScrolledFrame(arc_content_paned, width=340)
        arc_content_paned.add(self.arc_forum_outer, minsize=340)
        arc_forum_inner = self.arc_forum_outer.scrollable_frame
        tk.Label(arc_forum_inner, text="Arc Forum", font=("Arial", 10, "bold")).pack(anchor="w", pady=(8, 4), padx=8)
        left_controls = tk.Frame(arc_forum_inner)
        left_controls.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(left_controls, text="Arc Name:").grid(row=0, column=0, sticky="e", pady=3, padx=5)
        tk.Entry(left_controls, textvariable=self.arc_name_var, width=28).grid(row=0, column=1, pady=3)
        tk.Label(left_controls, text="Estimated:").grid(row=1, column=0, sticky="e", pady=3, padx=5)
        ttk.Combobox(left_controls, textvariable=self.arc_estimated_type_var,
                     values=["2-Finish (E2F)", "2-Start (E2S)", "Short-Hold-Time (SHT)", "Long-Hold-Time (LHT)"],
                     state="readonly", width=25).grid(row=1, column=1, pady=3)
        tk.Label(left_controls, text="Zone Type:").grid(row=2, column=0, sticky="e", pady=3, padx=5)
        ttk.Combobox(left_controls, textvariable=self.arc_zone_type_var,
                     values=['Safe (S)', 'Crawl (C)', 'Fight (F)', 'Mix0 (C+C)', 'Mix1 (C+F)', 'Mix2 (S+F)', 'Mix3 (C+S)', 'Mixed (ANY)'],
                     state="readonly", width=25).grid(row=2, column=1, pady=3)
        tk.Label(left_controls, text="Start Msg:").grid(row=3, column=0, sticky="e", pady=3, padx=5)
        tk.Entry(left_controls, textvariable=self.arc_start_msg_var, width=28).grid(row=3, column=1, pady=3)
        tk.Label(left_controls, text="Map:").grid(row=4, column=0, sticky="e", pady=3, padx=5)
        tk.Entry(left_controls, textvariable=self.arc_map_var, width=28).grid(row=4, column=1, pady=3)
        tk.Label(left_controls, text="Map Type:").grid(row=5, column=0, sticky="e", pady=3, padx=5)
        ttk.Combobox(left_controls, textvariable=self.arc_map_type_var,
                     values=['Generate', 'Import'], state="readonly", width=25).grid(row=5, column=1, pady=3)
        tk.Label(left_controls, text="Confirm Msg:").grid(row=6, column=0, sticky="e", pady=3, padx=5)
        tk.Entry(left_controls, textvariable=self.arc_confirm_msg_var, width=28).grid(row=6, column=1, pady=3)
        data_frame = tk.Frame(arc_content_paned)
        arc_content_paned.add(data_frame, minsize=380)
        tk.Label(data_frame, text="Arc Data:").pack(anchor="w", padx=8, pady=(8, 2))
        data_scroll = tk.Scrollbar(data_frame)
        data_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.arc_data_text = tk.Text(data_frame, height=12, wrap=tk.WORD, yscrollcommand=data_scroll.set)
        self.arc_data_text.pack(fill=tk.BOTH, expand=True, padx=8, pady=2)
        data_scroll.config(command=self.arc_data_text.yview)
        self.arc_data_text.bind("<<Modified>>", self.on_arc_modified)
        # ==================== MAP EDITOR SECTION ====================
        editor_frame = tk.Frame(self.bottom_paned)
        self.bottom_paned.add(editor_frame, minsize=500)
        tk.Label(editor_frame, text="Map Editor", font=("Arial", 11, "bold")).pack(pady=5)
        editor_paned = tk.PanedWindow(editor_frame, orient=tk.HORIZONTAL)
        editor_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        # Pane 1: Symbols
        symbols_frame = tk.Frame(editor_paned, width=180)
        editor_paned.add(symbols_frame, minsize=180)
        tk.Label(symbols_frame, text="Symbols", font=("Arial", 10, "bold")).pack(pady=4)
        sym_scroll = tk.Scrollbar(symbols_frame)
        sym_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.symbol_listbox = tk.Listbox(symbols_frame, height=20, yscrollcommand=sym_scroll.set)
        self.symbols = [
            (' ', 'Walk Space'),
            ('/', 'Non-Existing Untouchable Land'),
            ('\\', 'Not-Apart-Of-Map'),
            ('&', 'Barrier'),
            ('#', 'Wall'),
            ('%', 'Waterfall (Barrier/Wall [NON-INTERACTIVE])'),
            ('=', 'Waterfall (Barrier/Object [INTERACTIVE])'),
            ('@', 'Almond Water Supply'),
            (':', 'Climbable Wall'),
            ('|', 'Climbable Object'),
            ('!', 'Interactive Object'),
            ('?', 'Object Chest'),
            ('*', 'User Chest'),
            ('+', 'Door'),
            ('-', 'Non-Interactive Door'),
            ('[', 'Window (Start)'),
            ('.', 'Window (Middle)'),
            (']', 'Window (End)'),
            ('{', 'Break-in-Ground (Start)'),
            ('_', 'Break-in-Ground (Middle)'),
            ('}', 'Break-in-Ground (End)'),
            ('X', 'Boss Door'),
            ('D', 'Boss Spawner'),
            ('M', 'Mini-Boss Spawner'),
            ('T', 'Trap'),
            ('W', 'Weapon'),
            ('A', 'Armor'),
            ('S', 'Skill'),
            ('E', 'Enemy'),
            ('Y', 'Enemy Encampment'),
            ('O', 'Mini-Boss Group'),
            ('G', 'Boss Group'),
            ('C', 'Camp (NPCs)'),
            ('Z', 'Safe Zone'),
            ('L', 'Ladder Way (Up/Down)'),
            ('H', 'Hole (Down Only)'),
            ('R', 'Rope (Up Only)'),
            ('Q', 'Teleporter Home'),
            ('I', 'Teleporter Instance (Waypoint)'),
            ('P', 'Puzzle Piece'),
            ('V', 'Vending Unit'),
            ('B', 'Boat'),
            ('~', 'Water (Deadly [BOAT ONLY])'),
            (',', 'Water (Swimable [SKILL NEEDED])'),
            ('--', 'Properties Selector'),
            ('++', 'Paint Tool')
        ]
        for sym, desc in self.symbols:
            self.symbol_listbox.insert(tk.END, f"{sym} - {desc}")
        self.symbol_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sym_scroll.config(command=self.symbol_listbox.yview)
        self.symbol_listbox.bind("<<ListboxSelect>>", self.select_symbol)
        self.sym_desc_label = tk.Label(symbols_frame, text="", font=("Arial", 9), wraplength=170, justify=tk.LEFT)
        self.sym_desc_label.pack(pady=8, padx=8)
        # Pane 2: Map Canvas
        canvas_frame = tk.Frame(editor_paned)
        editor_paned.add(canvas_frame, minsize=400)
        self.map_canvas = tk.Canvas(canvas_frame, bg="#111111", highlightthickness=0)
        self.map_canvas.pack(fill=tk.BOTH, expand=True)
        self.map_canvas.bind("<Button-1>", self.paint_on_map)
        # Pane 3: Properties
        props_frame = tk.Frame(editor_paned, width=220)
        editor_paned.add(props_frame, minsize=220)
        tk.Label(props_frame, text="Cell Properties", font=("Arial", 10, "bold")).pack(pady=4)
        self.props_text = tk.Text(props_frame, height=15, wrap=tk.WORD)
        self.props_text.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        tk.Label(props_frame, text="World Info", font=("Arial", 10, "bold")).pack(pady=(20, 4))
        self.world_info_label = tk.Label(props_frame, text="", justify=tk.LEFT, font=("Arial", 9))
        self.world_info_label.pack(pady=4, padx=8)
        status_frame = tk.Frame(self.bottom_paned)
        self.bottom_paned.add(status_frame, minsize=200)
        self.status_label = tk.Label(status_frame, text="Ready")
        self.status_label.pack()
        # Pane bindings
        self.main_vertical_paned.bind("<ButtonRelease-1>", self.save_pane_positions)
        self.upper_paned.bind("<ButtonRelease-1>", self.save_pane_positions)
        self.bottom_paned.bind("<ButtonRelease-1>", self.save_pane_positions)
        self.root.bind("<Configure>", self.on_configure)
        self.root.after(150, self.load_pane_positions)
        self.new_world()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    # ==================== UDATA & PANES ====================
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
                for key, value in self.settings.items():
                    f.write(f"JAM:{key}={value}\n")
        except Exception as e:
            print("udata save warning:", e)

    def load_pane_positions(self):
        self.root.update_idletasks()
        w = self.root.winfo_width()
        h = self.root.winfo_height()
        key_prefix = f'pane_{w}x{h}_'
        try:
            v_h = self.main_vertical_paned.winfo_height()
            if v_h > 1:
                key = key_prefix + 'main_vertical_pos'
                pos = int(self.settings.get(key, int(v_h * 0.65)))
                pos = max(200, min(pos, v_h - 200))
                self.main_vertical_paned.sash_place(0, 0, pos)
        except:
            pass
        try:
            u_w = self.upper_paned.winfo_width()
            if u_w > 1:
                key1 = key_prefix + 'upper_horizontal_pos1'
                pos1 = int(self.settings.get(key1, 220))
                key2 = key_prefix + 'upper_horizontal_pos2'
                pos2 = int(self.settings.get(key2, u_w - 280))
                self.upper_paned.sash_place(0, pos1, 0)
                self.upper_paned.sash_place(1, pos2, 0)
        except:
            pass
        try:
            b_w = self.bottom_paned.winfo_width()
            if b_w > 1:
                key1 = key_prefix + 'bottom_horizontal_pos1'
                pos1 = int(self.settings.get(key1, 700))
                key2 = key_prefix + 'bottom_horizontal_pos2'
                pos2 = int(self.settings.get(key2, b_w - 500))
                self.bottom_paned.sash_place(0, pos1, 0)
                self.bottom_paned.sash_place(1, pos2, 0)
        except:
            pass

    def save_pane_positions(self, event=None):
        w = self.root.winfo_width()
        h = self.root.winfo_height()
        key_prefix = f'pane_{w}x{h}_'
        try:
            pos = self.main_vertical_paned.sash_coord(0)[1]
            self.settings[key_prefix + 'main_vertical_pos'] = str(pos)
        except:
            pass
        try:
            pos1 = self.upper_paned.sash_coord(0)[0]
            pos2 = self.upper_paned.sash_coord(1)[0]
            self.settings[key_prefix + 'upper_horizontal_pos1'] = str(pos1)
            self.settings[key_prefix + 'upper_horizontal_pos2'] = str(pos2)
        except:
            pass
        try:
            pos1 = self.bottom_paned.sash_coord(0)[0]
            pos2 = self.bottom_paned.sash_coord(1)[0]
            self.settings[key_prefix + 'bottom_horizontal_pos1'] = str(pos1)
            self.settings[key_prefix + 'bottom_horizontal_pos2'] = str(pos2)
        except:
            pass
        self.save_udata()

    def on_configure(self, event):
        if event.widget == self.root:
            self.load_pane_positions()

    def get_next_path(self, file):
        if not os.path.exists(file):
            return file
        base, ext = os.path.splitext(file)
        i = 2
        while True:
            new_path = f"{base}{i}{ext}"
            if not os.path.exists(new_path):
                return new_path
            i += 1

    def on_close(self):
        self.save_pane_positions()
        if messagebox.askyesno("Exit", "Auto-save world before closing?"):
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            auto_file = f"auto_save_{timestamp}.livemap"
            auto_path = self.get_next_path(auto_file)
            try:
                save_data = self.world.copy()
                save_data["map_positions"] = self.map_positions
                with open(auto_path, 'w') as f:
                    json.dump(save_data, f, indent=2)
                messagebox.showinfo("Auto-saved", f"World auto-saved to {auto_path}")
            except Exception as e:
                messagebox.showerror("Auto-save failed", str(e))
        self.root.destroy()

    # ==================== PAN METHODS ====================
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

    # ==================== ARC METHODS ====================
    def select_arc(self, event):
        selection = self.arc_listbox.curselection()
        if selection:
            idx = selection[0]
            self.current_arc_index = idx
            arc = self.world["arcs"][idx]
            self.arc_name_var.set(arc.get('name', "Title the Arc"))
            self.arc_estimated_type_var.set(arc.get('estimated', "2-Finish (E2F)"))
            self.arc_zone_type_var.set(arc.get('zone_type', "Safe"))
            self.arc_start_msg_var.set(arc.get('start_msg', "Start Message"))
            self.arc_map_var.set(arc.get('map', ""))
            self.arc_map_type_var.set(arc.get('map_type', "Import"))
            self.arc_confirm_msg_var.set(arc.get('confirm_msg', "Confirm Message"))
            self.arc_data_text.delete("1.0", tk.END)
            self.arc_data_text.insert("1.0", arc.get('arc_data', ""))
            self.last_arc_state = self.save_arc_state()

    def save_arc_state(self):
        return {
            'name': self.arc_name_var.get(),
            'estimated': self.arc_estimated_type_var.get(),
            'zone_type': self.arc_zone_type_var.get(),
            'start_msg': self.arc_start_msg_var.get(),
            'map': self.arc_map_var.get(),
            'map_type': self.arc_map_type_var.get(),
            'arc_data': self.arc_data_text.get("1.0", tk.END).strip(),
            'confirm_msg': self.arc_confirm_msg_var.get()
        }

    def set_arc_state(self, state):
        self.arc_name_var.set(state['name'])
        self.arc_estimated_type_var.set(state['estimated'])
        self.arc_zone_type_var.set(state['zone_type'])
        self.arc_start_msg_var.set(state['start_msg'])
        self.arc_map_var.set(state['map'])
        self.arc_map_type_var.set(state['map_type'])
        self.arc_data_text.delete("1.0", tk.END)
        self.arc_data_text.insert("1.0", state['arc_data'])
        self.arc_confirm_msg_var.set(state['confirm_msg'])

    def on_arc_modified(self, event=None):
        if self.arc_data_text.edit_modified():
            current = self.save_arc_state()
            if current != self.last_arc_state:
                self.arc_undo_stack.append(self.last_arc_state)
                self.last_arc_state = current
                self.arc_redo_stack.clear()
            self.arc_data_text.edit_modified(False)

    def undo_arc(self):
        if self.arc_undo_stack:
            current = self.save_arc_state()
            self.arc_redo_stack.append(current)
            prev = self.arc_undo_stack.pop()
            if prev:
                self.set_arc_state(prev)
                self.last_arc_state = prev
            self.status_label.config(text="Undo applied")

    def new_arc(self):
        new_arc = {
            'name': self.arc_name_var.get() or "New Arc",
            'estimated': self.arc_estimated_type_var.get(),
            'zone_type': self.arc_zone_type_var.get(),
            'start_msg': self.arc_start_msg_var.get(),
            'map': self.arc_map_var.get(),
            'map_type': self.arc_map_type_var.get(),
            'arc_data': self.arc_data_text.get("1.0", tk.END).strip(),
            'confirm_msg': self.arc_confirm_msg_var.get()
        }
        self.world["arcs"].append(new_arc)
        self.current_arc_index = len(self.world["arcs"]) - 1
        self.update_arc_list()
        self.arc_listbox.select_set(self.current_arc_index)
        self.status_label.config(text="New arc created")

    def save_selected_arc(self):
        if self.current_arc_index is None:
            self.new_arc()
            return
        arc = self.save_arc_state()
        self.world["arcs"][self.current_arc_index] = arc
        self.update_arc_list()
        self.status_label.config(text="Arc saved")

    def load_arc(self):
        file = filedialog.askopenfilename(filetypes=[("Arc Files", "*.arcs")])
        if file:
            with open(file, 'r') as f:
                line = f.read().strip()
            parts = line.split('||')
            if len(parts) >= 7:
                self.arc_name_var.set(parts[0])
                self.arc_estimated_type_var.set(parts[1])
                self.arc_zone_type_var.set(parts[2])
                self.arc_start_msg_var.set(parts[3])
                self.arc_map_var.set(parts[4])
                self.arc_data_text.delete("1.0", tk.END)
                self.arc_data_text.insert("1.0", parts[5])
                self.arc_confirm_msg_var.set(parts[6])
                if parts[4].startswith('$'):
                    self.arc_map_type_var.set("Import")
                else:
                    self.arc_map_type_var.set("Generate")
                self.status_label.config(text="Arc loaded from .arcs file")
            else:
                messagebox.showerror("Invalid File", "Arc file format not recognized.")

    def save_arc_to_file(self):
        if self.current_arc_index is None:
            messagebox.showerror("No Arc", "Select or create an arc first")
            return
        file = filedialog.asksaveasfilename(defaultextension=".arcs", filetypes=[("Arc Files", "*.arcs")])
        if file:
            arc = self.world["arcs"][self.current_arc_index]
            line = f"{arc.get('name', '')}||{arc.get('estimated', '')}||{arc.get('zone_type', '')}||{arc.get('start_msg', '')}||{arc.get('map', '')}||{arc.get('arc_data', '')}||{arc.get('confirm_msg', '')}"
            with open(file, 'w') as f:
                f.write(line)
            messagebox.showinfo("Saved", f"Arc saved to {file}")

    def attach_to_map(self):
        if self.current_arc_index is None:
            messagebox.showerror("No Arc", "No arc selected")
            return
        if not self.current_selected_map_id:
            messagebox.showerror("No Map", "Select a map first")
            return
        arc = copy.deepcopy(self.world["arcs"][self.current_arc_index])
        map_data = self.world["maps"][self.current_selected_map_id]
        if "attached_arcs" not in map_data:
            map_data["attached_arcs"] = []
        map_data["attached_arcs"].append(arc)
        self.status_label.config(text=f"Arc attached to {self.current_selected_map_id}")

    def delete_arc(self):
        if self.current_arc_index is not None:
            if messagebox.askyesno("Delete Arc", "Are you sure?"):
                del self.world["arcs"][self.current_arc_index]
                self.current_arc_index = None
                self.update_arc_list()
                self.clear_arc_fields()

    def clear_arc_fields(self):
        self.arc_name_var.set("Title the Arc")
        self.arc_estimated_type_var.set("2-Finish (E2F)")
        self.arc_zone_type_var.set("Safe")
        self.arc_start_msg_var.set("Start Message")
        self.arc_map_var.set("")
        self.arc_map_type_var.set("Import")
        self.arc_data_text.delete("1.0", tk.END)
        self.arc_confirm_msg_var.set("Confirm Message")

    def clear_arc_forum(self):
        self.arc_name_var.set("")
        self.arc_estimated_type_var.set("2-Finish (E2F)")
        self.arc_zone_type_var.set("Safe")
        self.arc_start_msg_var.set("")
        self.arc_map_var.set("")
        self.arc_map_type_var.set("Import")
        self.arc_confirm_msg_var.set("")
        self.status_label.config(text="Arc forum fields cleared")

    def reset_arc_forum(self):
        self.arc_name_var.set("Title the Arc")
        self.arc_estimated_type_var.set("2-Finish (E2F)")
        self.arc_zone_type_var.set("Safe")
        self.arc_start_msg_var.set("Start Message")
        self.arc_map_var.set("")
        self.arc_map_type_var.set("Import")
        self.arc_confirm_msg_var.set("Confirm Message")
        self.status_label.config(text="Arc forum reset to defaults")

    def update_arc_list(self):
        self.arc_listbox.delete(0, tk.END)
        for arc in self.world["arcs"]:
            self.arc_listbox.insert(tk.END, arc.get('name', 'Unnamed'))

    # ==================== SCRIPT INJECTOR METHODS ====================
    def select_input_gen_type(self, event):
        selection = self.input_gen_list.curselection()
        if selection:
            typ = self.input_gen_list.get(selection[0])
            self.build_script_form(typ)

    def build_script_form(self, typ):
        for widget in self.form_frame.winfo_children():
            widget.destroy()
        self.current_form_widgets = {}
        self.current_script_type = typ
        tk.Label(self.form_frame, text=f"{typ} Script Forum", font=("Arial", 11, "bold")).pack(pady=(5, 10))
        fields = self.get_script_fields(typ)
        for field in fields:
            row = tk.Frame(self.form_frame)
            row.pack(fill=tk.X, pady=3, padx=8)
            tk.Label(row, text=f"{field}:", width=18, anchor="e").pack(side=tk.LEFT)
            entry = tk.Entry(row)
            entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
            self.current_form_widgets[field] = entry
        ai_options = self.get_ai_options(typ)
        if ai_options:
            ai_frame = tk.Frame(self.form_frame)
            ai_frame.pack(fill=tk.X, pady=10, padx=8)
            tk.Label(ai_frame, text="AI Sequences (multi-select, max shown):", anchor="w").pack(anchor="w")
            ai_scroll = tk.Scrollbar(ai_frame)
            ai_scroll.pack(side=tk.RIGHT, fill=tk.Y)
            self.ai_listbox = tk.Listbox(ai_frame, selectmode=tk.MULTIPLE, height=6, yscrollcommand=ai_scroll.set)
            for opt in ai_options:
                self.ai_listbox.insert(tk.END, opt)
            self.ai_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
            ai_scroll.config(command=self.ai_listbox.yview)
            self.current_form_widgets["AI_Sequences"] = self.ai_listbox
        if typ == "Map Location":
            tk.Button(self.form_frame, text="Pick Location (current map center)", command=self.pick_map_location, bg="#4444aa", fg="white").pack(pady=8, fill=tk.X, padx=8)
        if typ == "Keys":
            bind_frame = tk.Frame(self.form_frame)
            bind_frame.pack(fill=tk.X, pady=8, padx=8)
            tk.Label(bind_frame, text="Bind Type:", font=("Arial", 10, "bold")).pack(anchor="w")
            self.bind_var = tk.StringVar(value="Bind-2-Action")
            for val, txt in [
                ("Bind-2-Action", "Bind-2-Action → Event to Action"),
                ("Bind-2-Event", "Bind-2-Event → Entity to Event"),
                ("Bind-2-Entity", "Bind-2-Entity → Object to Entity")
            ]:
                tk.Radiobutton(bind_frame, text=txt, variable=self.bind_var, value=val).pack(anchor="w", padx=20)
            self.bind_var.trace("w", self.update_key_labels)
            dyn_frame = tk.Frame(self.form_frame)
            dyn_frame.pack(fill=tk.X, pady=8, padx=8)
            self.key_field1_label = tk.Label(dyn_frame, text="Event:")
            self.key_field1_label.pack(anchor="w")
            self.key_field1_entry = tk.Entry(dyn_frame)
            self.key_field1_entry.pack(fill=tk.X, padx=5)
            self.key_field2_label = tk.Label(dyn_frame, text="Action:")
            self.key_field2_label.pack(anchor="w")
            self.key_field2_entry = tk.Entry(dyn_frame)
            self.key_field2_entry.pack(fill=tk.X, padx=5)
            self.current_form_widgets["key_bind"] = self.bind_var
            self.current_form_widgets["key_field1"] = self.key_field1_entry
            self.current_form_widgets["key_field2"] = self.key_field2_entry
            self.update_key_labels()
        tk.Button(self.form_frame, text="INJECT INTO ARC DATA", command=self.inject_script,
                  bg="#00cc00", fg="white", font=("Arial", 10, "bold")).pack(pady=12, fill=tk.X, padx=8)

    def get_script_fields(self, typ):
        if typ == "Enemy":
            return ["Name/Type", "Drop Rate", "Spawn Rate", "Color Base", "Value", "Texture"]
        elif typ == "Boss":
            return ["Name/Type", "Drop Rate", "Spawn Rate", "Health Base", "Defense Base", "Attack Base", "Color Base", "Value", "Texture"]
        elif typ == "Mini-Boss":
            return ["Name/Type", "Drop Rate", "Spawn Rate", "Level Difference", "Color", "Value", "Texture"]
        elif typ == "NPC":
            return ["Name", "Type", "Drop Rate", "Spawn Rate", "Wealth", "Bargaining Willpower", "Color", "Value", "Texture"]
        elif typ == "Group":
            return ["Entities", "Drop Rate", "Spawn Rate", "Color", "Value", "Texture"]
        elif typ == "Map Location":
            return ["Object", "XY", "Drop Rate", "Spawn Rate", "Color", "Value", "Texture"]
        elif typ == "Keys":
            return []
        return []

    def get_ai_options(self, typ):
        if typ == "Enemy":
            return ["Alert", "Seek", "Check", "Circle", "Pace", "Stand", "Guard", "Wait", "Rest", "Respond", "Team"]
        elif typ == "Boss":
            return ["Alert", "Scatter Manipulator [Random]", "Distance Based Strat [logical]", "Fastest Kill Shot [opportunistic]",
                    "Combo Baby Combo [Mixed approach]", "Flank Master [find-openings]", "Mix All [final-boss]"]
        elif typ == "Mini-Boss":
            return ["Alert", "Scatter Random", "Scatter Shortest Distance", "Scatter 2 target", "Scatter away target", "Mix Scatter", "Flank", "Mix All"]
        elif typ == "NPC":
            return ["Alert", "Check", "Pace", "Stand", "Wait", "Rest", "Respond"]
        elif typ == "Group":
            return ["Alert", "Scatter Random", "Scatter least motion", "Scatter 2 target", "Scatter away target", "Mix Response", "Flank"]
        return []

    def update_key_labels(self, *args):
        if not self.bind_var:
            return
        bind = self.bind_var.get()
        if bind == "Bind-2-Action":
            self.key_field1_label.config(text="Event:")
            self.key_field2_label.config(text="Action:")
        elif bind == "Bind-2-Event":
            self.key_field1_label.config(text="Entity:")
            self.key_field2_label.config(text="Event:")
        elif bind == "Bind-2-Entity":
            self.key_field1_label.config(text="Object:")
            self.key_field2_label.config(text="Entity:")

    def pick_map_location(self):
        if self.current_selected_map_id:
            m = self.world["maps"][self.current_selected_map_id]
            cx = m["width"] // 2
            cy = m["height"] // 2
            if "XY" in self.current_form_widgets:
                self.current_form_widgets["XY"].delete(0, tk.END)
                self.current_form_widgets["XY"].insert(0, f"{cx},{cy}")
            self.status_label.config(text=f"Location picked: center of {self.current_selected_map_id}")
        else:
            messagebox.showwarning("No Map Selected", "Select a map in the world view first.")

    def inject_script(self):
        if not self.current_script_type:
            return
        typ = self.current_script_type
        script_line = ""
        if typ == "Keys":
            bind_type = self.current_form_widgets["key_bind"].get()
            f1 = self.current_form_widgets["key_field1"].get().strip()
            f2 = self.current_form_widgets["key_field2"].get().strip()
            if bind_type == "Bind-2-Action":
                script_line = f"key({f1} -> {f2})"
            else:
                script_line = f"key({f1} {f2})"
        else:
            parts = []
            name_key = next((k for k in ["Name/Type", "Name", "Object", "Entities"] if k in self.current_form_widgets), None)
            if name_key:
                val = self.current_form_widgets[name_key].get().strip()
                if val:
                    parts.append(f"'{val}'")
            for rate_key in ["Drop Rate", "Spawn Rate"]:
                if rate_key in self.current_form_widgets:
                    val = self.current_form_widgets[rate_key].get().strip()
                    if val:
                        if not val.endswith("%"):
                            val += "%"
                        parts.append(val)
            for base_key in ["Health Base", "Defense Base", "Attack Base", "Level Difference", "Wealth", "Bargaining Willpower"]:
                if base_key in self.current_form_widgets:
                    val = self.current_form_widgets[base_key].get().strip()
                    if val:
                        short = base_key.lower().replace(" ", "_").replace("base", "").replace("difference", "lvl")
                        parts.append(f"{short}={val}")
            for col_key in ["Color Base", "Color"]:
                if col_key in self.current_form_widgets:
                    val = self.current_form_widgets[col_key].get().strip()
                    if val:
                        if not val.startswith("#"):
                            val = f"#{val}"
                        parts.append(f"color={val}")
            for extra in ["Value", "Texture"]:
                if extra in self.current_form_widgets:
                    val = self.current_form_widgets[extra].get().strip()
                    if val:
                        parts.append(f"{extra.lower()}={val}")
            if "AI_Sequences" in self.current_form_widgets:
                selected = [self.current_form_widgets["AI_Sequences"].get(i) for i in self.current_form_widgets["AI_Sequences"].curselection()]
                if selected:
                    ai_str = " ".join([f"!{s}!" for s in selected])
                    parts.append(ai_str)
            script_line = " ".join(parts)
        current = self.arc_data_text.get("1.0", tk.END).strip()
        if current:
            self.arc_data_text.insert(tk.END, "\n" + script_line)
        else:
            self.arc_data_text.insert("1.0", script_line)
        self.status_label.config(text=f"Injected {typ} → Arc Data")

    def inject_phrase(self, phrase):
        current = self.arc_data_text.get("1.0", tk.END).strip()
        if current:
            self.arc_data_text.insert(tk.END, " " + phrase)
        else:
            self.arc_data_text.insert("1.0", phrase)
        self.status_label.config(text=f"Injected phrase: {phrase}")

    # ==================== MAP EDITOR METHODS ====================
    def select_symbol(self, event):
        selection = self.symbol_listbox.curselection()
        if selection:
            idx = selection[0]
            sym = self.symbols[idx][0]
            self.current_symbol = sym
            desc = self.symbols[idx][1]
            self.sym_desc_label.config(text=desc)

    def paint_on_map(self, event):
        if not self.current_selected_map_id:
            return
        x = event.x // 15
        y = event.y // 15
        if 0 <= x < 48 and 0 <= y < 24:
            map_data = self.world["maps"][self.current_selected_map_id]
            map_data["grid"][y][x] = self.current_symbol
            self.update_map_editor()
            self.status_label.config(text=f"Painted {self.current_symbol} at ({x}, {y})")

    def update_map_editor(self):
        if not self.current_selected_map_id or not self.map_canvas:
            return
        self.map_canvas.delete("all")
        map_data = self.world["maps"][self.current_selected_map_id]
        grid = map_data["grid"]
        for y in range(24):
            for x in range(48):
                sym = grid[y][x]
                color = "#222222" if sym in ['#', '&', '%', '=', ':', '|', '!', '?', '*', '+', '-', '[', '.', ']', '{', '_', '}', 'X'] else "#0a0a0a"
                self.map_canvas.create_rectangle(x*15, y*15, (x+1)*15, (y+1)*15, fill=color, outline="#333333")
                self.map_canvas.create_text(x*15 + 7, y*15 + 7, text=sym, fill="#ffff00", font=("Arial", 10))
        self.world_info_label.config(text=f"World: {self.world['world_name']}\nSeed: {self.world['seed']}\nSelected: {self.current_selected_map_id}\nAttached Arcs: {len(map_data.get('attached_arcs', []))}")

    # ==================== CORRIDOR GENERATION ====================
    def generate_corridor(self):
        if not self.current_selected_map_id:
            self.generate_single_map()
            self.status_label.config(text="No tile selected - generated starter tile")
            return
        openings = self.world["maps"][self.current_selected_map_id].get("openings", "0000000").ljust(7, '0')
        possible_dirs = []
        for d in range(1, 5):  # Only cardinal N E S W
            rad = math.radians(self.direction_angles_deg[d])
            prop_cx = self.selected_center[0] + self.center_distance * self.zoom_level * math.cos(rad)
            prop_cy = self.selected_center[1] + self.center_distance * self.zoom_level * math.sin(rad)
            occupied = any(math.hypot(prop_cx - ecx, prop_cy - ecy) < self.base_radius * self.zoom_level * 1.3
                           for ecx, ecy in self.map_positions.values())
            if occupied:
                continue
            from_side = d - 1
            val = openings[from_side] if from_side < 7 else '0'
            if val in ('0', '4'):
                continue
            possible_dirs.append(d)
        if not possible_dirs:
            self.status_label.config(text="No cardinal direction available for corridor")
            return
        dir_num = random.choice(possible_dirs)
        self.corridor_pending = True
        self.corridor_dir = dir_num
        self.status_label.config(text=f"Corridor started in direction {dir_num} - click ghost to confirm first tile")
        self.draw_world_view()

    # ==================== CANVAS & DRAWING ====================
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

    def on_world_click(self, event):
        for map_id, (cx, cy) in self.map_positions.items():
            drawn_cx = cx + self.pan_offset_x
            drawn_cy = cy + self.pan_offset_y
            poly = self.get_octagon_points(drawn_cx, drawn_cy)
            if self.point_in_polygon(event.x, event.y, poly):
                self.current_selected_map_id = map_id
                self.selected_center = (cx, cy)
                self.update_map_info()
                self.update_map_editor()
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
                    if dir_num <= 4:
                        exit_val = openings[from_side] if from_side < 7 else '0'
                        if exit_val in ('0', '4'):
                            self.show_invalid_flash(drawn_pc_x, drawn_pc_y)
                            return
                    else:
                        if not self.is_diagonal_allowed(self.current_selected_map_id, from_side):
                            self.show_invalid_flash(drawn_pc_x, drawn_pc_y)
                            return
                    occupied = any(math.hypot(prop_cx - ecx, prop_cy - ecy) < self.base_radius * self.zoom_level * 1.3
                                   for ecx, ecy in self.map_positions.values())
                    if occupied:
                        return
                    if self.corridor_pending:
                        self.place_corridor_tile(dir_num, prop_cx, prop_cy)
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
                    self.update_map_info()
                    self.update_map_editor()
                    self.draw_world_view()
                    self.show_success_flash(drawn_pc_x, drawn_pc_y)
                    return

    def place_corridor_tile(self, dir_num, prop_cx, prop_cy):
        self.corridor_pending = False
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
        self.update_map_info()
        self.update_map_editor()
        self.draw_world_view()
        self.status_label.config(text=f"Corridor tile placed - continuing in direction {dir_num}")
        # Auto continue for 4 more (total 5)
        for _ in range(4):
            if not self.current_selected_map_id:
                break
            openings = self.world["maps"][self.current_selected_map_id].get("openings", "0000000").ljust(7, '0')
            rad = math.radians(self.direction_angles_deg[self.corridor_dir])
            prop_cx = self.selected_center[0] + self.center_distance * self.zoom_level * math.cos(rad)
            prop_cy = self.selected_center[1] + self.center_distance * self.zoom_level * math.sin(rad)
            occupied = any(math.hypot(prop_cx - ecx, prop_cy - ecy) < self.base_radius * self.zoom_level * 1.3
                           for ecx, ecy in self.map_positions.values())
            if occupied:
                self.status_label.config(text="Corridor stopped - direction blocked")
                break
            from_side = self.corridor_dir - 1
            val = openings[from_side] if from_side < 7 else '0'
            if val in ('0', '4'):
                self.status_label.config(text="Corridor stopped - no exit")
                break
            new_id = f"m{self.map_counter:03d}-{self.corridor_dir}"
            self.map_counter += 1
            from_side = self.corridor_dir - 1
            to_side = self.opposite_dir[self.corridor_dir] - 1
            self.world["connections"].append({
                "from_id": self.current_selected_map_id,
                "from_side": from_side,
                "to_id": new_id,
                "to_side": to_side
            })
            origin_z = self.world["maps"][self.current_selected_map_id].get("z_level", float(self.world["map_base_height"]))
            if self.corridor_dir in [5, 6]:
                new_z = origin_z + 1
            elif self.corridor_dir in [7, 8]:
                new_z = origin_z - 1
            else:
                new_z = origin_z
            arrival_dir = self.opposite_dir[self.corridor_dir]
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
            self.update_map_info()
            self.update_map_editor()
            self.draw_world_view()
        self.corridor_dir = None
        self.status_label.config(text="5-tile corridor completed")

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
                elif i < 4:
                    val = openings[i]
                    if val == '0':
                        col = "red"
                    elif val == '4':
                        col = "#222222"
                    else:
                        col = "white"
                else:
                    if self.is_diagonal_allowed(map_id, i):
                        col = "white"
                    else:
                        col = "#222222"
                self.world_canvas.create_line(sx, sy, ex, ey, fill=col, width=5)
            z_val = self.world["maps"][map_id].get("z_level", 0.0)
            attached = len(self.world["maps"][map_id].get("attached_arcs", []))
            label_text = f"{map_id}\nZ:{z_val:.1f}\n{openings}\nA:{attached}"
            self.world_canvas.create_rectangle(
                drawn_cx - 62 * self.zoom_level, drawn_cy - 48 * self.zoom_level,
                drawn_cx + 62 * self.zoom_level, drawn_cy + 48 * self.zoom_level,
                fill="#000000", stipple="gray25")
            self.world_canvas.create_text(drawn_cx, drawn_cy, text=label_text, fill="#ffff00",
                                          font=("Arial", int(10 * self.zoom_level), "bold"), justify="center")
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
                if dir_num <= 4:
                    val = openings_sel[from_side] if from_side < 7 else '0'
                    if val in ('0', '4'):
                        continue
                else:
                    if not self.is_diagonal_allowed(self.current_selected_map_id, from_side):
                        continue
                drawn_pc_x = prop_cx + self.pan_offset_x
                drawn_pc_y = prop_cy + self.pan_offset_y
                poly = self.get_octagon_points(drawn_pc_x, drawn_pc_y)
                self.world_canvas.create_polygon(poly, fill="", outline="#666666", width=3, dash=(12, 8))

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
            "attached_arcs": [],
            "z_level": z_level
        }
        self.map_positions[map_id] = (cx, cy)
        self.status_label.config(text=f"Generated {map_id}")
        self.draw_world_view()
        self.update_map_editor()

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
                self.update_map_editor()

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
            info = f"ID: {data['id']}\nSize: {data['width']}x{data['height']}\nProps: {len(data.get('props',[]))}\nZ: {data.get('z_level', 0.0)}\nArcs: {len(data.get('attached_arcs', []))}"
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
            if self.map_positions:
                first = next(iter(self.map_positions))
                self.current_selected_map_id = first
                self.selected_center = self.map_positions[first]
            self.update_arc_list()
            self.draw_world_view()
            self.update_map_info()
            self.update_map_editor()

    def load_premade_dict(self):
        if not self.current_selected_map_id:
            messagebox.showerror("No Tile", "Select a map tile first")
            return
        map_dir = "map"
        if not os.path.exists(map_dir):
            os.makedirs(map_dir)
        file = filedialog.askopenfilename(initialdir=map_dir, filetypes=[("Tile Map", "*.tmap")])
        if file:
            with open(file, 'r') as f:
                tmap = json.load(f)
            map_data = self.world["maps"][self.current_selected_map_id]
            map_data["grid"] = tmap.get("grid", map_data["grid"])
            map_data["props"] = tmap.get("props", map_data.get("props", []))
            if "attached_arcs" in tmap:
                map_data["attached_arcs"] = tmap.get("attached_arcs", [])
            self.draw_world_view()
            self.update_map_info()
            self.update_map_editor()
            self.status_label.config(text=f"Premade .tmap loaded into {self.current_selected_map_id}")

    def new_world(self):
        self.world = {
            "version": "1.0",
            "seed": random.randint(100000, 999999),
            "world_level": "0",
            "world_name": "The Yellow Halls",
            "params": {"spawn_enemy_rate": 0.35, "boss_chance": 0.05, "premade_percent": 0.3},
            "map_base_height": "1.0",
            "maps": {}, "connections": [], "arcs": []
        }
        self.map_counter = 1
        self.map_positions = {}
        self.pan_offset_x = 0
        self.pan_offset_y = 0
        self.zoom_level = 1.0
        self.arcs = []
        self.current_arc_index = None
        self.generate_single_map(openings="2120100", map_id="m001-0", cx=800, cy=500, z_level=float(self.world["map_base_height"]))
        self.current_selected_map_id = "m001-0"
        self.selected_center = (800, 500)
        self.update_map_info()
        self.update_arc_list()
        self.update_map_editor()
        self.status_label.config(text=f"New world - Seed: {self.world['seed']}")

if __name__ == "__main__":
    root = tk.Tk()
    app = WorldBuilder(root)
    root.mainloop()
