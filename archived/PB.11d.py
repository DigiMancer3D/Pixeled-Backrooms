# No additional dependencies are required beyond the Python standard library, as this uses Tkinter which is included.
# If Tkinter is not available on your system, install it with: sudo apt update && sudo apt install python3-tk
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import copy
import os
import re
import random
from datetime import datetime
import numpy as np
import uuid
import csv
import zipfile
from io import BytesIO, StringIO
import matplotlib.pyplot as plt
import string
import time
import tkinter.simpledialog as simpledialog

class ArcState:
    def __init__(self, name, estimated_type, estimated_parts, zone_type, start_msg, map_, map_type, arc_data, confirm_msg):
        self.name = name
        self.estimated_type = estimated_type
        self.estimated_parts = estimated_parts[:]
        self.zone_type = zone_type
        self.start_msg = start_msg
        self.map = map_
        self.map_type = map_type
        self.arc_data = arc_data
        self.confirm_msg = confirm_msg
    def __eq__(self, other):
        if not isinstance(other, ArcState):
            return False
        return (self.name == other.name and
                self.estimated_type == other.estimated_type and
                self.estimated_parts == other.estimated_parts and
                self.zone_type == other.zone_type and
                self.start_msg == other.start_msg and
                self.map == other.map and
                self.map_type == other.map_type and
                self.arc_data == other.arc_data and
                self.confirm_msg == other.confirm_msg)
class MapMaker:
    def __init__(self, root):
        self.root = root
        self.current_size = (0, 0)
        self.root.title("Pixeled Backrooms - Map Maker")
        self.root.geometry("1200x800")
        self.dtype = np.dtype([
            ('symbol', 'U1'),
            ('color', 'U20'),
            ('texture', 'U50'),
            ('name', 'U50'),
            ('value', 'i4'),
            ('depth', 'i4'),
            ('height', 'i4'),
            ('3d', 'i4'),
            ('range', 'f4'),
            ('sun', 'U3'),
        ])
        # Symbols with descriptions
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
            ('--', 'Properties Selector')
        ]
        # Current selected symbol for placement
        self.current_symbol = tk.StringVar(value='--')
        self.select_mode = True
        # Cell size
        self.cell_size = 20
        self.padding = self.cell_size * 10
        # Maps data
        self.maps = []
        self.var_dicts = []
        self.canvases = []
        self.zoom_sliders = []
        self.canvas_texts_list = []
        self.undo_stacks = []
        self.redo_stacks = []
        self.deleted_maps = []
        self.current_index = 0
        # Selected cell for properties
        self.selected_x = None
        self.selected_y = None
        # List of arcs (list of dicts)
        self.arcs = []
        # Current selected arc index
        self.current_arc_index = None
        # Arc fields variables
        self.arc_name_var = tk.StringVar(value="Title the Arc")
        self.arc_estimated_type_var = tk.StringVar(value="2-Finish (E2F)")
        self.arc_estimated_parts = []
        self.arc_zone_type_var = tk.StringVar(value="Safe")
        self.arc_start_msg_var = tk.StringVar(value="Start Message")
        self.arc_map_var = tk.StringVar(value="")
        self.arc_map_type_var = tk.StringVar(value="Import")
        self.arc_data_text = None # Will be Text widget
        self.arc_confirm_msg_var = tk.StringVar(value="Confirm Message")
        # User data file
        self.udata_file = "PB.udata"
        self.settings = self.load_udata()
        self.user_name = self.settings.get('unam', None)
        self.user_tag = self.settings.get('utag', None)
        self.user_uuid = self.settings.get('uuid', None)
        if not self.user_uuid:
            self.user_uuid = str(uuid.uuid4())
            self.settings['uuid'] = self.user_uuid
            self.save_udata()
        # Text color
        self.fg = self.settings.get('fg', 'black')
        self.hover_space_color = 'blue'
        self.hover_obj_color = 'yellow'
        self.multi_active_color = 'black'
        self.multi_selected_color = 'yellow'
        self.set_select_colors()
        # List of focusable sections for cycling
        self.focusable_sections = [] # Will populate in setup_ui
        # Current focused section index
        self.current_section_index = 0
        # Lock apply
        self.lock_var = tk.BooleanVar(value=False)
        self.locked_symbol = None
        self.locked_properties = None
        # Maps hidden state
        self.maps_hidden = False
        # Toolbar hidden state
        self.toolbar_hidden = False
        # Arc builder hidden state
        self.arc_hidden = False
        # Arc undo/redo
        self.arc_undo_stack = []
        self.arc_redo_stack = []
        self.last_arc_state = None
        self.deleted_arcs = []
        # Multi-select
        self.select_start = None
        self.select_end = None
        self.select_rect = None
        self.selected_region = None
        self.selected_rects = []
        self.clipboard = None
        self.clipboard_width = 0
        self.clipboard_height = 0
        self.paste_pos = None
        self.moving = False
        self.ongoing_action = None
        # Dirty flag for changes
        self.dirty = False
        # Input Generator
        self.input_gen_type = None
        self.input_gen_form_inner = None
        self.input_gen_vars = {}
        self.pick_mode = False
        self.picked_x = None
        self.picked_y = None
        self.picked_symbol = None
        self.hover_rect = None
        self.tooltip = None
        self.sunset_click = False
        self.sunrise_click = False
        self.prop_range_var = tk.StringVar(value="0")
        self.prop_range_dvar = tk.DoubleVar(value=0.0)
        self.prop_sun_var = tk.StringVar(value="NA")
        # Data Check
        self.data_check()
        # Help check
        self.help_check()
        self.main_vertical_paned, self.upper_horizontal_paned, self.bottom_horizontal_paned = self.setup_ui()
        self.setup_menu()
        self.apply_fg()
        # Add initial map
        self.add_map_tab("Unnamed")
        self.update_edit_menu_states()
        # Clear arc fields
        self.clear_arc_fields()
        # Bind exit to save udata
        self.root.protocol("WM_DELETE_WINDOW", self.save_and_exit)
        self.bind_events()
        self.root.bind("<Configure>", self.handle_configure)
        self.main_vertical_paned.bind("<B1-Motion>", self.save_pane_positions)
        self.upper_horizontal_paned.bind("<B1-Motion>", self.save_pane_positions)
        self.bottom_horizontal_paned.bind("<B1-Motion>", self.save_pane_positions)
        # Set initial sash positions to match defaults
        self.root.update() # Force window to size itself first
        self.current_size = (self.root.winfo_width(), self.root.winfo_height())
        self.load_pane_positions() # Load saved positions (or defaults)
        # Issue 1: Cursor locking
        self.locked_input = None
        # Issue 2: user_active
        self.user_active = 1 # 1 means unchanged
        self.cheating_detected = -2 # The cheating_detected flag starts at -2, allowing 3 accidental touches of forbidden land ('/' with value >1 or <0) before setting positive, which may trigger game engine penalties in future.
        self.cheating_reason = ""
        # Issue 3: last directories
        base_dir = os.getcwd()
        self.last_dir = {
            'file_load': base_dir,
            'arc_load': os.path.join(base_dir, 'arc'),
            'map_load': os.path.join(base_dir, 'map'),
            'dict_load': os.path.join(base_dir, 'dict')
        }
        self.update_time()
    def bind_events(self):
        self.root.bind_all("<Tab>", self.handle_tab)
        self.root.bind_all("<Shift-Tab>", self.handle_shift_tab)
        self.root.bind("<Motion>", self.track_mouse)
        self.root.bind("<Button>", self.unlock_cursor_on_action)
        self.root.bind("<MouseWheel>", self.unlock_cursor_on_action)
        self.root.bind_all("<Return>", self.unlock_cursor_on_action)
        self.root.bind_all("<Shift-Return>", self.unlock_cursor_on_action)
    def set_select_colors(self):
        mapping = {
            'gold': ('gold', 'brown', 'gold'),
            'green': ('green', 'limegreen', 'green'),
            'red': ('red', 'brown', 'orange'),
            'black': ('brown', 'blue', 'red'),
            'orange': ('orange', 'yellow', 'brown'),
            'purple': ('purple', 'green', 'red'),
            'brown': ('brown', 'red', 'green'),
            'pink': ('pink', 'blue', 'orange'),
            'limegreen': ('limegreen', 'brown', 'green'),
            'white': ('white', 'dimgray', 'gray'),
            'silver': ('silver', 'dimgray', 'silver'),
        }
        if self.fg in mapping:
            self.hover_space_color, self.multi_active_color, self.multi_selected_color = mapping[self.fg]
        self.hover_obj_color = self.multi_selected_color
    def track_mouse(self, event):
        if self.locked_input:
            self.unlock_cursor()
    def unlock_cursor_on_action(self, event):
        if self.locked_input:
            self.unlock_cursor()
    def lock_cursor(self, widget):
        self.locked_input = widget
        self.root.config(cursor='none')
    def unlock_cursor(self, event=None):
        self.locked_input = None
        self.root.config(cursor='')
    def data_check(self):
        dirs = {'tmap': 'map', 'mapd': 'dict', 'arcs': 'arc'}
        for ext, d in dirs.items():
            if not os.path.exists(d):
                os.mkdir(d)
        for f in os.listdir('.'):
            for ext, d in dirs.items():
                if f.endswith('.' + ext) and os.path.isfile(f):
                    os.rename(f, os.path.join(d, f))
                    break
    def help_check(self):
        help_dir = 'help'
        if not os.path.exists(help_dir):
            os.mkdir(help_dir)
        files = ["map.help", "door.guide", "arc.help", "arc.guide", "help.guide"]
        for f in files:
            old = f
            new = os.path.join(help_dir, f)
            if os.path.exists(old):
                os.rename(old, new)
    def load_udata(self):
        settings = {}
        if os.path.exists(self.udata_file):
            with open(self.udata_file, 'r') as f:
                lines = f.readlines()
            for line in lines:
                if line.startswith("PB:"):
                    key, value = line.strip()[3:].split('=', 1)
                    settings[key] = value
        return settings
    def save_udata(self):
        lines = []
        if os.path.exists(self.udata_file):
            with open(self.udata_file, 'r') as f:
                lines = f.readlines()
        with open(self.udata_file, 'w') as f:
            for line in lines:
                if not line.startswith("PB:"):
                    f.write(line)
            for key, value in self.settings.items():
                f.write(f"PB:{key}={value}\n")
    def on_close(self):
        self.deleted_arcs = []
        self.deleted_maps = []
        self.save_pane_positions()
        self.root.destroy()
    def apply_fg(self):
        style = ttk.Style()
        style.configure("TCombobox", foreground=self.fg, arrowcolor=self.fg)
        style.map("TCombobox", foreground=[('readonly', self.fg)])
        style.configure("TNotebook.Tab", foreground=self.fg)
        style.map("TNotebook.Tab", foreground=[('selected', self.fg)])
        style.configure("Vertical.TScale", foreground=self.fg)
        def set_colors(widget):
            try:
                widget.config(fg=self.fg)
                if 'insertbackground' in widget.keys():
                    widget.config(insertbackground=self.fg)
                if isinstance(widget, tk.Menu):
                    widget.config(fg=self.fg, activeforeground=self.fg)
                if isinstance(widget, tk.Checkbutton):
                    widget.config(fg=self.fg, activeforeground=self.fg)
            except:
                pass
            for child in widget.winfo_children():
                set_colors(child)
        set_colors(self.root)
        for i in range(len(self.canvases)):
            self.redraw_canvas(i)
        self.set_select_colors()
    def set_fg(self, color):
        self.fg = color
        self.settings['fg'] = color
        self.save_udata()
        self.apply_fg()
    def setup_menu(self):
        menubar = tk.Menu(self.root)
        # Main Menu button
        menubar.add_command(label="Main Menu", command=self.main_menu)
        # Help menu
        helpmenu = tk.Menu(menubar, tearoff=0)
        helpmenu.add_command(label="Map Help", command=lambda: self.show_help("map.help"))
        helpmenu.add_command(label="Door Transversal Guide", command=lambda: self.show_help("door.guide"))
        helpmenu.add_command(label="Arc Help", command=lambda: self.show_help("arc.help"))
        helpmenu.add_command(label="Arc Data Guide", command=lambda: self.show_help("arc.guide"))
        helpmenu.add_command(label="TLDR", command=lambda: self.show_help("help.guide"))
        menubar.add_cascade(label="Help", menu=helpmenu)
        # Epoch time display
        menubar.add_command(label="0", command=self.show_user_menu)
        self.time_index = menubar.index("end")
        # File menu
        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="New", command=self.new_with_save_check)
        filemenu.add_command(label="Load", command=self.load_with_save_check)
        filemenu.add_separator()
        filemenu.add_command(label="Save", command=self.save_file)
        filemenu.add_command(label="Save & Exit", command=self.save_and_exit)
        filemenu.add_command(label="Exit without Save", command=self.exit_without_save)
        filemenu.add_separator()
        filemenu.add_command(label="Export Maps .png", command=self.export_all_maps_png)
        filemenu.add_command(label="Export Arcs .csv", command=self.export_all_arcs_csv)
        filemenu.add_command(label="Export Full Dict", command=self.export_full_dict)
        menubar.add_cascade(label="File", menu=filemenu)
        # Edit menu
        self.editmenu = tk.Menu(menubar, tearoff=0)
        self.editmenu.add_command(label="Undo", command=self.undo)
        self.undo_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Redo", command=self.redo)
        self.redo_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Cancel Action", command=self.cancel_action)
        self.editmenu.add_command(label="Select", command=self.select_tool)
        self.editmenu.add_command(label="De-Select", command=self.deselect)
        self.editmenu.add_command(label="De-Select Arcs", command=self.deselect_arc, state='disabled')
        self.deselect_arc_edit_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Undo Map Delete", command=self.undo_map_delete, state='disabled')
        self.undo_map_delete_index = self.editmenu.index("end")
        self.editmenu.add_separator()
        self.editmenu.add_command(label="Copy", command=self.copy_selected, state='disabled')
        self.copy_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Cut", command=self.cut_selected, state='disabled')
        self.cut_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Paste", command=self.paste_selected, state='disabled')
        self.paste_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Replace", command=self.replace_selected, state='disabled')
        self.replace_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Make New Map", command=self.make_new_map, state='disabled')
        self.make_new_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Generate New Section", command=self.generate_new_section, state='disabled')
        self.gen_new_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Clear Selected Properties", command=self.clear_selected_properties, state='disabled')
        self.clear_prop_index = self.editmenu.index("end")
        self.editmenu.add_command(label="Remove Selected", command=self.remove_selected, state='disabled')
        self.remove_sel_index = self.editmenu.index("end")
        self.editmenu.add_separator()
        self.editmenu.add_command(label="Undo Arc Delete", command=self.undo_delete_arc, state='disabled')
        self.undo_arc_delete_index = self.editmenu.index("end")
        menubar.add_cascade(label="Edit", menu=self.editmenu)
        # Map menu
        self.mapmenu = tk.Menu(menubar, tearoff=0)
        self.mapmenu.add_command(label="New Map", command=lambda: self.add_map_tab(f"Unnamed {len(self.maps) + 1}"))
        self.mapmenu.add_command(label="Sunset Direction", command=self.set_sunset_direction)
        self.mapmenu.add_command(label="Hide Maps", command=self.hide_maps)
        self.hide_maps_index = self.mapmenu.index("end")
        self.mapmenu.add_command(label="Show Maps", command=self.show_maps, state='disabled')
        self.show_maps_index = self.mapmenu.index("end")
        self.mapmenu.add_command(label="Hide Toolbar", command=self.hide_toolbar)
        self.hide_toolbar_index = self.mapmenu.index("end")
        self.mapmenu.add_command(label="Show Toolbar", command=self.show_toolbar, state='disabled')
        self.show_toolbar_index = self.mapmenu.index("end")
        self.mapmenu.add_command(label="Map Picker", command=self.map_picker)
        self.mapmenu.add_command(label="Preview Map", command=self.preview_map)
        self.mapmenu.add_command(label="Preview Dictionary", command=self.preview_dictionary)
        self.mapmenu.add_command(label="Remove Arc from Map", command=self.remove_arc_from_map)
        self.mapmenu.add_command(label="Undo Map Delete", command=self.undo_map_delete, state='disabled')
        self.undo_map_delete_map_index = self.mapmenu.index("end")
        self.mapmenu.add_separator()
        self.mapmenu.add_command(label="Export Current png", command=self.export_current_map_png)
        self.export_current_png_index = self.mapmenu.index("end")
        self.mapmenu.add_command(label="Export All png", command=self.export_all_maps_png, state='disabled')
        self.export_all_png_index = self.mapmenu.index("end")
        menubar.add_cascade(label="Map", menu=self.mapmenu)
        # Arc menu
        self.arcmenu = tk.Menu(menubar, tearoff=0)
        self.arcmenu.add_command(label="Save Arc", command=self.save_arc_as)
        self.arcmenu.add_command(label="Load Arc", command=self.load_arc)
        self.arcmenu.add_command(label="Load Arc to Map", command=self.load_arc_to_map)
        self.arcmenu.add_command(label="Save Selected Arc from Map", command=self.save_selected_arc)
        self.arcmenu.add_command(label="Save All Arcs from Map", command=self.save_all_from_map)
        self.arcmenu.add_command(label="Save All Arcs from Dictionary", command=self.save_all_from_dict)
        self.arcmenu.add_command(label="Hide Arc Builder", command=self.hide_arc_builder)
        self.hide_arc_index = self.arcmenu.index("end")
        self.arcmenu.add_command(label="Show Arc Builder", command=self.show_arc_builder, state='disabled')
        self.show_arc_index = self.arcmenu.index("end")
        self.arcmenu.add_command(label="De-Select Arcs", command=self.deselect_arc, state='disabled')
        self.deselect_arc_arc_index = self.arcmenu.index("end")
        self.arcmenu.add_separator()
        self.arcmenu.add_command(label="Export Selected csv", command=self.export_selected_arc_csv, state='disabled')
        self.export_sel_arc_index = self.arcmenu.index("end")
        self.arcmenu.add_command(label="Export All csv", command=self.export_all_arcs_csv, state='disabled')
        self.export_all_arc_index = self.arcmenu.index("end")
        menubar.add_cascade(label="Arc", menu=self.arcmenu)
        # Text Color menu
        textcolormenu = tk.Menu(menubar, tearoff=0)
        textcolormenu.add_command(label="Classic", command=lambda: self.set_fg('gold'))
        textcolormenu.add_command(label="Moldy", command=lambda: self.set_fg('green'))
        textcolormenu.add_command(label="Rusty", command=lambda: self.set_fg('red'))
        textcolormenu.add_command(label="Ink", command=lambda: self.set_fg('black'))
        textcolormenu.add_command(label="Fruit", command=lambda: self.set_fg('orange'))
        textcolormenu.add_command(label="Graped", command=lambda: self.set_fg('purple'))
        textcolormenu.add_command(label="Tree", command=lambda: self.set_fg('brown'))
        textcolormenu.add_command(label="Kooled", command=lambda: self.set_fg('pink'))
        textcolormenu.add_command(label="Puked", command=lambda: self.set_fg('limegreen'))
        textcolormenu.add_command(label="Bone Ash", command=lambda: self.set_fg('white'))
        textcolormenu.add_command(label="Shiny", command=lambda: self.set_fg('silver'))
        menubar.add_cascade(label="Text Color", menu=textcolormenu)
        self.root.config(menu=menubar)
        menubar.bind("<Button-3>", lambda e: messagebox.showinfo("Top-Bar Menu Bar", "Main menu options for the application."))
        self.update_map_menu_states()
        self.update_toolbar_menu_states()
        self.update_arc_menu_states()
        # Removed self.update_edit_menu_states() from here
    def update_time(self):
        timestamp = int(time.time())
        self.root.nametowidget(self.root["menu"]).entryconfig(self.time_index, label=str(timestamp))
        self.root.after(1000, self.update_time)
    def show_user_menu(self):
        user_menu = tk.Menu(self.root, tearoff=0)
        name_label = f"User Name: {self.user_name if self.user_name else 'Click to set'}"
        user_menu.add_command(label=name_label, command=self.set_user_name)
        tag_label = f"User Tag: {self.user_tag if self.user_tag else 'Click to set'}"
        user_menu.add_command(label=tag_label, command=self.set_user_tag)
        uuid_label = f"User UUID: {self.user_uuid if self.user_uuid else 'Click to generate'}"
        user_menu.add_command(label=uuid_label, command=self.generate_uuid)
        try:
            user_menu.tk_popup(self.root.winfo_pointerx(), self.root.winfo_pointery())
        finally:
            user_menu.grab_release()
    def set_user_name(self):
        name = simpledialog.askstring("Set User Name", "Enter user name (max 29 chars):", initialvalue=self.user_name or "")
        if name is not None and len(name) <= 29:
            self.user_name = name
            self.settings['unam'] = name
            self.save_udata()
    def set_user_tag(self):
        tag = simpledialog.askstring("Set User Tag", "Enter user tag (max 19 chars):", initialvalue=self.user_tag or "")
        if tag is not None and len(tag) <= 19:
            self.user_tag = tag
            self.settings['utag'] = tag
            self.save_udata()
    def generate_uuid(self):
        if self.user_uuid:
            if not messagebox.askyesno("Regenerate UUID", "UUID already set. Regenerate?"):
                return
        last_digit = random.randint(0, 9)
        first_char = random.choice(string.ascii_letters)
        digits = []
        for i in range(4):
            d = (last_digit + i + random.randint(1, 9)) % 10
            digits.append(str(d))
        while all(d == digits[0] for d in digits) or digits[-1] == digits[-2]:
            digits[-1] = str((int(digits[-1]) + 1) % 10)
        four_digits = ''.join(digits)
        uuid_str = f"{first_char}x{four_digits}-{last_digit}"
        self.user_uuid = uuid_str
        self.settings['uuid'] = uuid_str
        self.save_udata()
    def update_map_menu_states(self):
        self.mapmenu.entryconfig(self.hide_maps_index, state='normal' if not self.maps_hidden else 'disabled')
        self.mapmenu.entryconfig(self.show_maps_index, state='disabled' if not self.maps_hidden else 'normal')
    def update_toolbar_menu_states(self):
        pos1 = self.upper_horizontal_paned.sash_coord(0)[0]
        u_width = self.upper_horizontal_paned.winfo_width()
        ratio = pos1 / u_width if u_width > 0 else 0
        if ratio > 0.15:
            self.mapmenu.entryconfig(self.hide_toolbar_index, state='normal')
            self.mapmenu.entryconfig(self.show_toolbar_index, state='disabled')
            self.toolbar_hidden = False
        else:
            self.mapmenu.entryconfig(self.hide_toolbar_index, state='disabled')
            self.mapmenu.entryconfig(self.show_toolbar_index, state='normal')
            self.toolbar_hidden = True
    def update_arc_menu_states(self):
        self.arcmenu.entryconfig(self.hide_arc_index, state='normal' if not self.arc_hidden else 'disabled')
        self.arcmenu.entryconfig(self.show_arc_index, state='disabled' if not self.arc_hidden else 'normal')
        self.arcmenu.entryconfig(self.deselect_arc_arc_index, state='normal' if self.current_arc_index is not None else 'disabled')
    def update_edit_menu_states(self):
        state = 'normal' if self.selected_region and (self.selected_region[2] - self.selected_region[0] > 1 or self.selected_region[3] - self.selected_region[1] > 1) else 'disabled'
        self.editmenu.entryconfig(self.copy_index, state=state)
        self.editmenu.entryconfig(self.cut_index, state=state)
        self.editmenu.entryconfig(self.replace_index, state=state)
        self.editmenu.entryconfig(self.make_new_index, state=state)
        self.editmenu.entryconfig(self.gen_new_index, state=state)
        self.editmenu.entryconfig(self.clear_prop_index, state=state)
        self.editmenu.entryconfig(self.remove_sel_index, state=state)
        paste_state = 'normal' if self.clipboard is not None else 'disabled'
        self.editmenu.entryconfig(self.paste_index, state=paste_state)
        undo_delete_state = 'normal' if self.deleted_arcs else 'disabled'
        self.editmenu.entryconfig(self.undo_arc_delete_index, state=undo_delete_state)
        undo_state = 'normal' if self.undo_stacks[self.current_index] else 'disabled'
        self.editmenu.entryconfig(self.undo_index, state=undo_state)
        redo_state = 'normal' if self.redo_stacks[self.current_index] else 'disabled'
        self.editmenu.entryconfig(self.redo_index, state=redo_state)
        map_all_state = 'normal' if len(self.maps) > 1 else 'disabled'
        self.mapmenu.entryconfig(self.export_all_png_index, state=map_all_state)
        arc_sel_state = 'normal' if self.current_arc_index is not None else 'disabled'
        self.arcmenu.entryconfig(self.export_sel_arc_index, state=arc_sel_state)
        self.editmenu.entryconfig(self.deselect_arc_edit_index, state=arc_sel_state)
        arc_all_state = 'normal' if self.arcs else 'disabled'
        self.arcmenu.entryconfig(self.export_all_arc_index, state=arc_all_state)
        undo_map_delete_state = 'normal' if self.deleted_maps else 'disabled'
        self.editmenu.entryconfig(self.undo_map_delete_index, state=undo_map_delete_state)
        self.mapmenu.entryconfig(self.undo_map_delete_map_index, state=undo_map_delete_state)
    def setup_ui(self):
        # Main vertical paned for upper and lower
        main_vertical_paned = tk.PanedWindow(self.root, orient=tk.VERTICAL, sashrelief=tk.FLAT)
        main_vertical_paned.pack(fill=tk.BOTH, expand=True)
        # Upper frame
        upper_frame = tk.Frame(main_vertical_paned)
        main_vertical_paned.add(upper_frame, minsize=0, stretch="never")
        self.upper_frame = upper_frame
        # Upper horizontal paned for left, center, right
        upper_horizontal_paned = tk.PanedWindow(upper_frame, orient=tk.HORIZONTAL, sashrelief=tk.FLAT)
        upper_horizontal_paned.pack(fill=tk.BOTH, expand=True)
        # Left toolbar: Symbol pick-n-place with descriptions
        left_frame = tk.Frame(upper_horizontal_paned)
        upper_horizontal_paned.add(left_frame, minsize=150, stretch="never")
        self.left_frame = left_frame
        symbols_label = tk.Label(left_frame, text="Symbols")
        symbols_label.pack(anchor=tk.CENTER)
        symbols_frame = tk.Frame(left_frame)
        symbols_frame.pack(fill=tk.BOTH, expand=True)
        symbols_vscroll = tk.Scrollbar(symbols_frame, orient=tk.VERTICAL)
        symbols_vscroll.pack(side=tk.LEFT, fill=tk.Y)
        self.symbol_list = tk.Listbox(symbols_frame, yscrollcommand=symbols_vscroll.set)
        for sym, desc in self.symbols:
            self.symbol_list.insert(tk.END, f"{sym} = {desc}")
        self.symbol_list.pack(fill=tk.BOTH, expand=True)
        symbols_vscroll.config(command=self.symbol_list.yview)
        self.symbol_list.bind("<<ListboxSelect>>", self.select_symbol)
        self.symbol_list.bind("<Button-3>", lambda e: messagebox.showinfo("Symbols List", "Select a symbol to place on the map or -- to enter select mode for properties."))
        self.symbol_list.bind("<Enter>", lambda e: self.symbol_list.focus_set())
        self.bind_scrolls(self.symbol_list)
        self.focusable_sections.append(self.symbol_list)
        # Center: Notebook for maps
        notebook_frame = tk.Frame(upper_horizontal_paned)
        upper_horizontal_paned.add(notebook_frame, minsize=600, stretch="always")
        self.notebook = ttk.Notebook(notebook_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)
        tab_btn_frame = tk.Frame(notebook_frame)
        tab_btn_frame.pack(side=tk.TOP, fill=tk.X)
        prev_btn = tk.Button(tab_btn_frame, text='<', command=self.prev_tab)
        prev_btn.pack(side=tk.LEFT)
        next_btn = tk.Button(tab_btn_frame, text='>', command=self.next_tab)
        next_btn.pack(side=tk.LEFT)
        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_change)
        # Right: Arcs and properties
        right_frame = tk.Frame(upper_horizontal_paned)
        upper_horizontal_paned.add(right_frame, minsize=250, stretch="never")
        arcs_label = tk.Label(right_frame, text="Arcs")
        arcs_label.pack(anchor=tk.CENTER)
        arc_list_frame = tk.Frame(right_frame)
        arc_list_frame.pack(fill=tk.BOTH, expand=True)
        arc_vscroll = tk.Scrollbar(arc_list_frame, orient=tk.VERTICAL)
        arc_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.arc_list = tk.Listbox(arc_list_frame, yscrollcommand=arc_vscroll.set, height=7)
        self.arc_list.pack(fill=tk.BOTH, expand=True)
        arc_vscroll.config(command=self.arc_list.yview)
        self.arc_list.bind("<<ListboxSelect>>", self.select_arc)
        self.arc_list.bind("<Button-1>", self.handle_arc_list_click)
        self.arc_list.bind("<Button-3>", lambda e: messagebox.showinfo("Arcs List", "Select an arc to edit or add new."))
        self.arc_list.bind("<Enter>", lambda e: self.arc_list.focus_set())
        self.bind_scrolls(self.arc_list)
        self.focusable_sections.append(self.arc_list)
        tk.Button(right_frame, text="New Arc", command=self.new_arc).pack(fill=tk.X)
        tk.Button(right_frame, text="Delete Arc", command=self.delete_arc).pack(fill=tk.X)
        # Property frame (hidden initially)
        self.property_canvas = tk.Canvas(right_frame)
        property_vscroll = tk.Scrollbar(right_frame, orient=tk.VERTICAL, command=self.property_canvas.yview)
        property_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.property_canvas.pack(fill=tk.BOTH, expand=True)
        self.property_canvas.config(yscrollcommand=property_vscroll.set)
        self.property_frame = tk.Frame(self.property_canvas)
        self.property_canvas.create_window((0,0), window=self.property_frame, anchor="nw")
        self.property_frame.bind("<Configure>", lambda e: self.property_canvas.config(scrollregion=self.property_canvas.bbox("all")))
        self.property_canvas.pack_forget() # Hide initially
        self.property_canvas.bind("<Button-3>", lambda e: messagebox.showinfo("Object Properties Drawer", "Edit properties of selected cells."))
        properties_label = tk.Label(self.property_frame, text="Properties")
        properties_label.pack(anchor=tk.CENTER)
        self.prop_name_var = tk.StringVar()
        tk.Label(self.property_frame, text="Name:").pack(anchor=tk.W)
        self.prop_name_entry = tk.Entry(self.property_frame, textvariable=self.prop_name_var)
        self.prop_name_entry.pack(fill=tk.X)
        self.prop_name_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_color_var = tk.StringVar(value="black")
        tk.Label(self.property_frame, text="Color:").pack(anchor=tk.W)
        self.prop_color_entry = tk.Entry(self.property_frame, textvariable=self.prop_color_var)
        self.prop_color_entry.pack(fill=tk.X)
        self.prop_color_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_texture_var = tk.StringVar()
        tk.Label(self.property_frame, text="Texture:").pack(anchor=tk.W)
        self.prop_texture_btn = tk.Button(self.property_frame, text="Select Texture", command=self.select_texture)
        self.prop_texture_btn.pack(fill=tk.X)
        tk.Label(self.property_frame, textvariable=self.prop_texture_var).pack(anchor=tk.W)
        self.prop_height_var = tk.StringVar(value="1")
        tk.Label(self.property_frame, text="Height:").pack(anchor=tk.W)
        def validate_int(P):
            return P.isdigit() or P == ''
        vcmd_int = self.root.register(validate_int)
        self.prop_height_entry = tk.Entry(self.property_frame, textvariable=self.prop_height_var, validate='key', validatecommand=(vcmd_int, '%P'))
        self.prop_height_entry.pack(fill=tk.X)
        self.prop_height_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_depth_var = tk.StringVar(value="1")
        tk.Label(self.property_frame, text="Depth:").pack(anchor=tk.W)
        self.prop_depth_entry = tk.Entry(self.property_frame, textvariable=self.prop_depth_var, validate='key', validatecommand=(vcmd_int, '%P'))
        self.prop_depth_entry.pack(fill=tk.X)
        self.prop_depth_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_value_var = tk.StringVar(value="0")
        tk.Label(self.property_frame, text="Value:").pack(anchor=tk.W)
        self.prop_value_entry = tk.Entry(self.property_frame, textvariable=self.prop_value_var, validate='key', validatecommand=(vcmd_int, '%P'))
        self.prop_value_entry.pack(fill=tk.X)
        self.prop_value_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_3d_var = tk.StringVar(value="0")
        tk.Label(self.property_frame, text="3D:").pack(anchor=tk.W)
        self.prop_3d_entry = tk.Entry(self.property_frame, textvariable=self.prop_3d_var, validate='key', validatecommand=(vcmd_int, '%P'))
        self.prop_3d_entry.pack(fill=tk.X)
        self.prop_3d_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        tk.Label(self.property_frame, text="Range:").pack(anchor=tk.W)
        def validate_float(P):
            if P == '':
                return True
            try:
                f = float(P)
                return f >= 0 and f <= 999999
            except:
                return False
        vcmd_float = self.root.register(validate_float)
        self.prop_range_entry = tk.Entry(self.property_frame, textvariable=self.prop_range_var, validate='key', validatecommand=(vcmd_float, '%P'))
        self.prop_range_entry.pack(fill=tk.X)
        self.prop_range_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_range_entry.bind("<FocusOut>", self.update_range_slider)
        self.prop_range_slider = tk.Scale(self.property_frame, orient=tk.HORIZONTAL, variable=self.prop_range_dvar, from_=0.0, to=9.9, resolution=0.1)
        self.prop_range_slider.pack(fill=tk.X)
        self.prop_range_slider.bind("<ButtonRelease-1>", self.sync_range_entry)
        self.sun_radio_frame = tk.Frame(self.property_frame)
        self.sun_radio_frame.pack(fill=tk.X)
        tk.Label(self.sun_radio_frame, text="Sun Position:").pack(anchor=tk.W)
        tk.Radiobutton(self.sun_radio_frame, text="Sunrise", variable=self.prop_sun_var, value="SR").pack(side=tk.LEFT)
        tk.Radiobutton(self.sun_radio_frame, text="Sunset", variable=self.prop_sun_var, value="SS").pack(side=tk.LEFT)
        tk.Radiobutton(self.sun_radio_frame, text="N/A", variable=self.prop_sun_var, value="NA").pack(side=tk.LEFT)
        tk.Button(self.property_frame, text="Apply", command=self.apply_properties).pack(fill=tk.X)
        self.lock_button = tk.Button(self.property_frame, text="Lock Apply", command=self.toggle_lock)
        self.lock_button.pack(fill=tk.X)
        # Bottom arc builder
        bottom_frame = tk.Frame(main_vertical_paned)
        main_vertical_paned.add(bottom_frame, minsize=50)
        # Bottom horizontal paned for arc fields, input gen, phrases, arc options
        bottom_horizontal_paned = tk.PanedWindow(bottom_frame, orient=tk.HORIZONTAL, sashrelief=tk.FLAT)
        bottom_horizontal_paned.pack(fill=tk.BOTH, expand=True)
        # Arc fields frame with both scrolls
        arc_fields_frame = tk.Frame(bottom_horizontal_paned)
        bottom_horizontal_paned.add(arc_fields_frame, minsize=600, stretch="always")
        arc_data_label = tk.Label(arc_fields_frame, text="Arc Data")
        arc_data_label.pack(anchor=tk.CENTER)
        arc_fields_canvas = tk.Canvas(arc_fields_frame)
        hscroll = tk.Scrollbar(arc_fields_frame, orient=tk.HORIZONTAL, command=arc_fields_canvas.xview)
        hscroll.pack(side=tk.BOTTOM, fill=tk.X)
        vscroll = tk.Scrollbar(arc_fields_frame, orient=tk.VERTICAL, command=arc_fields_canvas.yview)
        vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        arc_fields_canvas.pack(fill=tk.BOTH, expand=True)
        arc_fields_canvas.config(xscrollcommand=hscroll.set, yscrollcommand=vscroll.set)
        arc_inner_frame = tk.Frame(arc_fields_canvas)
        arc_fields_canvas.create_window((0,0), window=arc_inner_frame, anchor="nw")
        arc_inner_frame.bind("<Button-3>", lambda e: messagebox.showinfo("Arc Data", "Edit arc fields."))
        # Grid for labels and entries
        tk.Label(arc_inner_frame, text="Arc Name:").grid(row=0, column=0, sticky=tk.W)
        arc_name_entry = tk.Entry(arc_inner_frame, textvariable=self.arc_name_var)
        arc_name_entry.grid(row=0, column=1, sticky=tk.EW)
        def validate_len_18(P): return len(P) <= 18 or P == ''
        vcmd_name = self.root.register(validate_len_18)
        arc_name_entry.config(validate='key', validatecommand=(vcmd_name, '%P'))
        arc_name_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        arc_name_entry.bind("<FocusOut>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Estimated:").grid(row=1, column=0, sticky=tk.W)
        estimated_combo = ttk.Combobox(arc_inner_frame, textvariable=self.arc_estimated_type_var, values=["2-Finish (E2F)", "2-Start (E2S)", "Short-Hold-Time (SHT)", "Long-Hold-Time (LHT)"], state='readonly')
        estimated_combo.grid(row=1, column=1, sticky=tk.EW)
        estimated_combo.bind("<<ComboboxSelected>>", lambda e: [self.update_est_picker(), self.on_arc_change(e)])
        self.est_picker_frame = tk.Frame(arc_inner_frame)
        self.est_picker_frame.grid(row=2, column=1, sticky=tk.EW)
        self.update_est_picker()
        tk.Label(arc_inner_frame, text="Zone Type:").grid(row=3, column=0, sticky=tk.W)
        zone_combo = ttk.Combobox(arc_inner_frame, textvariable=self.arc_zone_type_var, values=['Safe', 'Crawl', 'Fight', 'Mix0', 'Mix1', 'Mix2', 'Mix3', 'Mixed'], state='readonly')
        zone_combo.grid(row=3, column=1, sticky=tk.EW)
        zone_combo.bind("<<ComboboxSelected>>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Start Msg:").grid(row=4, column=0, sticky=tk.W)
        arc_start_entry = tk.Entry(arc_inner_frame, textvariable=self.arc_start_msg_var)
        arc_start_entry.grid(row=4, column=1, sticky=tk.EW)
        def validate_len_150(P): return len(P) <= 150 or P == ''
        vcmd_150 = self.root.register(validate_len_150)
        arc_start_entry.config(validate='key', validatecommand=(vcmd_150, '%P'))
        arc_start_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        arc_start_entry.bind("<FocusOut>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Map:").grid(row=5, column=0, sticky=tk.W)
        arc_map_entry = tk.Entry(arc_inner_frame, textvariable=self.arc_map_var)
        arc_map_entry.grid(row=5, column=1, sticky=tk.EW)
        arc_map_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        arc_map_entry.bind("<FocusOut>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Map Type:").grid(row=6, column=0, sticky=tk.W)
        map_type_combo = ttk.Combobox(arc_inner_frame, textvariable=self.arc_map_type_var, values=['Generate', 'Import'], state='readonly')
        map_type_combo.grid(row=6, column=1, sticky=tk.EW)
        map_type_combo.bind("<<ComboboxSelected>>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Arc Data:").grid(row=7, column=0, sticky=tk.NW)
        self.arc_data_text = tk.Text(arc_inner_frame, height=10, wrap=tk.WORD)
        self.arc_data_text.grid(row=7, column=1, sticky=tk.EW)
        self.arc_data_text.bind("<<Modified>>", self.on_arc_modified)
        self.arc_data_text.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.arc_data_text.bind("<Button-3>", lambda e: messagebox.showinfo("Arc Data Text Field", "Enter arc data here."))
        tk.Label(arc_inner_frame, text="Confirm Msg:").grid(row=8, column=0, sticky=tk.W)
        arc_confirm_entry = tk.Entry(arc_inner_frame, textvariable=self.arc_confirm_msg_var)
        arc_confirm_entry.grid(row=8, column=1, sticky=tk.EW)
        arc_confirm_entry.config(validate='key', validatecommand=(vcmd_150, '%P'))
        arc_confirm_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        arc_confirm_entry.bind("<FocusOut>", self.on_arc_change)
        arc_inner_frame.columnconfigure(1, weight=1)
        arc_inner_frame.bind("<Configure>", lambda e: arc_fields_canvas.config(scrollregion=arc_fields_canvas.bbox("all")))
        self.bind_scrolls(arc_fields_canvas)
        self.focusable_sections.append(arc_fields_canvas)
        # Script Generator frame (old Input Generator)
        input_gen_frame = tk.Frame(bottom_horizontal_paned)
        bottom_horizontal_paned.add(input_gen_frame, minsize=200, stretch="never")
        script_gen_label = tk.Label(input_gen_frame, text="Script Generator")
        script_gen_label.pack(anchor=tk.CENTER)
        input_gen_list_frame = tk.Frame(input_gen_frame)
        input_gen_list_frame.pack(fill=tk.BOTH)
        input_gen_vscroll = tk.Scrollbar(input_gen_list_frame, orient=tk.VERTICAL)
        input_gen_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.input_gen_list = tk.Listbox(input_gen_list_frame, yscrollcommand=input_gen_vscroll.set, height=3)
        options = ["Enemy", "Boss", "Mini-Boss", "NPC", "Group", "Map Location"]
        for opt in options:
            self.input_gen_list.insert(tk.END, opt)
        self.input_gen_list.pack(fill=tk.BOTH, expand=True)
        input_gen_vscroll.config(command=self.input_gen_list.yview)
        self.input_gen_list.bind("<<ListboxSelect>>", self.select_input_gen_type)
        self.input_gen_list.bind("<Button-3>", lambda e: messagebox.showinfo("Script Generator Select", "Select a script type to generate."))
        # Input gen form with scrolls
        input_gen_form_frame = tk.Frame(input_gen_frame)
        input_gen_form_frame.pack(fill=tk.BOTH, expand=True)
        input_gen_form_canvas = tk.Canvas(input_gen_form_frame)
        input_gen_form_hscroll = tk.Scrollbar(input_gen_form_frame, orient=tk.HORIZONTAL, command=input_gen_form_canvas.xview)
        input_gen_form_hscroll.pack(side=tk.BOTTOM, fill=tk.X)
        input_gen_form_vscroll = tk.Scrollbar(input_gen_form_frame, orient=tk.VERTICAL, command=input_gen_form_canvas.yview)
        input_gen_form_vscroll.pack(side=tk.LEFT, fill=tk.Y)
        input_gen_form_canvas.pack(fill=tk.BOTH, expand=True)
        input_gen_form_canvas.config(xscrollcommand=input_gen_form_hscroll.set, yscrollcommand=input_gen_form_vscroll.set)
        self.input_gen_form_inner = tk.Frame(input_gen_form_canvas)
        input_gen_form_canvas.create_window((0,0), window=self.input_gen_form_inner, anchor="nw")
        self.input_gen_form_inner.bind("<Configure>", lambda e: input_gen_form_canvas.config(scrollregion=input_gen_form_canvas.bbox("all")))
        self.input_gen_form_inner.bind("<Button-3>", lambda e: messagebox.showinfo("Script Generator Form", "Enter details for the selected script type."))
        self.bind_scrolls(input_gen_form_canvas)
        self.focusable_sections.append(input_gen_form_canvas)
        # Phrases frame
        phrases_frame = tk.Frame(bottom_horizontal_paned)
        bottom_horizontal_paned.add(phrases_frame, minsize=200, stretch="never")
        data_phrases_label = tk.Label(phrases_frame, text="Data Phrases")
        data_phrases_label.pack(anchor=tk.CENTER)
        phrases_canvas = tk.Canvas(phrases_frame)
        hscroll_phrases = tk.Scrollbar(phrases_frame, orient=tk.HORIZONTAL, command=phrases_canvas.xview)
        hscroll_phrases.pack(side=tk.BOTTOM, fill=tk.X)
        vscroll_phrases = tk.Scrollbar(phrases_frame, orient=tk.VERTICAL, command=phrases_canvas.yview)
        vscroll_phrases.pack(side=tk.RIGHT, fill=tk.Y)
        phrases_canvas.pack(fill=tk.BOTH, expand=True)
        phrases_canvas.config(xscrollcommand=hscroll_phrases.set, yscrollcommand=vscroll_phrases.set)
        inner_frame = tk.Frame(phrases_canvas)
        phrases_canvas.create_window((0,0), window=inner_frame, anchor="nw")
        phrases = ["exit", "enter", "kill", "death", "squash", "XYZ", "pick", "acts", "touch", "user", "jim", "sarah", "bob", "obj", "weap", "armed", "arm", "speed", "faster", "slower", "slow", "glue", "hot", "cold", "froze", "flame", "drop", "xplode", "burp", "burpee", "slothee", "plop", "wrap", "parw", "par"]
        tooltips = {
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
        col = 0
        row = 0
        max_rows = 7 # Adjust based on height
        for phrase in phrases:
            btn = tk.Button(inner_frame, text=phrase, command=lambda p=phrase: self.insert_phrase(p))
            btn.grid(row=row, column=col, sticky=tk.EW)
            btn.bind("<Button-3>", lambda e, p=phrase: messagebox.showinfo("Phrase", f"Insert '{p}' into arc data"))
            btn.bind("<Enter>", lambda e, t=tooltips.get(phrase, ""): self.show_tooltip(e, t))
            btn.bind("<Leave>", self.hide_tooltip)
            btn.bind("<Motion>", lambda e, t=tooltips.get(phrase, ""): self.update_tooltip_pos(e, t))
            row += 1
            if row >= max_rows:
                row = 0
                col += 1
        def update_phrases_scroll(e):
            region = phrases_canvas.bbox("all")
            phrases_canvas.config(scrollregion=(region[0], region[1], region[2] + 50, region[3] + 50))
        inner_frame.bind("<Configure>", update_phrases_scroll)
        self.bind_scrolls(phrases_canvas)
        self.focusable_sections.append(phrases_canvas)
        # Arc options frame vertical with scroll, limited width
        arc_options_frame = tk.Frame(bottom_horizontal_paned)
        bottom_horizontal_paned.add(arc_options_frame, minsize=150, stretch="never")
        arc_options_label = tk.Label(arc_options_frame, text="Arc Options")
        arc_options_label.pack(anchor=tk.CENTER)
        arc_bottom_vscroll = tk.Scrollbar(arc_options_frame, orient=tk.VERTICAL)
        arc_bottom_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        arc_bottom_canvas = tk.Canvas(arc_options_frame, yscrollcommand=arc_bottom_vscroll.set)
        arc_bottom_canvas.pack(fill=tk.BOTH, expand=True)
        arc_bottom_vscroll.config(command=arc_bottom_canvas.yview)
        arc_bottom_inner = tk.Frame(arc_bottom_canvas)
        arc_bottom_canvas.create_window((0,0), window=arc_bottom_inner, anchor="nw")
        buttons = [
            ("Save Arc", self.save_arc),
            ("Load Arc", self.load_arc),
            ("Attach to Current Map", self.attach_to_map),
            ("Undo Arc", self.undo_arc),
            ("Redo Arc", self.redo_arc),
            ("Remove All Edits", self.remove_all_edits)
        ]
        for text, cmd in buttons:
            tk.Button(arc_bottom_inner, text=text, command=cmd).pack(fill=tk.X)
        arc_bottom_inner.bind("<Configure>", lambda e: arc_bottom_canvas.config(scrollregion=arc_bottom_canvas.bbox("all")) if arc_bottom_inner.winfo_height() > arc_bottom_canvas.winfo_height() else arc_bottom_canvas.config(scrollregion=(0,0,0,0)))
        arc_bottom_inner.bind("<Button-3>", lambda e: messagebox.showinfo("Arc Options", "Options for managing arcs."))
        self.bind_scrolls(arc_bottom_canvas)
        self.focusable_sections.append(arc_bottom_canvas)
        return main_vertical_paned, upper_horizontal_paned, bottom_horizontal_paned
    def select_texture(self):
        file = filedialog.askopenfilename(filetypes=[("PNG files", "*.png"), ("All files", "*.*")])
        if file:
            filename = os.path.basename(file)
            self.prop_texture_var.set(filename)
    def update_range_slider(self, event=None):
        try:
            val = float(self.prop_range_var.get())
            if val <= 9.9:
                self.prop_range_dvar.set(val)
                self.prop_range_slider.config(state='normal')
            else:
                self.prop_range_slider.config(state='disabled')
        except ValueError:
            pass
    def sync_range_entry(self, event=None):
        val = self.prop_range_dvar.get()
        self.prop_range_var.set(str(val))
    def bind_scrolls(self, widget):
        widget.bind("<MouseWheel>", self.handle_scroll)
        widget.bind("<Shift-MouseWheel>", self.handle_shift_scroll)
        widget.bind("<Button-4>", lambda e: self.handle_scroll(e))
        widget.bind("<Button-5>", lambda e: self.handle_scroll(e))
        widget.bind("<Shift-Button-4>", lambda e: self.handle_shift_scroll(e))
        widget.bind("<Shift-Button-5>", lambda e: self.handle_shift_scroll(e))
        widget.bind("<Key-Page_Up>", self.handle_page_up)
        widget.bind("<Key-Page_Down>", self.handle_page_down)
        widget.bind("<Shift-Key-Page_Up>", self.handle_shift_page_up)
        widget.bind("<Shift-Key-Page_Down>", self.handle_shift_page_down)
        widget.bind("<w>", lambda e: widget.yview_scroll(-1, "units"))
        widget.bind("<s>", lambda e: widget.yview_scroll(1, "units"))
        widget.bind("<a>", lambda e: widget.xview_scroll(-1, "units"))
        widget.bind("<d>", lambda e: widget.xview_scroll(1, "units"))
        widget.bind("<Up>", lambda e: widget.yview_scroll(-1, "units"))
        widget.bind("<Down>", lambda e: widget.yview_scroll(1, "units"))
        widget.bind("<Left>", lambda e: widget.xview_scroll(-1, "units"))
        widget.bind("<Right>", lambda e: widget.xview_scroll(1, "units"))
    def handle_shift_page_up(self, event):
        w = self.root.focus_get()
        if isinstance(w, (tk.Canvas, tk.Listbox, tk.Text)):
            w.xview_scroll(-1, "pages")
    def handle_shift_page_down(self, event):
        w = self.root.focus_get()
        if isinstance(w, (tk.Canvas, tk.Listbox, tk.Text)):
            w.xview_scroll(1, "pages")
    def select_input_gen_type(self, event):
        selection = self.input_gen_list.curselection()
        if selection:
            self.input_gen_type = self.input_gen_list.get(selection[0])
            self.show_input_gen_form()
    def show_input_gen_form(self):
        for widget in self.input_gen_form_inner.winfo_children():
            widget.destroy()
        fields = {
            "Enemy": ["Name/Type", "Drop Rate", "Spawn Rate", "Color Base", "Value", "Texture"],
            "Boss": ["Name/Type", "Drop Rate", "Spawn Rate", "Health Base", "Defense Base", "Attack Base", "Color Base", "Value", "Texture"],
            "Mini-Boss": ["Name/Type", "Drop Rate", "Spawn Rate", "Level Difference", "Color", "Value", "Texture"],
            "NPC": ["Name", "Type", "Drop Rate", "Spawn Rate", "Wealth", "Bargaining Willpower", "Color", "Value", "Texture"],
            "Group": ["Entities", "Drop Rate", "Spawn Rate", "Color", "Value", "Texture"], # Entities comma separated
            "Map Location": ["Object", "XY", "Drop Rate", "Spawn Rate", "Color", "Value", "Texture"]
        }.get(self.input_gen_type, [])
        self.input_gen_vars = {}
        row = 0
        for field in fields:
            tk.Label(self.input_gen_form_inner, text=field + ":").grid(row=row, column=0, sticky=tk.W)
            var = tk.StringVar()
            self.input_gen_vars[field] = var
            entry = tk.Entry(self.input_gen_form_inner, textvariable=var)
            entry.grid(row=row, column=1, sticky=tk.EW)
            entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
            if field in ["Drop Rate", "Spawn Rate", "Value", "Health Base", "Defense Base", "Attack Base", "Level Difference", "Wealth", "Bargaining Willpower"]:
                def validate_num(P):
                    return P.isdigit() or P == ''
                vcmd = self.root.register(validate_num)
                entry.config(validate='key', validatecommand=(vcmd, '%P'))
            if field == "XY" and self.input_gen_type == "Map Location":
                pick_button = tk.Button(self.input_gen_form_inner, text="Pick Location", command=self.start_pick_mode)
                pick_button.grid(row=row+1, column=0, columnspan=2, sticky=tk.EW)
                pick_button.config(anchor=tk.CENTER)
                row += 1
            row += 1
        if self.input_gen_type in ["Enemy", "Boss", "Mini-Boss", "NPC", "Group"]:
            tk.Label(self.input_gen_form_inner, text="AI Sequences:").grid(row=row, column=0, sticky=tk.W)
            ai_list = tk.Listbox(self.input_gen_form_inner, selectmode='multiple', height=5)
            options = {
                "Enemy": ["Alert", "Seek", "Check", "Circle", "Pace", "Stand", "Guard", "Wait", "Rest", "Respond", "Team"],
                "Boss": ["Alert", "Scatter Manipulator [Random]", "Distance Based Strat [logical]", "Fastest Kill Shot [opportunistic]", "Combo Baby Combo [Mixed approach]", "Flank Master [find-openings]", "Mix All [final-boss]"],
                "Mini-Boss": ["Alert", "Scatter Random", "Scatter Shortest Distance", "Scatter 2 target", "Scatter away target", "Mix Scatter", "Flank", "Mix All"],
                "NPC": ["Alert", "Check", "Pace", "Stand", "Wait", "Rest", "Respond"],
                "Group": ["Alert", "Scatter Random", "Scatter least motion", "Scatter 2 target", "Scatter away target", "Mix Response", "Flank"],
            }[self.input_gen_type]
            for opt in options:
                ai_list.insert(tk.END, opt)
            ai_list.grid(row=row, column=1, sticky=tk.EW)
            self.input_gen_vars['ai_list'] = ai_list
            row += 1
        tk.Button(self.input_gen_form_inner, text="Inject", command=self.inject_input_gen).grid(row=row, column=0, columnspan=2, sticky=tk.EW)
        self.input_gen_form_inner.columnconfigure(1, weight=1)
        self.apply_fg_to_widget(self.input_gen_form_inner)
    def apply_fg_to_widget(self, widget):
        def set_colors(w):
            try:
                w.config(fg=self.fg)
                if 'insertbackground' in w.keys():
                    w.config(insertbackground=self.fg)
            except:
                pass
            for child in w.winfo_children():
                set_colors(child)
        set_colors(widget)
    def start_pick_mode(self):
        self.pick_mode = True
        messagebox.showinfo("Pick Mode", "Click on the map to pick location.")
    def inject_input_gen(self):
        if self.input_gen_type:
            vars = {k: v.get() for k, v in self.input_gen_vars.items() if k != 'ai_list' and v.get()}
            ai_str = ''
            if 'ai_list' in self.input_gen_vars:
                sel = self.input_gen_vars['ai_list'].curselection()
                selected = [self.input_gen_vars['ai_list'].get(i) for i in sel]
                limits = {"Enemy": 2, "Boss": 3, "Mini-Boss": 2, "NPC": 4, "Group": 2}
                if len(selected) > limits.get(self.input_gen_type, 0):
                    messagebox.showerror("Error", "Too many AI sequences selected.")
                    return
                ai_str = ' '.join(f"!{s}!" for s in selected) if selected else ''
            if not vars:
                return
            insert_text = ""
            if self.input_gen_type == "Enemy":
                insert_text = f"'{vars.get('Name/Type', '')}' {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} {ai_str} color={vars.get('Color Base', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "Boss":
                insert_text = f"'{vars.get('Name/Type', '')}' (HP={vars.get('Health Base', '')}) (DEF={vars.get('Defense Base', '')}) (ATK={vars.get('Attack Base', '')}) {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} {ai_str} color={vars.get('Color Base', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "Mini-Boss":
                insert_text = f"'{vars.get('Name/Type', '')}' (level{vars.get('Level Difference', '')}) {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} {ai_str} color={vars.get('Color', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "NPC":
                insert_text = f"-{vars.get('Name', '')} {vars.get('Type', '')}- {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} coin={vars.get('Wealth', '')} willpwr={vars.get('Bargaining Willpower', '')} {ai_str} color={vars.get('Color', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "Group":
                insert_text = f"group{{{vars.get('Entities', '')}}} {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} {ai_str} color={vars.get('Color', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "Map Location":
                insert_text = f"^location (@{vars.get('XY', '')}) ^ ~{vars.get('Object', '')}~ {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} color={vars.get('Color', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            self.arc_data_text.insert(tk.INSERT, " " + insert_text + ", ")
    def update_est_picker(self):
        for widget in self.est_picker_frame.winfo_children():
            widget.destroy()
        option = self.arc_estimated_type_var.get()
        lengths = {
            "2-Finish (E2F)": [3,2,3],
            "2-Start (E2S)": [2,2,3],
            "Short-Hold-Time (SHT)": [2,3],
            "Long-Hold-Time (LHT)": [2,2],
        }.get(option, [])
        self.arc_estimated_parts = []
        col = 0
        for l in lengths:
            var = tk.StringVar()
            self.arc_estimated_parts.append(var)
            entry = tk.Entry(self.est_picker_frame, textvariable=var, width=l+1)
            def validate_num(P, maxl=l):
                return P.isdigit() and len(P) <= maxl or P == ''
            vcmd = self.root.register(validate_num)
            entry.config(validate='key', validatecommand=(vcmd, '%P'))
            entry.grid(row=0, column=col, sticky=tk.EW)
            entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
            entry.bind("<FocusOut>", self.on_arc_change)
            col += 1
            if l != lengths[-1]:
                tk.Label(self.est_picker_frame, text=":").grid(row=0, column=col)
                col += 1
        self.apply_fg_to_widget(self.est_picker_frame)
    def load_pane_positions(self):
        self.root.update()
        width = self.root.winfo_width()
        height = self.root.winfo_height()
        key_prefix = f'pane_{width}x{height}_'
        # main vertical
        v_height = self.main_vertical_paned.winfo_height()
        if v_height > 1:
            key = key_prefix + 'main_vertical_pos'
            if key in self.settings:
                pos = int(self.settings[key])
            else:
                pos = int(v_height * 0.8)
            pos = min(max(pos, 150), v_height - 50)
            self.main_vertical_paned.sash_place(0, 0, pos)
            ratio = pos / v_height
            if ratio <= 0.15:
                self.maps_hidden = True
            else:
                self.maps_hidden = False
            if ratio > 0.85:
                self.arc_hidden = True
            else:
                self.arc_hidden = False
            self.update_map_menu_states()
            self.update_arc_menu_states()
        # upper horizontal
        u_width = self.upper_horizontal_paned.winfo_width()
        if u_width > 1:
            key1 = key_prefix + 'upper_horizontal_pos1'
            if key1 in self.settings:
                pos1 = int(self.settings[key1])
            else:
                pos1 = int(u_width * 0.15)
            pos1 = min(max(pos1, 150), u_width - 600 - 250)
            key2 = key_prefix + 'upper_horizontal_pos2'
            if key2 in self.settings:
                pos2 = int(self.settings[key2])
            else:
                pos2 = int(u_width * 0.85)
            pos2 = min(max(pos2, pos1 + 600), u_width - 250)
            self.upper_horizontal_paned.sash_place(0, pos1, 0)
            self.upper_horizontal_paned.sash_place(1, pos2, 0)
        # bottom horizontal
        b_width = self.bottom_horizontal_paned.winfo_width()
        if b_width > 1:
            key1 = key_prefix + 'bottom_horizontal_pos1'
            if key1 in self.settings:
                pos1 = int(self.settings[key1])
            else:
                pos1 = int(b_width * 0.4)
            pos1 = min(max(pos1, 600), b_width - 200 - 200 - 150)
            key2 = key_prefix + 'bottom_horizontal_pos2'
            if key2 in self.settings:
                pos2 = int(self.settings[key2])
            else:
                pos2 = int(b_width * 0.6)
            pos2 = min(max(pos2, pos1 + 200), b_width - 200 - 150)
            key3 = key_prefix + 'bottom_horizontal_pos3'
            if key3 in self.settings:
                pos3 = int(self.settings[key3])
            else:
                pos3 = int(b_width * 0.85)
            pos3 = min(max(pos3, pos2 + 200), b_width - 150)
            self.bottom_horizontal_paned.sash_place(0, pos1, 0)
            self.bottom_horizontal_paned.sash_place(1, pos2, 0)
            self.bottom_horizontal_paned.sash_place(2, pos3, 0)
    def save_pane_positions(self, event=None):
        width = self.root.winfo_width()
        height = self.root.winfo_height()
        key_prefix = f'pane_{width}x{height}_'
        v_height = self.main_vertical_paned.winfo_height()
        if v_height > 1:
            pos = self.main_vertical_paned.sash_coord(0)[1]
            ratio = pos / v_height
            if ratio <= 0.15 and not self.maps_hidden:
                self.maps_hidden = True
                self.update_map_menu_states()
            elif ratio > 0.15 and self.maps_hidden:
                self.maps_hidden = False
                self.update_map_menu_states()
            if ratio > 0.85 and not self.arc_hidden:
                self.arc_hidden = True
                self.update_arc_menu_states()
            elif ratio <= 0.85 and self.arc_hidden:
                self.arc_hidden = False
                self.update_arc_menu_states()
            self.settings[key_prefix + 'main_vertical_pos'] = str(pos)
        u_width = self.upper_horizontal_paned.winfo_width()
        if u_width > 1:
            pos1 = self.upper_horizontal_paned.sash_coord(0)[0]
            ratio = pos1 / u_width
            if ratio <= 0.02 and not self.toolbar_hidden:
                self.toolbar_hidden = True
                self.update_toolbar_menu_states()
            elif ratio > 0.02 and self.toolbar_hidden:
                self.toolbar_hidden = False
                self.update_toolbar_menu_states()
            self.settings[key_prefix + 'upper_horizontal_pos1'] = str(pos1)
            pos2 = self.upper_horizontal_paned.sash_coord(1)[0]
            self.settings[key_prefix + 'upper_horizontal_pos2'] = str(pos2)
        b_width = self.bottom_horizontal_paned.winfo_width()
        if b_width > 1:
            pos1 = self.bottom_horizontal_paned.sash_coord(0)[0]
            self.settings[key_prefix + 'bottom_horizontal_pos1'] = str(pos1)
            pos2 = self.bottom_horizontal_paned.sash_coord(1)[0]
            self.settings[key_prefix + 'bottom_horizontal_pos2'] = str(pos2)
            pos3 = self.bottom_horizontal_paned.sash_coord(2)[0]
            self.settings[key_prefix + 'bottom_horizontal_pos3'] = str(pos3)
        self.save_udata()
    def handle_configure(self, event):
        new_width = self.root.winfo_width()
        new_height = self.root.winfo_height()
        if (new_width, new_height) != self.current_size:
            old_width, old_height = self.current_size
            self.current_size = (new_width, new_height)
            self.root.update_idletasks()
            key_prefix = f'pane_{new_width}x{new_height}_'
            has_saved = any((key_prefix + k) in self.settings for k in ['main_vertical_pos', 'upper_horizontal_pos1', 'upper_horizontal_pos2', 'bottom_horizontal_pos1', 'bottom_horizontal_pos2', 'bottom_horizontal_pos3'])
            if has_saved:
                self.load_pane_positions()
            else:
                # scale from old
                # main vertical
                v_height = self.main_vertical_paned.winfo_height()
                old_pos = self.main_vertical_paned.sash_coord(0)[1]
                pct = old_pos / old_height if old_height > 0 else 0.8
                new_pos = int(pct * new_height)
                new_pos = min(max(new_pos, 150), v_height - 50)
                self.main_vertical_paned.sash_place(0, 0, new_pos)
                # upper horizontal
                old_pos1 = self.upper_horizontal_paned.sash_coord(0)[0]
                pct1 = old_pos1 / old_width if old_width > 0 else 0.15
                new_pos1 = int(pct1 * new_width)
                new_pos1 = min(max(new_pos1, 150), new_width - 600 - 250)
                self.upper_horizontal_paned.sash_place(0, new_pos1, 0)
                old_pos2 = self.upper_horizontal_paned.sash_coord(1)[0]
                pct2 = old_pos2 / old_width if old_width > 0 else 0.85
                new_pos2 = int(pct2 * new_width)
                new_pos2 = min(max(new_pos2, new_pos1 + 600), new_width - 250)
                self.upper_horizontal_paned.sash_place(1, new_pos2, 0)
                # bottom horizontal
                old_pos1 = self.bottom_horizontal_paned.sash_coord(0)[0]
                pct1 = old_pos1 / old_width if old_width > 0 else 0.4
                new_pos1 = int(pct1 * new_width)
                new_pos1 = min(max(new_pos1, 600), new_width - 200 - 200 - 150)
                self.bottom_horizontal_paned.sash_place(0, new_pos1, 0)
                old_pos2 = self.bottom_horizontal_paned.sash_coord(1)[0]
                pct2 = old_pos2 / old_width if old_width > 0 else 0.6
                new_pos2 = int(pct2 * new_width)
                new_pos2 = min(max(new_pos2, new_pos1 + 200), new_width - 200 - 150)
                self.bottom_horizontal_paned.sash_place(1, new_pos2, 0)
                old_pos3 = self.bottom_horizontal_paned.sash_coord(2)[0]
                pct3 = old_pos3 / old_width if old_width > 0 else 0.85
                new_pos3 = int(pct3 * new_width)
                new_pos3 = min(max(new_pos3, new_pos2 + 200), new_width - 150)
                self.bottom_horizontal_paned.sash_place(2, new_pos3, 0)
    def add_map_tab(self, name):
        map_index = len(self.maps)
        width = 48
        height = 24
        grid = np.zeros((height, width), dtype=self.dtype)
        grid['symbol'] = ' '
        grid['color'] = 'black'
        grid['texture'] = ''
        grid['name'] = ''
        grid['value'] = 0
        grid['depth'] = 1
        grid['height'] = 1
        grid['3d'] = 0
        grid['range'] = 0.0
        grid['sun'] = 'NA'
        map_data = {
            'width': width,
            'height': height,
            'grid': grid,
            'openings': '0000000',
            'type': 'Safe',
            'name': name,
            'maker': 'User',
            'system': 'PB [no-jam] PyEditor',
            'attached_arcs': [],
            'dot_ids': [],
            'sunrise': None,
            'sunset': None,
            'sunrise_rect': None,
            'sunset_rect': None,
            'dirty': False
        }
        self.maps.append(map_data)
        frame = tk.Frame(self.notebook)
        tab_id = self.notebook.add(frame, text=name)
        # Header frame
        header_frame = tk.Frame(frame)
        header_frame.pack(fill=tk.X)
        close_btn = tk.Button(header_frame, text='X', command=lambda i=map_index: self.close_tab(i))
        close_btn.pack(side=tk.RIGHT)
        openings_var = tk.StringVar(value=map_data['openings'])
        tk.Label(header_frame, text="Openings:").pack(side=tk.LEFT)
        openings_entry = tk.Entry(header_frame, textvariable=openings_var, width=10)
        openings_entry.pack(side=tk.LEFT)
        def validate_openings(P):
            return len(P) <=7 and all(c in '01234' for c in P)
        vcmd_open = self.root.register(validate_openings)
        openings_entry.config(validate='key', validatecommand=(vcmd_open, '%P'))
        openings_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        width_var = tk.IntVar(value=map_data['width'])
        tk.Label(header_frame, text="Width:").pack(side=tk.LEFT)
        width_entry = tk.Entry(header_frame, textvariable=width_var, width=5)
        width_entry.pack(side=tk.LEFT)
        def validate_size(P):
            if P == '': return True
            try:
                v = int(P)
                return 0 <= v <= 1080
            except:
                return False
        vcmd_size = self.root.register(validate_size)
        width_entry.config(validate='key', validatecommand=(vcmd_size, '%P'))
        width_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        height_var = tk.IntVar(value=map_data['height'])
        tk.Label(header_frame, text="Height:").pack(side=tk.LEFT)
        height_entry = tk.Entry(header_frame, textvariable=height_var, width=5)
        height_entry.pack(side=tk.LEFT)
        height_entry.config(validate='key', validatecommand=(vcmd_size, '%P'))
        height_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        tk.Button(header_frame, text="Apply Size", command=lambda i=map_index: self.apply_size(i)).pack(side=tk.LEFT)
        type_var = tk.StringVar(value=map_data['type'])
        tk.Label(header_frame, text="Type:").pack(side=tk.LEFT)
        type_combo = ttk.Combobox(header_frame, textvariable=type_var, values=['Safe', 'Crawl', 'Fight', 'Mix0', 'Mix1', 'Mix2', 'Mix3', 'Mixed'], state='readonly', width=10)
        type_combo.pack(side=tk.LEFT)
        name_var = tk.StringVar(value=map_data['name'])
        tk.Label(header_frame, text="Name:").pack(side=tk.LEFT)
        name_entry = tk.Entry(header_frame, textvariable=name_var, width=15)
        name_entry.pack(side=tk.LEFT)
        def validate_len_28(P): return len(P) <= 28 or P == ''
        vcmd_28 = self.root.register(validate_len_28)
        name_entry.config(validate='key', validatecommand=(vcmd_28, '%P'))
        name_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        maker_var = tk.StringVar(value=map_data['maker'])
        tk.Label(header_frame, text="Maker:").pack(side=tk.LEFT)
        maker_entry = tk.Entry(header_frame, textvariable=maker_var, width=15)
        maker_entry.pack(side=tk.LEFT)
        def validate_len_21(P): return len(P) <= 21 or P == ''
        vcmd_21 = self.root.register(validate_len_21)
        maker_entry.config(validate='key', validatecommand=(vcmd_21, '%P'))
        maker_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        tk.Label(header_frame, text="System: " + map_data['system']).pack(side=tk.LEFT)
        # Canvas frame
        canvas_frame = tk.Frame(frame)
        canvas_frame.pack(fill=tk.BOTH, expand=True)
        canvas = tk.Canvas(canvas_frame, width=map_data['width'] * self.cell_size, height=map_data['height'] * self.cell_size + 40) # extra for dots
        hbar = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=canvas.xview)
        hbar.pack(side=tk.BOTTOM, fill=tk.X)
        vbar = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=canvas.yview)
        vbar.pack(side=tk.RIGHT, fill=tk.Y)
        zoom_slider = tk.Scale(canvas_frame, orient=tk.VERTICAL, from_=5, to=50, resolution=1, command=self.on_zoom)
        zoom_slider.set(self.cell_size)
        zoom_slider.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        canvas.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
        self.canvases.append(canvas)
        self.zoom_sliders.append(zoom_slider)
        self.canvas_texts_list.append([[None for _ in range(map_data['width'])] for _ in range(map_data['height'])])
        self.var_dicts.append({
            'openings_var': openings_var,
            'width_var': width_var,
            'height_var': height_var,
            'type_var': type_var,
            'name_var': name_var,
            'maker_var': maker_var
        })
        self.undo_stacks.append([])
        self.redo_stacks.append([])
        canvas.bind("<Button-1>", self.on_canvas_click)
        canvas.bind("<B1-Motion>", self.on_canvas_motion)
        canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        canvas.bind("<Button-3>", self.handle_right_click)
        canvas.bind("<Control-Return>", self.handle_keyboard_right_click)
        canvas.bind("<Enter>", lambda e: canvas.focus_set())
        canvas.bind("<Motion>", self.on_canvas_motion_hover)
        self.bind_scrolls(canvas)
        self.focusable_sections.append(canvas)
        self.redraw_canvas(map_index)
        self.center_canvas(map_index)
        self.apply_fg_to_widget(header_frame)
        self.apply_fg_to_widget(type_combo)
        self.apply_fg_to_widget(canvas_frame)
        self.apply_fg_to_widget(zoom_slider)
    def on_zoom(self, val):
        self.cell_size = int(val)
        self.padding = self.cell_size * 10
        self.redraw_canvas(self.current_index)
        self.center_canvas(self.current_index)
    def on_canvas_motion_hover(self, event):
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        if self.hover_rect:
            canvas.delete(self.hover_rect)
        map_data = self.maps[self.current_index]
        if 0 <= x < map_data['width'] and 0 <= y < map_data['height']:
            color = self.hover_space_color if map_data['grid'][y, x]['symbol'] == ' ' else self.hover_obj_color
            self.hover_rect = canvas.create_rectangle(x * self.cell_size, y * self.cell_size, (x + 1) * self.cell_size, (y + 1) * self.cell_size, outline=color, width=2)
    def draw_attached_dots(self, index):
        canvas = self.canvases[index]
        map_data = self.maps[index]
        h = map_data['height']
        bottom_y = h * self.cell_size + 10
        canvas.config(scrollregion=(-self.padding, -self.padding, map_data['width'] * self.cell_size + self.padding, bottom_y + 30 + self.padding))
        canvas.delete('arc_dot')
        dot_ids = []
        for i in range(len(map_data['attached_arcs'])):
            x = 10 + i * 30
            dot = canvas.create_oval(x, bottom_y, x+20, bottom_y+20, fill='green', tags='arc_dot')
            dot_ids.append(dot)
        map_data['dot_ids'] = dot_ids
    def on_tab_change(self, event):
        if self.notebook.tabs():
            self.current_index = self.notebook.index("current")
            self.deselect()
            self.update_edit_menu_states()
            self.draw_attached_dots(self.current_index)
    def select_symbol(self, event):
        selection = self.symbol_list.curselection()
        if selection:
            item = self.symbol_list.get(selection[0])
            sym = item.split(' = ')[0] if ' =' in item else item
            self.current_symbol.set(sym)
            self.select_mode = (sym == '--')
            if self.lock_var.get() and sym != self.locked_symbol:
                self.toggle_lock()
        else:
            self.current_symbol.set('--')
            self.select_mode = True
        if self.ongoing_action == 'paste':
            self.ongoing_action = None
    def on_canvas_click(self, event):
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        map_data = self.maps[self.current_index]
        if self.pick_mode:
            self.picked_x = x
            self.picked_y = y
            self.picked_symbol = map_data['grid'][y, x]['symbol']
            self.input_gen_vars['XY'].set(f"{x},{y}")
            self.input_gen_vars['Object'].set(self.picked_symbol)
            self.pick_mode = False
            return
        if self.sunset_click:
            map_data['sunset'] = (x, y)
            self.sunset_click = False
            self.sunrise_click = True
            self.redraw_canvas(self.current_index)
            return
        if self.sunrise_click:
            map_data['sunrise'] = (x, y)
            self.sunrise_click = False
            self.redraw_canvas(self.current_index)
            return
        if self.ongoing_action == 'paste':
            if self.selected_region:
                self.paste_pos = (self.selected_region[0], self.selected_region[1])
            else:
                self.paste_pos = (x, y)
            self.paste_selected()
            self.ongoing_action = None
            return
        bottom_y = map_data['height']
        if y >= bottom_y:
            items = canvas.find_closest(canvas.canvasx(event.x), canvas.canvasy(event.y))
            if items and 'arc_dot' in canvas.gettags(items[0]):
                item = items[0]
                arc_idx = map_data['dot_ids'].index(item)
                arc = map_data['attached_arcs'][arc_idx]
                found = False
                for j, g_arc in enumerate(self.arcs):
                    if g_arc['name'] == arc['name']:
                        self.current_arc_index = j
                        found = True
                        break
                if not found:
                    self.arcs.append(copy.deepcopy(arc))
                    self.arc_list.insert(tk.END, arc['name'])
                    self.current_arc_index = len(self.arcs) - 1
                self.select_arc(None)
                return
        if 0 <= x < map_data['width'] and 0 <= y < map_data['height']:
            if map_data['grid'][y, x]['symbol'] == '/' and (map_data['grid'][y, x]['value'] > 1 or map_data['grid'][y, x]['value'] < 0):
                self.cheating_detected += 1
                if self.cheating_detected > 0:
                    self.cheating_reason = "Touched forbidden land"
            if not self.select_mode:
                self.place_symbol(event)
                self.paste_pos = (x, y)
            else:
                self.deselect_multi()
                self.select_start = (x, y)
                self.select_end = (x, y)
                self.update_select_rect()
            map_data['dirty'] = True
    def on_canvas_motion(self, event):
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        if self.select_start and self.select_mode:
            self.select_end = (x, y)
            self.update_select_rect()
        elif not self.select_mode:
            self.place_symbol(event)
    def on_canvas_release(self, event):
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        map_data = self.maps[self.current_index]
        if self.select_start and self.select_mode:
            minx = min(self.select_start[0], self.select_end[0])
            miny = min(self.select_start[1], self.select_end[1])
            maxx = max(self.select_start[0], self.select_end[0]) + 1
            maxy = max(self.select_start[1], self.select_end[1]) + 1
            if minx < 0 or miny < 0 or maxx > map_data['width'] or maxy > map_data['height']:
                return
            self.selected_region = (minx, miny, maxx, maxy)
            self.select_start = None
            if self.select_rect:
                canvas.delete(self.select_rect)
            self.select_rect = None
            self.selected_rects = []
            for yy in range(miny, maxy):
                for xx in range(minx, maxx):
                    rect_id = canvas.create_rectangle(xx * self.cell_size, yy * self.cell_size, (xx + 1) * self.cell_size, (yy + 1) * self.cell_size, outline=self.multi_selected_color, width=3, stipple='gray25')
                    self.selected_rects.append(rect_id)
            if maxx - minx == 1 and maxy - miny == 1:
                self.selected_x = minx
                self.selected_y = miny
                cell = map_data['grid'][miny, minx]
                self.prop_name_var.set(cell['name'])
                self.prop_color_var.set(cell['color'])
                self.prop_texture_var.set(cell['texture'])
                self.prop_height_var.set(str(cell['height']))
                self.prop_depth_var.set(str(cell['depth']))
                self.prop_value_var.set(str(cell['value']))
                self.prop_3d_var.set(str(cell['3d']))
                self.prop_range_var.set(str(cell['range']))
                self.update_range_slider()
                self.prop_sun_var.set(cell['sun'])
                self.sun_radio_frame.pack(fill=tk.X)
                self.property_canvas.pack(fill=tk.BOTH, expand=True)
            else:
                self.sun_radio_frame.pack_forget()
                self.show_multi_properties()
            self.update_edit_menu_states()
    def update_select_rect(self):
        canvas = self.canvases[self.current_index]
        if self.select_rect:
            canvas.delete(self.select_rect)
        if self.select_start and self.select_end:
            minx = min(self.select_start[0], self.select_end[0])
            miny = min(self.select_start[1], self.select_end[1])
            maxx = max(self.select_start[0], self.select_end[0]) + 1
            maxy = max(self.select_start[1], self.select_end[1]) + 1
            self.select_rect = canvas.create_rectangle(minx * self.cell_size, miny * self.cell_size, maxx * self.cell_size, maxy * self.cell_size, outline=self.multi_active_color, width=3, dash=True, stipple='gray25')
    def deselect_multi(self):
        if self.selected_rects:
            canvas = self.canvases[self.current_index]
            for r in self.selected_rects:
                canvas.delete(r)
            self.selected_rects = []
        self.selected_region = None
        self.update_edit_menu_states()
    def get_shared_props(self):
        if not self.selected_region:
            return None
        minx, miny, maxx, maxy = self.selected_region
        map_data = self.maps[self.current_index]
        names = set()
        colors = set()
        textures = set()
        heights = set()
        depths = set()
        values = set()
        threed = set()
        ranges = set()
        suns = set()
        for yy in range(miny, maxy):
            for xx in range(minx, maxx):
                cell = map_data['grid'][yy, xx]
                names.add(cell['name'])
                colors.add(cell['color'])
                textures.add(cell['texture'])
                heights.add(cell['height'])
                depths.add(cell['depth'])
                values.add(cell['value'])
                threed.add(cell['3d'])
                ranges.add(cell['range'])
                suns.add(cell['sun'])
        shared = {}
        shared['name'] = list(names)[0] if len(names) == 1 else ''
        shared['color'] = list(colors)[0] if len(colors) == 1 else ''
        shared['texture'] = list(textures)[0] if len(textures) == 1 else ''
        shared['height'] = list(heights)[0] if len(heights) == 1 else ''
        shared['depth'] = list(depths)[0] if len(depths) == 1 else ''
        shared['value'] = list(values)[0] if len(values) == 1 else ''
        shared['3d'] = list(threed)[0] if len(threed) == 1 else 0
        shared['range'] = list(ranges)[0] if len(ranges) == 1 else 0.0
        shared['sun'] = list(suns)[0] if len(suns) == 1 else 'NA'
        return shared
    def show_multi_properties(self):
        shared = self.get_shared_props()
        if shared:
            self.prop_name_var.set(shared['name'])
            self.prop_color_var.set(shared['color'])
            self.prop_texture_var.set(shared['texture'])
            self.prop_height_var.set(str(shared['height']) if shared['height'] != '' else '')
            self.prop_depth_var.set(str(shared['depth']) if shared['depth'] != '' else '')
            self.prop_value_var.set(str(shared['value']) if shared['value'] != '' else '')
            self.prop_3d_var.set(str(shared['3d']) if shared['3d'] != '' else '')
            self.prop_range_var.set(str(shared['range']) if shared['range'] != '' else '')
            self.update_range_slider()
            self.prop_sun_var.set(shared['sun'])
            self.sun_radio_frame.pack_forget()
            self.property_canvas.pack(fill=tk.BOTH, expand=True)
            self.apply_fg_to_widget(self.property_canvas)
    def copy_selected(self):
        if self.selected_region:
            minx, miny, maxx, maxy = self.selected_region
            map_data = self.maps[self.current_index]
            self.clipboard = np.copy(map_data['grid'][miny:maxy, minx:maxx])
            self.clipboard_width = maxx - minx
            self.clipboard_height = maxy - miny
            self.update_edit_menu_states()
    def cut_selected(self):
        self.copy_selected()
        self.remove_selected()
    def paste_selected(self):
        if self.clipboard is not None:
            if not self.paste_pos and not self.selected_region:
                self.ongoing_action = 'paste'
                return
            if self.selected_region:
                x, y = self.selected_region[0], self.selected_region[1]
            else:
                x, y = self.paste_pos
            map_data = self.maps[self.current_index]
            height = map_data['height']
            width = map_data['width']
            clip_h, clip_w = self.clipboard.shape
            end_y = min(y + clip_h, height)
            end_x = min(x + clip_w, width)
            affected = {(yy, xx) for yy in range(y, end_y) for xx in range(x, end_x)}
            self.push_undo(False, affected)
            map_data['grid'][y:end_y, x:end_x] = self.clipboard[0:end_y-y, 0:end_x-x]
            self.update_canvas_changed(affected)
            self.update_edit_menu_states()
            self.set_dirty()
            map_data['dirty'] = True
    def replace_selected(self):
        if self.selected_region:
            minx, miny, maxx, maxy = self.selected_region
            map_data = self.maps[self.current_index]
            sym = self.current_symbol.get()
            if sym == '--' or sym == '':
                sym = ' '
            affected = {(yy, xx) for yy in range(miny, maxy) for xx in range(minx, maxx)}
            self.push_undo(False, affected)
            for yy in range(miny, maxy):
                for xx in range(minx, maxx):
                    map_data['grid'][yy, xx]['symbol'] = sym
                    if self.lock_var.get() and self.locked_properties:
                        for k, v in self.locked_properties.items():
                            map_data['grid'][yy, xx][k] = v
            self.update_canvas_changed(affected)
            self.update_edit_menu_states()
            self.set_dirty()
            map_data['dirty'] = True
    def make_new_map(self):
        if self.selected_region:
            minx, miny, maxx, maxy = self.selected_region
            new_width = maxx - minx
            new_height = maxy - miny
            self.add_map_tab("New Map")
            new_index = len(self.maps) - 1
            new_map = self.maps[new_index]
            new_map['width'] = new_width
            new_map['height'] = new_height
            old_map = self.maps[self.current_index]
            new_map['grid'] = np.copy(old_map['grid'][miny:maxy, minx:maxx])
            self.var_dicts[new_index]['width_var'].set(new_width)
            self.var_dicts[new_index]['height_var'].set(new_height)
            self.redraw_canvas(new_index)
            self.center_canvas(new_index)
            self.notebook.select(new_index)
            self.set_dirty()
            new_map['dirty'] = True
    def generate_new_section(self):
        messagebox.showinfo("TODO", "Generate New Section functionality is in TODO state.")
    def clear_selected_properties(self):
        if self.selected_region:
            focus = self.root.focus_get()
            prop_map = {
                self.prop_name_entry: ('name', ''),
                self.prop_color_entry: ('color', 'black'),
                self.prop_texture_btn: ('texture', ''), # adjusted
                self.prop_height_entry: ('height', 1),
                self.prop_depth_entry: ('depth', 1),
                self.prop_value_entry: ('value', 0),
                self.prop_3d_entry: ('3d', 0),
                self.prop_range_entry: ('range', 0.0),
            }
            minx, miny, maxx, maxy = self.selected_region
            map_data = self.maps[self.current_index]
            affected = {(yy, xx) for yy in range(miny, maxy) for xx in range(minx, maxx)}
            self.push_undo(False, affected)
            if focus in prop_map:
                key, default = prop_map[focus]
                for yy in range(miny, maxy):
                    for xx in range(minx, maxx):
                        map_data['grid'][yy, xx][key] = default
            else:
                for yy in range(miny, maxy):
                    for xx in range(minx, maxx):
                        map_data['grid'][yy, xx]['name'] = ''
                        map_data['grid'][yy, xx]['color'] = 'black'
                        map_data['grid'][yy, xx]['texture'] = ''
                        map_data['grid'][yy, xx]['height'] = 1
                        map_data['grid'][yy, xx]['depth'] = 1
                        map_data['grid'][yy, xx]['value'] = 0
                        map_data['grid'][yy, xx]['3d'] = 0
                        map_data['grid'][yy, xx]['range'] = 0.0
            self.update_canvas_changed(affected)
            self.update_edit_menu_states()
            self.set_dirty()
            map_data['dirty'] = True
    def remove_selected(self):
        if self.selected_region:
            minx, miny, maxx, maxy = self.selected_region
            map_data = self.maps[self.current_index]
            affected = {(yy, xx) for yy in range(miny, maxy) for xx in range(minx, maxx)}
            self.push_undo(False, affected)
            for yy in range(miny, maxy):
                for xx in range(minx, maxx):
                    map_data['grid'][yy, xx]['symbol'] = ' '
                    map_data['grid'][yy, xx]['name'] = ''
                    map_data['grid'][yy, xx]['color'] = 'black'
                    map_data['grid'][yy, xx]['texture'] = ''
                    map_data['grid'][yy, xx]['height'] = 1
                    map_data['grid'][yy, xx]['depth'] = 1
                    map_data['grid'][yy, xx]['value'] = 0
                    map_data['grid'][yy, xx]['3d'] = 0
                    map_data['grid'][yy, xx]['range'] = 0.0
                    map_data['grid'][yy, xx]['sun'] = 'NA'
            self.update_canvas_changed(affected)
            self.update_edit_menu_states()
            self.set_dirty()
            map_data['dirty'] = True
    def place_symbol(self, event):
        if self.select_mode:
            return
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        map_data = self.maps[self.current_index]
        if 0 <= x < map_data['width'] and 0 <= y < map_data['height']:
            sym = self.current_symbol.get()
            affected = {(y, x)}
            self.push_undo(False, affected)
            map_data['grid'][y, x]['symbol'] = sym
            if self.lock_var.get() and sym == self.locked_symbol and self.locked_properties:
                for k, v in self.locked_properties.items():
                    map_data['grid'][y, x][k] = v
            self.update_canvas_changed(affected)
            # Auto-select after place
            self.selected_x = x
            self.selected_y = y
            cell = map_data['grid'][y, x]
            self.prop_name_var.set(cell['name'])
            self.prop_color_var.set(cell['color'])
            self.prop_texture_var.set(cell['texture'])
            self.prop_height_var.set(str(cell['height']))
            self.prop_depth_var.set(str(cell['depth']))
            self.prop_value_var.set(str(cell['value']))
            self.prop_3d_var.set(str(cell['3d']))
            self.prop_range_var.set(str(cell['range']))
            self.update_range_slider()
            self.prop_sun_var.set(cell['sun'])
            self.sun_radio_frame.pack(fill=tk.X)
            self.property_canvas.pack(fill=tk.BOTH, expand=True)
            self.apply_fg_to_widget(self.property_canvas)
            self.update_edit_menu_states()
            self.set_dirty()
            map_data['dirty'] = True
    def handle_right_click(self, event):
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        map_data = self.maps[self.current_index]
        if 0 <= x < map_data['width'] and 0 <= y < map_data['height']:
            if self.select_mode or self.current_symbol.get() == '--':
                self.select_cell(event)
            else:
                affected = {(y, x)}
                self.push_undo(False, affected)
                map_data['grid'][y, x]['symbol'] = ' '
                self.update_canvas_changed(affected)
                self.set_dirty()
                map_data['dirty'] = True
        else:
            messagebox.showinfo("Canvas Info", "This is the map canvas. Left-click to place symbols, right-click to remove or select properties.")
    def handle_keyboard_right_click(self, event):
        canvas = self.canvases[self.current_index]
        root_x = canvas.winfo_rootx()
        root_y = canvas.winfo_rooty()
        pointer_x = self.root.winfo_pointerx() - root_x
        pointer_y = self.root.winfo_pointery() - root_y
        fake_event = type('FakeEvent', (object,), {'x': pointer_x, 'y': pointer_y, 'widget': canvas})()
        fake_event.canvasx = lambda x: x
        fake_event.canvasy = lambda y: y
        self.handle_right_click(fake_event)
    def select_cell(self, event):
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        map_data = self.maps[self.current_index]
        if 0 <= x < map_data['width'] and 0 <= y < map_data['height']:
            self.selected_x = x
            self.selected_y = y
            cell = map_data['grid'][y, x]
            self.prop_name_var.set(cell['name'])
            self.prop_color_var.set(cell['color'])
            self.prop_texture_var.set(cell['texture'])
            self.prop_height_var.set(str(cell['height']))
            self.prop_depth_var.set(str(cell['depth']))
            self.prop_value_var.set(str(cell['value']))
            self.prop_3d_var.set(str(cell['3d']))
            self.prop_range_var.set(str(cell['range']))
            self.update_range_slider()
            if (x, y) == map_data.get('sunrise', None):
                self.prop_sun_var.set('SR')
            elif (x, y) == map_data.get('sunset', None):
                self.prop_sun_var.set('SS')
            else:
                self.prop_sun_var.set('NA')
            self.sun_radio_frame.pack(fill=tk.X)
            self.property_canvas.pack(fill=tk.BOTH, expand=True)
            self.apply_fg_to_widget(self.property_canvas)
            if self.lock_var.get() and cell['symbol'] == self.locked_symbol:
                self.apply_properties()
    def toggle_lock(self):
        self.lock_var.set(not self.lock_var.get())
        if self.lock_var.get():
            self.lock_button.config(fg='red')
            if self.selected_x is not None and self.selected_y is not None:
                self.locked_symbol = self.maps[self.current_index]['grid'][self.selected_y, self.selected_x]['symbol']
                self.locked_properties = {
                    'name': self.prop_name_var.get(),
                    'color': self.prop_color_var.get(),
                    'texture': self.prop_texture_var.get(),
                    'height': int(self.prop_height_var.get()) if self.prop_height_var.get() else 1,
                    'depth': int(self.prop_depth_var.get()) if self.prop_depth_var.get() else 1,
                    'value': int(self.prop_value_var.get()) if self.prop_value_var.get() else 0,
                    '3d': int(self.prop_3d_var.get()) if self.prop_3d_var.get() else 0,
                    'range': float(self.prop_range_var.get()) if self.prop_range_var.get() else 0.0
                }
        else:
            self.lock_button.config(fg=self.fg)
            self.locked_symbol = None
            self.locked_properties = None
    def apply_properties(self):
        name = self.prop_name_var.get()
        color = self.prop_color_var.get()
        texture = self.prop_texture_var.get()
        height_str = self.prop_height_var.get()
        depth_str = self.prop_depth_var.get()
        value_str = self.prop_value_var.get()
        threed_str = self.prop_3d_var.get()
        range_str = self.prop_range_var.get()
        sun = self.prop_sun_var.get()
        map_data = self.maps[self.current_index]
        grid = map_data['grid']
        is_multi = self.selected_region and (self.selected_region[2] - self.selected_region[0] > 1 or self.selected_region[3] - self.selected_region[1] > 1)
        if is_multi:
            if not messagebox.askyesno("Confirm", "Attaching Mass Selected Properties will change the properties for all selected objects. Do you wish to continue?"):
                return
            minx, miny, maxx, maxy = self.selected_region
            affected = {(y, x) for y in range(miny, maxy) for x in range(minx, maxx)}
            self.push_undo(False, affected)
            for y in range(miny, maxy):
                for x in range(minx, maxx):
                    if name: grid[y, x]['name'] = name
                    if color: grid[y, x]['color'] = color
                    if texture: grid[y, x]['texture'] = texture
                    if height_str: grid[y, x]['height'] = int(height_str)
                    if depth_str: grid[y, x]['depth'] = int(depth_str)
                    if value_str: grid[y, x]['value'] = int(value_str)
                    if threed_str: grid[y, x]['3d'] = int(threed_str)
                    if range_str: grid[y, x]['range'] = float(range_str)
            self.update_canvas_changed(affected)
        else:
            if self.selected_x is not None and self.selected_y is not None:
                affected = {(self.selected_y, self.selected_x)}
                if self.lock_var.get():
                    self.locked_symbol = grid[self.selected_y, self.selected_x]['symbol']
                    for yy in range(map_data['height']):
                        for xx in range(map_data['width']):
                            if grid[yy, xx]['symbol'] == self.locked_symbol:
                                affected.add((yy, xx))
                self.push_undo(False, affected)
                height = int(height_str) if height_str else 1
                depth = int(depth_str) if depth_str else 1
                value = int(value_str) if value_str else 0
                threed = int(threed_str) if threed_str else 0
                range_val = float(range_str) if range_str else 0.0
                grid[self.selected_y, self.selected_x]['name'] = name
                grid[self.selected_y, self.selected_x]['color'] = color
                grid[self.selected_y, self.selected_x]['texture'] = texture
                grid[self.selected_y, self.selected_x]['height'] = height
                grid[self.selected_y, self.selected_x]['depth'] = depth
                grid[self.selected_y, self.selected_x]['value'] = value
                grid[self.selected_y, self.selected_x]['3d'] = threed
                grid[self.selected_y, self.selected_x]['range'] = range_val
                old_sunrise = map_data.get('sunrise')
                old_sunset = map_data.get('sunset')
                if sun == 'SR':
                    if old_sunrise and old_sunrise != (self.selected_x, self.selected_y):
                        oy, ox = old_sunrise
                        grid[oy, ox]['sun'] = 'NA'
                    map_data['sunrise'] = (self.selected_x, self.selected_y)
                    grid[self.selected_y, self.selected_x]['sun'] = 'SR'
                elif sun == 'SS':
                    if old_sunset and old_sunset != (self.selected_x, self.selected_y):
                        oy, ox = old_sunset
                        grid[oy, ox]['sun'] = 'NA'
                    map_data['sunset'] = (self.selected_x, self.selected_y)
                    grid[self.selected_y, self.selected_x]['sun'] = 'SS'
                elif sun == 'NA':
                    if (self.selected_x, self.selected_y) == old_sunrise:
                        map_data['sunrise'] = None
                    if (self.selected_x, self.selected_y) == old_sunset:
                        map_data['sunset'] = None
                    grid[self.selected_y, self.selected_x]['sun'] = 'NA'
                self.update_canvas_changed(affected)
                self.redraw_canvas(self.current_index) # to update rects
                if self.lock_var.get():
                    self.locked_properties = {
                        'name': name,
                        'color': color,
                        'texture': texture,
                        'height': height,
                        'depth': depth,
                        'value': value,
                        '3d': threed,
                        'range': range_val
                    }
                    for y in range(map_data['height']):
                        for x in range(map_data['width']):
                            if grid[y, x]['symbol'] == self.locked_symbol and (y, x) != (self.selected_y, self.selected_x):
                                grid[y, x]['name'] = name
                                grid[y, x]['color'] = color
                                grid[y, x]['texture'] = texture
                                grid[y, x]['height'] = height
                                grid[y, x]['depth'] = depth
                                grid[y, x]['value'] = value
                                grid[y, x]['3d'] = threed
                                grid[y, x]['range'] = range_val
                    self.update_canvas_changed(affected)
        self.update_edit_menu_states()
        self.set_dirty()
        map_data['dirty'] = True
    def deselect(self):
        self.selected_x = None
        self.selected_y = None
        if not self.lock_var.get():
            self.property_canvas.pack_forget()
        self.deselect_multi()
    def deselect_arc(self):
        self.arc_list.selection_clear(0, tk.END)
        self.current_arc_index = None
        self.clear_arc_fields()
        self.update_edit_menu_states()
    def handle_arc_list_click(self, event):
        # If click doesn't select an item, deselect
        self.root.after(100, self.check_arc_selection)
    def check_arc_selection(self):
        if not self.arc_list.curselection():
            self.deselect_arc()
    def insert_phrase(self, phrase):
        if self.arc_data_text:
            self.arc_data_text.insert(tk.INSERT, phrase + " ")
    def new_arc(self):
        self.clear_arc_fields()
        self.current_arc_index = None # New mode
        self.last_arc_state = self.save_arc_state()
    def save_arc(self):
        arc_data_raw = self.arc_data_text.get("1.0", tk.END).strip()
        arc_data = arc_data_raw # TODO: arc-data-filter is still needed
        estimated = ':'.join(v.get() for v in self.arc_estimated_parts)
        map_value = self.arc_map_var.get()
        map_type = self.arc_map_type_var.get()
        prefix = '$' if map_type == 'Import' else '#'
        map_str = prefix + map_value + '!'
        arc_dict = {
            'name': self.arc_name_var.get(),
            'estimated': estimated,
            'zone_type': self.arc_zone_type_var.get(),
            'start_msg': self.arc_start_msg_var.get(),
            'map': map_str,
            'arc_data': arc_data,
            'confirm_msg': self.arc_confirm_msg_var.get()
        }
        if self.current_arc_index is None or self.current_arc_index == -1:
            if self.current_arc_index == -1:
                # Update attached
                for a in self.maps[self.current_index]['attached_arcs']:
                    if a['name'] == arc_dict['name']:
                        a.update(arc_dict)
                        break
                self.current_arc_index = None
            else:
                self.arcs.append(arc_dict)
                self.arc_list.insert(tk.END, arc_dict['name'])
        else:
            self.arcs[self.current_arc_index] = arc_dict
            self.arc_list.delete(self.current_arc_index)
            self.arc_list.insert(self.current_arc_index, arc_dict['name'])
        self.set_dirty()
    def save_arc_as(self):
        if self.current_arc_index is None:
            messagebox.showerror("No Arc", "No arc selected")
            return
        arc = self.arcs[self.current_arc_index]
        filename = self.get_arc_filename(arc) + '.arcs'
        file = filedialog.asksaveasfilename(defaultextension=".arcs", filetypes=[("Arcs files", "*.arcs")], initialfile=filename)
        if file:
            path = file
            i = 1
            while os.path.exists(path):
                path = file[:-5] + f'_{str(i).zfill(2)}.arcs'
                i += 1
            arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
            with open(path, 'w') as f:
                f.write(arc_line)
    def get_arc_filename(self, arc):
        name_char = arc['name'][0].upper() if arc['name'] else 'A'
        est = arc['estimated']
        parts = est.split(':')
        if len(parts) == 3:
            est_char = 'F' if len(parts[0]) == 3 else 'S'
        elif len(parts) == 2:
            est_char = 'H' if len(parts[1]) == 3 else 'L'
        else:
            est_char = 'U'
        zone = arc['zone_type']
        zone_char = {'Safe': 'S', 'Crawl': 'C', 'Fight': 'G', 'Mix0': '0', 'Mix1': '1', 'Mix2': '2', 'Mix3': '3', 'Mixed': 'M'}.get(zone, 'U')
        map_str = arc['map'][1:-1]
        map_char = map_str[0].upper() if map_str else 'M'
        now = datetime.now()
        save_num = now.strftime('%m%d%Y%H%M%S%f')[:-3]
        return f"{name_char}{est_char}{zone_char}{map_char}_{save_num}"
    def load_arc(self):
        self.load_arc_file(add_to_list=True, auto_select=self.is_builder_default())
    def load_arc_to_map(self):
        self.load_arc_file(add_to_list=True, auto_select=self.is_builder_default())
    def load_arc_file(self, add_to_list=False, auto_select=False):
        file = filedialog.askopenfilename(initialdir=self.last_dir['arc_load'], filetypes=[("Arcs files", "*.arcs"), ("MapD files", "*.mapd")])
        if file:
            self.last_dir['arc_load'] = os.path.dirname(file)
            with open(file, 'r') as f:
                line = f.read().strip()
            parts = line.split('||')
            if len(parts) == 7:
                arc = {
                    'name': parts[0],
                    'estimated': parts[1],
                    'zone_type': parts[2],
                    'start_msg': parts[3],
                    'map': parts[4],
                    'arc_data': parts[5],
                    'confirm_msg': parts[6]
                }
                if add_to_list:
                    self.arcs.append(arc)
                    self.arc_list.insert(tk.END, arc['name'])
                    self.current_arc_index = len(self.arcs) - 1
                if auto_select or (not add_to_list):
                    self.load_arc_dict_to_fields(arc)
                    self.current_arc_index = None
            self.set_dirty()
    def is_builder_default(self):
        return (self.arc_name_var.get() == "Title the Arc" and
                self.arc_estimated_type_var.get() == "2-Finish (E2F)" and
                all(v.get() == '' for v in self.arc_estimated_parts) and
                self.arc_zone_type_var.get() == "Safe" and
                self.arc_start_msg_var.get() == "Start Message" and
                self.arc_map_var.get() == "" and
                self.arc_map_type_var.get() == "Import" and
                self.arc_data_text.get("1.0", tk.END).strip() == "" and
                self.arc_confirm_msg_var.get() == "Confirm Message")
    def load_arc_dict_to_fields(self, arc):
        self.arc_name_var.set(arc['name'])
        est = arc['estimated']
        parts = est.split(':')
        if len(parts) == 3:
            type_ = "2-Finish (E2F)" if len(parts[0]) == 3 else "2-Start (E2S)"
        elif len(parts) == 2:
            type_ = "Short-Hold-Time (SHT)" if len(parts[1]) == 3 else "Long-Hold-Time (LHT)"
        else:
            type_ = "2-Finish (E2F)"
        self.arc_estimated_type_var.set(type_)
        self.update_est_picker()
        for i, p in enumerate(parts):
            if i < len(self.arc_estimated_parts):
                self.arc_estimated_parts[i].set(p)
        self.arc_zone_type_var.set(arc['zone_type'])
        self.arc_start_msg_var.set(arc['start_msg'])
        map_str = arc['map']
        self.arc_map_type_var.set('Import' if map_str.startswith('$') else 'Generate')
        self.arc_map_var.set(map_str[1:-1])
        self.arc_data_text.delete("1.0", tk.END)
        self.arc_data_text.insert("1.0", arc['arc_data'])
        self.arc_confirm_msg_var.set(arc['confirm_msg'])
        self.last_arc_state = self.save_arc_state()
        self.apply_fg_to_widget(self.arc_data_text)
    def save_selected_arc(self):
        if self.current_arc_index is None:
            messagebox.showerror("No Arc", "No selected arc")
            return
        arc = self.arcs[self.current_arc_index]
        filename = self.get_arc_filename(arc) + '.arcs'
        file = filedialog.asksaveasfilename(defaultextension=".arcs", filetypes=[("Arcs files", "*.arcs")], initialfile=filename)
        if file:
            path = file
            i = 1
            while os.path.exists(path):
                path = file[:-5] + f'_{str(i).zfill(2)}.arcs'
                i += 1
            arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
            with open(path, 'w') as f:
                f.write(arc_line)
    def save_all_from_map(self):
        attached = self.maps[self.current_index]['attached_arcs']
        dir_ = 'arc'
        for arc in attached:
            filename = self.get_arc_filename(arc) + '.arcs'
            path = os.path.join(dir_, filename)
            i = 1
            while os.path.exists(path):
                path = os.path.join(dir_, filename[:-5] + f'_{str(i).zfill(2)}.arcs')
                i += 1
            arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
            with open(path, 'w') as f:
                f.write(arc_line)
    def save_all_from_dict(self):
        all_arcs = {a['name']: a for a in self.arcs}
        for m in self.maps:
            for a in m['attached_arcs']:
                if a['name'] not in all_arcs:
                    all_arcs[a['name'] ] = a
        dir_ = 'arc'
        for name, arc in all_arcs.items():
            filename = self.get_arc_filename(arc) + '.arcs'
            path = os.path.join(dir_, filename)
            i = 1
            while os.path.exists(path):
                path = os.path.join(dir_, filename[:-5] + f'_{str(i).zfill(2)}.arcs')
                i += 1
            arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
            with open(path, 'w') as f:
                f.write(arc_line)
    def hide_arc_builder(self):
        v_height = self.main_vertical_paned.winfo_height()
        self.main_vertical_paned.sash_place(0, 0, v_height - 50)
        self.arc_hidden = True
        self.update_arc_menu_states()
    def show_arc_builder(self):
        self.load_pane_positions()
        self.arc_hidden = False
        self.update_arc_menu_states()
    def delete_arc(self):
        if self.current_arc_index is not None:
            if messagebox.askyesno("Delete Arc", "Are you sure you want to delete this arc?"):
                arc = self.arcs[self.current_arc_index]
                self.deleted_arcs.append((self.current_arc_index, arc))
                del self.arcs[self.current_arc_index]
                self.arc_list.delete(self.current_arc_index)
                self.clear_arc_fields()
                self.current_arc_index = None
                self.update_edit_menu_states()
                self.set_dirty()
    def select_arc(self, event):
        selection = self.arc_list.curselection()
        if selection:
            self.current_arc_index = selection[0]
            arc = self.arcs[self.current_arc_index]
            self.load_arc_dict_to_fields(arc)
            self.last_arc_state = self.save_arc_state()
        self.update_edit_menu_states()
    def clear_arc_fields(self):
        self.arc_name_var.set("Title the Arc")
        self.arc_estimated_type_var.set("2-Finish (E2F)")
        self.update_est_picker()
        for v in self.arc_estimated_parts:
            v.set('')
        self.arc_zone_type_var.set("Safe")
        self.arc_start_msg_var.set("Start Message")
        self.arc_map_var.set("")
        self.arc_map_type_var.set("Import")
        self.arc_data_text.delete("1.0", tk.END)
        self.arc_confirm_msg_var.set("Confirm Message")
        self.last_arc_state = self.save_arc_state()
    def undo_arc(self):
        if self.arc_undo_stack:
            current = self.save_arc_state()
            self.arc_redo_stack.append(current)
            prev = self.arc_undo_stack.pop()
            if prev is not None:
                self.set_arc_state(prev)
                self.last_arc_state = prev
    def redo_arc(self):
        if self.arc_redo_stack:
            current = self.save_arc_state()
            self.arc_undo_stack.append(current)
            next_state = self.arc_redo_stack.pop()
            if next_state is not None:
                self.set_arc_state(next_state)
                self.last_arc_state = next_state
    def undo_delete_arc(self):
        if self.deleted_arcs:
            pos, arc = self.deleted_arcs.pop()
            if pos is not None:
                self.arcs.insert(pos, arc)
                self.arc_list.insert(pos, arc['name'])
            else:
                self.arcs.append(arc)
                self.arc_list.insert(tk.END, arc['name'])
            self.update_edit_menu_states()
            self.set_dirty()
    def undo_map_delete(self):
        if self.deleted_maps:
            pos, map_data, var_dict, canvas, zoom_slider, canvas_texts, undo_stack, redo_stack = self.deleted_maps.pop()
            self.maps.insert(pos, map_data)
            self.var_dicts.insert(pos, var_dict)
            self.canvases.insert(pos, canvas)
            self.zoom_sliders.insert(pos, zoom_slider)
            self.canvas_texts_list.insert(pos, canvas_texts)
            self.undo_stacks.insert(pos, undo_stack)
            self.redo_stacks.insert(pos, redo_stack)
            frame = tk.Frame(self.notebook)
            self.notebook.insert(pos, frame, text=map_data['name'])
            header_frame = tk.Frame(frame)
            header_frame.pack(fill=tk.X)
            close_btn = tk.Button(header_frame, text='X', command=lambda i=pos: self.close_tab(i))
            close_btn.pack(side=tk.RIGHT)
            tk.Label(header_frame, text="Openings:").pack(side=tk.LEFT)
            openings_entry = tk.Entry(header_frame, textvariable=var_dict['openings_var'], width=10)
            openings_entry.pack(side=tk.LEFT)
            def validate_openings(P):
                return len(P) <=7 and all(c in '01234' for c in P)
            vcmd_open = self.root.register(validate_openings)
            openings_entry.config(validate='key', validatecommand=(vcmd_open, '%P'))
            openings_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
            tk.Label(header_frame, text="Width:").pack(side=tk.LEFT)
            width_entry = tk.Entry(header_frame, textvariable=var_dict['width_var'], width=5)
            width_entry.pack(side=tk.LEFT)
            def validate_size(P):
                if P == '': return True
                try:
                    v = int(P)
                    return 0 <= v <= 1080
                except:
                    return False
            vcmd_size = self.root.register(validate_size)
            width_entry.config(validate='key', validatecommand=(vcmd_size, '%P'))
            width_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
            tk.Label(header_frame, text="Height:").pack(side=tk.LEFT)
            height_entry = tk.Entry(header_frame, textvariable=var_dict['height_var'], width=5)
            height_entry.pack(side=tk.LEFT)
            height_entry.config(validate='key', validatecommand=(vcmd_size, '%P'))
            height_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
            tk.Button(header_frame, text="Apply Size", command=lambda i=pos: self.apply_size(i)).pack(side=tk.LEFT)
            tk.Label(header_frame, text="Type:").pack(side=tk.LEFT)
            type_combo = ttk.Combobox(header_frame, textvariable=var_dict['type_var'], values=['Safe', 'Crawl', 'Fight', 'Mix0', 'Mix1', 'Mix2', 'Mix3', 'Mixed'], state='readonly', width=10)
            type_combo.pack(side=tk.LEFT)
            tk.Label(header_frame, text="Name:").pack(side=tk.LEFT)
            name_entry = tk.Entry(header_frame, textvariable=var_dict['name_var'], width=15)
            name_entry.pack(side=tk.LEFT)
            def validate_len_28(P): return len(P) <= 28 or P == ''
            vcmd_28 = self.root.register(validate_len_28)
            name_entry.config(validate='key', validatecommand=(vcmd_28, '%P'))
            name_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
            tk.Label(header_frame, text="Maker:").pack(side=tk.LEFT)
            maker_entry = tk.Entry(header_frame, textvariable=var_dict['maker_var'], width=15)
            maker_entry.pack(side=tk.LEFT)
            def validate_len_21(P): return len(P) <= 21 or P == ''
            vcmd_21 = self.root.register(validate_len_21)
            maker_entry.config(validate='key', validatecommand=(vcmd_21, '%P'))
            maker_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
            tk.Label(header_frame, text="System: " + map_data['system']).pack(side=tk.LEFT)
            canvas_frame = tk.Frame(frame)
            canvas_frame.pack(fill=tk.BOTH, expand=True)
            hbar = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=canvas.xview)
            hbar.pack(side=tk.BOTTOM, fill=tk.X)
            vbar = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=canvas.yview)
            vbar.pack(side=tk.RIGHT, fill=tk.Y)
            zoom_slider.pack(side=tk.RIGHT, fill=tk.Y)
            canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            canvas.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
            canvas.bind("<Button-1>", self.on_canvas_click)
            canvas.bind("<B1-Motion>", self.on_canvas_motion)
            canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
            canvas.bind("<Button-3>", self.handle_right_click)
            canvas.bind("<Control-Return>", self.handle_keyboard_right_click)
            canvas.bind("<Enter>", lambda e: canvas.focus_set())
            canvas.bind("<Motion>", self.on_canvas_motion_hover)
            self.bind_scrolls(canvas)
            self.redraw_canvas(pos)
            self.center_canvas(pos)
            self.apply_fg_to_widget(header_frame)
            self.apply_fg_to_widget(type_combo)
            self.apply_fg_to_widget(canvas_frame)
            self.apply_fg_to_widget(zoom_slider)
            self.update_edit_menu_states()
            self.set_dirty()
    def remove_all_edits(self):
        self.clear_arc_fields()
    def attach_to_map(self):
        if self.current_arc_index is not None:
            arc = self.arcs[self.current_arc_index]
            self.maps[self.current_index]['attached_arcs'].append(copy.deepcopy(arc))
            self.draw_attached_dots(self.current_index)
            self.set_dirty()
            self.maps[self.current_index]['dirty'] = True
        else:
            messagebox.showerror("No Arc", "No arc selected to attach.")
    def on_arc_change(self, event=None):
        current = self.save_arc_state()
        if current != self.last_arc_state:
            self.arc_undo_stack.append(self.last_arc_state)
            self.last_arc_state = current
            self.arc_redo_stack.clear()
        self.set_dirty()
    def on_arc_modified(self, event=None):
        if self.arc_data_text.edit_modified():
            self.on_arc_change()
            self.arc_data_text.edit_modified(False)
    def save_arc_state(self):
        return ArcState(
            self.arc_name_var.get(),
            self.arc_estimated_type_var.get(),
            [v.get() for v in self.arc_estimated_parts],
            self.arc_zone_type_var.get(),
            self.arc_start_msg_var.get(),
            self.arc_map_var.get(),
            self.arc_map_type_var.get(),
            self.arc_data_text.get("1.0", tk.END).strip(),
            self.arc_confirm_msg_var.get()
        )
    def set_arc_state(self, state):
        self.arc_name_var.set(state.name)
        self.arc_estimated_type_var.set(state.estimated_type)
        self.update_est_picker()
        for i, p in enumerate(state.estimated_parts):
            self.arc_estimated_parts[i].set(p)
        self.arc_zone_type_var.set(state.zone_type)
        self.arc_start_msg_var.set(state.start_msg)
        self.arc_map_var.set(state.map)
        self.arc_map_type_var.set(state.map_type)
        self.arc_data_text.delete("1.0", tk.END)
        self.arc_data_text.insert("1.0", state.arc_data)
        self.arc_confirm_msg_var.set(state.confirm_msg)
    def apply_size(self, index):
        var_dict = self.var_dicts[index]
        new_width = var_dict['width_var'].get()
        new_height = var_dict['height_var'].get()
        map_data = self.maps[index]
        if new_width != map_data['width'] or new_height != map_data['height']:
            self.push_undo(True)
            new_grid = np.zeros((new_height, new_width), dtype=self.dtype)
            new_grid['symbol'] = ' '
            new_grid['color'] = 'black'
            new_grid['texture'] = ''
            new_grid['name'] = ''
            new_grid['value'] = 0
            new_grid['depth'] = 1
            new_grid['height'] = 1
            new_grid['3d'] = 0
            new_grid['range'] = 0.0
            new_grid['sun'] = 'NA'
            min_h = min(map_data['height'], new_height)
            min_w = min(map_data['width'], new_width)
            new_grid[0:min_h, 0:min_w] = map_data['grid'][0:min_h, 0:min_w]
            map_data['grid'] = new_grid
            map_data['width'] = new_width
            map_data['height'] = new_height
            self.redraw_canvas(index)
            self.center_canvas(index)
            self.set_dirty()
            map_data['dirty'] = True
    def ask_save(self):
        if self.user_active > 0:
            return False
        if self.cheating_detected > 0:
            messagebox.showwarning("Cheating Detected", f"Cheating action noticed: {self.cheating_reason}")
            self.user_active = -9
            return False
        if messagebox.askyesno("Save Current", f"Do you want to save the current work before proceeding, {self.user_name or 'User'}?"):
            if messagebox.askyesno("Save Type", "Save as Map (yes) or Dictionary (no)?"):
                self.save_file_as('tmap')
            else:
                self.save_file_as('mapd')
            self.user_active = 1
            return True
        return False
    def save_file_as(self, file_type):
        if file_type == 'tmap':
            file = filedialog.asksaveasfilename(defaultextension=".tmap", filetypes=[("TMap files", "*.tmap")])
            if file:
                map_data = self.maps[self.current_index]
                var_dict = self.var_dicts[self.current_index]
                openings = var_dict['openings_var'].get().ljust(7, '0')
                map_type = var_dict['type_var'].get()
                name = var_dict['name_var'].get()
                maker = var_dict['maker_var'].get()
                system = map_data['system']
                header = f"{openings} {map_data['width']}x{map_data['height']}"
                sunrise_str = ''
                if map_data['sunrise'] and map_data['sunset']:
                    sunrise_str = f" sunrise xy({map_data['sunrise'][0]},{map_data['sunrise'][1]}); sunset xy({map_data['sunset'][0]},{map_data['sunset'][1]})"
                map_str = '\n'.join(''.join(cell['symbol'] for cell in row) for row in map_data['grid'])
                footer = f"{map_type}; {name}; {maker}; {system}"
                # Add properties array
                props = [
                    f'{cell["symbol"]}[\"{cell["color"]}\";\"{cell["name"]}\";\"{cell["texture"]}\";{cell["sun"] if cell["sun"] != "NA" else ""}({x},{cell["3d"]},{y},{cell["depth"]},{cell["height"]},{cell["range"]}){cell["value"]}]'
                    for y in range(map_data['height'])
                    for x in range(map_data['width'])
                    for cell in [map_data['grid'][y, x]]
                    if not (cell['symbol'] == ' ' and cell['color'] == 'black' and cell['texture'] == '' and cell['name'] == '' and cell['value'] == 0 and cell['depth'] == 1 and cell['height'] == 1 and cell['3d'] == 0 and cell['range'] == 0.0 and cell['sun'] == 'NA')
                ]
                props_str = ' ' + ' '.join(props) if props else ''
                # Add arcs
                arcs_str = ''
                if map_data['attached_arcs']:
                    arc_lines = ['||'.join([a[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']]) for a in map_data['attached_arcs']]
                    arcs_str = ';arcs::' + ';'.join(arc_lines)
                content = header + sunrise_str + '\n' + map_str + '\n' + footer + props_str + arcs_str
                with open(file, 'w') as f:
                    f.write(content)
                self.dirty = False
                map_data['dirty'] = False
                self.user_active = 1
        elif file_type == 'mapd':
            file = filedialog.asksaveasfilename(defaultextension=".mapd", filetypes=[("MapD files", "*.mapd")])
            if file:
                dir_path = os.path.dirname(file)
                map_names = []
                for i, map_data in enumerate(self.maps):
                    var_dict = self.var_dicts[i]
                    base_name = map_data['name']
                    ext = '.tmap'
                    tmap_file = os.path.join(dir_path, base_name + ext)
                    j = 1
                    while os.path.exists(tmap_file):
                        tmap_file = os.path.join(dir_path, f"{base_name}_{j:03d}{ext}")
                        j += 1
                    openings = var_dict['openings_var'].get().ljust(7, '0')
                    map_type = var_dict['type_var'].get()
                    name = var_dict['name_var'].get()
                    maker = var_dict['maker_var'].get()
                    system = map_data['system']
                    header = f"{openings} {map_data['width']}x{map_data['height']}"
                    sunrise_str = ''
                    if map_data['sunrise'] and map_data['sunset']:
                        sunrise_str = f" sunrise xy({map_data['sunrise'][0]},{map_data['sunrise'][1]}); sunset xy({map_data['sunset'][0]},{map_data['sunset'][1]})"
                    map_str = '\n'.join(''.join(cell['symbol'] for cell in row) for row in map_data['grid'])
                    footer = f"{map_type}; {name}; {maker}; {system}"
                    # Add properties array
                    props = [
                        f'{cell["symbol"]}[\"{cell["color"]}\";\"{cell["name"]}\";\"{cell["texture"]}\";{cell["sun"] if cell["sun"] != "NA" else ""}({x},{cell["3d"]},{y},{cell["depth"]},{cell["height"]},{cell["range"]}){cell["value"]}]'
                        for y in range(map_data['height'])
                        for x in range(map_data['width'])
                        for cell in [map_data['grid'][y, x]]
                        if not (cell['symbol'] == ' ' and cell['color'] == 'black' and cell['texture'] == '' and cell['name'] == '' and cell['value'] == 0 and cell['depth'] == 1 and cell['height'] == 1 and cell['3d'] == 0 and cell['range'] == 0.0 and cell['sun'] == 'NA')
                    ]
                    props_str = ' ' + ' '.join(props) if props else ''
                    # Add arcs
                    arcs_str = ''
                    if map_data['attached_arcs']:
                        arc_lines = ['||'.join([a[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']]) for a in map_data['attached_arcs']]
                        arcs_str = ';arcs::' + ';'.join(arc_lines)
                    content = header + sunrise_str + '\n' + map_str + '\n' + footer + props_str + arcs_str
                    with open(tmap_file, 'w') as f:
                        f.write(content)
                    saved_name = os.path.basename(tmap_file)[:-5]
                    map_names.append(saved_name)
                import_header = 'import {' + ', '.join(f'"{n}"' for n in map_names) + '}\n'
                arc_lines = []
                for arc in self.arcs:
                    arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
                    arc_lines.append(arc_line)
                content = import_header + '\n'.join(arc_lines)
                with open(file, 'w') as f:
                    f.write(content)
                self.dirty = False
                for m in self.maps:
                    m['dirty'] = False
                self.user_active = 1
    def new_with_save_check(self):
        self.ask_save()
        self.new_file()
    def new_file(self):
        # Clear all tabs and maps
        for tab in self.notebook.tabs():
            self.notebook.forget(tab)
        self.maps = []
        self.var_dicts = []
        self.canvases = []
        self.zoom_sliders = []
        self.canvas_texts_list = []
        self.undo_stacks = []
        self.redo_stacks = []
        self.arcs = []
        self.arc_list.delete(0, tk.END)
        self.clear_arc_fields()
        self.add_map_tab("Unnamed")
        self.update_edit_menu_states()
        self.dirty = False
        self.user_active = 1
    def load_with_save_check(self):
        self.ask_save()
        self.load_file()
    def load_file(self):
        file = filedialog.askopenfilename(initialdir=self.last_dir['file_load'], filetypes=[("All map files", "*.tmap *.mapd *.txt"), ("TMap files", "*.tmap"), ("MapD files", "*.mapd"), ("Text files", "*.txt")])
        if file:
            self.last_dir['file_load'] = os.path.dirname(file)
            if file.endswith('.tmap') or file.endswith('.txt'):
                self.load_tmap(file)
                self.last_dir['map_load'] = os.path.dirname(file)
            elif file.endswith('.mapd'):
                self.load_mapd(file)
                self.last_dir['dict_load'] = os.path.dirname(file)
            self.dirty = False
            self.user_active = 1
    def load_tmap(self, file):
        with open(file, 'r') as f:
            lines = [line.strip() for line in f.readlines() if line.strip()]
        if lines:
            self.add_map_tab(os.path.basename(file))
            map_index = len(self.maps) - 1
            map_data = self.maps[map_index]
            var_dict = self.var_dicts[map_index]
            header = lines[0]
            sunrise_match = re.search(r'sunrise xy\((\d+),(\d+)\); sunset xy\((\d+),(\d+)\)', header)
            if sunrise_match:
                map_data['sunrise'] = (int(sunrise_match.group(1)), int(sunrise_match.group(2)))
                map_data['sunset'] = (int(sunrise_match.group(3)), int(sunrise_match.group(4)))
                header = header[:sunrise_match.start()].strip()
            parts = header.split()
            openings = parts[0]
            if len(openings) < 7: openings = openings.ljust(7, '0')
            size = parts[1]
            width, height = map(int, size.split('x'))
            map_data['width'] = width
            map_data['height'] = height
            var_dict['width_var'].set(width)
            var_dict['height_var'].set(height)
            var_dict['openings_var'].set(openings)
            map_lines = lines[1:-1]
            if map_lines:
                grid = np.zeros((height, width), dtype=self.dtype)
                grid['symbol'] = ' '
                for y, line in enumerate(map_lines):
                    line = line.rstrip()
                    if len(line) < width:
                        line += ' ' * (width - len(line))
                    elif len(line) > width:
                        line = line[:width]
                    for x, char in enumerate(line):
                        grid[y, x]['symbol'] = char
                map_data['grid'] = grid
            footer_line = lines[-1]
            footer_parts = footer_line.split(';')
            map_type = footer_parts[0].strip() if len(footer_parts) > 0 else 'Safe'
            map_data['type'] = map_type.capitalize()
            var_dict['type_var'].set(map_data['type'])
            name = footer_parts[1].strip() if len(footer_parts) > 1 else 'Loaded Map'
            map_data['name'] = name
            var_dict['name_var'].set(name)
            self.notebook.tab(map_index, text=name)
            maker = footer_parts[2].strip() if len(footer_parts) > 2 else 'User'
            map_data['maker'] = maker
            var_dict['maker_var'].set(maker)
            system = footer_parts[3].strip() if len(footer_parts) > 3 else 'PB [no-jam] PyEditor'
            # Parse properties if present
            props_str = ''
            arcs_start = 4
            if len(footer_parts) > 4:
                rest = ';'.join(footer_parts[4:])
                if 'arcs::' in rest:
                    props_end = rest.find(';arcs::')
                    if props_end != -1:
                        props_str = rest[:props_end].strip()
                        arcs_str = rest[props_end + 7:].strip()
                    else:
                        props_str = rest.strip()
                else:
                    props_str = rest.strip()
                props = re.findall(r'(.)\["([^"]*)";"([^"]*)";"([^"]*)";?([A-Z]{2})?\((\d+),(\d+),(\d+),(\d+),(\d+),?(\d+\.?\d*)?\)(\d+)\]', props_str)
                for sym, color, name_, texture, sun, x, threed, y, d, h, r, val in props:
                    x, y = int(x), int(y)
                    r = float(r) if r else 0.0
                    sun = sun if sun else 'NA'
                    if 0 <= x < width and 0 <= y < height:
                        cell = grid[y, x]
                        cell['symbol'] = sym
                        cell['color'] = color
                        cell['name'] = name_
                        cell['texture'] = texture
                        cell['3d'] = int(threed)
                        cell['depth'] = int(d)
                        cell['height'] = int(h)
                        cell['value'] = int(val)
                        cell['range'] = r
                        cell['sun'] = sun
                if 'arcs_str' in locals():
                    arc_lines = arcs_str.split(';')
                    for arc_line in arc_lines:
                        if arc_line:
                            parts = arc_line.split('||')
                            if len(parts) == 7:
                                arc = {
                                    'name': parts[0],
                                    'estimated': parts[1],
                                    'zone_type': parts[2],
                                    'start_msg': parts[3],
                                    'map': parts[4],
                                    'arc_data': parts[5],
                                    'confirm_msg': parts[6]
                                }
                                map_data['attached_arcs'].append(arc)
                if map_data['sunrise']:
                    sx, sy = map_data['sunrise']
                    grid[sy, sx]['sun'] = 'SR'
                if map_data['sunset']:
                    sx, sy = map_data['sunset']
                    grid[sy, sx]['sun'] = 'SS'
            self.redraw_canvas(map_index)
            self.draw_attached_dots(map_index)
            self.center_canvas(map_index)
            self.notebook.select(map_index)
    def load_mapd(self, file):
        with open(file, 'r') as f:
            lines = f.readlines()
        if lines:
            import_line = lines[0].strip()
            if import_line.startswith("import {"):
                names = re.findall(r'"(.*?)"', import_line)
                dir_path = os.path.dirname(file)
                for n in names:
                    tmap_file = os.path.join(dir_path, n + '.tmap')
                    if os.path.exists(tmap_file):
                        self.load_tmap(tmap_file)
            arc_lines = lines[1:]
            self.arcs = []
            for line in arc_lines:
                if line.strip():
                    parts = line.strip().split('||')
                    if len(parts) == 7:
                        arc = {
                            'name': parts[0],
                            'estimated': parts[1],
                            'zone_type': parts[2],
                            'start_msg': parts[3],
                            'map': parts[4],
                            'arc_data': parts[5],
                            'confirm_msg': parts[6]
                        }
                        self.arcs.append(arc)
            self.arc_list.delete(0, tk.END)
            for arc in self.arcs:
                self.arc_list.insert(tk.END, arc['name'])
            self.apply_fg_to_widget(self.arc_list)
    def save_file(self):
        file_type = messagebox.askquestion("Save Type", "Save as .tmap (single map) or .mapd (dictionary)?", type="yesno")
        if file_type == "yes": # .tmap
            self.save_file_as('tmap')
        else: # .mapd
            self.save_file_as('mapd')
    def save_and_exit(self):
        if self.user_active > 0 and not self.dirty:
            self.on_close()
            return
        messagebox.showinfo("Saving", "Saving as auto mapd...")
        file = f"auto_save_{self.user_uuid or ''}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.mapd"
        dir_path = os.getcwd()
        map_names = []
        for i, map_data in enumerate(self.maps):
            var_dict = self.var_dicts[i]
            base_name = map_data['name']
            ext = '.tmap'
            tmap_file = os.path.join(dir_path, base_name + ext)
            j = 1
            while os.path.exists(tmap_file):
                tmap_file = os.path.join(dir_path, f"{base_name}_{j:03d}{ext}")
                j += 1
            openings = var_dict['openings_var'].get().ljust(7, '0')
            map_type = var_dict['type_var'].get()
            name = var_dict['name_var'].get()
            maker = var_dict['maker_var'].get()
            system = map_data['system']
            header = f"{openings} {map_data['width']}x{map_data['height']}"
            sunrise_str = ''
            if map_data['sunrise'] and map_data['sunset']:
                sunrise_str = f" sunrise xy({map_data['sunrise'][0]},{map_data['sunrise'][1]}); sunset xy({map_data['sunset'][0]},{map_data['sunset'][1]})"
            map_str = '\n'.join(''.join(cell['symbol'] for cell in row) for row in map_data['grid'])
            footer = f"{map_type}; {name}; {maker}; {system}"
            # Add properties array
            props = [
                f'{cell["symbol"]}[\"{cell["color"]}\";\"{cell["name"]}\";\"{cell["texture"]}\";{cell["sun"] if cell["sun"] != "NA" else ""}({x},{cell["3d"]},{y},{cell["depth"]},{cell["height"]},{cell["range"]}){cell["value"]}]'
                for y in range(map_data['height'])
                for x in range(map_data['width'])
                for cell in [map_data['grid'][y, x]]
                if not (cell['symbol'] == ' ' and cell['color'] == 'black' and cell['texture'] == '' and cell['name'] == '' and cell['value'] == 0 and cell['depth'] == 1 and cell['height'] == 1 and cell['3d'] == 0 and cell['range'] == 0.0 and cell['sun'] == 'NA')
            ]
            props_str = ' ' + ' '.join(props) if props else ''
            # Add arcs
            arcs_str = ''
            if map_data['attached_arcs']:
                arc_lines = ['||'.join([a[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']]) for a in map_data['attached_arcs']]
                arcs_str = ';arcs::' + ';'.join(arc_lines)
            content = header + sunrise_str + '\n' + map_str + '\n' + footer + props_str + arcs_str
            with open(tmap_file, 'w') as f:
                f.write(content)
            saved_name = os.path.basename(tmap_file)[:-5]
            map_names.append(saved_name)
        import_header = 'import {' + ', '.join(f'"{n}"' for n in map_names) + '}\n'
        arc_lines = []
        for arc in self.arcs:
            arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
            arc_lines.append(arc_line)
        content = import_header + '\n'.join(arc_lines)
        with open(file, 'w') as f:
            f.write(content)
        closing = tk.Toplevel(self.root)
        closing.title("Closing...")
        tk.Label(closing, text="Closing...").pack(padx=20, pady=20)
        self.root.update()
        self.unlock_cursor()
        if self.tooltip:
            self.hide_tooltip(None)
        self.root.unbind("<Motion>")
        self.root.unbind("<Button>")
        self.root.unbind("<MouseWheel>")
        self.root.unbind_all("<Return>")
        self.root.unbind_all("<Shift-Return>")
        self.data_check()
        self.help_check()
        closing.destroy()
        self.on_close()
    def exit_without_save(self):
        self.root.destroy()
    def redraw_canvas(self, index):
        canvas = self.canvases[index]
        map_data = self.maps[index]
        w = map_data['width']
        h = map_data['height']
        canvas.delete("all")
        for i in range(w + 1):
            canvas.create_line(i * self.cell_size, 0, i * self.cell_size, h * self.cell_size + 40, fill='gray')
        for j in range(h + 1):
            canvas.create_line(0, j * self.cell_size, w * self.cell_size, j * self.cell_size, fill='gray')
        canvas_texts = [[None for _ in range(w)] for _ in range(h)]
        for y in range(h):
            for x in range(w):
                cell = map_data['grid'][y, x]
                rel = cell['height'] - 1
                if rel > 0:
                    stip = 'gray50' if rel > 5 else 'gray25' if rel > 2 else 'gray12'
                    canvas.create_rectangle(x * self.cell_size, y * self.cell_size, (x + 1) * self.cell_size, (y + 1) * self.cell_size, fill='white', stipple=stip, outline='')
                elif rel < 0:
                    stip = 'gray50' if -rel > 5 else 'gray25' if -rel > 2 else 'gray12'
                    canvas.create_rectangle(x * self.cell_size, y * self.cell_size, (x + 1) * self.cell_size, (y + 1) * self.cell_size, fill='black', stipple=stip, outline='')
                text_id = canvas.create_text((x + 0.5) * self.cell_size, (y + 0.5) * self.cell_size, text=cell['symbol'], font=("Courier", 12), fill=cell['color'])
                canvas_texts[y][x] = text_id
        self.canvas_texts_list[index] = canvas_texts
        if map_data['sunrise']:
            rx, ry = map_data['sunrise']
            map_data['sunrise_rect'] = canvas.create_rectangle(rx * self.cell_size, ry * self.cell_size, (rx + 1) * self.cell_size, (ry + 1) * self.cell_size, outline='orange', width=2)
        if map_data['sunset']:
            sx, sy = map_data['sunset']
            map_data['sunset_rect'] = canvas.create_rectangle(sx * self.cell_size, sy * self.cell_size, (sx + 1) * self.cell_size, (sy + 1) * self.cell_size, outline='red', width=2)
        self.draw_attached_dots(index)
        # Re-draw selection if exists
        if self.selected_region and self.current_index == index:
            minx, miny, maxx, maxy = self.selected_region
            self.selected_rects = []
            for yy in range(miny, maxy):
                for xx in range(minx, maxx):
                    rect_id = canvas.create_rectangle(xx * self.cell_size, yy * self.cell_size, (xx + 1) * self.cell_size, (yy + 1) * self.cell_size, outline=self.multi_selected_color, width=3, stipple='gray25')
                    self.selected_rects.append(rect_id)
    def update_canvas_changed(self, positions):
        canvas = self.canvases[self.current_index]
        texts = self.canvas_texts_list[self.current_index]
        grid = self.maps[self.current_index]['grid']
        for y, x in positions:
            cell = grid[y, x]
            canvas.itemconfig(texts[y][x], text=cell['symbol'], fill=cell['color'])
    def center_canvas(self, index):
        self.root.update_idletasks()
        canvas = self.canvases[index]
        view_w = canvas.winfo_width()
        view_h = canvas.winfo_height()
        if view_w > 1 and view_h > 1:
            map_data = self.maps[index]
            total_w = map_data['width'] * self.cell_size + 2 * self.padding
            total_h = map_data['height'] * self.cell_size + 40 + 2 * self.padding
            x_frac = max(0, (total_w - view_w) / 2 / total_w)
            y_frac = max(0, (total_h - view_h) / 2 / total_h)
            canvas.xview_moveto(x_frac)
            canvas.yview_moveto(y_frac)
    def push_undo(self, is_full=False, affected=None):
        index = self.current_index
        grid = self.maps[index]['grid']
        if is_full:
            self.undo_stacks[index].append(('full', np.copy(grid)))
        else:
            delta = {(y, x): grid[y, x].copy() for y, x in affected}
            self.undo_stacks[index].append(('delta', delta))
        if len(self.undo_stacks[index]) > 69:
            self.undo_stacks[index].pop(0)
        self.redo_stacks[index].clear()
    def undo(self):
        index = self.current_index
        if self.undo_stacks[index]:
            item = self.undo_stacks[index].pop()
            grid = self.maps[index]['grid']
            if item[0] == 'full':
                current = ('full', np.copy(grid))
                self.redo_stacks[index].append(current)
                self.maps[index]['grid'] = item[1]
                self.redraw_canvas(index)
            else:
                delta = item[1]
                current_delta = {(y, x): grid[y, x].copy() for y, x in delta}
                self.redo_stacks[index].append(('delta', current_delta))
                for (y, x), old in delta.items():
                    grid[y, x] = old
                self.update_canvas_changed(delta.keys())
            self.update_edit_menu_states()
    def redo(self):
        index = self.current_index
        if self.redo_stacks[index]:
            item = self.redo_stacks[index].pop()
            grid = self.maps[index]['grid']
            if item[0] == 'full':
                current = ('full', np.copy(grid))
                self.undo_stacks[index].append(current)
                self.maps[index]['grid'] = item[1]
                self.redraw_canvas(index)
            else:
                delta = item[1]
                current_delta = {(y, x): grid[y, x].copy() for y, x in delta}
                self.undo_stacks[index].append(('delta', current_delta))
                for (y, x), new in delta.items():
                    grid[y, x] = new
                self.update_canvas_changed(delta.keys())
            self.update_edit_menu_states()
    def cancel_action(self):
        if self.ongoing_action:
            self.ongoing_action = None
        self.deselect()
    def select_tool(self):
        self.current_symbol.set('--')
        self.select_mode = True
    def hide_maps(self):
        self.main_vertical_paned.paneconfig(self.upper_frame, minsize=0)
        self.main_vertical_paned.sash_place(0, 0, 30) # Just below menu, assuming menu height ~30
        self.maps_hidden = True
        self.update_map_menu_states()
    def show_maps(self):
        self.main_vertical_paned.paneconfig(self.upper_frame, minsize=150)
        self.load_pane_positions()
        self.maps_hidden = False
        self.update_map_menu_states()
    def hide_toolbar(self):
        symbol_width = self.cell_size # Approximate width for symbols only
        self.upper_horizontal_paned.paneconfig(self.left_frame, minsize=symbol_width)
        self.upper_horizontal_paned.sash_place(0, symbol_width, 0)
        self.toolbar_hidden = True
        self.update_toolbar_menu_states()
    def show_toolbar(self):
        self.upper_horizontal_paned.paneconfig(self.left_frame, minsize=150)
        self.load_pane_positions()
        self.toolbar_hidden = False
        self.update_toolbar_menu_states()
    def map_picker(self):
        file = filedialog.askopenfilename(initialdir=self.last_dir['map_load'], filetypes=[("TMap files", "*.tmap"), ("MapD files", "*.mapd"), ("Text files", "*.txt")])
        if file:
            self.last_dir['map_load'] = os.path.dirname(file)
            if file.endswith('.tmap') or file.endswith('.txt'):
                self.load_tmap(file)
            elif file.endswith('.mapd'):
                self.load_mapd(file)
    def preview_map(self):
        preview_win = tk.Toplevel(self.root)
        preview_win.title("Map Preview")
        map_data = self.maps[self.current_index]
        canvas = tk.Canvas(preview_win, width=800, height=600, scrollregion=(-self.padding, -self.padding, map_data['width'] * self.cell_size + self.padding, map_data['height'] * self.cell_size + 40 + self.padding))
        hbar = tk.Scrollbar(preview_win, orient=tk.HORIZONTAL, command=canvas.xview)
        hbar.pack(side=tk.BOTTOM, fill=tk.X)
        vbar = tk.Scrollbar(preview_win, orient=tk.VERTICAL, command=canvas.yview)
        vbar.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        canvas.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
        # Draw grid and symbols
        w = map_data['width']
        h = map_data['height']
        for i in range(w + 1):
            canvas.create_line(i * self.cell_size, 0, i * self.cell_size, h * self.cell_size + 40, fill='gray')
        for j in range(h + 1):
            canvas.create_line(0, j * self.cell_size, w * self.cell_size, j * self.cell_size, fill='gray')
        for y in range(h):
            for x in range(w):
                cell = map_data['grid'][y, x]
                canvas.create_text((x + 0.5) * self.cell_size, (y + 0.5) * self.cell_size, text=cell['symbol'], font=("Courier", 12), fill=cell['color'])
        # Bind mouse motion for scroll
        def on_mouse_move(event):
            x_frac = event.x / preview_win.winfo_width()
            y_frac = event.y / preview_win.winfo_height()
            canvas.xview_moveto(x_frac - 0.5)
            canvas.yview_moveto(y_frac - 0.5)
        preview_win.bind("<Motion>", on_mouse_move)
        # Bind keys for scroll
        def scroll_up(event):
            canvas.yview_scroll(-1, "units")
        def scroll_down(event):
            canvas.yview_scroll(1, "units")
        def scroll_left(event):
            canvas.xview_scroll(-1, "units")
        def scroll_right(event):
            canvas.xview_scroll(1, "units")
        preview_win.bind("w", scroll_up)
        preview_win.bind("<Up>", scroll_up)
        preview_win.bind("s", scroll_down)
        preview_win.bind("<Down>", scroll_down)
        preview_win.bind("a", scroll_left)
        preview_win.bind("<Left>", scroll_left)
        preview_win.bind("d", scroll_right)
        preview_win.bind("<Right>", scroll_right)
        self.apply_fg_to_widget(preview_win)
    def preview_dictionary(self):
        messagebox.showinfo("Preview Dictionary", "TODO: implement preview for dictionary.")
    def main_menu(self):
        messagebox.showinfo("Main Menu", "Returning to main menu (placeholder).")
    def handle_scroll(self, event):
        w = self.root.focus_get()
        delta = event.delta if hasattr(event, 'delta') and event.delta else (120 if getattr(event, 'num', 0) == 4 else -120)
        if hasattr(w, 'yview_scroll'):
            if delta > 0:
                w.yview_scroll(-1, "units")
            else:
                w.yview_scroll(1, "units")
    def handle_shift_scroll(self, event):
        w = self.root.focus_get()
        delta = event.delta if hasattr(event, 'delta') and event.delta else (120 if getattr(event, 'num', 0) == 4 else -120)
        if hasattr(w, 'xview_scroll'):
            if delta > 0:
                w.xview_scroll(-1, "units")
            else:
                w.xview_scroll(1, "units")
    def handle_page_up(self, event):
        w = self.root.focus_get()
        if hasattr(w, 'yview_scroll'):
            w.yview_scroll(-1, "pages")
    def handle_page_down(self, event):
        w = self.root.focus_get()
        if hasattr(w, 'yview_scroll'):
            w.yview_scroll(1, "pages")
    def handle_tab(self, event):
        widget = self.root.focus_get()
        if isinstance(widget, tk.Listbox):
            current = widget.curselection()
            if current:
                next_index = (current[0] + 1) % widget.size()
            else:
                next_index = 0
            widget.selection_clear(0, tk.END)
            widget.selection_set(next_index)
            widget.activate(next_index)
            widget.see(next_index)
    def handle_shift_tab(self, event):
        self.current_section_index = (self.current_section_index + 1) % len(self.focusable_sections)
        self.focusable_sections[self.current_section_index].focus_set()
    def select_all(self, event):
        event.widget.select_range(0, tk.END)
        event.widget.icursor(tk.END)
        return "break"
    def show_help(self, filename):
        help_dir = 'help'
        filename = os.path.join(help_dir, filename)
        if not os.path.exists(filename):
            with open(filename, 'w') as f:
                f.write("")
        with open(filename, 'r') as f:
            text = f.read()
        win = tk.Toplevel(self.root)
        win.title(os.path.basename(filename))
        text_widget = tk.Text(win, wrap=tk.WORD, fg=self.fg)
        text_widget.insert(tk.END, text)
        text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vscroll = tk.Scrollbar(win, orient=tk.VERTICAL, command=text_widget.yview)
        vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        hscroll = tk.Scrollbar(win, orient=tk.HORIZONTAL, command=text_widget.xview)
        hscroll.pack(side=tk.BOTTOM, fill=tk.X)
        text_widget.config(yscrollcommand=vscroll.set, xscrollcommand=hscroll.set)
        self.bind_scrolls(text_widget)
        self.apply_fg_to_widget(win)
    def remove_arc_from_map(self):
        attached = self.maps[self.current_index]['attached_arcs']
        if not attached:
            messagebox.showinfo("No Arcs", "No arcs attached to this map.")
            return
        win = tk.Toplevel(self.root)
        win.title("Attached Arcs")
        listbox = tk.Listbox(win)
        for arc in attached:
            listbox.insert(tk.END, arc['name'])
        listbox.pack(fill=tk.BOTH, expand=True)
        button_frame = tk.Frame(win)
        button_frame.pack(fill=tk.X)
        def on_double_click(e):
            sel = listbox.curselection()
            if sel:
                del attached[sel[0]]
                self.draw_attached_dots(self.current_index)
                self.set_dirty()
                self.maps[self.current_index]['dirty'] = True
                win.destroy()
        listbox.bind("<Double-Button-1>", on_double_click)
        def on_select(e):
            sel = listbox.curselection()
            if sel:
                arc = attached[sel[0]]
                for child in button_frame.winfo_children():
                    child.destroy()
                edit_btn = tk.Button(button_frame, text="Edit", command=lambda: self.edit_attached_arc(sel[0], win))
                edit_btn.pack(side=tk.LEFT)
                detach_btn = tk.Button(button_frame, text="Detach", command=lambda: self.detach_arc(sel[0], win))
                detach_btn.pack(side=tk.LEFT)
                in_arcs = any(a['name'] == arc['name'] for a in self.arcs)
                if in_arcs:
                    select_btn = tk.Button(button_frame, text="Select in Arcs", command=lambda: self.select_in_arcs(arc['name'], win))
                    select_btn.pack(side=tk.LEFT)
                else:
                    add_btn = tk.Button(button_frame, text="Add to Arcs", command=lambda: self.add_to_arcs(arc, win))
                    add_btn.pack(side=tk.LEFT)
        listbox.bind("<<ListboxSelect>>", on_select)
        self.apply_fg_to_widget(win)
    def edit_attached_arc(self, idx, win):
        arc = self.maps[self.current_index]['attached_arcs'][idx]
        self.load_arc_dict_to_fields(arc)
        self.current_arc_index = -1 # Special for attached edit
        win.destroy()
    def detach_arc(self, idx, win):
        if messagebox.askyesno("Detach Arc", "Are you sure you want to detach this arc?"):
            arc = self.maps[self.current_index]['attached_arcs'].pop(idx)
            self.draw_attached_dots(self.current_index)
            in_arcs = any(a['name'] == arc['name'] for a in self.arcs)
            if not in_arcs:
                self.deleted_arcs.append((None, copy.deepcopy(arc)))
            self.set_dirty()
            self.maps[self.current_index]['dirty'] = True
            win.destroy()
    def select_in_arcs(self, name, win):
        for j, a in enumerate(self.arcs):
            if a['name'] == name:
                self.arc_list.selection_clear(0, tk.END)
                self.arc_list.selection_set(j)
                self.select_arc(None)
                break
        win.destroy()
    def add_to_arcs(self, arc, win):
        self.arcs.append(copy.deepcopy(arc))
        self.arc_list.insert(tk.END, arc['name'])
        self.select_in_arcs(arc['name'], win)
        self.set_dirty()
    def set_sunset_direction(self):
        messagebox.showinfo("Set Direction", f"After clicking 'OK', click anywhere on the map grid to pick a sunset location, then click anywhere on the map grid to pick a sunrise location, {self.user_name or 'User'}.")
        self.sunset_click = True
        self.canvases[self.current_index].bind("<Button-1>", self.on_sunset_click)
    def on_sunset_click(self, event):
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        map_data = self.maps[self.current_index]
        if 0 <= x < map_data['width'] and 0 <= y < map_data['height']:
            if self.sunset_click:
                if map_data['sunset']:
                    ox, oy = map_data['sunset']
                    map_data['grid'][oy, ox]['sun'] = 'NA'
                map_data['sunset'] = (x, y)
                map_data['grid'][y, x]['sun'] = 'SS'
                self.sunset_click = False
                self.sunrise_click = True
            elif self.sunrise_click:
                if map_data['sunrise']:
                    ox, oy = map_data['sunrise']
                    map_data['grid'][oy, ox]['sun'] = 'NA'
                map_data['sunrise'] = (x, y)
                map_data['grid'][y, x]['sun'] = 'SR'
                self.sunrise_click = False
                self.canvases[self.current_index].bind("<Button-1>", self.on_canvas_click)
            self.redraw_canvas(self.current_index)
            map_data['dirty'] = True
    def close_tab(self, index):
        map_data = self.maps[index]
        if map_data['dirty']:
            if messagebox.askyesno(f"Close {map_data['name']}", f"Save changes before closing, {self.user_name or 'User'}?"):
                self.save_single_map(index)
        self.deleted_maps.append((index, copy.deepcopy(map_data), copy.deepcopy(self.var_dicts[index]), self.canvases[index], self.zoom_sliders[index], copy.deepcopy(self.canvas_texts_list[index]), copy.deepcopy(self.undo_stacks[index]), copy.deepcopy(self.redo_stacks[index])))
        self.notebook.forget(index)
        del self.maps[index]
        del self.var_dicts[index]
        del self.canvases[index]
        del self.zoom_sliders[index]
        del self.canvas_texts_list[index]
        del self.undo_stacks[index]
        del self.redo_stacks[index]
        if self.current_index >= len(self.maps):
            self.current_index -= 1
        if self.current_index >= 0:
            self.notebook.select(self.current_index)
        self.update_edit_menu_states()
    def save_single_map(self, index):
        map_data = self.maps[index]
        var_dict = self.var_dicts[index]
        base_name = map_data['name']
        file = f"auto_close_{base_name}_{self.user_uuid or ''}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.tmap"
        openings = var_dict['openings_var'].get().ljust(7, '0')
        map_type = var_dict['type_var'].get()
        name = var_dict['name_var'].get()
        maker = var_dict['maker_var'].get()
        system = map_data['system']
        header = f"{openings} {map_data['width']}x{map_data['height']}"
        sunrise_str = ''
        if map_data['sunrise'] and map_data['sunset']:
            sunrise_str = f" sunrise xy({map_data['sunrise'][0]},{map_data['sunrise'][1]}); sunset xy({map_data['sunset'][0]},{map_data['sunset'][1]})"
        map_str = '\n'.join(''.join(cell['symbol'] for cell in row) for row in map_data['grid'])
        footer = f"{map_type}; {name}; {maker}; {system}"
        props = [
            f'{cell["symbol"]}[\"{cell["color"]}\";\"{cell["name"]}\";\"{cell["texture"]}\";{cell["sun"] if cell["sun"] != "NA" else ""}({x},{cell["3d"]},{y},{cell["depth"]},{cell["height"]},{cell["range"]}){cell["value"]}]'
            for y in range(map_data['height'])
            for x in range(map_data['width'])
            for cell in [map_data['grid'][y, x]]
            if not (cell['symbol'] == ' ' and cell['color'] == 'black' and cell['texture'] == '' and cell['name'] == '' and cell['value'] == 0 and cell['depth'] == 1 and cell['height'] == 1 and cell['3d'] == 0 and cell['range'] == 0.0 and cell['sun'] == 'NA')
        ]
        props_str = ' ' + ' '.join(props) if props else ''
        # Add arcs
        arcs_str = ''
        if map_data['attached_arcs']:
            arc_lines = ['||'.join([a[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']]) for a in map_data['attached_arcs']]
            arcs_str = ';arcs::' + ';'.join(arc_lines)
        content = header + sunrise_str + '\n' + map_str + '\n' + footer + props_str + arcs_str
        with open(file, 'w') as f:
            f.write(content)
        map_data['dirty'] = False
    def set_dirty(self):
        self.dirty = True
        self.user_active = 0
    def prev_tab(self):
        curr = self.notebook.index('current')
        if curr > 0:
            self.notebook.select(curr - 1)
    def next_tab(self):
        curr = self.notebook.index('current')
        if curr < len(self.maps) - 1:
            self.notebook.select(curr + 1)
    def show_tooltip(self, event, text):
        if text:
            self.tooltip = tk.Toplevel(self.root)
            self.tooltip.wm_overrideredirect(True)
            label = tk.Label(self.tooltip, text=text, wraplength=300, justify=tk.LEFT, bg='yellow', fg='black', relief=tk.SOLID, borderwidth=1)
            label.pack()
            x = self.root.winfo_pointerx() + 15
            y = self.root.winfo_pointery() - label.winfo_reqheight() - 5
            self.tooltip.wm_geometry(f"+{x}+{y}")
    def hide_tooltip(self, event):
        if self.tooltip:
            self.tooltip.destroy()
            self.tooltip = None
    def update_tooltip_pos(self, event, text):
        if self.tooltip:
            x = self.root.winfo_pointerx() + 15
            y = self.root.winfo_pointery() - self.tooltip.winfo_height() - 5
            self.tooltip.wm_geometry(f"+{x}+{y}")
    def export_map_png(self, index, path_or_buf):
        map_data = self.maps[index]
        w, h = map_data['width'], map_data['height']
        fig = plt.figure(figsize=(w / 2, h / 2))
        ax = fig.add_axes([0, 0, 1, 1])
        ax.set_xlim(0, w)
        ax.set_ylim(0, h)
        ax.invert_yaxis()
        ax.set_aspect('equal')
        # grid lines
        ax.set_xticks(range(w + 1))
        ax.set_yticks(range(h + 1))
        ax.grid(True, color='gray')
        # texts
        for y in range(h):
            for x in range(w):
                cell = map_data['grid'][y, x]
                ax.text(x + 0.5, y + 0.5, cell['symbol'], ha='center', va='center', color=cell['color'], fontsize=12)
        # sun positions
        if map_data['sunrise']:
            rx, ry = map_data['sunrise']
            ax.add_patch(plt.Rectangle((rx, ry), 1, 1, fill=False, edgecolor='orange', lw=2))
        if map_data['sunset']:
            sx, sy = map_data['sunset']
            ax.add_patch(plt.Rectangle((sx, sy), 1, 1, fill=False, edgecolor='red', lw=2))
        plt.axis('off')
        if hasattr(path_or_buf, 'write'):
            plt.savefig(path_or_buf, format='png', bbox_inches='tight')
        else:
            plt.savefig(path_or_buf, bbox_inches='tight')
        plt.close()
        # Create accompanying txt file
        base_path, ext = os.path.splitext(path_or_buf)
        txt_path = base_path + '.txt'
        i = 1
        while os.path.exists(txt_path):
            txt_path = base_path + f'_{str(i).zfill(2)}.txt'
            i += 1
        var_dict = self.var_dicts[index]
        openings = var_dict['openings_var'].get().ljust(7, '0')
        map_type = var_dict['type_var'].get()
        name = var_dict['name_var'].get()
        maker = var_dict['maker_var'].get()
        system = map_data['system']
        header = f"{openings} {map_data['width']}x{map_data['height']}"
        sunrise_str = ''
        if map_data['sunrise'] and map_data['sunset']:
            sunrise_str = f" sunrise xy({map_data['sunrise'][0]},{map_data['sunrise'][1]}); sunset xy({map_data['sunset'][0]},{map_data['sunset'][1]})"
        footer = f"{map_type}; {name}; {maker}; {system}"
        # Add properties array
        props = [
            f'{cell["symbol"]}[\"{cell["color"]}\";\"{cell["name"]}\";\"{cell["texture"]}\";{cell["sun"] if cell["sun"] != "NA" else ""}({x},{cell["3d"]},{y},{cell["depth"]},{cell["height"]},{cell["range"]}){cell["value"]}]'
            for y in range(map_data['height'])
            for x in range(map_data['width'])
            for cell in [map_data['grid'][y, x]]
            if not (cell['symbol'] == ' ' and cell['color'] == 'black' and cell['texture'] == '' and cell['name'] == '' and cell['value'] == 0 and cell['depth'] == 1 and cell['height'] == 1 and cell['3d'] == 0 and cell['range'] == 0.0 and cell['sun'] == 'NA')
        ]
        props_str = ' ' + ' '.join(props) if props else ''
        # Add arcs
        arcs_str = ''
        if map_data['attached_arcs']:
            arc_lines = ['||'.join([a[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']]) for a in map_data['attached_arcs']]
            arcs_str = ';arcs::' + ';'.join(arc_lines)
        txt_content = header + sunrise_str + '  ' + footer + props_str + arcs_str
        with open(txt_path, 'w') as f:
            f.write(txt_content)
    def export_all_maps_png(self):
        for i in range(len(self.maps)):
            map_data = self.maps[i]
            file = map_data['name'] + '.png'
            path = file
            j = 1
            while os.path.exists(path):
                path = map_data['name'] + f'_{str(j).zfill(2)}.png'
                j += 1
            self.export_map_png(i, path)
    def export_current_map_png(self):
        map_data = self.maps[self.current_index]
        file = map_data['name'] + '.png'
        path = file
        j = 1
        while os.path.exists(path):
            path = map_data['name'] + f'_{str(j).zfill(2)}.png'
            j += 1
        self.export_map_png(self.current_index, path)
    def export_arc_csv(self, arc, path_or_buf):
        fields = ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']
        if hasattr(path_or_buf, 'write'):
            writer = csv.writer(path_or_buf)
        else:
            f = open(path_or_buf, 'w', newline='')
            writer = csv.writer(f)
        for field in fields:
            writer.writerow([field, arc[field]])
        if not hasattr(path_or_buf, 'write'):
            f.close()
    def export_selected_arc_csv(self):
        if self.current_arc_index is not None:
            arc = self.arcs[self.current_arc_index]
            file = arc['name'] + '.csv'
            path = file
            j = 1
            while os.path.exists(path):
                path = arc['name'] + f'_{str(j).zfill(2)}.csv'
                j += 1
            self.export_arc_csv(arc, path)
    def export_all_arcs_csv(self):
        for arc in self.arcs:
            file = arc['name'] + '.csv'
            path = file
            j = 1
            while os.path.exists(path):
                path = arc['name'] + f'_{str(j).zfill(2)}.csv'
                j += 1
            self.export_arc_csv(arc, path)
    def export_full_dict(self):
        unique = datetime.now().strftime('%Y%m%d%H%M%S%f')[:-3]
        zip_file = f'PB_dict_{unique}.zip'
        path = zip_file
        j = 1
        while os.path.exists(path):
            path = f'PB_dict_{unique}_{str(j).zfill(2)}.zip'
            j += 1
        with zipfile.ZipFile(path, 'w') as zf:
            for i, map_data in enumerate(self.maps):
                buf = BytesIO()
                self.export_map_png(i, buf)
                buf.seek(0)
                zf.writestr(f'map/{map_data["name"]}.png', buf.read())
            for arc in self.arcs:
                buf = StringIO()
                self.export_arc_csv(arc, buf)
                buf.seek(0)
                zf.writestr(f'arc/{arc["name"]}.csv', buf.getvalue())
if __name__ == "__main__":
    root = tk.Tk()
    app = MapMaker(root)
    root.mainloop()
