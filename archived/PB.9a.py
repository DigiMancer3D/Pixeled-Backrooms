# No additional dependencies are required beyond the Python standard library, as this uses Tkinter which is included.
# If Tkinter is not available on your system, install it with: sudo apt update && sudo apt install python3-tk
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import copy
import os
import re
import random
from datetime import datetime

class MapMaker:
    def __init__(self, root):
        self.root = root
        self.current_size = (0, 0)
        self.root.title("Pixeled Backrooms - Map Maker")
        self.root.geometry("1200x800")
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
        self.canvas_texts_list = []
        self.undo_stacks = []
        self.redo_stacks = []
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
        # Theme
        self.theme = self.settings.get('theme', 'dark') # 'dark' or 'terminal'
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
        # Data Check
        self.data_check()
        # Help check
        self.help_check()
        self.main_vertical_paned, self.upper_horizontal_paned, self.bottom_horizontal_paned = self.setup_ui()
        self.setup_menu()
        self.apply_theme()
        # Add initial map
        self.add_map_tab("Unnamed")
        # Clear arc fields
        self.clear_arc_fields()
        # Bind exit to save udata
        self.root.protocol("WM_DELETE_WINDOW", self.save_and_exit)
        # Global bindings for tab and shift-tab
        self.root.bind_all("<Tab>", self.handle_tab)
        self.root.bind_all("<Shift-Tab>", self.handle_shift_tab)
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
        self.mouse_history = []
        self.root.bind("<Motion>", self.track_mouse)
        self.root.bind("<Button>", self.unlock_cursor_on_action)
        self.root.bind("<MouseWheel>", self.unlock_cursor_on_action)
        self.root.bind_all("<Return>", self.unlock_cursor_on_action)
        self.root.bind_all("<Shift-Return>", self.unlock_cursor_on_action)
        # Issue 2: user_active
        self.user_active = 1  # 1 means unchanged
        self.cheating_detected = False
        self.cheating_reason = ""
        # Issue 3: last directories
        base_dir = os.getcwd()
        self.last_dir = {
            'file_load': base_dir,
            'arc_load': os.path.join(base_dir, 'arc'),
            'map_load': os.path.join(base_dir, 'map'),
            'dict_load': os.path.join(base_dir, 'dict')
        }

    def track_mouse(self, event):
        if self.locked_input:
            self.mouse_history.append((event.x_root, event.y_root, datetime.now().timestamp()))
            if len(self.mouse_history) > 10:
                self.mouse_history.pop(0)
            if self.detect_mouse_pattern():
                self.unlock_cursor()

    def detect_mouse_pattern(self):
        if len(self.mouse_history) < 3:
            return False
        # Constant velocity
        dx1 = self.mouse_history[-1][0] - self.mouse_history[-2][0]
        dy1 = self.mouse_history[-1][1] - self.mouse_history[-2][1]
        dt1 = self.mouse_history[-1][2] - self.mouse_history[-2][2]
        dx2 = self.mouse_history[-2][0] - self.mouse_history[-3][0]
        dy2 = self.mouse_history[-2][1] - self.mouse_history[-3][1]
        dt2 = self.mouse_history[-2][2] - self.mouse_history[-3][2]
        if dt1 > 0 and dt2 > 0:
            vx1 = dx1 / dt1
            vy1 = dy1 / dt1
            vx2 = dx2 / dt2
            vy2 = dy2 / dt2
            if abs(vx1 - vx2) < 5 and abs(vy1 - vy2) < 5 and (abs(vx1) > 0 or abs(vy1) > 0):
                return True
        # Shaking
        if abs(dx1 + dx2) < 5 and abs(dy1 + dy2) < 5 and (abs(dx1) > 10 or abs(dy1) > 10):
            return True
        # Patterns like circles: check change in direction
        directions = []
        for i in range(1, len(self.mouse_history)):
            dx = self.mouse_history[i][0] - self.mouse_history[i-1][0]
            dy = self.mouse_history[i][1] - self.mouse_history[i-1][1]
            if abs(dx) > abs(dy):
                dir_ = 'right' if dx > 0 else 'left'
            else:
                dir_ = 'down' if dy > 0 else 'up'
            directions.append(dir_)
        if len(set(directions)) >= 3:
            return True
        return False

    def unlock_cursor_on_action(self, event):
        if self.locked_input:
            self.unlock_cursor()

    def lock_cursor(self, widget):
        self.locked_input = widget
        self.root.config(cursor='none')

    def unlock_cursor(self):
        self.locked_input = None
        self.root.config(cursor='')
        self.mouse_history = []

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
        self.save_pane_positions()
        self.root.destroy()

    def apply_theme(self):
        if self.theme == 'terminal':
            fg = 'green'
            bg = 'black'
        else: # dark
            fg = 'white'
            bg = '#333333'
        # Apply to widgets, placeholder
        self.root.config(bg=bg)

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
        # File menu
        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="New", command=self.new_with_save_check)
        filemenu.add_command(label="Load", command=self.load_with_save_check)
        filemenu.add_separator()
        filemenu.add_command(label="Save", command=self.save_file)
        filemenu.add_command(label="Save & Exit", command=self.save_and_exit)
        filemenu.add_command(label="Exit without Save", command=self.exit_without_save)
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
        menubar.add_cascade(label="Arc", menu=self.arcmenu)
        self.root.config(menu=menubar)
        self.update_map_menu_states()
        self.update_toolbar_menu_states()
        self.update_arc_menu_states()

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

    def update_edit_menu_states(self):
        state = 'normal' if self.selected_region and (self.selected_region[2] - self.selected_region[0] > 1 or self.selected_region[3] - self.selected_region[1] > 1) else 'disabled'
        self.editmenu.entryconfig(self.copy_index, state=state)
        self.editmenu.entryconfig(self.cut_index, state=state)
        self.editmenu.entryconfig(self.replace_index, state=state)
        self.editmenu.entryconfig(self.make_new_index, state=state)
        self.editmenu.entryconfig(self.gen_new_index, state=state)
        self.editmenu.entryconfig(self.clear_prop_index, state=state)
        self.editmenu.entryconfig(self.remove_sel_index, state=state)
        paste_state = 'normal' if self.clipboard else 'disabled'
        self.editmenu.entryconfig(self.paste_index, state=paste_state)
        undo_delete_state = 'normal' if self.deleted_arcs else 'disabled'
        self.editmenu.entryconfig(self.undo_arc_delete_index, state=undo_delete_state)
        undo_state = 'normal' if self.undo_stacks[self.current_index] else 'disabled'
        self.editmenu.entryconfig(self.undo_index, state=undo_state)
        redo_state = 'normal' if self.redo_stacks[self.current_index] else 'disabled'
        self.editmenu.entryconfig(self.redo_index, state=redo_state)

    def setup_ui(self):
        # Main vertical paned for upper and lower
        main_vertical_paned = tk.PanedWindow(self.root, orient=tk.VERTICAL, sashrelief=tk.RAISED)
        main_vertical_paned.pack(fill=tk.BOTH, expand=True)
        # Upper frame
        upper_frame = tk.Frame(main_vertical_paned, bg="#222222")
        main_vertical_paned.add(upper_frame, minsize=0, stretch="never")
        self.upper_frame = upper_frame
        # Upper horizontal paned for left, center, right
        upper_horizontal_paned = tk.PanedWindow(upper_frame, orient=tk.HORIZONTAL, sashrelief=tk.RAISED)
        upper_horizontal_paned.pack(fill=tk.BOTH, expand=True)
        # Left toolbar: Symbol pick-n-place with descriptions
        left_frame = tk.Frame(upper_horizontal_paned, bg="#333333")
        upper_horizontal_paned.add(left_frame, minsize=150, stretch="never")
        self.left_frame = left_frame
        tk.Label(left_frame, text="Symbols", fg="white", bg="#333333").pack(anchor=tk.W)
        symbols_frame = tk.Frame(left_frame, bg="#333333")
        symbols_frame.pack(fill=tk.BOTH, expand=True)
        symbols_vscroll = tk.Scrollbar(symbols_frame, orient=tk.VERTICAL)
        symbols_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.symbol_list = tk.Listbox(symbols_frame, bg="#444444", fg="white", yscrollcommand=symbols_vscroll.set)
        for sym, desc in self.symbols:
            self.symbol_list.insert(tk.END, f"{sym} = {desc}")
        self.symbol_list.pack(fill=tk.BOTH, expand=True)
        symbols_vscroll.config(command=self.symbol_list.yview)
        self.symbol_list.bind("<<ListboxSelect>>", self.select_symbol)
        self.symbol_list.bind("<Button-3>", lambda e: messagebox.showinfo("Symbols List", "Select a symbol to place on the map or -- to enter select mode for properties."))
        self.symbol_list.bind("<Enter>", lambda e: self.symbol_list.focus_set())
        self.symbol_list.bind("<MouseWheel>", self.handle_scroll)
        self.symbol_list.bind("<Shift-MouseWheel>", self.handle_shift_scroll)
        self.symbol_list.bind("<Button-4>", lambda e: self.handle_scroll(e, delta=120))
        self.symbol_list.bind("<Button-5>", lambda e: self.handle_scroll(e, delta=-120))
        self.symbol_list.bind("<Shift-Button-4>", lambda e: self.handle_shift_scroll(e, delta=120))
        self.symbol_list.bind("<Shift-Button-5>", lambda e: self.handle_shift_scroll(e, delta=-120))
        self.symbol_list.bind("<Key-Page_Up>", self.handle_page_up)
        self.symbol_list.bind("<Key-Page_Down>", self.handle_page_down)
        self.focusable_sections.append(self.symbol_list)
        # Center: Notebook for maps
        self.notebook = ttk.Notebook(upper_horizontal_paned)
        upper_horizontal_paned.add(self.notebook, minsize=600, stretch="always")
        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_change)
        # Right: Arcs and properties
        right_frame = tk.Frame(upper_horizontal_paned, bg="#333333")
        upper_horizontal_paned.add(right_frame, minsize=250, stretch="never")
        tk.Label(right_frame, text="Arcs", fg="white", bg="#333333").pack()
        arc_list_frame = tk.Frame(right_frame, bg="#333333")
        arc_list_frame.pack(fill=tk.BOTH, expand=True)
        arc_vscroll = tk.Scrollbar(arc_list_frame, orient=tk.VERTICAL)
        arc_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.arc_list = tk.Listbox(arc_list_frame, bg="#444444", fg="white", yscrollcommand=arc_vscroll.set, height=7)
        self.arc_list.pack(fill=tk.BOTH, expand=True)
        arc_vscroll.config(command=self.arc_list.yview)
        self.arc_list.bind("<<ListboxSelect>>", self.select_arc)
        self.arc_list.bind("<Button-3>", lambda e: messagebox.showinfo("Arcs List", "Select an arc to edit or add new."))
        self.arc_list.bind("<Enter>", lambda e: self.arc_list.focus_set())
        self.arc_list.bind("<MouseWheel>", self.handle_scroll)
        self.arc_list.bind("<Shift-MouseWheel>", self.handle_shift_scroll)
        self.arc_list.bind("<Button-4>", lambda e: self.handle_scroll(e, delta=120))
        self.arc_list.bind("<Button-5>", lambda e: self.handle_scroll(e, delta=-120))
        self.arc_list.bind("<Shift-Button-4>", lambda e: self.handle_shift_scroll(e, delta=120))
        self.arc_list.bind("<Shift-Button-5>", lambda e: self.handle_shift_scroll(e, delta=-120))
        self.arc_list.bind("<Key-Page_Up>", self.handle_page_up)
        self.arc_list.bind("<Key-Page_Down>", self.handle_page_down)
        self.focusable_sections.append(self.arc_list)
        tk.Button(right_frame, text="New Arc", command=self.new_arc, bg="#555555", fg="white").pack(fill=tk.X)
        tk.Button(right_frame, text="Delete Arc", command=self.delete_arc, bg="#555555", fg="white").pack(fill=tk.X)
        # Property frame (hidden initially)
        self.property_frame = tk.Frame(right_frame, bg="#444444")
        self.property_frame.pack(fill=tk.BOTH, expand=True)
        self.property_frame.pack_forget() # Hide initially
        tk.Label(self.property_frame, text="Properties", fg="white", bg="#444444").pack()
        self.prop_color_var = tk.StringVar(value="white")
        tk.Label(self.property_frame, text="Color:", fg="white", bg="#444444").pack(anchor=tk.W)
        self.prop_color_entry = tk.Entry(self.property_frame, textvariable=self.prop_color_var)
        self.prop_color_entry.pack(fill=tk.X)
        self.prop_color_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_texture_var = tk.StringVar()
        tk.Label(self.property_frame, text="Texture:", fg="white", bg="#444444").pack(anchor=tk.W)
        self.prop_texture_entry = tk.Entry(self.property_frame, textvariable=self.prop_texture_var)
        self.prop_texture_entry.pack(fill=tk.X)
        self.prop_texture_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_name_var = tk.StringVar()
        tk.Label(self.property_frame, text="Name:", fg="white", bg="#444444").pack(anchor=tk.W)
        self.prop_name_entry = tk.Entry(self.property_frame, textvariable=self.prop_name_var)
        self.prop_name_entry.pack(fill=tk.X)
        self.prop_name_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_value_var = tk.StringVar(value="0")
        tk.Label(self.property_frame, text="Value:", fg="white", bg="#444444").pack(anchor=tk.W)
        def validate_int(P):
            return P.isdigit() or P == '' # Allow digits or empty (for deleting)
        vcmd_int = self.root.register(validate_int)
        self.prop_value_entry = tk.Entry(self.property_frame, textvariable=self.prop_value_var, validate='key', validatecommand=(vcmd_int, '%P'))
        self.prop_value_entry.pack(fill=tk.X)
        self.prop_value_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_depth_var = tk.StringVar(value="1")
        tk.Label(self.property_frame, text="Depth:", fg="white", bg="#444444").pack(anchor=tk.W)
        self.prop_depth_entry = tk.Entry(self.property_frame, textvariable=self.prop_depth_var, validate='key', validatecommand=(vcmd_int, '%P'))
        self.prop_depth_entry.pack(fill=tk.X)
        self.prop_depth_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_height_var = tk.StringVar(value="1")
        tk.Label(self.property_frame, text="Height:", fg="white", bg="#444444").pack(anchor=tk.W)
        self.prop_height_entry = tk.Entry(self.property_frame, textvariable=self.prop_height_var, validate='key', validatecommand=(vcmd_int, '%P'))
        self.prop_height_entry.pack(fill=tk.X)
        self.prop_height_entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        self.prop_3d_var = tk.BooleanVar(value=False)
        self.prop_3d_check = tk.Checkbutton(self.property_frame, text="3D Effect", variable=self.prop_3d_var, bg="#444444", fg="white", selectcolor="#555555")
        self.prop_3d_check.pack(anchor=tk.W)
        tk.Button(self.property_frame, text="Apply", command=self.apply_properties, bg="#555555", fg="white").pack(fill=tk.X)
        self.lock_button = tk.Button(self.property_frame, text="Lock Apply", command=self.toggle_lock, bg="#555555", fg="white")
        self.lock_button.pack(fill=tk.X)
        # Bottom arc builder
        bottom_frame = tk.Frame(main_vertical_paned, bg="#333333")
        main_vertical_paned.add(bottom_frame, minsize=50)
        # Bottom horizontal paned for arc fields, input gen, phrases, arc options
        bottom_horizontal_paned = tk.PanedWindow(bottom_frame, orient=tk.HORIZONTAL, sashrelief=tk.RAISED)
        bottom_horizontal_paned.pack(fill=tk.BOTH, expand=True)
        # Arc fields frame with both scrolls
        arc_fields_frame = tk.Frame(bottom_horizontal_paned, bg="#333333")
        bottom_horizontal_paned.add(arc_fields_frame, minsize=600, stretch="always")
        arc_fields_canvas = tk.Canvas(arc_fields_frame, bg="#333333")
        hscroll = tk.Scrollbar(arc_fields_frame, orient=tk.HORIZONTAL, command=arc_fields_canvas.xview)
        hscroll.pack(side=tk.BOTTOM, fill=tk.X)
        vscroll = tk.Scrollbar(arc_fields_frame, orient=tk.VERTICAL, command=arc_fields_canvas.yview)
        vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        arc_fields_canvas.pack(fill=tk.BOTH, expand=True)
        arc_fields_canvas.config(xscrollcommand=hscroll.set, yscrollcommand=vscroll.set)
        arc_inner_frame = tk.Frame(arc_fields_canvas, bg="#333333")
        arc_fields_canvas.create_window((0,0), window=arc_inner_frame, anchor="nw")
        # Grid for labels and entries
        tk.Label(arc_inner_frame, text="Arc Name:", fg="white", bg="#333333").grid(row=0, column=0, sticky=tk.W)
        arc_name_entry = tk.Entry(arc_inner_frame, textvariable=self.arc_name_var)
        arc_name_entry.grid(row=0, column=1, sticky=tk.EW)
        def validate_len_18(P): return len(P) <= 18 or P == ''
        vcmd_name = self.root.register(validate_len_18)
        arc_name_entry.config(validate='key', validatecommand=(vcmd_name, '%P'))
        arc_name_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        arc_name_entry.bind("<FocusOut>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Estimated:", fg="white", bg="#333333").grid(row=1, column=0, sticky=tk.W)
        estimated_combo = ttk.Combobox(arc_inner_frame, textvariable=self.arc_estimated_type_var, values=["2-Finish (E2F)", "2-Start (E2S)", "Short-Hold-Time (SHT)", "Long-Hold-Time (LHT)"], state='readonly')
        estimated_combo.grid(row=1, column=1, sticky=tk.EW)
        estimated_combo.bind("<<ComboboxSelected>>", lambda e: [self.update_est_picker(), self.on_arc_change(e)])
        self.est_picker_frame = tk.Frame(arc_inner_frame, bg="#333333")
        self.est_picker_frame.grid(row=2, column=1, sticky=tk.EW)
        self.update_est_picker()
        tk.Label(arc_inner_frame, text="Zone Type:", fg="white", bg="#333333").grid(row=3, column=0, sticky=tk.W)
        zone_combo = ttk.Combobox(arc_inner_frame, textvariable=self.arc_zone_type_var, values=['Safe', 'Crawl', 'Fight', 'Mix0', 'Mix1', 'Mix2', 'Mix3', 'Mixed'], state='readonly')
        zone_combo.grid(row=3, column=1, sticky=tk.EW)
        zone_combo.bind("<<ComboboxSelected>>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Start Msg:", fg="white", bg="#333333").grid(row=4, column=0, sticky=tk.W)
        arc_start_entry = tk.Entry(arc_inner_frame, textvariable=self.arc_start_msg_var)
        arc_start_entry.grid(row=4, column=1, sticky=tk.EW)
        def validate_len_150(P): return len(P) <= 150 or P == ''
        vcmd_150 = self.root.register(validate_len_150)
        arc_start_entry.config(validate='key', validatecommand=(vcmd_150, '%P'))
        arc_start_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        arc_start_entry.bind("<FocusOut>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Map:", fg="white", bg="#333333").grid(row=5, column=0, sticky=tk.W)
        arc_map_entry = tk.Entry(arc_inner_frame, textvariable=self.arc_map_var)
        arc_map_entry.grid(row=5, column=1, sticky=tk.EW)
        arc_map_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        arc_map_entry.bind("<FocusOut>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Map Type:", fg="white", bg="#333333").grid(row=6, column=0, sticky=tk.W)
        map_type_combo = ttk.Combobox(arc_inner_frame, textvariable=self.arc_map_type_var, values=['Generate', 'Import'], state='readonly')
        map_type_combo.grid(row=6, column=1, sticky=tk.EW)
        map_type_combo.bind("<<ComboboxSelected>>", self.on_arc_change)
        tk.Label(arc_inner_frame, text="Arc Data:", fg="white", bg="#333333").grid(row=7, column=0, sticky=tk.NW)
        self.arc_data_text = tk.Text(arc_inner_frame, height=10, bg="#444444", fg="white", wrap=tk.WORD)
        self.arc_data_text.grid(row=7, column=1, sticky=tk.EW)
        self.arc_data_text.bind("<<Modified>>", self.on_arc_modified)
        self.arc_data_text.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
        tk.Label(arc_inner_frame, text="Confirm Msg:", fg="white", bg="#333333").grid(row=8, column=0, sticky=tk.W)
        arc_confirm_entry = tk.Entry(arc_inner_frame, textvariable=self.arc_confirm_msg_var)
        arc_confirm_entry.grid(row=8, column=1, sticky=tk.EW)
        arc_confirm_entry.config(validate='key', validatecommand=(vcmd_150, '%P'))
        arc_confirm_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        arc_confirm_entry.bind("<FocusOut>", self.on_arc_change)
        arc_inner_frame.columnconfigure(1, weight=1)
        arc_inner_frame.bind("<Configure>", lambda e: arc_fields_canvas.config(scrollregion=arc_fields_canvas.bbox("all")))
        arc_fields_canvas.bind("<MouseWheel>", self.handle_scroll)
        arc_fields_canvas.bind("<Shift-MouseWheel>", self.handle_shift_scroll)
        arc_fields_canvas.bind("<Button-4>", lambda e: self.handle_scroll(e, delta=120))
        arc_fields_canvas.bind("<Button-5>", lambda e: self.handle_scroll(e, delta=-120))
        arc_fields_canvas.bind("<Shift-Button-4>", lambda e: self.handle_shift_scroll(e, delta=120))
        arc_fields_canvas.bind("<Shift-Button-5>", lambda e: self.handle_shift_scroll(e, delta=-120))
        arc_fields_canvas.bind("<Key-Page_Up>", self.handle_page_up)
        arc_fields_canvas.bind("<Key-Page_Down>", self.handle_page_down)
        arc_fields_canvas.bind("<Enter>", lambda e: arc_fields_canvas.focus_set())
        self.focusable_sections.append(arc_fields_canvas)
        # Script Generator frame (old Input Generator)
        input_gen_frame = tk.Frame(bottom_horizontal_paned, bg="#333333")
        bottom_horizontal_paned.add(input_gen_frame, minsize=200, stretch="never")
        tk.Label(input_gen_frame, text="Script Generator", fg="white", bg="#333333").pack(anchor=tk.W)
        input_gen_list_frame = tk.Frame(input_gen_frame, bg="#333333")
        input_gen_list_frame.pack(fill=tk.BOTH)
        input_gen_vscroll = tk.Scrollbar(input_gen_list_frame, orient=tk.VERTICAL)
        input_gen_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.input_gen_list = tk.Listbox(input_gen_list_frame, bg="#444444", fg="white", yscrollcommand=input_gen_vscroll.set, height=3)
        options = ["Enemy", "Boss", "Mini-Boss", "NPC", "Group", "Map Location"]
        for opt in options:
            self.input_gen_list.insert(tk.END, opt)
        self.input_gen_list.pack(fill=tk.BOTH, expand=True)
        input_gen_vscroll.config(command=self.input_gen_list.yview)
        self.input_gen_list.bind("<<ListboxSelect>>", self.select_input_gen_type)
        # Input gen form with scrolls
        input_gen_form_frame = tk.Frame(input_gen_frame, bg="#333333")
        input_gen_form_frame.pack(fill=tk.BOTH, expand=True)
        input_gen_form_canvas = tk.Canvas(input_gen_form_frame, bg="#333333")
        input_gen_form_hscroll = tk.Scrollbar(input_gen_form_frame, orient=tk.HORIZONTAL, command=input_gen_form_canvas.xview)
        input_gen_form_hscroll.pack(side=tk.BOTTOM, fill=tk.X)
        input_gen_form_vscroll = tk.Scrollbar(input_gen_form_frame, orient=tk.VERTICAL, command=input_gen_form_canvas.yview)
        input_gen_form_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        input_gen_form_canvas.pack(fill=tk.BOTH, expand=True)
        input_gen_form_canvas.config(xscrollcommand=input_gen_form_hscroll.set, yscrollcommand=input_gen_form_vscroll.set)
        self.input_gen_form_inner = tk.Frame(input_gen_form_canvas, bg="#333333")
        input_gen_form_canvas.create_window((0,0), window=self.input_gen_form_inner, anchor="nw")
        self.input_gen_form_inner.bind("<Configure>", lambda e: input_gen_form_canvas.config(scrollregion=input_gen_form_canvas.bbox("all")))
        input_gen_form_canvas.bind("<MouseWheel>", self.handle_scroll)
        input_gen_form_canvas.bind("<Shift-MouseWheel>", self.handle_shift_scroll)
        input_gen_form_canvas.bind("<Button-4>", lambda e: self.handle_scroll(e, delta=120))
        input_gen_form_canvas.bind("<Button-5>", lambda e: self.handle_scroll(e, delta=-120))
        input_gen_form_canvas.bind("<Shift-Button-4>", lambda e: self.handle_shift_scroll(e, delta=120))
        input_gen_form_canvas.bind("<Shift-Button-5>", lambda e: self.handle_shift_scroll(e, delta=-120))
        input_gen_form_canvas.bind("<Key-Page_Up>", self.handle_page_up)
        input_gen_form_canvas.bind("<Key-Page_Down>", self.handle_page_down)
        input_gen_form_canvas.bind("<Enter>", lambda e: input_gen_form_canvas.focus_set())
        self.focusable_sections.append(input_gen_form_canvas)
        # Phrases frame
        phrases_frame = tk.Frame(bottom_horizontal_paned, bg="#333333")
        bottom_horizontal_paned.add(phrases_frame, minsize=200, stretch="never")
        tk.Label(phrases_frame, text="Data Phrases", fg="white", bg="#333333").pack(anchor=tk.W)
        phrases_canvas = tk.Canvas(phrases_frame, bg="#333333")
        hscroll_phrases = tk.Scrollbar(phrases_frame, orient=tk.HORIZONTAL, command=phrases_canvas.xview)
        hscroll_phrases.pack(side=tk.BOTTOM, fill=tk.X)
        vscroll_phrases = tk.Scrollbar(phrases_frame, orient=tk.VERTICAL, command=phrases_canvas.yview)
        vscroll_phrases.pack(side=tk.RIGHT, fill=tk.Y)
        phrases_canvas.pack(fill=tk.BOTH, expand=True)
        phrases_canvas.config(xscrollcommand=hscroll_phrases.set, yscrollcommand=vscroll_phrases.set)
        inner_frame = tk.Frame(phrases_canvas, bg="#333333")
        phrases_canvas.create_window((0,0), window=inner_frame, anchor="nw")
        phrases = ["exit", "enter", "kill", "death", "squash", "XYZ", "pick", "acts", "touch", "user", "jim", "sarah", "bob", "obj", "weap", "armed", "arm", "speed", "faster", "slower", "slow", "glue", "hot", "cold", "froze", "flame", "drop", "xplode", "burp", "burpee", "slothee", "plop", "wrap", "parw", "par"]
        col = 0
        row = 0
        max_rows = 7 # Adjust based on height
        for phrase in phrases:
            btn = tk.Button(inner_frame, text=phrase, command=lambda p=phrase: self.insert_phrase(p), bg="#555555", fg="white")
            btn.grid(row=row, column=col, sticky=tk.EW)
            btn.bind("<Button-3>", lambda e, p=phrase: messagebox.showinfo("Phrase", f"Insert '{p}' into arc data"))
            row += 1
            if row >= max_rows:
                row = 0
                col += 1
        def update_phrases_scroll(e):
            region = phrases_canvas.bbox("all")
            phrases_canvas.config(scrollregion=(region[0], region[1], region[2] + 50, region[3] + 50))
        inner_frame.bind("<Configure>", update_phrases_scroll)
        phrases_canvas.bind("<MouseWheel>", self.handle_scroll)
        phrases_canvas.bind("<Shift-MouseWheel>", self.handle_shift_scroll)
        phrases_canvas.bind("<Button-4>", lambda e: self.handle_scroll(e, delta=120))
        phrases_canvas.bind("<Button-5>", lambda e: self.handle_scroll(e, delta=-120))
        phrases_canvas.bind("<Shift-Button-4>", lambda e: self.handle_shift_scroll(e, delta=120))
        phrases_canvas.bind("<Shift-Button-5>", lambda e: self.handle_shift_scroll(e, delta=-120))
        phrases_canvas.bind("<Key-Page_Up>", self.handle_page_up)
        phrases_canvas.bind("<Key-Page_Down>", self.handle_page_down)
        phrases_canvas.bind("<Enter>", lambda e: phrases_canvas.focus_set())
        self.focusable_sections.append(phrases_canvas)
        # Arc options frame vertical with scroll, limited width
        arc_options_frame = tk.Frame(bottom_horizontal_paned, bg="#333333")
        bottom_horizontal_paned.add(arc_options_frame, minsize=150, stretch="never")
        tk.Label(arc_options_frame, text="Arc Options", fg="white", bg="#333333").pack(anchor=tk.W)
        arc_bottom_canvas = tk.Canvas(arc_options_frame, bg="#333333")
        vscroll_arc = tk.Scrollbar(arc_options_frame, orient=tk.VERTICAL, command=arc_bottom_canvas.yview)
        vscroll_arc.pack(side=tk.RIGHT, fill=tk.Y)
        arc_bottom_canvas.pack(fill=tk.BOTH, expand=True)
        arc_bottom_canvas.config(yscrollcommand=vscroll_arc.set)
        arc_bottom_inner = tk.Frame(arc_bottom_canvas, bg="#333333")
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
            tk.Button(arc_bottom_inner, text=text, command=cmd, bg="#555555", fg="white").pack(fill=tk.X)
        arc_bottom_inner.bind("<Configure>", lambda e: arc_bottom_canvas.config(scrollregion=arc_bottom_canvas.bbox("all")) if arc_bottom_inner.winfo_height() > arc_bottom_canvas.winfo_height() else arc_bottom_canvas.config(scrollregion=(0,0,0,0)))
        arc_bottom_canvas.bind("<MouseWheel>", self.handle_scroll)
        arc_bottom_canvas.bind("<Shift-MouseWheel>", self.handle_shift_scroll)
        arc_bottom_canvas.bind("<Button-4>", lambda e: self.handle_scroll(e, delta=120))
        arc_bottom_canvas.bind("<Button-5>", lambda e: self.handle_scroll(e, delta=-120))
        arc_bottom_canvas.bind("<Shift-Button-4>", lambda e: self.handle_shift_scroll(e, delta=120))
        arc_bottom_canvas.bind("<Shift-Button-5>", lambda e: self.handle_shift_scroll(e, delta=-120))
        arc_bottom_canvas.bind("<Key-Page_Up>", self.handle_page_up)
        arc_bottom_canvas.bind("<Key-Page_Down>", self.handle_page_down)
        arc_bottom_canvas.bind("<Enter>", lambda e: arc_bottom_canvas.focus_set())
        self.focusable_sections.append(arc_bottom_canvas)
        return main_vertical_paned, upper_horizontal_paned, bottom_horizontal_paned

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
            tk.Label(self.input_gen_form_inner, text=field + ":", fg="white", bg="#333333").grid(row=row, column=0, sticky=tk.W)
            var = tk.StringVar()
            self.input_gen_vars[field] = var
            entry = tk.Entry(self.input_gen_form_inner, textvariable=var)
            entry.grid(row=row, column=1, sticky=tk.EW)
            entry.bind("<FocusIn>", lambda e: self.lock_cursor(e.widget))
            if field == "XY" and self.input_gen_type == "Map Location":
                tk.Button(self.input_gen_form_inner, text="Pick Location", command=self.start_pick_mode).grid(row=row, column=2)
            row += 1
        tk.Button(self.input_gen_form_inner, text="Inject", command=self.inject_input_gen).grid(row=row, column=0, columnspan=2)

    def start_pick_mode(self):
        self.pick_mode = True
        messagebox.showinfo("Pick Mode", "Click on the map to pick location.")

    def inject_input_gen(self):
        if self.input_gen_type:
            vars = {k: v.get() for k, v in self.input_gen_vars.items() if v.get()}
            if not vars:
                return
            insert_text = ""
            if self.input_gen_type == "Enemy":
                insert_text = f"'{vars.get('Name/Type', '')}' {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} color={vars.get('Color Base', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "Boss":
                insert_text = f"'{vars.get('Name/Type', '')}' (HP={vars.get('Health Base', '')}) (DEF={vars.get('Defense Base', '')}) (ATK={vars.get('Attack Base', '')}) {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} color={vars.get('Color Base', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "Mini-Boss":
                insert_text = f"'{vars.get('Name/Type', '')}' (level{vars.get('Level Difference', '')}) {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} color={vars.get('Color', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "NPC":
                insert_text = f"-{vars.get('Name', '')} {vars.get('Type', '')}- {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} coin={vars.get('Wealth', '')} willpwr={vars.get('Bargaining Willpower', '')} color={vars.get('Color', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "Group":
                insert_text = f"group{{{vars.get('Entities', '')}}} {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} color={vars.get('Color', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            elif self.input_gen_type == "Map Location":
                insert_text = f"^location (@{vars.get('XY', '')}) ^ ~{vars.get('Object', '')}~ {vars.get('Drop Rate', '')}% +{vars.get('Spawn Rate', '')} color={vars.get('Color', '')} value={vars.get('Value', '')} texture={vars.get('Texture', '')}"
            self.arc_data_text.insert(tk.INSERT, insert_text + " ")

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
                tk.Label(self.est_picker_frame, text=":", fg="white", bg="#333333").grid(row=0, column=col)
                col += 1

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
        map_data = {
            'width': 48,
            'height': 24,
            'grid': [[{'symbol': ' ', 'color': 'white', 'texture': '', 'name': '', 'value': 0, 'depth': 1, 'height': 1, '3d': False} for _ in range(48)] for _ in range(24)],
            'openings': '0000000',
            'type': 'Safe',
            'name': name,
            'maker': 'User',
            'system': 'PB [no-jam] PyEditor',
            'attached_arcs': [],
            'dot_ids': []
        }
        self.maps.append(map_data)
        frame = tk.Frame(self.notebook, bg="#222222")
        tab_id = self.notebook.add(frame, text=name)
        # Header frame
        header_frame = tk.Frame(frame, bg="#222222")
        header_frame.pack(fill=tk.X)
        openings_var = tk.StringVar(value=map_data['openings'])
        tk.Label(header_frame, text="Openings:", fg="white", bg="#222222").pack(side=tk.LEFT)
        openings_entry = tk.Entry(header_frame, textvariable=openings_var, width=10)
        openings_entry.pack(side=tk.LEFT)
        def validate_openings(P):
            return len(P) <=7 and all(c in '01234' for c in P)
        vcmd_open = self.root.register(validate_openings)
        openings_entry.config(validate='key', validatecommand=(vcmd_open, '%P'))
        openings_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        width_var = tk.IntVar(value=map_data['width'])
        tk.Label(header_frame, text="Width:", fg="white", bg="#222222").pack(side=tk.LEFT)
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
        tk.Label(header_frame, text="Height:", fg="white", bg="#222222").pack(side=tk.LEFT)
        height_entry = tk.Entry(header_frame, textvariable=height_var, width=5)
        height_entry.pack(side=tk.LEFT)
        height_entry.config(validate='key', validatecommand=(vcmd_size, '%P'))
        height_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        tk.Button(header_frame, text="Apply Size", command=lambda i=map_index: self.apply_size(i), fg="white", bg="#555555").pack(side=tk.LEFT)
        type_var = tk.StringVar(value=map_data['type'])
        tk.Label(header_frame, text="Type:", fg="white", bg="#222222").pack(side=tk.LEFT)
        ttk.Combobox(header_frame, textvariable=type_var, values=['Safe', 'Crawl', 'Fight', 'Mix0', 'Mix1', 'Mix2', 'Mix3', 'Mixed'], state='readonly', width=10).pack(side=tk.LEFT)
        name_var = tk.StringVar(value=map_data['name'])
        tk.Label(header_frame, text="Name:", fg="white", bg="#222222").pack(side=tk.LEFT)
        name_entry = tk.Entry(header_frame, textvariable=name_var, width=15)
        name_entry.pack(side=tk.LEFT)
        def validate_len_28(P): return len(P) <= 28 or P == ''
        vcmd_28 = self.root.register(validate_len_28)
        name_entry.config(validate='key', validatecommand=(vcmd_28, '%P'))
        name_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        maker_var = tk.StringVar(value=map_data['maker'])
        tk.Label(header_frame, text="Maker:", fg="white", bg="#222222").pack(side=tk.LEFT)
        maker_entry = tk.Entry(header_frame, textvariable=maker_var, width=15)
        maker_entry.pack(side=tk.LEFT)
        def validate_len_21(P): return len(P) <= 21 or P == ''
        vcmd_21 = self.root.register(validate_len_21)
        maker_entry.config(validate='key', validatecommand=(vcmd_21, '%P'))
        maker_entry.bind("<FocusIn>", lambda e: [self.select_all(e), self.lock_cursor(e.widget)])
        tk.Label(header_frame, text="System: " + map_data['system'], fg="white", bg="#222222").pack(side=tk.LEFT)
        # Canvas frame
        canvas_frame = tk.Frame(frame)
        canvas_frame.pack(fill=tk.BOTH, expand=True)
        canvas = tk.Canvas(canvas_frame, bg="#222222", width=map_data['width'] * self.cell_size, height=map_data['height'] * self.cell_size + 40) # extra for dots
        hbar = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=canvas.xview)
        hbar.pack(side=tk.BOTTOM, fill=tk.X)
        vbar = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=canvas.yview)
        vbar.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        canvas.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
        self.canvases.append(canvas)
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
        canvas.bind("<MouseWheel>", self.handle_scroll)
        canvas.bind("<Shift-MouseWheel>", self.handle_shift_scroll)
        canvas.bind("<Button-4>", lambda e: self.handle_scroll(e, delta=120))
        canvas.bind("<Button-5>", lambda e: self.handle_scroll(e, delta=-120))
        canvas.bind("<Shift-Button-4>", lambda e: self.handle_shift_scroll(e, delta=120))
        canvas.bind("<Shift-Button-5>", lambda e: self.handle_shift_scroll(e, delta=-120))
        canvas.bind("<Key-Page_Up>", self.handle_page_up)
        canvas.bind("<Key-Page_Down>", self.handle_page_down)
        canvas.bind("<w>", lambda e: canvas.yview_scroll(-1, "units"))
        canvas.bind("<s>", lambda e: canvas.yview_scroll(1, "units"))
        canvas.bind("<a>", lambda e: canvas.xview_scroll(-1, "units"))
        canvas.bind("<d>", lambda e: canvas.xview_scroll(1, "units"))
        canvas.bind("<Up>", lambda e: canvas.yview_scroll(-1, "units"))
        canvas.bind("<Down>", lambda e: canvas.yview_scroll(1, "units"))
        canvas.bind("<Left>", lambda e: canvas.xview_scroll(-1, "units"))
        canvas.bind("<Right>", lambda e: canvas.xview_scroll(1, "units"))
        self.focusable_sections.append(canvas)
        self.redraw_canvas(map_index)
        self.center_canvas(map_index)

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

    def handle_dot_right_click(self, event):
        # Removed, as now left click
        pass

    def attach_to_map(self):
        if self.current_arc_index is not None:
            arc = self.arcs[self.current_arc_index]
            self.maps[self.current_index]['attached_arcs'].append(copy.deepcopy(arc))
            self.draw_attached_dots(self.current_index)
            self.set_dirty()
        else:
            messagebox.showerror("No Arc", "No arc selected to attach.")

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
            self.picked_symbol = map_data['grid'][y][x]['symbol']
            self.input_gen_vars['XY'].set(f"{x},{y}")
            self.input_gen_vars['Object'].set(self.picked_symbol)
            self.pick_mode = False
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
            if not self.select_mode:
                self.place_symbol(event)
                self.paste_pos = (x, y)
            else:
                self.deselect_multi()
                self.select_start = (x, y)
                self.select_end = (x, y)
                self.update_select_rect()

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
                    rect_id = canvas.create_rectangle(xx * self.cell_size, yy * self.cell_size, (xx + 1) * self.cell_size, (yy + 1) * self.cell_size, outline='yellow', width=1)
                    self.selected_rects.append(rect_id)
            if maxx - minx == 1 and maxy - miny == 1:
                self.selected_x = minx
                self.selected_y = miny
                cell = map_data['grid'][miny][minx]
                self.prop_color_var.set(cell['color'])
                self.prop_texture_var.set(cell['texture'])
                self.prop_name_var.set(cell['name'])
                self.prop_value_var.set(str(cell['value']))
                self.prop_depth_var.set(str(cell['depth']))
                self.prop_height_var.set(str(cell['height']))
                self.prop_3d_var.set(cell['3d'])
                self.property_frame.pack(fill=tk.BOTH, expand=True)
            else:
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
            self.select_rect = canvas.create_rectangle(minx * self.cell_size, miny * self.cell_size, maxx * self.cell_size, maxy * self.cell_size, outline='white', dash=True)

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
        colors = set()
        textures = set()
        names = set()
        values = set()
        depths = set()
        heights = set()
        threed = set()
        for yy in range(miny, maxy):
            for xx in range(minx, maxx):
                cell = map_data['grid'][yy][xx]
                colors.add(cell['color'])
                textures.add(cell['texture'])
                names.add(cell['name'])
                values.add(cell['value'])
                depths.add(cell['depth'])
                heights.add(cell['height'])
                threed.add(cell['3d'])
        shared = {}
        shared['color'] = list(colors)[0] if len(colors) == 1 else ''
        shared['texture'] = list(textures)[0] if len(textures) == 1 else ''
        shared['name'] = list(names)[0] if len(names) == 1 else ''
        shared['value'] = list(values)[0] if len(values) == 1 else ''
        shared['depth'] = list(depths)[0] if len(depths) == 1 else ''
        shared['height'] = list(heights)[0] if len(heights) == 1 else ''
        shared['3d'] = list(threed)[0] if len(threed) == 1 else False
        return shared

    def show_multi_properties(self):
        shared = self.get_shared_props()
        if shared:
            self.prop_color_var.set(shared['color'])
            self.prop_texture_var.set(shared['texture'])
            self.prop_name_var.set(shared['name'])
            self.prop_value_var.set(str(shared['value']) if shared['value'] != '' else '')
            self.prop_depth_var.set(str(shared['depth']) if shared['depth'] != '' else '')
            self.prop_height_var.set(str(shared['height']) if shared['height'] != '' else '')
            self.prop_3d_var.set(shared['3d'])
            self.property_frame.pack(fill=tk.BOTH, expand=True)

    def copy_selected(self):
        if self.selected_region:
            minx, miny, maxx, maxy = self.selected_region
            map_data = self.maps[self.current_index]
            self.clipboard = [[map_data['grid'][yy][xx].copy() for xx in range(minx, maxx)] for yy in range(miny, maxy)]
            self.clipboard_width = maxx - minx
            self.clipboard_height = maxy - miny
            self.update_edit_menu_states()

    def cut_selected(self):
        self.copy_selected()
        self.remove_selected()

    def paste_selected(self):
        if self.clipboard:
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
            self.undo_stacks[self.current_index].append(copy.deepcopy(map_data['grid']))
            if len(self.undo_stacks[self.current_index]) > 69:
                self.undo_stacks[self.current_index].pop(0)
            self.redo_stacks[self.current_index].clear()
            for dy in range(self.clipboard_height):
                for dx in range(self.clipboard_width):
                    if y + dy < height and x + dx < width:
                        map_data['grid'][y + dy][x + dx] = copy.deepcopy(self.clipboard[dy][dx])
                        canvas = self.canvases[self.current_index]
                        canvas.itemconfig(self.canvas_texts_list[self.current_index][y + dy][x + dx], text=self.clipboard[dy][dx]['symbol'], fill=self.clipboard[dy][dx]['color'])
            self.redraw_canvas(self.current_index)
            self.update_edit_menu_states()
            self.set_dirty()

    def replace_selected(self):
        if self.selected_region:
            minx, miny, maxx, maxy = self.selected_region
            map_data = self.maps[self.current_index]
            sym = self.current_symbol.get()
            self.undo_stacks[self.current_index].append(copy.deepcopy(map_data['grid']))
            if len(self.undo_stacks[self.current_index]) > 69:
                self.undo_stacks[self.current_index].pop(0)
            self.redo_stacks[self.current_index].clear()
            for yy in range(miny, maxy):
                for xx in range(minx, maxx):
                    map_data['grid'][yy][xx]['symbol'] = sym
                    if self.lock_var.get() and self.locked_properties:
                        map_data['grid'][yy][xx].update(self.locked_properties)
                    canvas = self.canvases[self.current_index]
                    color = map_data['grid'][yy][xx]['color']
                    canvas.itemconfig(self.canvas_texts_list[self.current_index][yy][xx], text=sym, fill=color)
            self.update_edit_menu_states()
            self.set_dirty()

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
            new_grid = [[old_map['grid'][miny + dy][minx + dx].copy() for dx in range(new_width)] for dy in range(new_height)]
            new_map['grid'] = new_grid
            self.var_dicts[new_index]['width_var'].set(new_width)
            self.var_dicts[new_index]['height_var'].set(new_height)
            self.redraw_canvas(new_index)
            self.center_canvas(new_index)
            self.notebook.select(new_index)
            self.set_dirty()

    def generate_new_section(self):
        messagebox.showinfo("TODO", "Generate New Section functionality is in TODO state.")
        # TODO: Implement smart generation for new section

    def clear_selected_properties(self):
        if self.selected_region:
            focus = self.root.focus_get()
            prop_map = {
                self.prop_color_entry: ('color', 'white'),
                self.prop_texture_entry: ('texture', ''),
                self.prop_name_entry: ('name', ''),
                self.prop_value_entry: ('value', 0),
                self.prop_depth_entry: ('depth', 1),
                self.prop_height_entry: ('height', 1),
                self.prop_3d_check: ('3d', False),
            }
            minx, miny, maxx, maxy = self.selected_region
            map_data = self.maps[self.current_index]
            self.undo_stacks[self.current_index].append(copy.deepcopy(map_data['grid']))
            if len(self.undo_stacks[self.current_index]) > 69:
                self.undo_stacks[self.current_index].pop(0)
            self.redo_stacks[self.current_index].clear()
            if focus in prop_map:
                key, default = prop_map[focus]
                for yy in range(miny, maxy):
                    for xx in range(minx, maxx):
                        map_data['grid'][yy][xx][key] = default
                        if key == 'color':
                            canvas = self.canvases[self.current_index]
                            canvas.itemconfig(self.canvas_texts_list[self.current_index][yy][xx], fill=default)
            else:
                for yy in range(miny, maxy):
                    for xx in range(minx, maxx):
                        cell = map_data['grid'][yy][xx]
                        cell['color'] = 'white'
                        cell['texture'] = ''
                        cell['name'] = ''
                        cell['value'] = 0
                        cell['depth'] = 1
                        cell['height'] = 1
                        cell['3d'] = False
                        canvas = self.canvases[self.current_index]
                        canvas.itemconfig(self.canvas_texts_list[self.current_index][yy][xx], fill='white')
            self.update_edit_menu_states()
            self.set_dirty()

    def remove_selected(self):
        if self.selected_region:
            minx, miny, maxx, maxy = self.selected_region
            map_data = self.maps[self.current_index]
            self.undo_stacks[self.current_index].append(copy.deepcopy(map_data['grid']))
            if len(self.undo_stacks[self.current_index]) > 69:
                self.undo_stacks[self.current_index].pop(0)
            self.redo_stacks[self.current_index].clear()
            for yy in range(miny, maxy):
                for xx in range(minx, maxx):
                    cell = map_data['grid'][yy][xx]
                    cell['symbol'] = ' '
                    cell['color'] = 'white'
                    cell['texture'] = ''
                    cell['name'] = ''
                    cell['value'] = 0
                    cell['depth'] = 1
                    cell['height'] = 1
                    cell['3d'] = False
                    canvas = self.canvases[self.current_index]
                    canvas.itemconfig(self.canvas_texts_list[self.current_index][yy][xx], text=' ', fill='white')
            self.update_edit_menu_states()
            self.set_dirty()

    def place_symbol(self, event):
        if self.select_mode:
            return
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        map_data = self.maps[self.current_index]
        if 0 <= x < map_data['width'] and 0 <= y < map_data['height']:
            sym = self.current_symbol.get()
            self.undo_stacks[self.current_index].append(copy.deepcopy(map_data['grid']))
            if len(self.undo_stacks[self.current_index]) > 69:
                self.undo_stacks[self.current_index].pop(0)
            self.redo_stacks[self.current_index].clear()
            map_data['grid'][y][x]['symbol'] = sym
            if self.lock_var.get() and sym == self.locked_symbol and self.locked_properties:
                map_data['grid'][y][x].update(self.locked_properties)
                canvas.itemconfig(self.canvas_texts_list[self.current_index][y][x], text=sym, fill=self.locked_properties['color'])
            else:
                canvas.itemconfig(self.canvas_texts_list[self.current_index][y][x], text=sym, fill=map_data['grid'][y][x]['color'])
            # Auto-select after place
            self.selected_x = x
            self.selected_y = y
            cell = map_data['grid'][y][x]
            self.prop_color_var.set(cell['color'])
            self.prop_texture_var.set(cell['texture'])
            self.prop_name_var.set(cell['name'])
            self.prop_value_var.set(str(cell['value']))
            self.prop_depth_var.set(str(cell['depth']))
            self.prop_height_var.set(str(cell['height']))
            self.prop_3d_var.set(cell['3d'])
            self.property_frame.pack(fill=tk.BOTH, expand=True)
            self.update_edit_menu_states()
            self.set_dirty()

    def handle_right_click(self, event):
        canvas = self.canvases[self.current_index]
        x = int(canvas.canvasx(event.x) // self.cell_size)
        y = int(canvas.canvasy(event.y) // self.cell_size)
        map_data = self.maps[self.current_index]
        if 0 <= x < map_data['width'] and 0 <= y < map_data['height']:
            if self.select_mode or self.current_symbol.get() == '--':
                self.select_cell(event)
            else:
                self.undo_stacks[self.current_index].append(copy.deepcopy(map_data['grid']))
                if len(self.undo_stacks[self.current_index]) > 69:
                    self.undo_stacks[self.current_index].pop(0)
                self.redo_stacks[self.current_index].clear()
                map_data['grid'][y][x]['symbol'] = ' '
                canvas.itemconfig(self.canvas_texts_list[self.current_index][y][x], text=' ', fill='white')
                self.set_dirty()
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
            cell = map_data['grid'][y][x]
            self.prop_color_var.set(cell['color'])
            self.prop_texture_var.set(cell['texture'])
            self.prop_name_var.set(cell['name'])
            self.prop_value_var.set(str(cell['value']))
            self.prop_depth_var.set(str(cell['depth']))
            self.prop_height_var.set(str(cell['height']))
            self.prop_3d_var.set(cell['3d'])
            self.property_frame.pack(fill=tk.BOTH, expand=True)
            if self.lock_var.get() and cell['symbol'] == self.locked_symbol:
                self.apply_properties()

    def toggle_lock(self):
        self.lock_var.set(not self.lock_var.get())
        if self.lock_var.get():
            self.lock_button.config(bg="#333333", fg="red")
            if self.selected_x is not None and self.selected_y is not None:
                self.locked_symbol = self.maps[self.current_index]['grid'][self.selected_y][self.selected_x]['symbol']
                self.locked_properties = {
                    'color': self.prop_color_var.get(),
                    'texture': self.prop_texture_var.get(),
                    'name': self.prop_name_var.get(),
                    'value': int(self.prop_value_var.get()) if self.prop_value_var.get() else 0,
                    'depth': int(self.prop_depth_var.get()) if self.prop_depth_var.get() else 1,
                    'height': int(self.prop_height_var.get()) if self.prop_height_var.get() else 1,
                    '3d': self.prop_3d_var.get()
                }
        else:
            self.lock_button.config(bg="#555555", fg="white")
            self.locked_symbol = None
            self.locked_properties = None

    def apply_properties(self):
        color = self.prop_color_var.get()
        texture = self.prop_texture_var.get()
        name = self.prop_name_var.get()
        value_str = self.prop_value_var.get()
        depth_str = self.prop_depth_var.get()
        height_str = self.prop_height_var.get()
        threed = self.prop_3d_var.get()
        map_data = self.maps[self.current_index]
        grid = map_data['grid']
        is_multi = self.selected_region and (self.selected_region[2] - self.selected_region[0] > 1 or self.selected_region[3] - self.selected_region[1] > 1)
        if is_multi:
            if not messagebox.askyesno("Confirm", "Attaching Mass Selected Properties will change the properties for all selected objects. Do you wish to continue?"):
                return
            minx, miny, maxx, maxy = self.selected_region
            self.undo_stacks[self.current_index].append(copy.deepcopy(grid))
            if len(self.undo_stacks[self.current_index]) > 69:
                self.undo_stacks[self.current_index].pop(0)
            self.redo_stacks[self.current_index].clear()
            for y in range(miny, maxy):
                for x in range(minx, maxx):
                    if color: grid[y][x]['color'] = color
                    if texture: grid[y][x]['texture'] = texture
                    if name: grid[y][x]['name'] = name
                    if value_str: grid[y][x]['value'] = int(value_str)
                    if depth_str: grid[y][x]['depth'] = int(depth_str)
                    if height_str: grid[y][x]['height'] = int(height_str)
                    grid[y][x]['3d'] = threed # always set bool
                    canvas = self.canvases[self.current_index]
                    canvas.itemconfig(self.canvas_texts_list[self.current_index][y][x], fill=grid[y][x]['color'])
        else:
            if self.selected_x is not None and self.selected_y is not None:
                self.undo_stacks[self.current_index].append(copy.deepcopy(grid))
                if len(self.undo_stacks[self.current_index]) > 69:
                    self.undo_stacks[self.current_index].pop(0)
                self.redo_stacks[self.current_index].clear()
                value = int(value_str) if value_str else 0
                depth = int(depth_str) if depth_str else 1
                height = int(height_str) if height_str else 1
                grid[self.selected_y][self.selected_x]['color'] = color
                grid[self.selected_y][self.selected_x]['texture'] = texture
                grid[self.selected_y][self.selected_x]['name'] = name
                grid[self.selected_y][self.selected_x]['value'] = value
                grid[self.selected_y][self.selected_x]['depth'] = depth
                grid[self.selected_y][self.selected_x]['height'] = height
                grid[self.selected_y][self.selected_x]['3d'] = threed
                canvas = self.canvases[self.current_index]
                canvas.itemconfig(self.canvas_texts_list[self.current_index][self.selected_y][self.selected_x], fill=color)
                if self.lock_var.get():
                    self.locked_properties = {
                        'color': color,
                        'texture': texture,
                        'name': name,
                        'value': value,
                        'depth': depth,
                        'height': height,
                        '3d': threed
                    }
                    for y in range(map_data['height']):
                        for x in range(map_data['width']):
                            if grid[y][x]['symbol'] == self.locked_symbol:
                                grid[y][x]['color'] = color
                                grid[y][x]['texture'] = texture
                                grid[y][x]['name'] = name
                                grid[y][x]['value'] = value
                                grid[y][x]['depth'] = depth
                                grid[y][x]['height'] = height
                                grid[y][x]['3d'] = threed
                                canvas.itemconfig(self.canvas_texts_list[self.current_index][y][x], fill=color)
        self.update_edit_menu_states()
        self.set_dirty()

    def deselect(self):
        self.selected_x = None
        self.selected_y = None
        if not self.lock_var.get():
            self.property_frame.pack_forget()
        self.deselect_multi()

    def insert_phrase(self, phrase):
        if self.arc_data_text:
            self.arc_data_text.insert(tk.INSERT, phrase + " ")

    def new_arc(self):
        self.clear_arc_fields()
        self.current_arc_index = None # New mode
        self.last_arc_state = self.save_arc_state()

    def save_arc(self):
        arc_data_raw = self.arc_data_text.get("1.0", tk.END).strip()
        allowed_chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789[](){}~*,#!$'+%/\\^_--> "
        arc_data = ''.join(c for c in arc_data_raw if c in allowed_chars)
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
        if self.current_arc_index is None:
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
            arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
            with open(file, 'w') as f:
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
        self.load_arc_file(add_to_list=False)

    def load_arc_to_map(self):
        self.load_arc_file(add_to_list=True, auto_select=self.is_builder_default())

    def load_arc_file(self, add_to_list=False, auto_select=False):
        file = filedialog.askopenfilename(initialdir=self.last_dir['arc_load'], filetypes=[("Arcs files", "*.arcs")])
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
                if (add_to_list and auto_select) or (not add_to_list):
                    self.load_arc_dict_to_fields(arc)
                    if add_to_list:
                        self.current_arc_index = len(self.arcs) - 1
                    else:
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
        for i in range(len(parts)):
            if i < len(self.arc_estimated_parts):
                self.arc_estimated_parts[i].set(parts[i])
        self.arc_zone_type_var.set(arc['zone_type'])
        self.arc_start_msg_var.set(arc['start_msg'])
        map_str = arc['map']
        self.arc_map_type_var.set('Import' if map_str.startswith('$') else 'Generate')
        self.arc_map_var.set(map_str[1:-1])
        self.arc_data_text.delete("1.0", tk.END)
        self.arc_data_text.insert("1.0", arc['arc_data'])
        self.arc_confirm_msg_var.set(arc['confirm_msg'])
        self.last_arc_state = self.save_arc_state()

    def save_selected_arc(self):
        if self.current_arc_index is None:
            messagebox.showerror("No Arc", "No selected arc")
            return
        arc = self.arcs[self.current_arc_index]
        filename = self.get_arc_filename(arc) + '.arcs'
        file = filedialog.asksaveasfilename(defaultextension=".arcs", filetypes=[("Arcs files", "*.arcs")], initialfile=filename)
        if file:
            arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
            with open(file, 'w') as f:
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
                    all_arcs[a['name']] = a
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

    def load_arc(self):
        file = filedialog.askopenfilename(initialdir=self.last_dir['arc_load'], filetypes=[("MapD files", "*.mapd"), ("Arcs files", "*.arcs")])
        if file:
            self.last_dir['arc_load'] = os.path.dirname(file)
            with open(file, 'r') as f:
                lines = f.readlines()
            arc_lines = lines
            if file.endswith('.mapd'):
                if lines and lines[0].strip().startswith('import {'):
                    arc_lines = lines[1:]
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
                        self.arc_list.insert(tk.END, arc['name'])
            self.set_dirty()

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

    def remove_all_edits(self):
        self.clear_arc_fields()

    def exit_without_save_arc(self):
        self.clear_arc_fields()
        self.current_arc_index = None

    def save_and_exit_arc(self):
        self.save_arc()
        self.clear_arc_fields()
        self.current_arc_index = None

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
        return {
            'name': self.arc_name_var.get(),
            'estimated_type': self.arc_estimated_type_var.get(),
            'estimated_parts': [v.get() for v in self.arc_estimated_parts],
            'zone_type': self.arc_zone_type_var.get(),
            'start_msg': self.arc_start_msg_var.get(),
            'map': self.arc_map_var.get(),
            'map_type': self.arc_map_type_var.get(),
            'arc_data': self.arc_data_text.get("1.0", tk.END).strip(),
            'confirm_msg': self.arc_confirm_msg_var.get()
        }

    def set_arc_state(self, state):
        self.arc_name_var.set(state['name'])
        self.arc_estimated_type_var.set(state['estimated_type'])
        self.update_est_picker()
        for i, p in enumerate(state['estimated_parts']):
            self.arc_estimated_parts[i].set(p)
        self.arc_zone_type_var.set(state['zone_type'])
        self.arc_start_msg_var.set(state['start_msg'])
        self.arc_map_var.set(state['map'])
        self.arc_map_type_var.set(state['map_type'])
        self.arc_data_text.delete("1.0", tk.END)
        self.arc_data_text.insert("1.0", state['arc_data'])
        self.arc_confirm_msg_var.set(state['confirm_msg'])

    def apply_size(self, index):
        var_dict = self.var_dicts[index]
        new_width = var_dict['width_var'].get()
        new_height = var_dict['height_var'].get()
        map_data = self.maps[index]
        if new_width != map_data['width'] or new_height != map_data['height']:
            new_grid = [[{'symbol': ' ', 'color': 'white', 'texture': '', 'name': '', 'value': 0, 'depth': 1, 'height': 1, '3d': False} for _ in range(new_width)] for _ in range(new_height)]
            for y in range(min(map_data['height'], new_height)):
                for x in range(min(map_data['width'], new_width)):
                    new_grid[y][x] = map_data['grid'][y][x].copy()
            map_data['grid'] = new_grid
            map_data['width'] = new_width
            map_data['height'] = new_height
            self.redraw_canvas(index)
            self.center_canvas(index)
            self.set_dirty()

    def ask_save(self):
        if self.user_active > 0:
            return False
        if self.cheating_detected:
            messagebox.showwarning("Cheating Detected", f"Cheating action noticed: {self.cheating_reason}")
            self.user_active = -9
            return False
        if messagebox.askyesno("Save Current", "Do you want to save the current work before proceeding?"):
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
                map_str = '\n'.join(''.join(cell['symbol'] for cell in row) for row in map_data['grid'])
                footer = f"{map_type}; {name}; {maker}; {system}"
                # Add properties array
                props = []
                for y in range(map_data['height']):
                    for x in range(map_data['width']):
                        cell = map_data['grid'][y][x]
                        if not (cell['symbol'] == ' ' and cell['color'] == 'white' and cell['texture'] == '' and cell['name'] == '' and cell['value'] == 0 and cell['depth'] == 1 and cell['height'] == 1 and not cell['3d']):
                            sym = cell['symbol']
                            text_part = f'"{cell["color"]}";"{cell["name"]}";"{cell["texture"]}";'
                            non_text = f'({x},1,{y},1,{cell["height"]}){cell["value"]}'
                            prop_str = f'{sym}[{text_part}{non_text}]'
                            props.append(prop_str)
                props_str = ' ' + ' '.join(props) if props else ''
                # Add arcs
                arcs_str = ''
                if map_data['attached_arcs']:
                    arc_lines = ['||'.join([a[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']]) for a in map_data['attached_arcs']]
                    arcs_str = ';arcs::' + ';'.join(arc_lines)
                content = header + '\n' + map_str + '\n' + footer + props_str + arcs_str
                with open(file, 'w') as f:
                    f.write(content)
                self.dirty = False
                self.user_active = 1
        elif file_type == 'mapd':
            file = filedialog.asksaveasfilename(defaultextension=".mapd", filetypes=[("MapD files", "*.mapd")])
            if file:
                dir_path = os.path.dirname(file)
                map_names = []
                for i, map_data in enumerate(self.maps):
                    var_dict = self.var_dicts[i]
                    tmap_file = os.path.join(dir_path, map_data['name'] + '.tmap')
                    openings = var_dict['openings_var'].get().ljust(7, '0')
                    map_type = var_dict['type_var'].get()
                    name = var_dict['name_var'].get()
                    maker = var_dict['maker_var'].get()
                    system = map_data['system']
                    header = f"{openings} {map_data['width']}x{map_data['height']}"
                    map_str = '\n'.join(''.join(cell['symbol'] for cell in row) for row in map_data['grid'])
                    footer = f"{map_type}; {name}; {maker}; {system}"
                    # Add properties array
                    props = []
                    for y in range(map_data['height']):
                        for x in range(map_data['width']):
                            cell = map_data['grid'][y][x]
                            if not (cell['symbol'] == ' ' and cell['color'] == 'white' and cell['texture'] == '' and cell['name'] == '' and cell['value'] == 0 and cell['depth'] == 1 and cell['height'] == 1 and not cell['3d']):
                                sym = cell['symbol']
                                text_part = f'"{cell["color"]}";"{cell["name"]}";"{cell["texture"]}";'
                                non_text = f'({x},1,{y},1,{cell["height"]}){cell["value"]}'
                                prop_str = f'{sym}[{text_part}{non_text}]'
                                props.append(prop_str)
                    props_str = ' ' + ' '.join(props) if props else ''
                    # Add arcs
                    arcs_str = ''
                    if map_data['attached_arcs']:
                        arc_lines = ['||'.join([a[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']]) for a in map_data['attached_arcs']]
                        arcs_str = ';arcs::' + ';'.join(arc_lines)
                    content = header + '\n' + map_str + '\n' + footer + props_str + arcs_str
                    with open(tmap_file, 'w') as f:
                        f.write(content)
                    map_names.append(name)
                import_header = 'import {' + ', '.join(f'"{n}"' for n in map_names) + '}\n'
                arc_lines = []
                for arc in self.arcs:
                    arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
                    arc_lines.append(arc_line)
                content = import_header + '\n'.join(arc_lines)
                with open(file, 'w') as f:
                    f.write(content)
                self.dirty = False
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
            parts = header.split()
            openings = parts[0].replace('#', '2')
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
                min_indent = min(len(line) - len(line.lstrip()) for line in map_lines if line.strip())
                grid = [[{'symbol': ' ', 'color': 'white', 'texture': '', 'name': '', 'value': 0, 'depth': 1, 'height': 1, '3d': False} for _ in range(width)] for _ in range(height)]
                for y, line in enumerate(map_lines):
                    line = line[min_indent:]
                    for x, char in enumerate(line):
                        if x < width:
                            grid[y][x]['symbol'] = char
                    for x in range(len(line), width):
                        grid[y][x]['symbol'] = ' '
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
                        arcs_str = rest[props_end + 1:].strip()
                    else:
                        props_str = rest.strip()
                else:
                    props_str = rest.strip()
                props = re.findall(r'(.)\["([^"]*)";"([^"]*)";"([^"]*)";\((\d+),(\d+),(\d+),(\d+),(\d+)\)(\d+)\]', props_str)
                for sym, color, name_, texture, x, w, y, d, z, val in props:
                    x, y = int(x), int(y)
                    if 0 <= x < width and 0 <= y < height:
                        cell = grid[y][x]
                        cell['symbol'] = sym
                        cell['color'] = color
                        cell['name'] = name_
                        cell['texture'] = texture
                        cell['value'] = int(val)
                        cell['depth'] = int(d)
                        cell['height'] = int(z)
                        cell['3d'] = False # assume
                if 'arcs_str' in locals():
                    if arcs_str.startswith('arcs::'):
                        arcs_str = arcs_str[6:]
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
        file = f"auto_save_{datetime.now().strftime('%Y%m%d_%H%M%S')}.mapd"
        dir_path = os.getcwd()
        map_names = []
        for i, map_data in enumerate(self.maps):
            var_dict = self.var_dicts[i]
            tmap_file = os.path.join(dir_path, map_data['name'] + '.tmap')
            openings = var_dict['openings_var'].get().ljust(7, '0')
            map_type = var_dict['type_var'].get()
            name = var_dict['name_var'].get()
            maker = var_dict['maker_var'].get()
            system = map_data['system']
            header = f"{openings} {map_data['width']}x{map_data['height']}"
            map_str = '\n'.join(''.join(cell['symbol'] for cell in row) for row in map_data['grid'])
            footer = f"{map_type}; {name}; {maker}; {system}"
            # Add properties array
            props = []
            for y in range(map_data['height']):
                for x in range(map_data['width']):
                    cell = map_data['grid'][y][x]
                    if not (cell['symbol'] == ' ' and cell['color'] == 'white' and cell['texture'] == '' and cell['name'] == '' and cell['value'] == 0 and cell['depth'] == 1 and cell['height'] == 1 and not cell['3d']):
                        sym = cell['symbol']
                        text_part = f'"{cell["color"]}";"{cell["name"]}";"{cell["texture"]}";'
                        non_text = f'({x},1,{y},1,{cell["height"]}){cell["value"]}'
                        prop_str = f'{sym}[{text_part}{non_text}]'
                        props.append(prop_str)
            props_str = ' ' + ' '.join(props) if props else ''
            # Add arcs
            arcs_str = ''
            if map_data['attached_arcs']:
                arc_lines = ['||'.join([a[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']]) for a in map_data['attached_arcs']]
                arcs_str = ';arcs::' + ';'.join(arc_lines)
            content = header + '\n' + map_str + '\n' + footer + props_str + arcs_str
            with open(tmap_file, 'w') as f:
                f.write(content)
            map_names.append(name)
        import_header = 'import {' + ', '.join(f'"{n}"' for n in map_names) + '}\n'
        arc_lines = []
        for arc in self.arcs:
            arc_line = '||'.join([arc[k] for k in ['name', 'estimated', 'zone_type', 'start_msg', 'map', 'arc_data', 'confirm_msg']])
            arc_lines.append(arc_line)
        content = import_header + '\n'.join(arc_lines)
        with open(file, 'w') as f:
            f.write(content)
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
            canvas.create_line(i * self.cell_size, 0, i * self.cell_size, h * self.cell_size + 40, fill="#444444")
        for j in range(h + 1):
            canvas.create_line(0, j * self.cell_size, w * self.cell_size, j * self.cell_size, fill="#444444")
        canvas_texts = [[None for _ in range(w)] for _ in range(h)]
        for y in range(h):
            for x in range(w):
                cell = map_data['grid'][y][x]
                text_id = canvas.create_text((x + 0.5) * self.cell_size, (y + 0.5) * self.cell_size, text=cell['symbol'], font=("Courier", 12), fill=cell['color'])
                canvas_texts[y][x] = text_id
        self.canvas_texts_list[index] = canvas_texts
        self.draw_attached_dots(index)
        # Re-draw selection if exists
        if self.selected_region and self.current_index == index:
            minx, miny, maxx, maxy = self.selected_region
            self.selected_rects = []
            for yy in range(miny, maxy):
                for xx in range(minx, maxx):
                    rect_id = canvas.create_rectangle(xx * self.cell_size, yy * self.cell_size, (xx + 1) * self.cell_size, (yy + 1) * self.cell_size, outline='yellow', width=1)
                    self.selected_rects.append(rect_id)

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

    def undo(self):
        if self.undo_stacks[self.current_index]:
            self.redo_stacks[self.current_index].append(copy.deepcopy(self.maps[self.current_index]['grid']))
            if len(self.redo_stacks[self.current_index]) > 69:
                self.redo_stacks[self.current_index].pop(0)
            self.maps[self.current_index]['grid'] = self.undo_stacks[self.current_index].pop()
            self.redraw_canvas(self.current_index)
            self.update_edit_menu_states()

    def redo(self):
        if self.redo_stacks[self.current_index]:
            self.undo_stacks[self.current_index].append(copy.deepcopy(self.maps[self.current_index]['grid']))
            if len(self.undo_stacks[self.current_index]) > 69:
                self.undo_stacks[self.current_index].pop(0)
            self.maps[self.current_index]['grid'] = self.redo_stacks[self.current_index].pop()
            self.redraw_canvas(self.current_index)
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
        canvas = tk.Canvas(preview_win, bg="#222222", width=800, height=600, scrollregion=(-self.padding, -self.padding, map_data['width'] * self.cell_size + self.padding, map_data['height'] * self.cell_size + 40 + self.padding))
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
            canvas.create_line(i * self.cell_size, 0, i * self.cell_size, h * self.cell_size + 40, fill="#444444")
        for j in range(h + 1):
            canvas.create_line(0, j * self.cell_size, w * self.cell_size, j * self.cell_size, fill="#444444")
        for y in range(h):
            for x in range(w):
                cell = map_data['grid'][y][x]
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

    def preview_dictionary(self):
        # TODO: implement preview for entire dictionary, stitching maps based on openings and arcs
        # TODO: use enter/exit guide to build how to generate map sections
        # TODO: consider user's arc data attached to the map
        # TODO: add way to mark arcs attached to maps in arc selector
        messagebox.showinfo("Preview Dictionary", "TODO: implement preview for dictionary.")

    def main_menu(self):
        messagebox.showinfo("Main Menu", "Returning to main menu (placeholder).")
        # TODO: implement main menu for larger program

    def handle_scroll(self, event, delta=None, widget=None):
        w = widget or self.root.focus_get()
        if isinstance(w, (tk.Canvas, tk.Listbox, tk.Text)):
            if delta is None:
                delta = event.delta if event.delta else (120 if event.num == 4 else -120)
            if delta > 0:
                w.yview_scroll(-1, "units")
            else:
                w.yview_scroll(1, "units")

    def handle_shift_scroll(self, event, delta=None, widget=None):
        w = widget or self.root.focus_get()
        if isinstance(w, (tk.Canvas, tk.Listbox, tk.Text)):
            if delta is None:
                delta = event.delta if event.delta else (120 if event.num == 4 else -120)
            if delta > 0:
                w.xview_scroll(-1, "units")
            else:
                w.xview_scroll(1, "units")

    def handle_page_up(self, event, widget=None):
        w = widget or self.root.focus_get()
        if isinstance(w, (tk.Canvas, tk.Listbox, tk.Text)):
            w.yview_scroll(-1, "pages")

    def handle_page_down(self, event, widget=None):
        w = widget or self.root.focus_get()
        if isinstance(w, (tk.Canvas, tk.Listbox, tk.Text)):
            w.yview_scroll(1, "pages")

    def handle_tab(self, event):
        widget = self.root.focus_get()
        if isinstance(widget, tk.Listbox):
            # Switch to next item in listbox
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
        # Cycle through sections
        self.current_section_index = (self.current_section_index + 1) % len(self.focusable_sections)
        self.focusable_sections[self.current_section_index].focus_set()

    def select_all(self, event):
        event.widget.select_range(0, tk.END)
        event.widget.icursor(tk.END)
        return "break"

    def show_help(self, filename):
        help_dir = 'help'
        if not os.path.exists(help_dir):
            os.mkdir(help_dir)
        filename = os.path.join(help_dir, filename)
        if os.path.exists(filename.replace('help/', '')):
            os.rename(filename.replace('help/', ''), filename)
        if not os.path.exists(filename):
            # Default content if not exist
            with open(filename, 'w') as f:
                f.write("No content available.")
        with open(filename, 'r') as f:
            text = f.read()
        win = tk.Toplevel(self.root)
        win.title(os.path.basename(filename))
        text_widget = tk.Text(win, wrap=tk.WORD, bg="#444444", fg="white")
        text_widget.insert(tk.END, text)
        text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vscroll = tk.Scrollbar(win, orient=tk.VERTICAL, command=text_widget.yview)
        vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        hscroll = tk.Scrollbar(win, orient=tk.HORIZONTAL, command=text_widget.xview)
        hscroll.pack(side=tk.BOTTOM, fill=tk.X)
        text_widget.config(yscrollcommand=vscroll.set, xscrollcommand=hscroll.set)
        text_widget.bind("<MouseWheel>", lambda e: self.handle_scroll(e, widget=text_widget))
        text_widget.bind("<Shift-MouseWheel>", lambda e: self.handle_shift_scroll(e, widget=text_widget))
        text_widget.bind("<Button-4>", lambda e: self.handle_scroll(e, delta=120, widget=text_widget))
        text_widget.bind("<Button-5>", lambda e: self.handle_scroll(e, delta=-120, widget=text_widget))
        text_widget.bind("<Shift-Button-4>", lambda e: self.handle_shift_scroll(e, delta=120, widget=text_widget))
        text_widget.bind("<Shift-Button-5>", lambda e: self.handle_shift_scroll(e, delta=-120, widget=text_widget))
        text_widget.bind("<Key-Page_Up>", lambda e: self.handle_page_up(e, widget=text_widget))
        text_widget.bind("<Key-Page_Down>", lambda e: self.handle_page_down(e, widget=text_widget))
        text_widget.bind("<Up>", lambda e: text_widget.yview_scroll(-1, "units"))
        text_widget.bind("<Down>", lambda e: text_widget.yview_scroll(1, "units"))
        text_widget.bind("<Left>", lambda e: text_widget.xview_scroll(-1, "units"))
        text_widget.bind("<Right>", lambda e: text_widget.xview_scroll(1, "units"))
        text_widget.bind("w", lambda e: text_widget.yview_scroll(-1, "units"))
        text_widget.bind("s", lambda e: text_widget.yview_scroll(1, "units"))
        text_widget.bind("a", lambda e: text_widget.xview_scroll(-1, "units"))
        text_widget.bind("d", lambda e: text_widget.xview_scroll(1, "units"))

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

    def edit_attached_arc(self, idx, win):
        arc = self.maps[self.current_index]['attached_arcs'][idx]
        self.load_arc_dict_to_fields(arc)
        self.current_arc_index = -1  # Special for attached edit
        win.destroy()
        # On save_arc, check if current_arc_index == -1, update attached
    def save_arc(self):
        # existing
        if self.current_arc_index == -1:
            # Update attached
            for a in self.maps[self.current_index]['attached_arcs']:
                if a['name'] == arc_dict['name']:
                    a.update(arc_dict)
                    break
            self.current_arc_index = None
        # existing else
        self.set_dirty()

    def detach_arc(self, idx, win):
        arc = self.maps[self.current_index]['attached_arcs'].pop(idx)
        self.draw_attached_dots(self.current_index)
        in_arcs = any(a['name'] == arc['name'] for a in self.arcs)
        if not in_arcs:
            self.deleted_arcs.append((None, copy.deepcopy(arc)))
        self.set_dirty()
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

    def set_dirty(self):
        self.dirty = True
        self.user_active = 0

if __name__ == "__main__":
    root = tk.Tk()
    app = MapMaker(root)
    root.mainloop()
