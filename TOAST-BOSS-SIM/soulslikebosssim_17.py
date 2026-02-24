import tkinter as tk
from tkinter import colorchooser
from math import sin, cos, tan, pi, radians, sqrt, atan2
import time
import sys
import ctypes
import random
import copy
import json
sys.setrecursionlimit(2000)

# GJK helper functions
def cross(a, b):
    return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]

def dot(a, b):
    return sum(ai*bi for ai,bi in zip(a,b))

def sub(a, b):
    return [ai-bi for ai,bi in zip(a,b)]

def add(a, b):
    return [ai+bi for ai,bi in zip(a,b)]

def scal_mul(s, a):
    return [s*ai for ai in a]

def neg(a):
    return [-ai for ai in a]

def norm_sq(a):
    return dot(a,a)

def support(shape, d):
    if shape['type'] == 'sphere':
        pos = shape['pos']
        r = shape['radius']
        n = sqrt(norm_sq(d))
        if n == 0: return pos[:]
        nd = scal_mul(1/n, d)
        return add(pos, scal_mul(r, nd))
    elif shape['type'] == 'poly':
        verts = shape['verts']
        pos = shape['pos']
        scale = shape['scale']
        max_dot = -float('inf')
        max_v = None
        for v in verts:
            world_v = add(pos, scal_mul(scale, v))
            cur_dot = dot(world_v, d)
            if cur_dot > max_dot:
                max_dot = cur_dot
                max_v = world_v
        return max_v

def update_line(simplex, d):
    b, a = simplex
    ab = sub(b, a)
    ao = neg(a)
    ab_ao = cross(ab, ao)
    new_d = cross(ab_ao, ab)
    if norm_sq(new_d) < 1e-6:
        return [], d
    d[:] = new_d
    return simplex, d

def update_triangle(simplex, d):
    c, b, a = simplex
    ab = sub(b, a)
    ac = sub(c, a)
    ao = neg(a)
    abc = cross(ab, ac)
    abc_ac = cross(abc, ac)
    if dot(abc_ac, ao) > 0:
        return update_line([c, a], d)
    abc_ab = cross(ab, abc)
    if dot(abc_ab, ao) > 0:
        return update_line([b, a], d)
    if dot(abc, ao) > 0:
        d[:] = abc
        return simplex, d
    else:
        d[:] = neg(abc)
        return [c, b, a], d

def update_tetra(simplex, d):
    dpt, c, b, a = simplex
    ab = sub(b, a)
    ac = sub(c, a)
    ad = sub(dpt, a)
    ao = neg(a)
    abc = cross(ab, ac)
    if dot(abc, ao) > 0:
        return update_triangle([c, b, a], d)
    abd = cross(ab, ad)
    if dot(abd, ao) > 0:
        return update_triangle([b, dpt, a], d)
    acd = cross(ac, ad)
    if dot(acd, ao) > 0:
        return update_triangle([c, dpt, a], d)
    return [], d

def tetra_contains_origin(simplex):
    a, b, c, d = simplex
    ab = sub(b, a)
    ac = sub(c, a)
    ad = sub(d, a)
    ao = neg(a)
    if dot(cross(ab, ac), ao) < 0: return False
    if dot(cross(ab, ad), ao) < 0: return False
    if dot(cross(ac, ad), ao) < 0: return False
    return True

def gjk_intersect(shape1, shape2):
    d = [1.0, 0.0, 0.0]
    simplex = []
    a = sub(support(shape1, d), support(shape2, neg(d)))
    if dot(a, d) < 0: return False
    simplex.append(a)
    d = neg(a)
    if norm_sq(d) < 1e-6: d = [1.0, 0.0, 0.0]
    iter = 0
    while iter < 32:
        a = sub(support(shape1, d), support(shape2, neg(d)))
        if dot(a, d) < 0: return False
        simplex.append(a)
        if len(simplex) == 4:
            if tetra_contains_origin(simplex): return True
            simplex, d = update_tetra(simplex, d)
            if not simplex: return False
        elif len(simplex) == 3:
            simplex, d = update_triangle(simplex, d)
            if not simplex: return False
        elif len(simplex) == 2:
            simplex, d = update_line(simplex, d)
            if not simplex: return False
        iter += 1
    return False

ACTION_LIST = [
    'north', 'south', 'west', 'east', 'northwest', 'northeast', 'southwest', 'southeast',
    'mouse-specific', 'jump', 'dodge', 'defense stance', 'quick defend', 'sprint',
    'attack', 'strong-attack', 'charge attack', 'slide', 'front-flip', 'wall-run', 'double jump'
]

class Game:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Souls-Like Boss Simulator")
        self.screen_mode = 'normal'
        self.width = 800
        self.height = 600
        self.canvas = tk.Canvas(self.root, width=self.width, height=self.height, bg='black')
        self.canvas.pack()

        self.root.bind('<KeyPress>', self.key_press)
        self.root.bind('<KeyRelease>', self.key_release)
        self.root.bind('<Button-1>', self.left_press)
        self.root.bind('<ButtonRelease-1>', self.left_release)
        self.root.bind('<Button-3>', self.right_press)
        self.root.bind('<ButtonRelease-3>', self.right_release)
        self.root.bind('<Motion>', self.mouse_motion)
        self.root.bind('<Escape>', self.toggle_pause)

        self.mouse_captured = True
        self.center_x = self.width // 2
        self.center_y = self.height // 2
        self.root.attributes('-fullscreen', False)
        self.hide_cursor()
        self.last_warp = 0
        self.center_mouse()

        self.running = True
        self.paused = False
        self.level = 0
        self.exp = 0
        self.exp_needed = 3
        self.health = 100
        self.max_health = 100
        self.stamina = 100
        self.max_stamina = 100
        self.magic = 50
        self.max_magic = 50
        self.attack_level = 1
        self.defense_level = 1
        self.skill_level = 1
        self.life_steal = 0
        self.armor = 0
        self.elements = {'cold': 0, 'hot': 0, 'poison': 0, 'dry': 0, 'humid': 0, 'physical': 1}
        self.weapon = 'fists'
        self.next_weapon = 'sword'
        self.equip = {'head': None, 'chest': 'basic', 'legs': None}
        self.progression = ['armor', 'weapon', 'skill_point']
        self.choose_gain = False
        self.choice_text_id = None
        self.bosses = []
        self.projectiles = []
        self.objects = []
        self.pickups = []
        self.view_mode = '2d_top'
        self.player_color = '#0000ff'

        self.vel_x = self.vel_y = self.vel_z = 0
        self.on_ground = True
        self.eye_height = 1.8
        self.player_radius = 1.5
        self.gravity = 30.0
        self.jump_speed = 12.0
        self.max_move_speed = 6.0
        self.move_accel = 25.0
        self.air_move_accel = 15.0
        self.friction = 15.0

        self.cam_pos = [0, 1.8, 0]
        self.yaw = 0
        self.pitch = 0
        self.target_yaw = 0
        self.target_pitch = 0
        self.fov = 90
        self.turn_speed = 0.003
        self.smooth_factor = 0.2
        self.invert_y = False
        self.invert_x = False

        self.keys = set()
        self.e_pressed = False

        self.arena_radius = 100.0
        self.arena_height = 50.0
        self.arena_sides = 8
        self.themes = ['office', 'volcano', 'corn field', 'skyscraper', 'furniture']

        self.particles = []
        self.max_particles = 100
        self.trails = []

        self.left_held = self.right_held = False
        self.left_hold_start = self.right_hold_start = 0
        self.last_left_click = self.last_right_click = 0
        self.invulnerable_time = 0
        self.invulnerable_duration = 0.5
        self.left_charge = self.right_charge = 0
        self.max_left_charge_time = 1.0
        self.max_right_charge_time = 1.5

        self.left_single_action = 'attack'
        self.left_double_action = 'strong-attack'
        self.left_hold_action = 'charge attack'
        self.right_single_action = 'dodge'
        self.right_double_action = 'jump'
        self.right_hold_action = 'defense stance'

        self.stats_text_id = None
        self.pause_menu = None
        self.tutorial_frame = None
        self.boss_id_counter = 0
        self.tutorial_flag = 1

        self.light_dir = [0.5, 1.0, -0.5]
        n = sqrt(dot(self.light_dir, self.light_dir))
        if n > 0: self.light_dir = scal_mul(1/n, self.light_dir)

        self.creature_types = ['Smiler', 'Hound', 'Partygoer', 'Skin-Stealer', 'Deathmoth', 'Clumps', 'Dullers', 'Jerry', 'Facelings', 'Wretches']

        self.report = []

        self.load_game()

        self.generate_arena()
        self.generate_boss()

        self.last_time = time.time()

        if self.level == 0 and self.tutorial_flag == 1:
            self.paused = True
            self.mouse_captured = False
            self.show_cursor()
            self.show_tutorial()
        else:
            if self.level == 0:
                self.level = 1
            self.paused = False
            self.mouse_captured = True
            self.hide_cursor()

        self.loop()

    def hide_cursor(self): self.root.config(cursor='none')
    def show_cursor(self): self.root.config(cursor='')

    def center_mouse(self):
        current = time.time()
        if self.mouse_captured and current - self.last_warp > 0.05:
            self.last_warp = current
            try:
                x = self.root.winfo_rootx() + self.center_x
                y = self.root.winfo_rooty() + self.center_y
                if sys.platform == 'win32':
                    ctypes.windll.user32.SetCursorPos(x, y)
                self.root.event_generate("<Motion>", warp=True, x=self.center_x, y=self.center_y)
            except: pass

    def mouse_motion(self, event):
        if not self.mouse_captured or self.paused: return
        dx = event.x - self.center_x
        dy = event.y - self.center_y
        if self.invert_x: dx = -dx
        invert_mult = -1 if self.invert_y else 1
        self.target_yaw = (self.target_yaw - dx * self.turn_speed) % (2 * pi)
        self.target_pitch = max(min(self.target_pitch - dy * self.turn_speed * invert_mult, pi/2 - 0.01), -pi/2 + 0.01)
        self.center_mouse()

    def key_press(self, event):
        key = event.keysym.lower()
        self.keys.add(key)
        if key == 'e': self.e_pressed = True
        if self.choose_gain:
            if key == 'h':
                self.max_health += 20 + self.level // 10
                self.health = self.max_health
                self.choose_gain = False
                if self.choice_text_id: self.canvas.delete(self.choice_text_id)
                self.choice_text_id = None
            elif key == 's':
                self.max_stamina += 20 + self.level // 10
                self.stamina = self.max_stamina
                self.choose_gain = False
                if self.choice_text_id: self.canvas.delete(self.choice_text_id)
                self.choice_text_id = None
            elif key in ['1','2','3','4','5','6']:
                elem_map = {'1':'cold','2':'hot','3':'poison','4':'dry','5':'humid','6':'physical'}
                self.elements[elem_map[key]] += 1
                self.choose_gain = False

    def key_release(self, event):
        key = event.keysym.lower()
        self.keys.discard(key)
        if key == 'e': self.e_pressed = False

    def left_press(self, event):
        current = time.time()
        if current - self.last_left_click < 0.3:
            self.perform_action(self.left_double_action)
        else:
            self.perform_action(self.left_single_action)
        self.last_left_click = current
        self.left_held = True
        self.left_hold_start = current
        if self.right_held:
            self.left_charge += self.right_charge * 0.5
            self.right_charge = 0
            self.do_attack_in_defense()

    def left_release(self, event):
        if self.left_held and time.time() - self.left_hold_start > 0.2:
            self.perform_action(self.left_hold_action)
        self.left_held = False

    def right_press(self, event):
        current = time.time()
        if current - self.last_right_click < 0.3:
            self.perform_action(self.right_double_action)
        else:
            self.perform_action(self.right_single_action)
        self.last_right_click = current
        self.right_held = True
        self.right_hold_start = current
        if self.left_held:
            self.right_charge += self.left_charge * 0.5
            self.left_charge = 0
            self.do_charged_defense()

    def right_release(self, event):
        if self.right_held and time.time() - self.right_hold_start > 0.3:
            self.perform_action(self.right_hold_action)
        self.right_held = False

    def perform_action(self, action):
        if action == 'attack':
            self.do_normal_attack()
        elif action == 'strong-attack':
            self.do_strong_attack()
        elif action == 'charge attack':
            self.do_charge_attack(self.left_charge if self.left_held else 1.0)
        elif action == 'jump':
            self.do_jump()
        elif action == 'dodge':
            self.do_dodge()
        elif action == 'defense stance':
            self.do_defend_stance(self.right_charge if self.right_held else 1.0)
        elif action == 'sprint':
            self.max_move_speed *= 1.5
            self.root.after(500, lambda: setattr(self, 'max_move_speed', 6.0))
        else:
            self.do_normal_attack()

    def toggle_pause(self, event=None):
        self.paused = not self.paused
        if self.paused:
            self.show_cursor()
            self.mouse_captured = False
            self.show_pause_menu()
        else:
            self.hide_cursor()
            self.mouse_captured = True
            self.center_mouse()
            if self.pause_menu:
                self.pause_menu.destroy()
                self.pause_menu = None

    def show_pause_menu(self):
        self.pause_menu = tk.Frame(self.root, bg='gray')
        self.pause_menu.place(relx=0.5, rely=0.5, anchor='center')
        scrolled = tk.Frame(self.pause_menu, bg='gray')
        scrolled.pack(fill='both', expand=True)

        tk.Label(scrolled, text="Pause", bg='gray', fg='white', font=('Arial', 16)).pack(pady=10)

        fov_scale = tk.Scale(scrolled, from_=30, to=120, orient='horizontal', label='FOV', command=self.set_fov, bg='gray', fg='white')
        fov_scale.set(self.fov); fov_scale.pack()
        turn_scale = tk.Scale(scrolled, from_=0.001, to=0.01, resolution=0.001, orient='horizontal', label='Mouse Sensitivity', command=self.set_turn_speed, bg='gray', fg='white')
        turn_scale.set(self.turn_speed); turn_scale.pack()
        smooth_scale = tk.Scale(scrolled, from_=0.0, to=1.0, resolution=0.05, orient='horizontal', label='Smoothing Factor', command=self.set_smooth_factor, bg='gray', fg='white')
        smooth_scale.set(self.smooth_factor); smooth_scale.pack()

        invert_y_var = tk.BooleanVar(value=self.invert_y)
        tk.Checkbutton(scrolled, text="Invert Y Axis", variable=invert_y_var, command=lambda: self.set_invert_y(invert_y_var.get()), bg='gray', fg='white', selectcolor='lime').pack()
        invert_x_var = tk.BooleanVar(value=self.invert_x)
        tk.Checkbutton(scrolled, text="Invert X Axis", variable=invert_x_var, command=lambda: self.set_invert_x(invert_x_var.get()), bg='gray', fg='white', selectcolor='lime').pack()

        tk.Button(scrolled, text="Change User Color", command=self.change_user_color, bg='darkgray', fg='white').pack(pady=5)

        screen_var = tk.StringVar(value=self.screen_mode)
        tk.OptionMenu(scrolled, screen_var, 'normal', 'double', 'fullscreen', command=self.set_screen_mode).pack()

        view_var = tk.StringVar(value=self.view_mode)
        tk.OptionMenu(scrolled, view_var, '1st', '3rd', 'helicopter', '2d_top', '2d_side', 'faux3d_xy_3rd', 'faux3d_xy_1st', command=self.set_view_mode).pack()

        weapon_frame = tk.Frame(scrolled, bg='gray')
        weapon_frame.pack(pady=10)
        weapons = ['fists', 'sword', 'axe', 'gun', 'bow', 'magic']
        for i, w in enumerate(weapons):
            r = i // 3
            c = i % 3
            tk.Button(weapon_frame, text=w.capitalize(), width=10, command=lambda ww=w: self.set_weapon(ww), bg='darkgray', fg='white').grid(row=r, column=c, padx=5, pady=5)

        tut_text = "Remove Tutorial" if self.tutorial_flag == 1 else "Restore Tutorial"
        self.tut_button = tk.Button(scrolled, text=tut_text, command=self.toggle_tutorial, bg='darkgray', fg='white')
        self.tut_button.pack(pady=5)

        btn_frame = tk.Frame(scrolled, bg='gray')
        btn_frame.pack(pady=10)
        tk.Button(btn_frame, text="Reset", command=self.reset, bg='darkgray', fg='white', width=12).pack(side='left', padx=20)
        tk.Button(btn_frame, text="Exit", command=self.exit_game, bg='darkgray', fg='white', width=12).pack(side='left', padx=20)

    def toggle_tutorial(self):
        self.tutorial_flag = 1 - self.tutorial_flag
        self.pause_menu.destroy()
        self.show_pause_menu()

    def set_screen_mode(self, mode):
        self.screen_mode = mode
        if mode == 'fullscreen':
            self.root.attributes('-fullscreen', True)
        else:
            self.root.attributes('-fullscreen', False)
            w = 1600 if mode == 'double' else 800
            h = 1200 if mode == 'double' else 600
            self.root.geometry(f"{w}x{h}")
            self.canvas.config(width=w, height=h)
            self.width = w
            self.height = h
            self.center_x = w // 2
            self.center_y = h // 2

    def change_user_color(self):
        color = colorchooser.askcolor(title="Choose Player Color")[1]
        if color:
            self.player_color = color

    def set_fov(self, val): self.fov = float(val)
    def set_turn_speed(self, val): self.turn_speed = float(val)
    def set_smooth_factor(self, val): self.smooth_factor = float(val)
    def set_invert_y(self, val): self.invert_y = bool(val)
    def set_invert_x(self, val): self.invert_x = bool(val)
    def set_view_mode(self, mode): self.view_mode = mode
    def set_weapon(self, w): self.weapon, self.next_weapon = w, self.weapon

    def reset(self):
        self.level = 0
        self.exp = 0
        self.exp_needed = 3
        self.health = 100
        self.max_health = 100
        self.stamina = 100
        self.max_stamina = 100
        self.magic = 50
        self.max_magic = 50
        self.attack_level = 1
        self.defense_level = 1
        self.skill_level = 1
        self.life_steal = 0
        self.armor = 0
        self.elements = {'cold':0,'hot':0,'poison':0,'dry':0,'humid':0,'physical':1}
        self.weapon = 'fists'
        self.next_weapon = 'sword'
        self.cam_pos = [0, self.eye_height, 0]
        self.yaw = 0
        self.pitch = 0
        self.target_yaw = 0
        self.target_pitch = 0
        self.vel_x = self.vel_y = self.vel_z = 0
        self.bosses = []
        self.projectiles = []
        self.objects = []
        self.pickups = []
        self.invert_y = False
        self.invert_x = False
        self.tutorial_flag = 1
        self.screen_mode = 'normal'
        self.generate_arena()
        self.generate_boss()

    def exit_game(self):
        self.save_game()
        self.running = False
        self.root.quit()

    def save_game(self):
        save_data = {
            'level': self.level, 'exp': self.exp, 'exp_needed': self.exp_needed,
            'health': self.health, 'max_health': self.max_health,
            'stamina': self.stamina, 'max_stamina': self.max_stamina,
            'magic': self.magic, 'max_magic': self.max_magic,
            'attack_level': self.attack_level, 'defense_level': self.defense_level,
            'skill_level': self.skill_level, 'life_steal': self.life_steal,
            'armor': self.armor, 'elements': self.elements,
            'weapon': self.weapon, 'next_weapon': self.next_weapon,
            'equip': self.equip, 'cam_pos': self.cam_pos,
            'yaw': self.yaw, 'pitch': self.pitch,
            'view_mode': self.view_mode, 'player_color': self.player_color,
            'invert_y': self.invert_y, 'invert_x': self.invert_x,
            'tutorial_flag': self.tutorial_flag,
            'screen_mode': self.screen_mode,
            'report': self.report
        }
        with open('game.crumbs', 'w') as f:
            json.dump(save_data, f)

    def load_game(self):
        try:
            with open('game.crumbs', 'r') as f:
                save_data = json.load(f)
            self.level = save_data.get('level', 0)
            self.exp = save_data.get('exp', 0)
            self.exp_needed = save_data.get('exp_needed', 3)
            self.health = save_data.get('health', 100)
            self.max_health = save_data.get('max_health', 100)
            self.stamina = save_data.get('stamina', 100)
            self.max_stamina = save_data.get('max_stamina', 100)
            self.magic = save_data.get('magic', 50)
            self.max_magic = save_data.get('max_magic', 50)
            self.attack_level = save_data.get('attack_level', 1)
            self.defense_level = save_data.get('defense_level', 1)
            self.skill_level = save_data.get('skill_level', 1)
            self.life_steal = save_data.get('life_steal', 0)
            self.armor = save_data.get('armor', 0)
            self.elements = save_data.get('elements', {'cold':0,'hot':0,'poison':0,'dry':0,'humid':0,'physical':1})
            self.weapon = save_data.get('weapon', 'fists')
            self.next_weapon = save_data.get('next_weapon', 'sword')
            self.equip = save_data.get('equip', {'head':None,'chest':'basic','legs':None})
            self.cam_pos = save_data.get('cam_pos', [0,1.8,0])
            self.yaw = save_data.get('yaw', 0)
            self.pitch = save_data.get('pitch', 0)
            self.target_yaw = self.yaw
            self.target_pitch = self.pitch
            self.view_mode = save_data.get('view_mode', '2d_top')
            self.player_color = save_data.get('player_color', '#0000ff')
            self.invert_y = save_data.get('invert_y', False)
            self.invert_x = save_data.get('invert_x', False)
            self.tutorial_flag = save_data.get('tutorial_flag', 1)
            self.screen_mode = save_data.get('screen_mode', 'normal')
            report = save_data.get('report', [])
            if report:
                print("## REPORT ##")
                print("\n".join(report))
                print("## END REPORT ##")
            self.report = []
        except FileNotFoundError:
            self.report = []
            self.tutorial_flag = 1
            self.screen_mode = 'normal'
            self.invert_y = False
            self.invert_x = False
        except Exception as e:
            self.report.append(str(e))

    def show_tutorial(self):
        self.tutorial_frame = tk.Frame(self.root, bg='gray')
        self.tutorial_frame.place(relx=0.5, rely=0.5, anchor='center')
        tk.Label(self.tutorial_frame, text="Tutorial", bg='gray', fg='white', font=('Arial', 16)).pack()
        tk.Label(self.tutorial_frame, text="WASD: Move\nSpace: Jump\nLeft Click: Attack\nRight Click: Dodge\nEsc: Pause", bg='gray', fg='white').pack()
        tk.Button(self.tutorial_frame, text="Start", command=self.start_tutorial, bg='darkgray', fg='white').pack()

    def start_tutorial(self):
        if self.tutorial_frame:
            self.tutorial_frame.destroy()
            self.tutorial_frame = None
        self.paused = False
        self.mouse_captured = True
        self.hide_cursor()
        self.center_mouse()

    def get_stats_text(self):
        elements_str = ', '.join([f"{k}:{v}" for k,v in self.elements.items()])
        top_left = f"Level: {self.level} Exp: {self.exp}/{self.exp_needed}\nElements: {elements_str}\nSkill: {self.skill_level}\nWeapon: {self.weapon} Next: {self.next_weapon}\nLife Steal: {self.life_steal}"
        if self.tutorial_flag == 0:
            top_left += "\nTut: 0"
        return top_left

    def generate_arena(self):
        self.objects = []
        theme_idx = self.level // 10 % len(self.themes)
        theme = self.themes[theme_idx]
        num_objects = random.randint(5, 10)
        for _ in range(num_objects):
            obj_type = random.choice(['desk','wall','rock'] if theme=='office' else ['rock','hill'] if theme=='volcano' else ['corn','furniture'])
            obj = self.get_object_config(obj_type)
            obj['pos'] = [random.uniform(-80,80), 0, random.uniform(-80,80)]
            obj['static'] = True
            self.objects.append(obj)

    def get_object_config(self, obj_type):
        if obj_type == 'desk':
            verts = [[-1,0,-1],[1,0,-1],[1,0,1],[-1,0,1],[-1,2,-1],[1,2,-1],[1,2,1],[-1,2,1]]
            faces = [[0,1,2,3],[4,5,6,7],[0,1,5,4],[1,2,6,5],[2,3,7,6],[3,0,4,7]]
            color = 'brown'
        elif obj_type == 'wall':
            verts = [[-2,0,-0.5],[2,0,-0.5],[2,0,0.5],[-2,0,0.5],[-2,10,-0.5],[2,10,-0.5],[2,10,0.5],[-2,10,0.5]]
            faces = [[0,1,2,3],[4,5,6,7],[0,1,5,4],[1,2,6,5],[2,3,7,6],[3,0,4,7]]
            color = 'gray'
        elif obj_type == 'rock':
            n = 6
            verts = [[cos(i*2*pi/n)+random.uniform(-0.2,0.2),0,sin(i*2*pi/n)+random.uniform(-0.2,0.2)] for i in range(n)]
            verts += [[v[0],3+random.uniform(-1,1),v[2]] for v in verts]
            sides = [[i,(i+1)%n,n+(i+1)%n,n+i] for i in range(n)]
            faces = [list(range(n)), list(reversed(range(n,2*n)))] + sides
            color = 'darkgray'
        else:
            verts = [[-1,0,-1],[1,0,-1],[1,0,1],[-1,0,1],[-1,2,-1],[1,2,-1],[1,2,1],[-1,2,1]]
            faces = [[0,1,2,3],[4,5,6,7],[0,1,5,4],[1,2,6,5],[2,3,7,6],[3,0,4,7]]
            color = 'green'
        return {'type':'poly','verts':verts,'faces':faces,'color':color,'scale':random.uniform(2,5),'radius':3,'interactive':random.random()<0.3,'obj_type':obj_type if random.random()<0.3 else None}

    def generate_boss(self):
        is_predetermined = self.level % 100 == 0 and self.level > 0
        if is_predetermined:
            creature_idx = (self.level // 100) % len(self.creature_types)
            creature_name = self.creature_types[creature_idx]
            boss = self.get_creature_config(creature_name)
        else:
            n = 20 if self.level == 0 else (self.level % 8) + 3
            verts = [[cos(i * 2 * pi / n) + random.uniform(-0.1,0.1) if n % 3 == 0 else cos(i * 2 * pi / n), 0, sin(i * 2 * pi / n) + random.uniform(-0.1,0.1) if n % 3 == 0 else sin(i * 2 * pi / n)] for i in range(n)]
            height = 5 + self.level * 0.1
            verts += [[v[0], height, v[2]] for v in verts]
            front_face = list(range(n))
            back_face = list(reversed(range(n, 2*n)))
            sides = [[i, (i+1)%n, n+(i+1)%n, n+i] for i in range(n)]
            faces = [front_face, back_face] + sides
            edges = [[i, (i+1) % n] for i in range(n)] + [[n+i, n+(i+1)%n] for i in range(n)] + [[i, n+i] for i in range(n)]
            boss_health = 5 * (self.exp + 1) if self.level == 0 else 100 + self.level * 20
            radius = 3 + self.level * 0.2
            pos = [random.uniform(-80, 80), 4.0, random.uniform(10, 40)]
            scale = 3 + self.level * 0.2
            if self.level % 100 == 0:
                scale *= 2.0
                boss_health *= 5
            summoner_chance = 0 if self.level == 0 else 0.3 if random.random() < 0.3 else 0
            attack_type = random.choice(['melee', 'range', 'run_away']) if summoner_chance == 0 else 'summoner'
            behavior = 'normal' if self.level == 0 else random.choice(['aggressive', 'defensive', 'summoner']) if n % 3 == 0 else 'normal'
            boss = {
                'type': 'poly', 'pos': pos, 'vel_x': 0.0, 'vel_z': 0.0, 'scale': scale,
                'health': boss_health, 'max_health': boss_health,
                'verts': verts, 'faces': faces, 'edges': edges,
                'radius': radius, 'height': height,
                'speed': 4 + self.level * 0.1, 'damage': 10 + self.level * 2,
                'attack_cooldown': time.time() + random.uniform(0.5, 1.5),
                'split': False, 'element': random.choice(list(self.elements.keys())),
                'color': 'red', 'attack_type': attack_type, 'behavior': behavior,
                'effects': {'cold': 0, 'hot': 0, 'poison': 0, 'dry': 0, 'humid': 0},
                'id': self.boss_id_counter, 'anim_time': 0, 'state': None, 'state_time': 0,
                'visible': True, 'can_split': False if self.level == 0 else True
            }
            self.boss_id_counter += 1
        self.bosses.append(boss)

    def get_creature_config(self, name):
        if name == 'Smiler':
            n = 10
            verts = [[cos(i*2*pi/n)+random.uniform(-0.2,0.2),0,sin(i*2*pi/n)+random.uniform(-0.2,0.2)] for i in range(n)]
            height = 6
            verts += [[v[0],height,v[2]] for v in verts[:n]]
            front_face = list(range(n))
            back_face = list(reversed(range(n,2*n)))
            sides = [[i,(i+1)%n,n+(i+1)%n,n+i] for i in range(n)]
            faces = [front_face, back_face] + sides
            eye_left = [[-0.3,height,0.3],[-0.4,height,0.25],[-0.2,height,0.25]]
            eye_right = [[0.3,height,0.3],[0.4,height,0.25],[0.2,height,0.25]]
            smile = [[-0.5,height,0],[-0.3,height,-0.2],[0,height,-0.3],[0.3,height,-0.2],[0.5,height,0]]
            verts += eye_left + eye_right + smile
            eye_left_face = [2*n,2*n+1,2*n+2]
            eye_right_face = [2*n+3,2*n+4,2*n+5]
            smile_face = [2*n+6,2*n+7,2*n+8,2*n+9,2*n+10]
            faces += [eye_left_face, eye_right_face, smile_face]
            face_colors = ['black']*len(faces[:-3]) + ['white','white','white']
            behavior = 'stealth'
            attack_type = 'melee'
        elif name == 'Hound':
            n = 8
            verts = [[cos(i*2*pi/n)*1.5,0,sin(i*2*pi/n)*0.8] for i in range(n)]
            height = 4
            verts += [[v[0],height,v[2]] for v in verts[:n]]
            front_face = list(range(n))
            back_face = list(reversed(range(n,2*n)))
            sides = [[i,(i+1)%n,n+(i+1)%n,n+i] for i in range(n)]
            faces = [front_face, back_face] + sides
            face_colors = ['gray']*len(faces)
            behavior = 'frenzy'
            attack_type = 'melee'
        else:
            n = 12
            verts = [[cos(i*2*pi/n),0,sin(i*2*pi/n)] for i in range(n)]
            height = 5
            verts += [[v[0],height,v[2]] for v in verts[:n]]
            front_face = list(range(n))
            back_face = list(reversed(range(n,2*n)))
            sides = [[i,(i+1)%n,n+(i+1)%n,n+i] for i in range(n)]
            faces = [front_face, back_face] + sides
            face_colors = ['red']*len(faces)
            behavior = 'normal'
            attack_type = 'melee'
        boss_health = 100 + self.level*20
        radius = 3 + self.level*0.2
        pos = [random.uniform(-80,80),4.0,random.uniform(10,40)]
        scale = 3 + self.level*0.2
        boss = {
            'type':'poly','pos':pos,'vel_x':0.0,'vel_z':0.0,'scale':scale,
            'health':boss_health,'max_health':boss_health,
            'verts':verts,'faces':faces,'face_colors':face_colors,
            'radius':radius,'height':height,
            'speed':4+self.level*0.1,'damage':10+self.level*2,
            'attack_cooldown':time.time()+random.uniform(0.5,1.5),
            'split':False,'element':random.choice(list(self.elements.keys())),
            'color':'red','attack_type':attack_type,'behavior':behavior,
            'effects':{'cold':0,'hot':0,'poison':0,'dry':0,'humid':0},
            'id':self.boss_id_counter,'anim_time':0,'state':None,'state_time':0,
            'visible':True,'can_split':True
        }
        self.boss_id_counter += 1
        return boss

    def do_normal_attack(self):
        damage = self.attack_level * (1 + sum(self.elements.values()) * 0.1) * (1 + self.level // 10 * 0.01)
        range_ = 5 if self.weapon in ['fists','sword','axe'] else 20 if self.weapon in ['gun','bow'] else 30
        if range_ == 30: self.magic -= 10
        self.fire_projectile(damage, range_)

    def do_strong_attack(self):
        self.do_normal_attack()
        self.do_normal_attack()

    def do_charge_attack(self, charge):
        mult = min(5, 1 + charge / self.max_left_charge_time * 4)
        damage = self.attack_level * mult * (1 + sum(self.elements.values()) * 0.1) * (1 + self.level // 10 * 0.01)
        self.fire_projectile(damage, 10)

    def do_dodge(self):
        self.vel_x += sin(self.yaw) * 10
        self.vel_z += cos(self.yaw) * 10
        self.stamina -= 20
        self.invulnerable_duration += 0.5

    def do_jump(self):
        if self.on_ground:
            self.vel_y = self.jump_speed
            self.stamina -= 10

    def do_charged_defense(self):
        self.armor *= 1.5

    def do_defend_stance(self, charge):
        window = min(2, charge / self.max_right_charge_time * 2)
        self.invulnerable_duration += window + 0.1 * (charge / 0.3)

    def do_attack_in_defense(self):
        self.do_normal_attack()

    def fire_projectile(self, damage, range_):
        dx = sin(self.yaw) * cos(self.pitch)
        dy = -sin(self.pitch)
        dz = cos(self.yaw) * cos(self.pitch)
        pos = self.cam_pos[:]
        if self.view_mode == '3rd':
            pos[0] += sin(self.yaw) * 10
            pos[1] -= 2
            pos[2] += cos(self.yaw) * 10
        vel = [dx * 20, dy * 20, dz * 20]
        color = 'red'
        self.projectiles.append({'pos': pos, 'vel': vel, 'damage': damage, 'range': range_, 'color': color, 'lifetime': 2.0, 'start_time': time.time()})

    def add_boss_trail(self, pos, dir_vec, color):
        length_off = 4
        sx = pos[0] + dir_vec[0] * -1.5
        sy = pos[1] + dir_vec[1] * -1.5
        sz = pos[2] + dir_vec[2] * -1.5
        ex = pos[0] + dir_vec[0] * length_off
        ey = pos[1] + dir_vec[1] * length_off
        ez = pos[2] + dir_vec[2] * length_off
        vel = [dir_vec[0]*20, dir_vec[1]*20, dir_vec[2]*20]
        self.trails.append({'start': [sx,sy,sz], 'end': [ex,ey,ez], 'vel': vel, 'color': color, 'lifetime': 0.6, 'start_time': time.time()})

    def hit_boss(self, idx, damage):
        boss = self.bosses[idx]
        elem_dmg = damage * (self.elements.get(boss['element'], 0) * 0.2)
        total_dmg = damage + elem_dmg
        boss['health'] -= total_dmg
        self.add_particles(boss['pos'], 'yellow')
        if self.life_steal > 0:
            heal = total_dmg * self.life_steal / 100
            self.health = min(self.max_health, self.health + heal)
        for elem, level in self.elements.items():
            if level > 0 and elem != 'physical':
                boss['effects'][elem] += level
        if boss['health'] <= 0:
            self.on_boss_kill(idx)
            return
        if boss['health'] <= boss['max_health']/2 and not boss.get('split',False) and len(boss['verts'])//2 % 2 == 0 and boss.get('can_split',True) and random.random() < 0.5 and len(self.bosses) < 5:
            self.split_boss(idx)

    def on_boss_kill(self, idx):
        boss = self.bosses.pop(idx)
        self.exp += 1
        drop = 'armor' if self.level == 0 else random.choice(self.progression)
        self.pickups.append({'pos': boss['pos'][:], 'type': drop, 'start_time': time.time(), 'radius': 2, 'color': 'gold'})
        if not boss.get('minor', False):
            self.bosses = [b for b in self.bosses if b.get('parent_id', -1) != boss['id']]
        while self.exp >= self.exp_needed:
            self.level += 1
            self.exp -= self.exp_needed
            self.exp_needed = 3 + self.level*3 + (self.level//10)*10
            if self.level % 100 == 0:
                self.attack_level *= 1.1
                self.defense_level *= 1.1
                self.max_health *= 1.1
                self.max_stamina *= 1.1
                self.max_magic *= 1.1
            self.choose_gain = True
            self.choice_text_id = self.canvas.create_text(self.center_x, self.height-30, anchor='s', fill='white', text="1-6: Element (cold/hot/poison/dry/humid/physical) then H: Health | S: Stamina")
        self.generate_arena()
        self.generate_boss()

    def split_boss(self, idx):
        boss = self.bosses[idx]
        new_pos = boss['pos'][:]
        new_pos[0] += random.uniform(-10,10)
        new_pos[2] += random.uniform(-10,10)
        new_boss = copy.deepcopy(boss)
        new_boss['pos'] = new_pos
        new_boss['vel_x'] = new_boss['vel_z'] = 0
        new_boss['health'] = boss['max_health']/4
        new_boss['max_health'] = boss['max_health']/2
        new_boss['split'] = True
        new_boss['attack_cooldown'] = time.time() + random.uniform(0.5,1.5)
        new_boss['original_scale'] = new_boss['scale']
        new_boss['scale'] = 0
        new_boss['anim_time'] = time.time()
        new_boss['anim_type'] = 'scale_up'
        new_boss['can_split'] = False
        self.bosses.insert(idx + 1, new_boss)
        boss['split'] = True
        boss['health'] = boss['max_health']/4
        boss['max_health'] = boss['max_health']/2
        boss['original_scale'] = boss['scale']
        boss['scale'] = 0
        boss['anim_time'] = time.time()
        boss['anim_type'] = 'scale_up'
        boss['can_split'] = False
        self.add_particles(boss['pos'], 'red', count=30)
        dist = sqrt((self.cam_pos[0]-boss['pos'][0])**2 + (self.cam_pos[2]-boss['pos'][2])**2)
        if dist < 10:
            self.boss_hits_player(boss['damage']/2)

    def boss_hits_player(self, damage):
        current = time.time()
        if current < self.invulnerable_time: return
        net_damage = max(0, damage - self.armor)
        if self.right_held: net_damage *= 0.4
        self.health -= net_damage
        self.add_particles(self.cam_pos, 'orange')
        self.invulnerable_time = current + self.invulnerable_duration
        if self.health <= 0:
            self.health = self.max_health * 0.3
            self.cam_pos = [0, self.eye_height, 0]
            self.vel_x = self.vel_y = self.vel_z = 0

    def add_particles(self, pos, color, count=15):
        if len(self.particles) + count > self.max_particles:
            self.particles = self.particles[count:]
        for _ in range(count):
            vel = [random.uniform(-8,8), random.uniform(3,12), random.uniform(-8,8)]
            self.particles.append({'pos':pos[:], 'vel':vel, 'color':color, 'lifetime':1.2, 'start_time':time.time()})

    def project(self, point, cam_pos=None, yaw=None, pitch=None):
        if cam_pos is None: cam_pos = self.cam_pos
        if yaw is None: yaw = self.yaw
        if pitch is None: pitch = self.pitch
        cx,cy,cz = cam_pos
        dx = point[0]-cx
        dy = point[1]-cy
        dz = point[2]-cz
        dx2 = dx*cos(yaw) + dz*sin(yaw)
        dz2 = -dx*sin(yaw) + dz*cos(yaw)
        dy2 = dy
        dy3 = dy2*cos(pitch) - dz2*sin(pitch)
        dz3 = dy2*sin(pitch) + dz2*cos(pitch)
        dx3 = dx2
        if dz3 < 0.001: return None
        f = (self.width/2.0) / tan(radians(self.fov)/2)
        sx = self.center_x + dx3*f/dz3
        sy = self.center_y - dy3*f/dz3
        return (sx, sy, dz3)

    def iso_project(self, point, cam_pos=None, yaw=None, pitch=None):
        if cam_pos is None: cam_pos = self.cam_pos
        if yaw is None: yaw = self.yaw
        if pitch is None: pitch = self.pitch
        cx,cy,cz = cam_pos
        dx = point[0]-cx
        dz = point[2]-cz
        dx2 = dx*cos(yaw) + dz*sin(yaw)
        dz2 = -dx*sin(yaw) + dz*cos(yaw)
        scale = 5
        height_scale = scale*1.5
        angle = radians(26.565) if self.view_mode == 'faux3d_xy_3rd' else radians(30)
        sx = (dx2 - dz2)*cos(angle)*scale + self.center_x
        sy = self.center_y - point[1]*height_scale - (dx2 + dz2)*sin(angle)*scale
        return (sx, sy, point[1])

    def fisheye_iso_project(self, point, cam_pos=None, yaw=None, pitch=None):
        if cam_pos is None: cam_pos = self.cam_pos
        if yaw is None: yaw = self.yaw
        if pitch is None: pitch = self.pitch
        cx,cy,cz = cam_pos
        dx = point[0]-cx
        dz = point[2]-cz
        dx2 = dx*cos(yaw) + dz*sin(yaw)
        dz2 = -dx*sin(yaw) + dz*cos(yaw)
        scale = 5
        height_scale = scale*1.5
        angle = radians(30)
        sx = (dx2 - dz2)*cos(angle)*scale + self.center_x
        sy = self.center_y - point[1]*height_scale - (dx2 + dz2)*sin(angle)*scale
        dx = sx - self.center_x
        dy = sy - self.center_y
        dist = sqrt(dx**2 + dy**2)
        if dist == 0: return (sx, sy, point[1])
        r = min(self.width, self.height)/2
        factor = 1 + 0.2*(dist/r)**2
        sx = self.center_x + dx*factor
        sy = self.center_y + dy*factor
        return (sx, sy, point[1])

    def update(self):
        current = time.time()
        dt = min(current - self.last_time, 0.05)
        self.last_time = current

        self.max_left_charge_time = 1.0 + self.level//10*0.01
        self.max_right_charge_time = 1.5 + self.level//10*0.01
        if self.left_held: self.left_charge = min(self.max_left_charge_time, current - self.left_hold_start)
        if self.right_held: self.right_charge = min(self.max_right_charge_time, current - self.right_hold_start)

        self.yaw += (self.target_yaw - self.yaw) * self.smooth_factor
        self.pitch += (self.target_pitch - self.pitch) * self.smooth_factor

        if self.view_mode in ['helicopter','2d_top','faux3d_xy_3rd','faux3d_xy_1st']:
            self.pitch = 0
            self.target_pitch = 0
        if self.view_mode == 'helicopter':
            self.pitch = -radians(80)
            self.target_pitch = -radians(80)
        if self.view_mode == '2d_side':
            self.yaw = pi/2
            self.target_yaw = pi/2
            step = pi/8
            self.target_pitch = round(self.target_pitch/step)*step
            self.pitch = self.target_pitch

        self.vel_y -= self.gravity * dt
        input_x = input_z = 0.0
        if self.view_mode == '2d_side':
            if 'a' in self.keys: input_x -= 1
            if 'd' in self.keys: input_x += 1
        else:
            if 'w' in self.keys: input_x += sin(self.yaw); input_z += cos(self.yaw)
            if 's' in self.keys: input_x -= sin(self.yaw); input_z -= cos(self.yaw)
            if 'a' in self.keys: input_x -= cos(self.yaw); input_z += sin(self.yaw)
            if 'd' in self.keys: input_x += cos(self.yaw); input_z -= sin(self.yaw)
        input_len = sqrt(input_x**2 + input_z**2)
        if input_len > 0:
            input_x /= input_len
            input_z /= input_len
        accel = self.air_move_accel if not self.on_ground else self.move_accel
        self.vel_x += input_x * accel * dt
        self.vel_z += input_z * accel * dt
        horiz_spd = sqrt(self.vel_x**2 + self.vel_z**2)
        if horiz_spd > self.max_move_speed:
            self.vel_x = (self.vel_x/horiz_spd)*self.max_move_speed
            self.vel_z = (self.vel_z/horiz_spd)*self.max_move_speed
        if self.on_ground:
            fric = self.friction * dt
            if horiz_spd > 0:
                self.vel_x -= (self.vel_x/horiz_spd)*fric
                self.vel_z -= (self.vel_z/horiz_spd)*fric
        self.cam_pos[0] += self.vel_x*dt
        self.cam_pos[1] += self.vel_y*dt
        self.cam_pos[2] += self.vel_z*dt
        if self.cam_pos[1] < self.eye_height:
            self.cam_pos[1] = self.eye_height
            self.vel_y = 0
            self.on_ground = True
        else:
            self.on_ground = False
        dist_xz = sqrt(self.cam_pos[0]**2 + self.cam_pos[2]**2)
        if dist_xz > self.arena_radius - self.player_radius:
            factor = (self.arena_radius - self.player_radius)/dist_xz
            self.cam_pos[0] *= factor
            self.cam_pos[2] *= factor
            self.vel_x = self.vel_z = 0

        px, _, pz = self.cam_pos
        for boss in self.bosses[:]:
            if boss.get('minor', False) and 'despawn_time' in boss and current > boss['despawn_time']:
                self.bosses.remove(boss)
                continue
            if 'anim_type' in boss and boss['anim_type'] == 'scale_up':
                t = (current - boss['anim_time']) / 1.0
                boss['scale'] = boss.get('original_scale', boss['scale']) * min(1, t)
                if t >= 1:
                    del boss['anim_type']
                    del boss['original_scale']
            speed_mod = 1.0
            if boss['effects']['cold'] > 0:
                speed_mod *= (1 - 0.05 * min(10, boss['effects']['cold']))
                boss['effects']['cold'] -= dt
            if boss['effects']['hot'] > 0:
                boss['health'] -= dt * boss['effects']['hot']
                boss['effects']['hot'] -= dt
            if boss['effects']['poison'] > 0:
                boss['health'] -= dt * boss['effects']['poison'] * 0.5
                boss['effects']['poison'] -= dt
            if boss['effects']['dry'] > 0:
                boss['damage'] *= (1 - 0.03 * boss['effects']['dry'])
                boss['effects']['dry'] -= dt
            if boss['effects']['humid'] > 0:
                speed_mod *= (1 - 0.02 * boss['effects']['humid'])
                boss['effects']['humid'] -= dt
            dx = px - boss['pos'][0]
            dz = pz - boss['pos'][2]
            dist_xz = sqrt(dx**2 + dz**2)
            if dist_xz > 0:
                dx /= dist_xz
                dz /= dist_xz
            boss_speed = boss['speed'] * speed_mod
            if boss['behavior'] == 'stealth':
                boss['visible'] = dist_xz <= 10
            if boss['behavior'] == 'fly':
                boss['pos'][1] = 4 + sin(current * 2) * 2
            if boss['state'] == 'lunge':
                boss_speed *= 2
                if current > boss['state_time'] + 0.5:
                    boss['state'] = None
            if dist_xz > 2:
                boss['vel_x'] = dx * boss_speed
                boss['vel_z'] = dz * boss_speed
            else:
                boss['vel_x'] = boss['vel_z'] = 0
            if random.random() < 0.1:
                choices = ['melee', 'range', 'run_away'] if self.level == 0 else ['melee', 'range', 'run_away', 'summoner']
                boss['attack_type'] = random.choice(choices)
            if boss['attack_type'] == 'run_away' and dist_xz < 5:
                boss['vel_x'] = -boss['vel_x']
                boss['vel_z'] = -boss['vel_z']
            if boss['attack_type'] == 'summoner' and current > boss['attack_cooldown'] and len(self.bosses) < 10:
                num_minors = random.randint(2, 5)
                for _ in range(num_minors):
                    minor = copy.deepcopy(boss)
                    minor['pos'][0] += random.uniform(-5, 5)
                    minor['pos'][2] += random.uniform(-5, 5)
                    minor['scale'] *= 0.5
                    minor['health'] = boss['max_health'] / 4
                    minor['damage'] /= 2
                    minor['minor'] = True
                    minor['parent_id'] = boss['id']
                    minor['despawn_time'] = current + 30
                    minor['attack_type'] = 'melee'
                    self.bosses.append(minor)
                boss['attack_cooldown'] = current + random.uniform(5, 10)
            boss['pos'][0] += boss['vel_x'] * dt
            boss['pos'][2] += boss['vel_z'] * dt
            b_dist = sqrt(boss['pos'][0]**2 + boss['pos'][2]**2)
            if b_dist > self.arena_radius - boss['radius']:
                factor = (self.arena_radius - boss['radius']) / b_dist
                boss['pos'][0] *= factor
                boss['pos'][2] *= factor
                boss['vel_x'] = boss['vel_z'] = 0

        player_shape = {'type': 'sphere', 'pos': self.cam_pos, 'radius': self.player_radius}
        for shape_list, is_boss in [(self.bosses, True), (self.objects, False)]:
            for i, shape in enumerate(shape_list):
                shape_shape = {'type': shape['type'], 'pos': shape['pos'], 'radius': shape['radius'], 'scale': shape['scale'], 'verts': shape['verts']}
                if gjk_intersect(player_shape, shape_shape):
                    dx = self.cam_pos[0] - shape['pos'][0]
                    dz = self.cam_pos[2] - shape['pos'][2]
                    dist = sqrt(dx**2 + dz**2)
                    if dist > 0:
                        dx /= dist
                        dz /= dist
                        overlap = self.player_radius + shape['radius'] - dist
                        self.cam_pos[0] += dx * overlap / 2
                        self.cam_pos[2] += dz * overlap / 2
                        if not shape.get('static', False):
                            shape['pos'][0] -= dx * overlap / 2
                            shape['pos'][2] -= dz * overlap / 2
                if is_boss:
                    for j in range(i + 1, len(shape_list)):
                        other = shape_list[j]
                        other_shape = {'type': other['type'], 'pos': other['pos'], 'radius': other['radius'], 'scale': other['scale'], 'verts': other['verts']}
                        if gjk_intersect(shape_shape, other_shape):
                            dx = shape['pos'][0] - other['pos'][0]
                            dz = shape['pos'][2] - other['pos'][2]
                            dist = sqrt(dx**2 + dz**2)
                            if dist > 0:
                                dx /= dist
                                dz /= dist
                                overlap = shape['radius'] + other['radius'] - dist
                                shape['pos'][0] += dx * overlap / 2
                                shape['pos'][2] += dz * overlap / 2
                                other['pos'][0] -= dx * overlap / 2
                                other['pos'][2] -= dz * overlap / 2

        for p in self.pickups[:]:
            p_shape = {'type': 'sphere', 'pos': p['pos'], 'radius': p['radius']}
            if gjk_intersect(player_shape, p_shape):
                self.collect_pickup(p)
                self.pickups.remove(p)

        if self.e_pressed:
            self.e_pressed = False
            nearest_obj = None
            min_dist = float('inf')
            for obj in self.objects:
                if obj.get('interactive', False):
                    dist = sqrt((self.cam_pos[0] - obj['pos'][0])**2 + (self.cam_pos[2] - obj['pos'][2])**2)
                    if dist < 5 and dist < min_dist:
                        min_dist = dist
                        nearest_obj = obj
            if nearest_obj:
                self.interact_object(nearest_obj)

        for boss in self.bosses:
            if current > boss['attack_cooldown']:
                dx = self.cam_pos[0] - boss['pos'][0]
                dy = self.cam_pos[1] - boss['pos'][1]
                dz = self.cam_pos[2] - boss['pos'][2]
                dist3d = sqrt(dx**2 + dy**2 + dz**2)
                if dist3d < 14:
                    self.boss_hits_player(boss['damage'])
                    self.add_boss_trail(boss['pos'], [dx/dist3d if dist3d>0 else 0, dy/dist3d if dist3d>0 else 0, dz/dist3d if dist3d>0 else 0], 'red')
                    boss['attack_cooldown'] = current + random.uniform(0.8, 2.5)
                    if boss['behavior'] == 'frenzy':
                        boss['state'] = 'lunge'
                        boss['state_time'] = current

        new_proj = []
        for proj in self.projectiles:
            if current - proj['start_time'] < proj['lifetime']:
                proj['pos'][0] += proj['vel'][0] * dt
                proj['pos'][1] += proj['vel'][1] * dt
                proj['pos'][2] += proj['vel'][2] * dt
                proj['vel'][1] -= self.gravity * dt
                if proj['pos'][1] < 0: continue
                proj_dist = sqrt(proj['pos'][0]**2 + proj['pos'][2]**2)
                if proj_dist > self.arena_radius: continue
                proj_shape = {'type': 'sphere', 'pos': proj['pos'], 'radius': 0.5}
                hit = False
                for i, boss in enumerate(self.bosses):
                    boss_shape = {'type': boss['type'], 'pos': boss['pos'], 'radius': boss['radius'], 'scale': boss['scale'], 'verts': boss['verts']}
                    if gjk_intersect(proj_shape, boss_shape):
                        self.hit_boss(i, proj['damage'])
                        self.add_particles(proj['pos'], proj['color'])
                        hit = True
                        break
                if not hit:
                    new_proj.append(proj)
        self.projectiles = new_proj

        self.particles = [p for p in self.particles if current - p['start_time'] < p['lifetime']]
        for p in self.particles:
            p['pos'][0] += p['vel'][0] * dt
            p['pos'][1] += p['vel'][1] * dt
            p['pos'][2] += p['vel'][2] * dt
            p['vel'][1] -= self.gravity * dt

        self.trails = [t for t in self.trails if current - t['start_time'] < t['lifetime']]
        for t in self.trails:
            t['start'][0] += t['vel'][0] * dt
            t['start'][1] += t['vel'][1] * dt
            t['start'][2] += t['vel'][2] * dt
            t['end'][0] += t['vel'][0] * dt
            t['end'][1] += t['vel'][1] * dt
            t['end'][2] += t['vel'][2] * dt

        if self.stamina < self.max_stamina: self.stamina += 25 * dt
        if self.magic < self.max_magic: self.magic += 10 * dt
        self.stamina = min(self.max_stamina, max(0, self.stamina))
        self.magic = min(self.max_magic, max(0, self.magic))
        self.health = min(self.max_health, max(0, self.health))

        for p in self.pickups:
            if random.random() < 0.1:
                self.add_particles(p['pos'], 'yellow', count=5)

    def collect_pickup(self, pickup):
        drop = pickup['type']
        if drop == 'armor':
            self.armor += 3 + self.level // 2
        elif drop == 'weapon':
            self.next_weapon = random.choice(['sword', 'axe', 'gun', 'bow', 'magic'])
        elif drop == 'skill_point':
            self.skill_level += 1
        self.add_particles(pickup['pos'], 'green')

    def interact_object(self, obj):
        if obj.get('obj_type') == 'chest':
            drop = random.choice(self.progression)
            if drop == 'armor':
                self.armor += 10
            self.add_particles(obj['pos'], 'blue')
        self.objects.remove(obj)

    def render(self):
        try:
            self.canvas.delete("all")

            cam_pos = self.cam_pos[:]
            yaw = self.yaw
            pitch = self.pitch
            render_player = True
            proj_func = self.project

            if self.view_mode == '1st':
                render_player = False
            elif self.view_mode == '3rd':
                cam_pos[0] -= sin(yaw) * 10
                cam_pos[2] -= cos(yaw) * 10
                cam_pos[1] += 2
            elif self.view_mode == 'helicopter':
                cam_pos[1] = 50
                pitch = -radians(80)
            elif self.view_mode in ['faux3d_xy_3rd']:
                proj_func = self.iso_project
            elif self.view_mode in ['faux3d_xy_1st']:
                proj_func = self.fisheye_iso_project
                render_player = False

            if self.view_mode in ['2d_top', '2d_side']:
                scale = 5
                offset_x = self.width // 2 - self.cam_pos[0] * scale
                offset_z = self.height // 2 - self.cam_pos[2] * scale
                offset_y = self.height // 2 + self.cam_pos[1] * scale
                if self.view_mode == '2d_top':
                    px = self.width // 2
                    pz = self.height // 2
                    self.canvas.create_oval(px-5, pz-5, px+5, pz+5, fill=self.player_color)
                    aim_pos = [self.cam_pos[0] + sin(self.yaw) * 2, self.cam_pos[1], self.cam_pos[2] + cos(self.yaw) * 2]
                    aim_x = offset_x + aim_pos[0] * scale
                    aim_z = offset_z + aim_pos[2] * scale
                    self.canvas.create_oval(aim_x-2, aim_z-2, aim_x+2, aim_z+2, fill='white')
                    for entity_list in [self.bosses, self.objects]:
                        for entity in entity_list:
                            if 'visible' in entity and not entity['visible']: continue
                            bx = offset_x + entity['pos'][0] * scale
                            bz = offset_z + entity['pos'][2] * scale
                            r = entity['radius'] * scale
                            self.canvas.create_oval(bx-r, bz-r, bx+r, bz+r, outline=entity['color'])
                            health_ratio = entity.get('health',1)/entity.get('max_health',1) if 'health' in entity else 1
                            self.canvas.create_arc(bx-r, bz-r, bx+r, bz+r, start=0, extent=360*health_ratio, style='arc', outline='red', width=2)
                            if 'health' in entity and entity['health'] < entity['max_health']/2:
                                glow_color = {'cold':'cyan','hot':'orange','poison':'green','dry':'brown','humid':'blue','physical':'gray'}.get(entity['element'],'white')
                                self.canvas.create_oval(bx-r-2, bz-r-2, bx+r+2, bz+r+2, outline=glow_color)
                    for proj in self.projectiles:
                        px = offset_x + proj['pos'][0] * scale
                        pz = offset_z + proj['pos'][2] * scale
                        self.canvas.create_oval(px-2, pz-2, px+2, pz+2, fill=proj['color'])
                    for p in self.particles:
                        px = offset_x + p['pos'][0] * scale
                        pz = offset_z + p['pos'][2] * scale
                        self.canvas.create_oval(px-1, pz-1, px+1, pz+1, fill=p['color'])
                    for t in self.trails:
                        sx = offset_x + t['start'][0] * scale
                        sz = offset_z + t['start'][2] * scale
                        ex = offset_x + t['end'][0] * scale
                        ez = offset_z + t['end'][2] * scale
                        self.canvas.create_line(sx, sz, ex, ez, fill=t['color'], width=2)
                    for pickup in self.pickups:
                        px = offset_x + pickup['pos'][0] * scale
                        pz = offset_z + pickup['pos'][2] * scale
                        self.canvas.create_oval(px-3, pz-3, px+3, pz+3, fill=pickup['color'])
                    return
                else:
                    px = self.width // 2
                    py = self.height // 2
                    self.canvas.create_oval(px-5, py-5, px+5, py+5, fill=self.player_color)
                    for entity_list in [self.bosses, self.objects]:
                        for entity in entity_list:
                            if 'visible' in entity and not entity['visible']: continue
                            bx = offset_x + entity['pos'][0] * scale
                            by = offset_y - entity['pos'][1] * scale
                            r = entity['radius'] * scale
                            self.canvas.create_oval(bx-r, by-r, bx+r, by+r, outline=entity['color'])
                            health_ratio = entity.get('health',1)/entity.get('max_health',1) if 'health' in entity else 1
                            self.canvas.create_arc(bx-r, by-r, bx+r, by+r, start=0, extent=360*health_ratio, style='arc', outline='red', width=2)
                            if 'health' in entity and entity['health'] < entity['max_health']/2:
                                glow_color = {'cold':'cyan','hot':'orange','poison':'green','dry':'brown','humid':'blue','physical':'gray'}.get(entity['element'],'white')
                                self.canvas.create_oval(bx-r-2, by-r-2, bx+r+2, by+r+2, outline=glow_color)
                    for proj in self.projectiles:
                        px = offset_x + proj['pos'][0] * scale
                        py = offset_y - proj['pos'][1] * scale
                        self.canvas.create_oval(px-2, py-2, px+2, py+2, fill=proj['color'])
                    for p in self.particles:
                        px = offset_x + p['pos'][0] * scale
                        py = offset_y - p['pos'][1] * scale
                        self.canvas.create_oval(px-1, py-1, px+1, py+1, fill=p['color'])
                    for t in self.trails:
                        sx = offset_x + t['start'][0] * scale
                        sy = offset_y - t['start'][1] * scale
                        ex = offset_x + t['end'][0] * scale
                        ey = offset_y - t['end'][1] * scale
                        self.canvas.create_line(sx, sy, ex, ey, fill=t['color'], width=2)
                    for pickup in self.pickups:
                        px = offset_x + pickup['pos'][0] * scale
                        py = offset_y - pickup['pos'][1] * scale
                        self.canvas.create_oval(px-3, py-3, px+3, py+3, fill=pickup['color'])
                    return

            oct_verts = [[self.arena_radius*cos(i*2*pi/self.arena_sides), self.arena_radius*sin(i*2*pi/self.arena_sides)] for i in range(self.arena_sides)]
            oct_verts3d = [[oct_verts[i][0],0,oct_verts[i][1]] for i in range(self.arena_sides)]
            projected = [proj_func(v,cam_pos,yaw,pitch) for v in oct_verts3d]
            if all(p is not None for p in projected):
                points = [(p[0],p[1]) for p in projected]
                self.canvas.create_polygon(points,fill='darkgreen')
            for i in range(self.arena_sides):
                p1 = [oct_verts[i][0],0,oct_verts[i][1]]
                p2 = [oct_verts[(i+1)%self.arena_sides][0],0,oct_verts[(i+1)%self.arena_sides][1]]
                proj1 = proj_func(p1,cam_pos,yaw,pitch)
                proj2 = proj_func(p2,cam_pos,yaw,pitch)
                if proj1 and proj2:
                    self.canvas.create_line(proj1[0],proj1[1],proj2[0],proj2[1],fill='darkgray',width=2)
            for i in range(self.arena_sides):
                bot1 = [oct_verts[i][0],0,oct_verts[i][1]]
                bot2 = [oct_verts[(i+1)%self.arena_sides][0],0,oct_verts[(i+1)%self.arena_sides][1]]
                top1 = [bot1[0],self.arena_height,bot1[2]]
                top2 = [bot2[0],self.arena_height,bot2[2]]
                pairs = [(bot1,bot2),(top1,top2),(bot1,top1),(bot2,top2)]
                for pair in pairs:
                    pr1 = proj_func(pair[0],cam_pos,yaw,pitch)
                    pr2 = proj_func(pair[1],cam_pos,yaw,pitch)
                    if pr1 and pr2:
                        self.canvas.create_line(pr1[0],pr1[1],pr2[0],pr2[1],fill='gray',width=1)

            for entity_list in [self.bosses,self.objects]:
                for entity in entity_list:
                    if 'visible' in entity and not entity['visible']: continue
                    projected_verts = []
                    for v in entity['verts']:
                        world_v = add(entity['pos'],scal_mul(entity['scale'],v))
                        proj = proj_func(world_v,cam_pos,yaw,pitch)
                        if proj: projected_verts.append(proj)
                    face_colors = entity.get('face_colors',[entity['color']]*len(entity['faces']))
                    for f_idx,face in enumerate(entity['faces']):
                        projs = [projected_verts[j] for j in face if j < len(projected_verts)]
                        if len(projs) == len(face):
                            points = [(p[0],p[1]) for p in projs]
                            v0 = scal_mul(entity['scale'],entity['verts'][face[0]])
                            v1 = scal_mul(entity['scale'],entity['verts'][face[1]])
                            v2 = scal_mul(entity['scale'],entity['verts'][face[2]])
                            normal = cross(sub(v1,v0),sub(v2,v0))
                            norm = sqrt(dot(normal,normal))
                            if norm > 0:
                                normal = scal_mul(1/norm,normal)
                            dot_nl = max(0,dot(normal,self.light_dir))
                            shade = 0.3 + 0.7*dot_nl
                            base_color = face_colors[f_idx]
                            if base_color=='red': r,g,b=255,0,0
                            elif base_color=='black': r,g,b=0,0,0
                            elif base_color=='gray': r,g,b=128,128,128
                            else: r,g,b=255,255,255
                            fill_color = '#%02x%02x%02x' % (int(r*shade),int(g*shade),int(b*shade))
                            self.canvas.create_polygon(points,fill=fill_color,outline='black')
                    center_proj = proj_func(entity['pos'],cam_pos,yaw,pitch)
                    if center_proj and 'health' in entity:
                        rad_screen = 25 / max(1,center_proj[2]*0.1)
                        health_ratio = entity['health']/entity['max_health']
                        bbox = (center_proj[0]-rad_screen,center_proj[1]-rad_screen,center_proj[0]+rad_screen,center_proj[1]+rad_screen)
                        self.canvas.create_arc(bbox,start=0,extent=360*health_ratio,style='arc',outline='red' if health_ratio>0.3 else 'darkred',width=4)
                        if entity['health'] < entity['max_health']/2:
                            glow_color = {'cold':'cyan','hot':'orange','poison':'green','dry':'brown','humid':'blue','physical':'gray'}.get(entity['element'],'white')
                            self.canvas.create_oval(center_proj[0]-rad_screen-2,center_proj[1]-rad_screen-2,center_proj[0]+rad_screen+2,center_proj[1]+rad_screen+2,outline=glow_color)

            for proj in self.projectiles:
                proj_proj = proj_func(proj['pos'],cam_pos,yaw,pitch)
                if proj_proj:
                    size = 5 / max(1,proj_proj[2]*0.05)
                    self.canvas.create_oval(proj_proj[0]-size,proj_proj[1]-size,proj_proj[0]+size,proj_proj[1]+size,fill=proj['color'])

            for p in self.particles:
                proj = proj_func(p['pos'],cam_pos,yaw,pitch)
                if proj:
                    size = 3 - (proj[2]*0.01)
                    self.canvas.create_oval(proj[0]-size,proj[1]-size,proj[0]+size,proj[1]+size,fill=p['color'])

            for t in self.trails:
                ps = proj_func(t['start'],cam_pos,yaw,pitch)
                pe = proj_func(t['end'],cam_pos,yaw,pitch)
                if ps and pe:
                    self.canvas.create_line(ps[0],ps[1],pe[0],pe[1],fill=t['color'],width=4)

            for pickup in self.pickups:
                p_proj = proj_func(pickup['pos'],cam_pos,yaw,pitch)
                if p_proj:
                    size = 5 / max(1,p_proj[2]*0.05)
                    self.canvas.create_oval(p_proj[0]-size,p_proj[1]-size,p_proj[0]+size,p_proj[1]+size,fill=pickup['color'])

            if render_player:
                p_proj = proj_func(self.cam_pos,cam_pos,yaw,pitch)
                if p_proj:
                    self.canvas.create_oval(p_proj[0]-5,p_proj[1]-5,p_proj[0]+5,p_proj[1]+5,fill=self.player_color)
                    if sum(self.elements.values()) > 0:
                        self.canvas.create_oval(p_proj[0]-7,p_proj[1]-7,p_proj[0]+7,p_proj[1]+7,outline='white')

            if self.view_mode in ['1st', '3rd']:
                self.canvas.create_line(self.center_x-15, self.center_y, self.center_x+15, self.center_y, fill='lime', width=2)
                self.canvas.create_line(self.center_x, self.center_y-15, self.center_x, self.center_y+15, fill='lime', width=2)

            if self.view_mode in ['faux3d_xy_3rd', 'faux3d_xy_1st']:
                self.canvas.create_oval(self.center_x-2, self.center_y-2, self.center_x+2, self.center_y+2, fill='white')

            # HUD - drawn LAST
            stats_text = self.get_stats_text()
            self.canvas.create_text(10, 10, anchor='nw', fill='white', text=stats_text, font=('Courier', 10))

            self.canvas.create_text(self.width - 10, 10, anchor='ne', text=f"Attack: {self.attack_level}", fill='pink')
            self.canvas.create_text(self.width - 10, 30, anchor='ne', text=f"Defense: {self.defense_level}", fill='teal')
            self.canvas.create_text(self.width - 10, 50, anchor='ne', text=f"Stamina: {self.stamina:.0f}", fill='grey')

            self.canvas.create_text(10, self.height - 30, anchor='sw', text=f"Magic: {self.magic:.0f}", fill='blue')
            self.canvas.create_text(100, self.height - 30, anchor='sw', text=f"Health: {self.health:.0f}", fill='red')
            self.canvas.create_text(200, self.height - 30, anchor='sw', text=f"Armor: {self.armor}", fill='yellow', font=('Courier', 8))

            equip_text = f"Weapon: {self.weapon} Next: {self.next_weapon}\nEquip: {self.equip}"
            self.canvas.create_text(self.width - 10, self.height - 30, anchor='se', text=equip_text, fill='white')

        except Exception as e:
            self.report.append(str(e))

    def loop(self):
        if not self.running: return
        if not self.paused and not self.choose_gain:
            self.update()
        self.render()
        self.root.after(16, self.loop)

if __name__ == "__main__":
    game = Game()
    game.root.mainloop()
