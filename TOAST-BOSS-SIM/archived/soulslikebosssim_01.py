import tkinter as tk
from math import sin, cos, tan, pi, radians, sqrt, atan2
import time
import sys
import ctypes
import random
import copy

sys.setrecursionlimit(2000)  # Increase to avoid recursion error

# GJK helper functions (unchanged)
def cross(a, b):
    return [
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0]
    ]

def dot(a, b):
    return sum(ai * bi for ai, bi in zip(a, b))

def sub(a, b):
    return [ai - bi for ai, bi in zip(a, b)]

def add(a, b):
    return [ai + bi for ai, bi in zip(a, b)]

def scal_mul(s, a):
    return [s * ai for ai in a]

def neg(a):
    return [-ai for ai in a]

def norm_sq(a):
    return dot(a, a)

def support(shape, d):
    if shape['type'] == 'sphere':
        pos = shape['pos']
        r = shape['radius']
        n = sqrt(norm_sq(d))
        if n == 0:
            return pos[:]
        nd = scal_mul(1 / n, d)
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
        return [], d  # degenerate
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
        return [c, b, a], d  # flip triangle

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
    if dot(cross(ab, ac), ao) < 0:
        return False
    if dot(cross(ab, ad), ao) < 0:
        return False
    if dot(cross(ac, ad), ao) < 0:
        return False
    return True

def gjk_intersect(shape1, shape2):
    d = [1.0, 0.0, 0.0]
    simplex = []
    a = sub(support(shape1, d), support(shape2, neg(d)))
    if dot(a, d) < 0:
        return False
    simplex.append(a)
    d = neg(a)
    if norm_sq(d) < 1e-6:
        d = [1.0, 0.0, 0.0]
    iter = 0
    while iter < 32:
        a = sub(support(shape1, d), support(shape2, neg(d)))
        if dot(a, d) < 0:
            return False
        simplex.append(a)
        if len(simplex) == 4:
            if tetra_contains_origin(simplex):
                return True
            simplex, d = update_tetra(simplex, d)
            if not simplex:
                return False
        elif len(simplex) == 3:
            simplex, d = update_triangle(simplex, d)
            if not simplex:
                return False
        elif len(simplex) == 2:
            simplex, d = update_line(simplex, d)
            if not simplex:
                return False
        iter += 1
    return False

class Game:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Souls-Like Boss Simulator")
        self.width = 800
        self.height = 600
        self.canvas = tk.Canvas(self.root, width=self.width, height=self.height, bg='black')
        self.canvas.pack()

        # Bindings
        self.root.bind('<KeyPress>', self.key_press)
        self.root.bind('<KeyRelease>', self.key_release)
        self.root.bind('<Button-1>', self.left_press)
        self.root.bind('<ButtonRelease-1>', self.left_release)
        self.root.bind('<Button-3>', self.right_press)
        self.root.bind('<ButtonRelease-3>', self.right_release)
        self.root.bind('<Motion>', self.mouse_motion)
        self.root.bind('<Escape>', self.toggle_pause)

        # Mouse capture (fixed: cross-platform warp)
        self.mouse_captured = True
        self.center_x = self.width // 2
        self.center_y = self.height // 2
        self.root.attributes('-fullscreen', True)  # Fullscreen for lock
        self.hide_cursor()
        self.last_warp = 0  # Debounce
        self.center_mouse()

        # Game state
        self.running = True
        self.paused = False
        self.level = 0
        self.exp = 0
        self.exp_needed = 3  # Level 0: 3xp
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
        self.elements = {'cold': 0, 'hot': 0, 'poison': 0, 'dry': 0, 'humid': 0, 'physical': 1}  # Start physical
        self.weapon = 'fists'
        self.next_weapon = 'sword'
        self.equip = {'head': None, 'chest': 'basic', 'legs': None}  # Basic armor drop
        self.progression = ['armor', 'weapon', 'skill_point']  # Random drops after level 0
        self.progress_index = 0
        self.choose_gain = False
        self.choice_text_id = None
        self.bosses = []
        self.projectiles = []
        self.view_mode = '2d_top'  # Default: 2D top-down; options: '1st', '3rd', 'helicopter', '2d_top', '2d_side', 'faux3d_xy_3rd', 'faux3d_xy_1st'
        self.player_color = 'blue'  # Default

        # Physics
        self.vel_x = 0
        self.vel_y = 0
        self.vel_z = 0
        self.on_ground = True
        self.eye_height = 1.8
        self.player_radius = 1.5
        self.gravity = 30.0
        self.jump_speed = 12.0
        self.max_move_speed = 6.0
        self.move_accel = 25.0
        self.air_move_accel = 15.0
        self.friction = 15.0

        # Camera
        self.cam_pos = [0, 1.8, 0]
        self.yaw = 0
        self.pitch = 0
        self.target_yaw = 0
        self.target_pitch = 0
        self.fov = 90
        self.turn_speed = 0.003
        self.smooth_factor = 0.2
        self.invert_y = False

        # Keys
        self.keys = set()

        # Arena
        self.arena_radius = 100.0
        self.arena_height = 50.0
        self.arena_sides = 8

        # Particles
        self.particles = []

        # Attack trails
        self.trails = []

        # Attack states (fixed: hold/transfer logic)
        self.left_held = False
        self.right_held = False
        self.left_hold_start = 0
        self.right_hold_start = 0
        self.last_left_click = 0
        self.last_right_click = 0
        self.invulnerable_time = 0
        self.invulnerable_duration = 0.5  # Base
        self.left_charge = 0  # Damage multiplier (max 5x)
        self.right_charge = 0  # Invuln window (max 2s)
        self.max_left_charge_time = 1.0  # 5x at 1s
        self.max_right_charge_time = 1.5  # 2s at 1.5s

        # UI
        self.stats_text_id = None

        # Pause menu (JAM-style scrolled frame)
        self.pause_menu = None

        # Init game
        self.generate_boss()  # Level 0: sphere
        self.last_time = time.time()
        self.loop()

    def hide_cursor(self):
        self.root.config(cursor='none')

    def show_cursor(self):
        self.root.config(cursor='')

    def center_mouse(self):
        current = time.time()
        if self.mouse_captured and current - self.last_warp > 0.05:  # Debounce
            self.last_warp = current
            try:
                x = self.root.winfo_rootx() + self.center_x
                y = self.root.winfo_rooty() + self.center_y
                if sys.platform == 'win32':
                    ctypes.windll.user32.SetCursorPos(x, y)
                # Cross-platform fallback: warp event
                self.root.event_generate("<Motion>", warp=True, x=self.center_x, y=self.center_y)
            except:
                pass

    def mouse_motion(self, event):
        if not self.mouse_captured or self.paused:
            return
        dx = event.x - self.center_x
        dy = event.y - self.center_y
        invert_mult = -1 if self.invert_y else 1
        self.target_yaw = (self.target_yaw - dx * self.turn_speed) % (2 * pi)
        self.target_pitch = max(min(self.target_pitch - dy * self.turn_speed * invert_mult, pi/2 - 0.01), -pi/2 + 0.01)
        self.center_mouse()

    def key_press(self, event):
        key = event.keysym.lower()
        self.keys.add(key)
        if self.choose_gain:
            if key == 'h':
                self.max_health += 20 + self.level // 10
                self.health = self.max_health
                self.choose_gain = False
                self.canvas.delete(self.choice_text_id)
                self.choice_text_id = None
            elif key == 's':
                self.max_stamina += 20 + self.level // 10
                self.stamina = self.max_stamina
                self.choose_gain = False
                self.canvas.delete(self.choice_text_id)
                self.choice_text_id = None
            elif key in ['1', '2', '3', '4', '5', '6']:  # Elements
                elem_map = {'1': 'cold', '2': 'hot', '3': 'poison', '4': 'dry', '5': 'humid', '6': 'physical'}
                self.elements[elem_map[key]] += 1
                self.choose_gain = False  # After element, prompt health/stamina

    def key_release(self, event):
        self.keys.discard(event.keysym.lower())

    def left_press(self, event):
        current = time.time()
        if current - self.last_left_click < 0.3:
            self.do_strong_attack()
        else:
            self.do_normal_attack()
        self.last_left_click = current
        self.left_held = True
        self.left_hold_start = current
        if self.right_held:
            # Transfer right charge to left
            self.left_charge += self.right_charge * 0.5  # Partial transfer
            self.right_charge = 0
            self.do_attack_in_defense()

    def left_release(self, event):
        if self.left_held and time.time() - self.left_hold_start > 0.2:
            self.do_charge_attack(self.left_charge)
            self.left_charge = 0
        self.left_held = False

    def right_press(self, event):
        current = time.time()
        if current - self.last_right_click < 0.3:
            self.do_jump()
        else:
            self.do_dodge()
        self.last_right_click = current
        self.right_held = True
        self.right_hold_start = current
        if self.left_held:
            # Transfer left charge to right
            self.right_charge += self.left_charge * 0.5
            self.left_charge = 0
            self.do_charged_defense()

    def right_release(self, event):
        if self.right_held and time.time() - self.right_hold_start > 0.3:
            self.do_defend_stance(self.right_charge)
            self.right_charge = 0
        self.right_held = False

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
        # JAM-style scrolled frame
        self.pause_menu = tk.Frame(self.root, bg='gray')
        self.pause_menu.place(relx=0.5, rely=0.5, anchor='center')
        scrolled = tk.Frame(self.pause_menu)  # Simple scroll (no full ScrolledFrame for brevity)
        scrolled.pack(fill='both', expand=True)
        tk.Label(scrolled, text="Pause", bg='gray', fg='white', font=('Arial', 16)).pack()
        fov_scale = tk.Scale(scrolled, from_=30, to=120, orient='horizontal', label='FOV', command=self.set_fov, bg='gray', fg='white')
        fov_scale.set(self.fov)
        fov_scale.pack()
        turn_scale = tk.Scale(scrolled, from_=0.001, to=0.01, resolution=0.001, orient='horizontal', label='Mouse Sensitivity', command=self.set_turn_speed, bg='gray', fg='white')
        turn_scale.set(self.turn_speed)
        turn_scale.pack()
        smooth_scale = tk.Scale(scrolled, from_=0.0, to=1.0, resolution=0.05, orient='horizontal', label='Smoothing Factor', command=self.set_smooth_factor, bg='gray', fg='white')
        smooth_scale.set(self.smooth_factor)
        smooth_scale.pack()
        invert_var = tk.BooleanVar(value=self.invert_y)
        invert_check = tk.Checkbutton(scrolled, text="Invert Y Axis", variable=invert_var, command=lambda: self.set_invert_y(invert_var.get()), bg='gray', fg='white')
        invert_check.pack()
        color_button = tk.Button(scrolled, text="Change User Color", command=self.change_user_color, bg='darkgray', fg='white')
        color_button.pack()
        view_var = tk.StringVar(value=self.view_mode)
        view_menu = tk.OptionMenu(scrolled, view_var, '1st', '3rd', 'helicopter', '2d_top', '2d_side', 'faux3d_xy_3rd', 'faux3d_xy_1st', command=self.set_view_mode)
        view_menu.pack()
        for w in ['fists', 'sword', 'axe', 'gun', 'bow', 'magic']:
            tk.Button(scrolled, text=w.capitalize(), command=lambda ww=w: self.set_weapon(ww), bg='darkgray', fg='white').pack()
        tk.Button(scrolled, text="Reset", command=self.reset, bg='darkgray', fg='white').pack()
        tk.Button(scrolled, text="Exit", command=self.exit_game, bg='darkgray', fg='white').pack()

    def set_fov(self, val):
        self.fov = float(val)

    def set_turn_speed(self, val):
        self.turn_speed = float(val)

    def set_smooth_factor(self, val):
        self.smooth_factor = float(val)

    def set_invert_y(self, val):
        self.invert_y = bool(val)

    def change_user_color(self):
        self.player_color = random.choice(['blue', 'green', 'purple', 'red', 'yellow'])

    def set_view_mode(self, mode):
        self.view_mode = mode

    def set_weapon(self, w):
        self.weapon, self.next_weapon = w, self.weapon  # Swap

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
        self.elements = {'cold': 0, 'hot': 0, 'poison': 0, 'dry': 0, 'humid': 0, 'physical': 1}
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
        self.generate_boss()

    def exit_game(self):
        if tk.messagebox.askyesno("Exit", "Save before exit?"):
            # Placeholder save
            pass
        self.running = False
        self.root.quit()

    def get_stats_text(self):
        elements_str = ', '.join([f"{k}:{v}" for k, v in self.elements.items()])
        total_boss_health = sum(b['health'] for b in self.bosses)
        total_boss_max = sum(b['max_health'] for b in self.bosses)
        boss_str = f"{len(self.bosses)} Bosses: {total_boss_health:.0f}/{total_boss_max:.0f}"
        equip_str = f"Head: {self.equip['head'] or 'None'}, Chest: {self.equip['chest'] or 'None'}, Legs: {self.equip['legs'] or 'None'}"
        return f"Level: {self.level} Exp: {self.exp}/{self.exp_needed}\nAttack: {self.attack_level} (Pink)\nDefense: {self.defense_level} (Teal)\nStamina: {self.stamina:.0f}/{self.max_stamina} (Grey)\nMagic: {self.magic:.0f}/{self.max_magic} (Blue)\nHealth: {self.health:.0f}/{self.max_health} (Red)\nArmor: {self.armor} (Yellow)\nSkill: {self.skill_level} Weapon: {self.weapon} Next: {self.next_weapon}\nElements: {elements_str}\nLife Steal: {self.life_steal}\n{equip_str}\n{boss_str}"

    def generate_boss(self):
        if self.level == 0:
            n = 20  # Sphere approx (high verts)
        else:
            n = (self.level % 8) + 3  # Increasing complexity
        verts = [[cos(i * 2 * pi / n), 0, sin(i * 2 * pi / n)] for i in range(n)]  # Circle/poly
        edges = [[i, (i+1) % n] for i in range(n)]
        boss_health = 100 + self.level * 20
        radius = 3 + self.level * 0.2
        pos = [random.uniform(-80, 80), 4.0, random.uniform(10, 40)]
        scale = 3 + self.level * 0.2
        boss = {
            'type': 'poly' if n > 20 else 'sphere',
            'pos': pos,
            'vel_x': 0.0,
            'vel_z': 0.0,
            'scale': scale,
            'health': boss_health,
            'max_health': boss_health,
            'verts': verts,
            'edges': edges,
            'radius': radius,
            'speed': 4 + self.level * 0.1,
            'damage': 10 + self.level * 2,
            'attack_cooldown': time.time() + random.uniform(0.5, 1.5),
            'split': False,
            'element': random.choice(list(self.elements.keys())),
            'color': 'red',  # Base
            'attack_type': random.choice(['melee', 'range', 'run_away'])  # Fixed: initialize
        }
        self.bosses.append(boss)

    def do_normal_attack(self):
        # Range-based
        damage = self.attack_level * (1 + sum(self.elements.values()) * 0.1)
        if self.weapon in ['fists', 'sword', 'axe']:  # Close
            range_ = 5
        elif self.weapon in ['gun', 'bow']:  # Mid
            range_ = 20
        else:  # Magic
            range_ = 30
            self.magic -= 10
        self.fire_projectile(damage, range_)

    def do_strong_attack(self):
        self.do_normal_attack()  # Double damage
        self.do_normal_attack()

    def do_charge_attack(self, charge):
        mult = min(5, 1 + charge / self.max_left_charge_time * 4)
        self.do_normal_attack()  # With mult
        # Apply mult to damage in fire_projectile

    def do_dodge(self):
        # Roll: add vel in dir
        self.vel_x += sin(self.yaw) * 10
        self.vel_z += cos(self.yaw) * 10
        self.stamina -= 20
        self.invulnerable_duration += 0.5

    def do_jump(self):
        if self.on_ground:
            self.vel_y = self.jump_speed
            self.stamina -= 10

    def do_charged_defense(self):
        self.armor *= 1.5  # Temp boost

    def do_defend_stance(self, charge):
        window = min(2, charge / self.max_right_charge_time * 2)
        self.invulnerable_duration += window + 0.1 * (charge / 0.3)  # +0.1s per 0.3s

    def do_attack_in_defense(self):
        self.do_normal_attack()  # With defense boost

    def fire_projectile(self, damage, range_):
        dx = sin(self.yaw) * cos(self.pitch)
        dy = -sin(self.pitch)
        dz = cos(self.yaw) * cos(self.pitch)
        pos = self.cam_pos[:]
        vel = [dx * 20, dy * 20, dz * 20]
        color = 'yellow'
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
        self.trails.append({'start': [sx, sy, sz], 'end': [ex, ey, ez], 'vel': vel, 'color': color, 'lifetime': 0.6, 'start_time': time.time()})

    def hit_boss(self, idx, damage):
        elem_dmg = damage * (self.elements.get(self.bosses[idx]['element'], 0) * 0.2)
        total_dmg = damage + elem_dmg
        self.bosses[idx]['health'] -= total_dmg
        self.add_particles(self.bosses[idx]['pos'], 'yellow')
        if self.life_steal > 0:
            heal = total_dmg * self.life_steal / 100
            self.health = min(self.max_health, self.health + heal)
        if self.bosses[idx]['health'] <= 0:
            self.on_boss_kill(idx)
            return
        if self.bosses[idx]['health'] <= self.bosses[idx]['max_health'] / 2 and not self.bosses[idx].get('split', False) and len(self.bosses[idx]['verts']) % 2 == 0:
            self.split_boss(idx)

    def on_boss_kill(self, idx):
        del self.bosses[idx]
        self.exp += 1  # 1 XP per boss
        if self.level == 0:
            drop = 'armor'  # Guaranteed
            self.armor += 10
            self.equip['chest'] = 'basic_armor'
        else:
            drop = random.choice(self.progression)
            if drop == 'armor':
                self.armor += 3 + self.level // 2
            elif drop == 'weapon':
                self.next_weapon = random.choice(['sword', 'axe', 'gun', 'bow', 'magic'])
            elif drop == 'skill_point':
                self.skill_level += 1
        # Level up check
        while self.exp >= self.exp_needed:
            self.level += 1
            self.exp -= self.exp_needed
            # Curve: level 1=9, 10=39, 100=319, +10% stats per 100 levels
            self.exp_needed = 3 + self.level * 3 + (self.level // 10) * 10
            if self.level % 100 == 0:
                self.attack_level *= 1.1
                self.defense_level *= 1.1
                self.max_health *= 1.1
                self.max_stamina *= 1.1
                self.max_magic *= 1.1
            self.choose_gain = True  # Pick element then health/stamina
            self.choice_text_id = self.canvas.create_text(self.center_x, self.height - 30, anchor='s', fill='white', text="1-6: Element (cold/hot/poison/dry/humid/physical) then H: Health | S: Stamina")
        self.generate_boss()

    def split_boss(self, idx):
        boss = self.bosses[idx]
        new_pos = boss['pos'][:]
        new_pos[0] += random.uniform(-10, 10)
        new_pos[2] += random.uniform(-10, 10)
        new_boss = copy.deepcopy(boss)
        new_boss['pos'] = new_pos
        new_boss['vel_x'] = new_boss['vel_z'] = 0
        new_boss['health'] = boss['max_health'] / 4
        new_boss['split'] = True
        new_boss['attack_cooldown'] = time.time() + random.uniform(0.5, 1.5)
        self.bosses.insert(idx + 1, new_boss)
        boss['split'] = True
        boss['health'] = boss['max_health'] / 4
        # Explosion damage to player
        dist = sqrt((self.cam_pos[0] - boss['pos'][0])**2 + (self.cam_pos[2] - boss['pos'][2])**2)
        if dist < 10:
            self.boss_hits_player(boss['damage'] / 2)

    def boss_hits_player(self, damage):
        current = time.time()
        if current < self.invulnerable_time:
            return
        net_damage = max(0, damage - self.armor)
        if self.right_held:
            net_damage *= 0.4
        self.health -= net_damage
        self.add_particles(self.cam_pos, 'orange')
        self.invulnerable_time = current + self.invulnerable_duration
        if self.health <= 0:
            self.health = self.max_health * 0.3
            self.cam_pos = [0, self.eye_height, 0]
            self.vel_x = self.vel_y = self.vel_z = 0

    def add_particles(self, pos, color):
        for _ in range(15):
            vel = [random.uniform(-8, 8), random.uniform(3, 12), random.uniform(-8, 8)]
            self.particles.append({'pos': pos[:], 'vel': vel, 'color': color, 'lifetime': 1.2, 'start_time': time.time()})

    def project(self, point, cam_pos=None, yaw=None, pitch=None):
        if cam_pos is None:
            cam_pos = self.cam_pos
        if yaw is None:
            yaw = self.yaw
        if pitch is None:
            pitch = self.pitch
        # Fixed: added epsilon to avoid crash
        cx, cy, cz = cam_pos
        dx = point[0] - cx
        dy = point[1] - cy
        dz = point[2] - cz
        # yaw
        dx2 = dx * cos(yaw) + dz * sin(yaw)
        dz2 = -dx * sin(yaw) + dz * cos(yaw)
        dy2 = dy
        # pitch
        dy3 = dy2 * cos(pitch) - dz2 * sin(pitch)
        dz3 = dy2 * sin(pitch) + dz2 * cos(pitch)
        dx3 = dx2
        if dz3 < 0.001:  # Fixed threshold
            return None
        f = (self.width / 2.0) / tan(radians(self.fov) / 2)
        sx = self.center_x + dx3 * f / dz3
        sy = self.center_y - dy3 * f / dz3
        return (sx, sy, dz3)

    def iso_project(self, point):
        # Simple faux 3D isometric on xy
        scale = 5
        angle = radians(30)
        sx = (point[0] - point[2]) * cos(angle) * scale + self.center_x
        sy = self.center_y - point[1] * scale - (point[0] + point[2]) * sin(angle) * scale
        return (sx, sy, point[1])  # Depth approx y

    def update(self):
        current = time.time()
        dt = min(current - self.last_time, 0.05)
        self.last_time = current

        # Charges update
        if self.left_held:
            self.left_charge = min(self.max_left_charge_time, time.time() - self.left_hold_start)
        if self.right_held:
            self.right_charge = min(self.max_right_charge_time, time.time() - self.right_hold_start)

        # Smooth camera
        self.yaw += (self.target_yaw - self.yaw) * self.smooth_factor
        self.pitch += (self.target_pitch - self.pitch) * self.smooth_factor

        # Player physics (unchanged, but add charges to max)
        self.max_left_charge_time = 1.0 + self.level / 100 * 0.1  # Increase with level
        self.max_right_charge_time = 1.5 + self.level / 100 * 0.1
        self.vel_y -= self.gravity * dt

        # Input (unchanged)
        input_x = input_z = 0.0
        if 'w' in self.keys:
            input_x += sin(self.yaw)
            input_z += cos(self.yaw)
        if 's' in self.keys:
            input_x -= sin(self.yaw)
            input_z -= cos(self.yaw)
        if 'a' in self.keys:
            input_x -= cos(self.yaw)
            input_z += sin(self.yaw)
        if 'd' in self.keys:
            input_x += cos(self.yaw)
            input_z -= sin(self.yaw)
        input_len = sqrt(input_x**2 + input_z**2)
        if input_len > 0:
            input_x /= input_len
            input_z /= input_len
        accel = self.air_move_accel if not self.on_ground else self.move_accel
        self.vel_x += input_x * accel * dt
        self.vel_z += input_z * accel * dt

        # Limit horiz speed
        horiz_spd = sqrt(self.vel_x**2 + self.vel_z**2)
        if horiz_spd > self.max_move_speed:
            self.vel_x = (self.vel_x / horiz_spd) * self.max_move_speed
            self.vel_z = (self.vel_z / horiz_spd) * self.max_move_speed

        # Friction
        if self.on_ground:
            fric = self.friction * dt
            if horiz_spd > 0:
                self.vel_x -= (self.vel_x / horiz_spd) * fric
                self.vel_z -= (self.vel_z / horiz_spd) * fric

        # Integrate
        self.cam_pos[0] += self.vel_x * dt
        self.cam_pos[1] += self.vel_y * dt
        self.cam_pos[2] += self.vel_z * dt

        # Ground collision
        if self.cam_pos[1] < self.eye_height:
            self.cam_pos[1] = self.eye_height
            self.vel_y = 0
            self.on_ground = True
        else:
            self.on_ground = False

        # Arena walls player (placeholder: circle clamp)
        dist_xz = sqrt(self.cam_pos[0]**2 + self.cam_pos[2]**2)
        if dist_xz > self.arena_radius - self.player_radius:
            factor = (self.arena_radius - self.player_radius) / dist_xz
            self.cam_pos[0] *= factor
            self.cam_pos[2] *= factor
            self.vel_x = self.vel_z = 0

        # Boss updates
        px, pz = self.cam_pos[0], self.cam_pos[2]
        for boss in self.bosses:
            dx = px - boss['pos'][0]
            dz = pz - boss['pos'][2]
            dist_xz = sqrt(dx**2 + dz**2)
            if dist_xz > 2:
                dx /= dist_xz
                dz /= dist_xz
                boss['vel_x'] = dx * boss['speed']
                boss['vel_z'] = dz * boss['speed']
            else:
                boss['vel_x'] = boss['vel_z'] = 0
            # AI variety: random attack type
            if random.random() < 0.1:
                boss['attack_type'] = random.choice(['melee', 'range', 'run_away'])
            if boss['attack_type'] == 'run_away' and dist_xz < 5:
                boss['vel_x'] = -boss['vel_x']
                boss['vel_z'] = -boss['vel_z']
            boss['pos'][0] += boss['vel_x'] * dt
            boss['pos'][2] += boss['vel_z'] * dt
            # Arena clamp for boss
            b_dist = sqrt(boss['pos'][0]**2 + boss['pos'][2]**2)
            if b_dist > self.arena_radius - boss['radius']:
                factor = (self.arena_radius - boss['radius']) / b_dist
                boss['pos'][0] *= factor
                boss['pos'][2] *= factor
                boss['vel_x'] = boss['vel_z'] = 0

        # Collisions (player-boss, boss-boss using GJK)
        player_shape = {'type': 'sphere', 'pos': self.cam_pos, 'radius': self.player_radius}
        for i, boss in enumerate(self.bosses):
            boss_shape = {'type': boss['type'], 'pos': boss['pos'], 'radius': boss['radius'], 'scale': boss['scale'], 'verts': boss['verts']}
            if gjk_intersect(player_shape, boss_shape):
                # Resolve: push apart
                dx = self.cam_pos[0] - boss['pos'][0]
                dz = self.cam_pos[2] - boss['pos'][2]
                dist = sqrt(dx**2 + dz**2)
                if dist > 0:
                    dx /= dist
                    dz /= dist
                    overlap = self.player_radius + boss['radius'] - dist
                    self.cam_pos[0] += dx * overlap / 2
                    self.cam_pos[2] += dz * overlap / 2
                    boss['pos'][0] -= dx * overlap / 2
                    boss['pos'][2] -= dz * overlap / 2
            for j in range(i + 1, len(self.bosses)):
                other = self.bosses[j]
                other_shape = {'type': other['type'], 'pos': other['pos'], 'radius': other['radius'], 'scale': other['scale'], 'verts': other['verts']}
                if gjk_intersect(boss_shape, other_shape):
                    # Push apart
                    dx = boss['pos'][0] - other['pos'][0]
                    dz = boss['pos'][2] - other['pos'][2]
                    dist = sqrt(dx**2 + dz**2)
                    if dist > 0:
                        dx /= dist
                        dz /= dist
                        overlap = boss['radius'] + other['radius'] - dist
                        boss['pos'][0] += dx * overlap / 2
                        boss['pos'][2] += dz * overlap / 2
                        other['pos'][0] -= dx * overlap / 2
                        other['pos'][2] -= dz * overlap / 2

        # Boss attacks
        for boss in self.bosses:
            if current > boss['attack_cooldown']:
                dx = self.cam_pos[0] - boss['pos'][0]
                dy = self.cam_pos[1] - boss['pos'][1]
                dz = self.cam_pos[2] - boss['pos'][2]
                dist3d = sqrt(dx**2 + dy**2 + dz**2)
                if dist3d < 14:
                    self.boss_hits_player(boss['damage'])
                    self.add_boss_trail(boss['pos'], [dx, dy, dz], 'red')
                    boss['attack_cooldown'] = current + random.uniform(0.8, 2.5)

        # Projectiles update
        new_proj = []
        for proj in self.projectiles:
            if current - proj['start_time'] < proj['lifetime']:
                proj['pos'][0] += proj['vel'][0] * dt
                proj['pos'][1] += proj['vel'][1] * dt
                proj['pos'][2] += proj['vel'][2] * dt
                proj['vel'][1] -= self.gravity * dt
                # Ground/arena collision (simple)
                if proj['pos'][1] < 0:
                    continue
                proj_dist = sqrt(proj['pos'][0]**2 + proj['pos'][2]**2)
                if proj_dist > self.arena_radius:
                    continue
                # Hit boss
                proj_shape = {'type': 'sphere', 'pos': proj['pos'], 'radius': 0.5}
                for i, boss in enumerate(self.bosses):
                    boss_shape = {'type': boss['type'], 'pos': boss['pos'], 'radius': boss['radius'], 'scale': boss['scale'], 'verts': boss['verts']}
                    if gjk_intersect(proj_shape, boss_shape):
                        self.hit_boss(i, proj['damage'])
                        self.add_particles(proj['pos'], proj['color'])
                        break
                else:
                    new_proj.append(proj)
        self.projectiles = new_proj

        # Particles
        self.particles = [p for p in self.particles if current - p['start_time'] < p['lifetime']]
        for p in self.particles:
            p['pos'][0] += p['vel'][0] * dt
            p['pos'][1] += p['vel'][1] * dt
            p['pos'][2] += p['vel'][2] * dt
            p['vel'][1] -= self.gravity * dt

        # Trails
        self.trails = [t for t in self.trails if current - t['start_time'] < t['lifetime']]
        for t in self.trails:
            t['start'][0] += t['vel'][0] * dt
            t['start'][1] += t['vel'][1] * dt
            t['start'][2] += t['vel'][2] * dt
            t['end'][0] += t['vel'][0] * dt
            t['end'][1] += t['vel'][1] * dt
            t['end'][2] += t['vel'][2] * dt

        # Regen
        if self.stamina < self.max_stamina:
            self.stamina += 25 * dt
        if self.magic < self.max_magic:
            self.magic += 10 * dt

        # Clamp
        self.stamina = min(self.max_stamina, max(0, self.stamina))
        self.magic = min(self.max_magic, max(0, self.magic))
        self.health = min(self.max_health, max(0, self.health))

    def render(self):
        self.canvas.delete("all")

        # HUD
        stats_text = self.get_stats_text()
        self.stats_text_id = self.canvas.create_text(10, 10, anchor='nw', fill='white', text=stats_text, font=('Courier', 10))
        # Magic (bottom left, blue)
        self.canvas.create_text(10, self.height - 30, anchor='sw', text=f"Magic: {self.magic:.0f}", fill='blue')
        # Health (next to magic, red)
        self.canvas.create_text(100, self.height - 30, anchor='sw', text=f"Health: {self.health:.0f}", fill='red')
        # Armor (next to health, yellow small)
        self.canvas.create_text(200, self.height - 30, anchor='sw', text=f"Armor: {self.armor}", fill='yellow', font=('Courier', 8))
        # Weapon/equip (bottom right)
        equip_text = f"Weapon: {self.weapon} Next: {self.next_weapon}\nEquip: {self.equip}"
        self.canvas.create_text(self.width - 10, self.height - 30, anchor='se', text=equip_text, fill='white')
        # Attack/defense/stamina (top right)
        self.canvas.create_text(self.width - 10, 10, anchor='ne', text=f"Attack: {self.attack_level}", fill='pink')
        self.canvas.create_text(self.width - 10, 30, anchor='ne', text=f"Defense: {self.defense_level}", fill='teal')
        self.canvas.create_text(self.width - 10, 50, anchor='ne', text=f"Stamina: {self.stamina:.0f}", fill='grey')

        if self.choice_text_id:
            self.canvas.delete(self.choice_text_id)
            self.choice_text_id = self.canvas.create_text(self.center_x, self.height - 30, anchor='s', fill='lime', text="1-6: Element (cold/hot/poison/dry/humid/physical) then H: Health | S: Stamina", font=('Arial', 14, 'bold'))

        # View-specific rendering
        elem_glow_map = {'cold': 'cyan', 'hot': 'orange', 'poison': 'green', 'dry': 'brown', 'humid': 'blue', 'physical': 'gray'}
        cam_pos = self.cam_pos[:]
        yaw = self.yaw
        pitch = self.pitch
        render_player = True
        proj_func = self.project

        if self.view_mode == '1st':
            render_player = False
        elif self.view_mode == '3rd':
            # Behind player
            cam_pos[0] -= sin(yaw) * 10
            cam_pos[2] -= cos(yaw) * 10
            cam_pos[1] += 2
        elif self.view_mode == 'helicopter':
            # High above
            cam_pos[1] = 50
            pitch = -radians(80)  # Look down
        elif self.view_mode == 'faux3d_xy_3rd' or self.view_mode == 'faux3d_xy_1st':
            proj_func = self.iso_project
            if self.view_mode == 'faux3d_xy_1st':
                render_player = False
        # For 2d_top and 2d_side: flat scale
        elif self.view_mode in ['2d_top', '2d_side']:
            scale = 5
            offset_x, offset_y = self.width // 2, self.height // 2
            if self.view_mode == '2d_top':
                # Player
                px = offset_x + cam_pos[0] * scale
                pz = offset_y + cam_pos[2] * scale
                self.canvas.create_oval(px - 5, pz - 5, px + 5, pz + 5, fill=self.player_color)
                # Bosses
                for boss in self.bosses:
                    bx = offset_x + boss['pos'][0] * scale
                    bz = offset_y + boss['pos'][2] * scale
                    self.canvas.create_oval(bx - boss['radius']*scale, bz - boss['radius']*scale, bx + boss['radius']*scale, bz + boss['radius']*scale, outline=boss['color'])
                    # Health ring
                    health_ratio = boss['health'] / boss['max_health']
                    self.canvas.create_arc(bx - boss['radius']*scale, bz - boss['radius']*scale, bx + boss['radius']*scale, bz + boss['radius']*scale, start=0, extent=360*health_ratio, style='arc', outline='red', width=2)
                    # Glow if element
                    if boss['health'] < boss['max_health'] / 2:
                        glow_color = elem_glow_map.get(boss['element'], 'white')
                        self.canvas.create_oval(bx - boss['radius']*scale - 2, bz - boss['radius']*scale - 2, bx + boss['radius']*scale + 2, bz + boss['radius']*scale + 2, outline=glow_color)
                # Projectiles etc.
                for proj in self.projectiles:
                    px = offset_x + proj['pos'][0] * scale
                    pz = offset_y + proj['pos'][2] * scale
                    self.canvas.create_oval(px - 2, pz - 2, px + 2, pz + 2, fill=proj['color'])
                for p in self.particles:
                    px = offset_x + p['pos'][0] * scale
                    pz = offset_y + p['pos'][2] * scale
                    self.canvas.create_oval(px - 1, pz - 1, px + 1, pz + 1, fill=p['color'])
                for t in self.trails:
                    sx = offset_x + t['start'][0] * scale
                    sz = offset_y + t['start'][2] * scale
                    ex = offset_x + t['end'][0] * scale
                    ez = offset_y + t['end'][2] * scale
                    self.canvas.create_line(sx, sz, ex, ez, fill=t['color'], width=2)
                return  # Skip 3D
            else:  # 2d_side
                # Player
                px = offset_x + cam_pos[0] * scale
                py = offset_y - cam_pos[1] * scale
                self.canvas.create_oval(px - 5, py - 5, px + 5, py + 5, fill=self.player_color)
                # Bosses
                for boss in self.bosses:
                    bx = offset_x + boss['pos'][0] * scale
                    by = offset_y - boss['pos'][1] * scale
                    self.canvas.create_oval(bx - boss['radius']*scale, by - boss['radius']*scale, bx + boss['radius']*scale, by + boss['radius']*scale, outline=boss['color'])
                    # Health ring
                    health_ratio = boss['health'] / boss['max_health']
                    self.canvas.create_arc(bx - boss['radius']*scale, by - boss['radius']*scale, bx + boss['radius']*scale, by + boss['radius']*scale, start=0, extent=360*health_ratio, style='arc', outline='red', width=2)
                    # Glow
                    if boss['health'] < boss['max_health'] / 2:
                        glow_color = elem_glow_map.get(boss['element'], 'white')
                        self.canvas.create_oval(bx - boss['radius']*scale - 2, by - boss['radius']*scale - 2, bx + boss['radius']*scale + 2, by + boss['radius']*scale + 2, outline=glow_color)
                # Projectiles etc.
                for proj in self.projectiles:
                    px = offset_x + proj['pos'][0] * scale
                    py = offset_y - proj['pos'][1] * scale
                    self.canvas.create_oval(px - 2, py - 2, px + 2, py + 2, fill=proj['color'])
                for p in self.particles:
                    px = offset_x + p['pos'][0] * scale
                    py = offset_y - p['pos'][1] * scale
                    self.canvas.create_oval(px - 1, py - 1, px + 1, py + 1, fill=p['color'])
                for t in self.trails:
                    sx = offset_x + t['start'][0] * scale
                    sy = offset_y - t['start'][1] * scale
                    ex = offset_x + t['end'][0] * scale
                    ey = offset_y - t['end'][1] * scale
                    self.canvas.create_line(sx, sy, ex, ey, fill=t['color'], width=2)
                return

        # Perspective views: arena
        oct_verts = [[self.arena_radius * cos(i * 2 * pi / self.arena_sides),
                      self.arena_radius * sin(i * 2 * pi / self.arena_sides)] for i in range(self.arena_sides)]
        # Floor lines
        for i in range(self.arena_sides):
            p1 = [oct_verts[i][0], 0, oct_verts[i][1]]
            p2 = [oct_verts[(i+1)%self.arena_sides][0], 0, oct_verts[(i+1)%self.arena_sides][1]]
            proj1 = proj_func(p1, cam_pos, yaw, pitch)
            proj2 = proj_func(p2, cam_pos, yaw, pitch)
            if proj1 and proj2:
                self.canvas.create_line(proj1[0], proj1[1], proj2[0], proj2[1], fill='darkgray', width=2)
        # Walls
        for i in range(self.arena_sides):
            bot1 = [oct_verts[i][0], 0, oct_verts[i][1]]
            bot2 = [oct_verts[(i+1)%self.arena_sides][0], 0, oct_verts[(i+1)%self.arena_sides][1]]
            top1 = [bot1[0], self.arena_height, bot1[2]]
            top2 = [bot2[0], self.arena_height, bot2[2]]
            pairs = [(bot1, bot2), (top1, top2), (bot1, top1), (bot2, top2)]
            for pair in pairs:
                pr1 = proj_func(pair[0], cam_pos, yaw, pitch)
                pr2 = proj_func(pair[1], cam_pos, yaw, pitch)
                if pr1 and pr2:
                    self.canvas.create_line(pr1[0], pr1[1], pr2[0], pr2[1], fill='gray', width=1)

        # Bosses
        for boss in self.bosses:
            projected_verts = []
            for v in boss['verts']:
                world_v = [v[0] * boss['scale'] + boss['pos'][0],
                           v[1] * boss['scale'] + boss['pos'][1],
                           v[2] * boss['scale'] + boss['pos'][2]]
                proj = proj_func(world_v, cam_pos, yaw, pitch)
                if proj:
                    projected_verts.append(proj)
            for e in boss['edges']:
                if e[0] < len(projected_verts) and e[1] < len(projected_verts):
                    p1 = projected_verts[e[0]]
                    p2 = projected_verts[e[1]]
                    if p1 and p2:
                        self.canvas.create_line(p1[0], p1[1], p2[0], p2[1], fill='red', width=2)
            # Health ring
            center_proj = proj_func(boss['pos'], cam_pos, yaw, pitch)
            if center_proj:
                rad_screen = 25 / max(1, center_proj[2] * 0.1)
                health_ratio = max(0, boss['health'] / boss['max_health'])
                bbox = (center_proj[0] - rad_screen, center_proj[1] - rad_screen,
                        center_proj[0] + rad_screen, center_proj[1] + rad_screen)
                self.canvas.create_arc(bbox, start=0, extent=360 * health_ratio, style='arc',
                                       outline='red' if health_ratio > 0.3 else 'darkred', width=4)
            # Element glow
            if center_proj:
                glow_color = elem_glow_map.get(boss['element'], 'white')
                self.canvas.create_oval(center_proj[0] - rad_screen - 2, center_proj[1] - rad_screen - 2, center_proj[0] + rad_screen + 2, center_proj[1] + rad_screen + 2, outline=glow_color)

        # Projectiles/particles/trails
        for proj in self.projectiles:
            proj_proj = proj_func(proj['pos'], cam_pos, yaw, pitch)
            if proj_proj:
                size = 5 / max(1, proj_proj[2] * 0.05)
                self.canvas.create_oval(proj_proj[0] - size, proj_proj[1] - size, proj_proj[0] + size, proj_proj[1] + size, fill=proj['color'])
        for p in self.particles:
            proj = proj_func(p['pos'], cam_pos, yaw, pitch)
            if proj:
                size = 3 - (proj[2] * 0.01)
                self.canvas.create_oval(proj[0]-size, proj[1]-size, proj[0]+size, proj[1]+size, fill=p['color'])
        for t in self.trails:
            ps = proj_func(t['start'], cam_pos, yaw, pitch)
            pe = proj_func(t['end'], cam_pos, yaw, pitch)
            if ps and pe:
                self.canvas.create_line(ps[0], ps[1], pe[0], pe[1], fill=t['color'], width=4)

        # Player render if applicable
        if render_player:
            p_proj = proj_func(self.cam_pos, cam_pos, yaw, pitch)
            if p_proj:
                self.canvas.create_oval(p_proj[0]-5, p_proj[1]-5, p_proj[0]+5, p_proj[1]+5, fill=self.player_color)
                # Player glow if elements
                if sum(self.elements.values()) > 0:
                    self.canvas.create_oval(p_proj[0]-7, p_proj[1]-7, p_proj[0]+7, p_proj[1]+7, outline='white')

    def loop(self):
        if not self.running:
            return
        if not self.paused and not self.choose_gain:
            self.update()
        self.render()
        self.root.after(16, self.loop)  # ~60 FPS

if __name__ == "__main__":
    game = Game()
    game.root.mainloop()
