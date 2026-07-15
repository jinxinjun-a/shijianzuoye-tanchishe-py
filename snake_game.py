"""
贪吃蛇小游戏 - 关卡版
↑↓←→ / WASD 移动 | Space 重试 | P 暂停 | R 返回选关 | F11 全屏
红果 +10分 | 紫炸弹果 炸掉最近怪物
🏰 5个关卡 | 每关怪物递增2只 | 20分解锁下一关
3条命 | 无敌穿墙传送
自动适配屏幕分辨率，窗口化全屏运行
"""

import tkinter as tk
import random
import time
import json
import os

# ==================== 常量 ====================
CELL = 20                     # 每格像素（会根据屏幕微调）
GW, GH = 30, 20               # 网格宽高（启动时根据屏幕自动计算）
TOTAL = GW * GH
SPEED = 140
INIT_LEN = 3
FOOD_SCORE = 10

MON_LEN = 3
MON_SPAWN_LO = 3000
MON_SPAWN_HI = 7000
CHASE_R = 15                    # 怪物追人索敌范围
FOOD_CHASE_R = 30              # 怪物找食物索敌范围（= 2× 追人范围）
MP_MAX_MON = 5                 # 多人模式默认最大怪物数

LIVES = 3
INV_MS = 3000
BLINK = 150

# ==================== 关卡配置 ====================
# 每关怪物数：第1关3条，之后每关+2
LEVEL_CONFIG = {
    1: {"name": "第一关", "max_mon": 3, "color": "#4ade80", "icon": "🌱", "border": "#22c55e"},
    2: {"name": "第二关", "max_mon": 5, "color": "#60a5fa", "icon": "🌿", "border": "#3b82f6"},
    3: {"name": "第三关", "max_mon": 7, "color": "#f59e0b", "icon": "🔥", "border": "#d97706"},
    4: {"name": "第四关", "max_mon": 9, "color": "#f472b6", "icon": "💎", "border": "#db2777"},
    5: {"name": "第五关", "max_mon": 11, "color": "#ef4444", "icon": "👑", "border": "#dc2626"},
}
TARGET_SCORE = 20
TOTAL_LEVELS = 5

# 存档路径
SAVE_DIR = "saves"
SAVE_FILE = os.path.join(SAVE_DIR, "progress.json")

# 颜色
CBG = "#1a1a2e"
CGR = "#16213e"
CHD = "#00ff88"
CBD = "#00cc6a"
CINV = "#ffdd57"
CFD = "#ff4757"
CBM = "#a855f7"
CBO = "#c084fc"
CMH = "#ff6348"
CMB = "#e74c3c"
CTX = "#ffffff"
CDM = "#888888"
COV = "#ff6b6b"
CLOCKED_BG = "#2a2a3a"
CLOCKED_FG = "#555555"
CARD_BG = "#1e1e3a"

# 多人模式颜色
CP1 = "#00ff88"                # 玩家1 绿色
CP1B = "#00cc6a"
CP2 = "#4da6ff"                # 玩家2 蓝色
CP2B = "#0066cc"
CMP_BTN = "#0a3d2e"           # 多人按钮背景

DIR = {"UP": (0,-1), "DOWN": (0,1), "LEFT": (-1,0), "RIGHT": (1,0)}
REV = {"UP":"DOWN", "DOWN":"UP", "LEFT":"RIGHT", "RIGHT":"LEFT"}

def ok(x, y):
    return 0 <= x < GW and 0 <= y < GH

def dist(a, b):
    return abs(a[0]-b[0]) + abs(a[1]-b[1])


class SnakeGame:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("贪吃蛇 - 关卡模式")

        # ---- 根据屏幕分辨率自动计算网格 ----
        self._calc_grid()

        self.root.resizable(True, True)
        self.root.configure(bg=CBG)
        self.root.minsize(400, 300)

        # 顶栏
        self._topbar()

        # 主内容区（可伸缩，用于居中画布）
        self.content = tk.Frame(self.root, bg=CBG)
        self.content.pack(fill=tk.BOTH, expand=True)

        # 画布
        self.canvas = tk.Canvas(self.content, width=self.cw, height=self.ch,
                                bg=CBG, highlightthickness=0)
        self.canvas.pack(expand=True)  # 在窗口中居中

        # 底栏
        self._botbar()
        # 按键
        self._keys()

        self.high = 0
        self.fullscreen = False

        # ---- 多人模式状态 ----
        self.multiplayer = False        # 是否多人模式
        self.snake2 = []                # 玩家2蛇身
        self.dr2 = "LEFT"               # 玩家2当前方向
        self.ndr2 = "LEFT"              # 玩家2下一个方向
        self.score2 = 0                 # 玩家2分数
        self.lives2 = LIVES             # 玩家2命数
        self.inv2 = False               # 玩家2无敌状态
        self.inv_end2 = 0
        self.inv_show2 = True
        self.food2 = None               # 多人模式第2个食物
        self.winner = None              # 多人模式胜者: 0=平局, 1=玩家1, 2=玩家2
        self.mp_over = False            # 多人模式是否结束
        self.mp_history = {"games": 0, "p1_wins": 0, "p2_wins": 0, "ties": 0,
                           "p1_best": 0, "p2_best": 0}

        # ---- 成就系统（仅单人关卡模式计数） ----
        self.ach_kills = 0        # 炸弹击杀怪物数（目标100）
        self.ach_fruits = 0       # 累计吃果子数（目标100）
        self.ach_mon_deaths = 0   # 怪物撞玩家/自撞死亡数（目标10）
        self.ach_thresholds = {"kills": 100, "fruits": 100, "mon_deaths": 10}
        self._ach_loaded = False  # 防止重复加载覆盖

        # ---- 关卡系统状态 ----
        self.current_level = 0          # 0=选关界面, 1-5=游戏中
        self.unlocked = {1}             # 已解锁关卡集合（默认仅第1关）
        self.level_best = {i: 0 for i in range(1, TOTAL_LEVELS + 1)}
        self.max_mon = LEVEL_CONFIG[1]["max_mon"]  # 当前关卡最大怪物数
        self.level_cards = []           # [(x1,y1,x2,y2,level), ...] 点击检测
        self.exit_btn_rect = None       # 退出按钮矩形 (x1,y1,x2,y2)
        self.mp_btn_rect = None         # 多人模式按钮矩形
        self.mp_settle_btns = []        # 结算界面按钮 [(x1,y1,x2,y2,action), ...]
        self.unlock_msg = None          # 解锁提示文本
        self.unlock_msg_end = 0         # 提示过期时间戳(ms)

        # 加载存档
        self._load_progress()
        self._load_mp_history()
        self._load_achievements()

        # 鼠标点击绑定
        self.canvas.bind("<Button-1>", self._on_click)
        # 窗口关闭时保存
        self.root.protocol("WM_DELETE_WINDOW", self._on_exit)

        self._init()
        self._grid()
        self._bar()
        self._show_level_select()

        # 启动时最大化（窗口化全屏）
        self.root.update_idletasks()
        self._maximize()

        self.root.mainloop()

    # ========== 屏幕适配 ==========
    def _calc_grid(self):
        """根据屏幕分辨率计算最优网格大小"""
        global CELL, GW, GH, TOTAL
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()

        # 为标题栏 + UI 条 + 任务栏预留空间
        reserve_h = 110   # 标题栏~30 + 顶栏34 + 底栏22 + 任务栏~40
        reserve_w = 30    # 窗口边框

        avail_w = sw - reserve_w
        avail_h = sh - reserve_h

        GW = avail_w // CELL
        GH = (avail_h - 56) // CELL   # 56 = 顶栏+底栏

        # 确保最小网格；如果屏幕太小则缩小 CELL
        MIN_GW, MIN_GH = 40, 25
        if GW < MIN_GW or GH < MIN_GH:
            new_cw = avail_w // MIN_GW
            new_ch = (avail_h - 56) // MIN_GH
            CELL = max(15, min(new_cw, new_ch))
            GW = avail_w // CELL
            GH = (avail_h - 56) // CELL

        TOTAL = GW * GH
        self.cw = GW * CELL
        self.ch = GH * CELL

    def _maximize(self):
        """跨平台最大化窗口"""
        try:
            self.root.state('zoomed')          # Windows
        except tk.TclError:
            try:
                self.root.attributes('-zoomed', True)  # 部分 Linux WM
            except tk.TclError:
                # 回退：手动设置为屏幕 90%
                sw = self.root.winfo_screenwidth()
                sh = self.root.winfo_screenheight()
                self.root.geometry(f"{int(sw*0.9)}x{int(sh*0.85)}+{int(sw*0.05)}+{int(sh*0.05)}")

    def _toggle_fullscreen(self, event=None):
        """F11 切换真全屏 / 窗口化"""
        self.fullscreen = not self.fullscreen
        self.root.attributes('-fullscreen', self.fullscreen)
        if not self.fullscreen:
            self._maximize()

    # ========== UI ==========
    def _topbar(self):
        f = tk.Frame(self.root, bg="#0f0f23", height=34)
        f.pack(fill=tk.X); f.pack_propagate(False)
        F = ("Microsoft YaHei", 10, "bold")

        # ---- 左侧子框架：P1 数据 ----
        left_f = tk.Frame(f, bg="#0f0f23")
        left_f.pack(side=tk.LEFT)

        def _sepl(parent=left_f):
            lb = tk.Label(parent, text="│", font=("Microsoft YaHei", 9),
                          fg="#333", bg="#0f0f23")
            lb.pack(side=tk.LEFT)
            return lb

        self.lvl = tk.Label(left_f, text="🗺️ 选关", font=F, fg=CHD, bg="#0f0f23")
        self.lvl.pack(side=tk.LEFT, padx=(10, 4))
        _sepl()

        self.lsc = tk.Label(left_f, text="🍎 0", font=F, fg=CTX, bg="#0f0f23")
        self.lsc.pack(side=tk.LEFT, padx=4)
        _sepl()

        self.llv = tk.Label(left_f, text="", font=F, fg=CFD, bg="#0f0f23")
        self.llv.pack(side=tk.LEFT, padx=4)
        _sepl()

        # P1 无敌计时（紧贴 P1 数据）
        self.liv = tk.Label(left_f, text="", font=F, fg=CINV, bg="#0f0f23")
        self.liv.pack(side=tk.LEFT, padx=4)

        # ---- 中间子框架：怪物数（居中） ----
        center_f = tk.Frame(f, bg="#0f0f23")
        center_f.pack(side=tk.LEFT, expand=True, fill=tk.X)

        self.lmn = tk.Label(center_f, text="👾 0/1", font=F, fg=CMH, bg="#0f0f23")
        self.lmn.pack(expand=True)  # 在子框架内居中

        # ---- 右侧子框架：P2 数据（从右往左 pack） ----
        right_f = tk.Frame(f, bg="#0f0f23")
        right_f.pack(side=tk.RIGHT)

        def _sepr(parent=right_f):
            lb = tk.Label(parent, text="│", font=("Microsoft YaHei", 9),
                          fg="#333", bg="#0f0f23")
            lb.pack(side=tk.RIGHT)
            return lb

        self.lhi = tk.Label(right_f, text="🏆 0", font=F, fg="#ffd700", bg="#0f0f23")
        self.lhi.pack(side=tk.RIGHT, padx=(4, 10))
        self.sep_r1 = _sepr()

        self.lsc2 = tk.Label(right_f, text="", font=F, fg=CP2, bg="#0f0f23")
        self.lsc2.pack(side=tk.RIGHT, padx=4)
        self.sep_r2 = _sepr()

        self.llv2 = tk.Label(right_f, text="", font=F, fg="#4da6ff", bg="#0f0f23")
        self.llv2.pack(side=tk.RIGHT, padx=4)
        self.sep_r3 = _sepr()

        # P2 无敌计时（紧贴 P2 数据）
        self.liv2 = tk.Label(right_f, text="", font=F, fg=CINV, bg="#0f0f23")
        self.liv2.pack(side=tk.RIGHT, padx=4)

    def _botbar(self):
        f = tk.Frame(self.root, bg="#0f0f23", height=22)
        f.pack(fill=tk.X); f.pack_propagate(False)
        tk.Label(f, text="🖱 点击卡片选关 | ↑↓←→/WASD 移动 | Space 重试 | P 暂停 | R 返回选关 | F11 全屏",
                 font=("Microsoft YaHei",8), fg=CDM, bg="#0f0f23").pack()

    def _keys(self):
        # 玩家1：WASD
        for k, d in [("<w>","UP"),("<s>","DOWN"),("<a>","LEFT"),("<d>","RIGHT")]:
            self.root.bind(k, lambda e, d=d: self._dir_p1(d))
        # 玩家2 / 单人：方向键
        for k, d in [("<Up>","UP"),("<Down>","DOWN"),("<Left>","LEFT"),("<Right>","RIGHT")]:
            self.root.bind(k, lambda e, d=d: self._dir_arrow(d))
        self.root.bind("<p>", lambda e: self._pause())
        self.root.bind("<r>", lambda e: self._restart())
        self.root.bind("<space>", lambda e: self._start())
        self.root.bind("<F11>", lambda e: self._toggle_fullscreen())
        self.root.bind("<Escape>", lambda e: self._esc_fullscreen())

    def _esc_fullscreen(self):
        """ESC 退出全屏"""
        if self.fullscreen:
            self._toggle_fullscreen()

    # ========== 初始化 ==========
    def _init(self):
        self.snake = []
        self.dr = "RIGHT"
        self.ndr = "RIGHT"
        self.food = None
        self.bomb = None
        self.mons = []
        self.mdr = []
        self.score = 0
        self.lives = LIVES
        self.run = False
        self.paused = False
        self.over = False
        self.inv = False
        self.inv_end = 0
        self.inv_show = True
        self.spawn_at = 0
        self.kills = 0
        self._tid = None
        self.unlock_msg = None
        self.unlock_msg_end = 0
        cx, cy = GW//2, GH//2
        for i in range(INIT_LEN):
            self.snake.append((cx-i, cy))

    def _grid(self):
        for x in range(0, self.cw, CELL):
            self.canvas.create_line(x,0,x,self.ch, fill=CGR, dash=(1,3))
        for y in range(0, self.ch, CELL):
            self.canvas.create_line(0,y,self.cw,y, fill=CGR, dash=(1,3))

    # ========== 关卡选择界面 ==========
    def _show_level_select(self):
        """绘制关卡选择界面"""
        self.current_level = 0
        self.unlock_msg = None
        self.unlock_msg_end = 0
        c = self.canvas
        c.delete("all")

        cw, ch = self.cw, self.ch

        # ---- 标题 ----
        title_y = int(ch * 0.07)
        c.create_text(cw // 2, title_y,
                      text="🗺️  选 择 关 卡",
                      font=("Microsoft YaHei", 28, "bold"),
                      fill=CHD, tags="lvlsel")

        # ---- 副标题 ----
        sub_y = title_y + 34
        c.create_text(cw // 2, sub_y,
                      text=f"💡 当前关卡达成 {TARGET_SCORE} 分解锁下一关",
                      font=("Microsoft YaHei", 11),
                      fill=CDM, tags="lvlsel")

        # ---- 卡片布局（自适应） ----
        card_w = max(100, min(140, int(cw * 0.13)))
        card_h = max(140, min(175, int(ch * 0.38)))
        gap = max(15, int(card_w * 0.18))
        total_w = card_w * TOTAL_LEVELS + gap * (TOTAL_LEVELS - 1)
        start_x = (cw - total_w) // 2
        start_y = int(ch * 0.22)

        self.level_cards = []

        for lv in range(1, TOTAL_LEVELS + 1):
            cfg = LEVEL_CONFIG[lv]
            x1 = start_x + (lv - 1) * (card_w + gap)
            y1 = start_y
            x2 = x1 + card_w
            y2 = y1 + card_h

            self.level_cards.append((x1, y1, x2, y2, lv))

            unlocked = lv in self.unlocked
            best = self.level_best[lv]

            if unlocked:
                bg = CARD_BG
                border = cfg["border"]
                border_w = 3
            else:
                bg = CLOCKED_BG
                border = CLOCKED_FG
                border_w = 2

            # 卡片背景
            c.create_rectangle(x1, y1, x2, y2, fill=bg, outline=border,
                               width=border_w, tags="lvlsel")

            # 顶部色条
            bar_color = cfg["color"] if unlocked else CLOCKED_FG
            c.create_rectangle(x1 + 3, y1 + 3, x2 - 3, y1 + 9,
                               fill=bar_color, outline="", tags="lvlsel")

            # 图标
            icon_color = cfg["color"] if unlocked else CLOCKED_FG
            c.create_text((x1 + x2) // 2, y1 + 30,
                          text=cfg["icon"],
                          font=("Segoe UI Emoji", 24),
                          fill=icon_color, tags="lvlsel")

            # 关卡数字
            c.create_text((x1 + x2) // 2, y1 + 60,
                          text=str(lv),
                          font=("Microsoft YaHei", 22, "bold"),
                          fill=icon_color, tags="lvlsel")

            # 关卡名称
            c.create_text((x1 + x2) // 2, y1 + 86,
                          text=cfg["name"],
                          font=("Microsoft YaHei", 12),
                          fill=CTX if unlocked else CLOCKED_FG,
                          tags="lvlsel")

            # 怪物数量
            c.create_text((x1 + x2) // 2, y1 + 110,
                          text=f"👾 ×{cfg['max_mon']}",
                          font=("Microsoft YaHei", 10),
                          fill=CMH if unlocked else CLOCKED_FG,
                          tags="lvlsel")

            # 底部信息：最高分 或 锁定图标
            if unlocked:
                if best > 0:
                    best_text = f"🏆 {best}"
                    best_color = "#ffd700"
                else:
                    best_text = "新关卡"
                    best_color = CDM
                c.create_text((x1 + x2) // 2, y1 + 140,
                              text=best_text,
                              font=("Microsoft YaHei", 10),
                              fill=best_color, tags="lvlsel")

                # 已解锁卡片内虚线框暗示可点击
                c.create_rectangle(x1 + 6, y1 + 6, x2 - 6, y2 - 6,
                                   outline=border, width=1, dash=(3, 3),
                                   tags="lvlsel")
            else:
                c.create_text((x1 + x2) // 2, y1 + 140,
                              text="🔒 未解锁",
                              font=("Microsoft YaHei", 10),
                              fill=CLOCKED_FG, tags="lvlsel")

        # ---- 底部提示 ----
        hint_y = start_y + card_h + 42
        c.create_text(cw // 2, hint_y,
                      text="🖱 点击已解锁的关卡卡片开始游戏  |  R 返回选关  |  Space 重新挑战",
                      font=("Microsoft YaHei", 10),
                      fill=CDM, tags="lvlsel")

        # ---- 多人模式按钮 ----
        btn_w, btn_h = 170, 36
        mp_btn_x1 = (cw - btn_w) // 2
        mp_btn_y1 = hint_y + 28
        mp_btn_x2 = mp_btn_x1 + btn_w
        mp_btn_y2 = mp_btn_y1 + btn_h
        self.mp_btn_rect = (mp_btn_x1, mp_btn_y1, mp_btn_x2, mp_btn_y2)

        c.create_rectangle(mp_btn_x1, mp_btn_y1, mp_btn_x2, mp_btn_y2,
                           fill=CMP_BTN, outline=CP2, width=2, tags="lvlsel")
        c.create_text((mp_btn_x1 + mp_btn_x2) // 2, (mp_btn_y1 + mp_btn_y2) // 2,
                      text="👥  多 人 模 式",
                      font=("Microsoft YaHei", 12, "bold"),
                      fill=CP2, tags="lvlsel")

        # ---- 退出按钮 ----
        exit_x1 = (cw - btn_w) // 2
        exit_y1 = mp_btn_y2 + 10
        exit_x2 = exit_x1 + btn_w
        exit_y2 = exit_y1 + btn_h
        self.exit_btn_rect = (exit_x1, exit_y1, exit_x2, exit_y2)

        c.create_rectangle(exit_x1, exit_y1, exit_x2, exit_y2,
                           fill="#3d1111", outline="#ff4757", width=2, tags="lvlsel")
        c.create_text((exit_x1 + exit_x2) // 2, (exit_y1 + exit_y2) // 2,
                      text="🚪  退 出 游 戏",
                      font=("Microsoft YaHei", 12, "bold"),
                      fill="#ff6b6b", tags="lvlsel")

        # ---- 左下角：成就入口 ----
        ach_x1, ach_y1 = 10, ch - 70
        ach_x2, ach_y2 = 220, ch - 10
        self.ach_btn_rect = (ach_x1, ach_y1, ach_x2, ach_y2)
        c.create_rectangle(ach_x1, ach_y1, ach_x2, ach_y2,
                           fill="#1a1a2e", outline="#553344", width=1, tags="lvlsel")
        kp = min(100, int(self.ach_kills / max(1, self.ach_thresholds["kills"]) * 100))
        fp = min(100, int(self.ach_fruits / max(1, self.ach_thresholds["fruits"]) * 100))
        mp = min(100, int(self.ach_mon_deaths / max(1, self.ach_thresholds["mon_deaths"]) * 100))
        dk = "✅" if kp >= 100 else f"{kp}%"
        df = "✅" if fp >= 100 else f"{fp}%"
        dm = "✅" if mp >= 100 else f"{mp}%"
        c.create_text(ach_x1 + 8, ach_y1 + 8, anchor="nw",
                      text=f"🏆 成就系统",
                      font=("Microsoft YaHei", 9, "bold"), fill="#ffd700", tags="lvlsel")
        c.create_text(ach_x1 + 8, ach_y1 + 24, anchor="nw",
                      text=f"怪物杀手 {dk}  果子王 {df}  收藏家 {dm}",
                      font=("Microsoft YaHei", 8), fill="#ff6b6b", tags="lvlsel")
        c.create_text(ach_x1 + 8, ach_y1 + 40, anchor="nw",
                      text=f"点击查看详情 →",
                      font=("Microsoft YaHei", 7), fill=CDM, tags="lvlsel")

        self._bar()

    def _on_click(self, event):
        """鼠标点击处理：关卡卡片 / 多人模式 / 退出 / 结算按钮"""
        # 只在选关界面响应点击（多人结算除外）
        if self.current_level != 0 and not self.mp_over:
            return

        cx, cy = event.x, event.y

        # 成就面板（左下角，仅选关界面）
        if self.current_level == 0 and self.ach_btn_rect:
            x1, y1, x2, y2 = self.ach_btn_rect
            if x1 <= cx <= x2 and y1 <= cy <= y2:
                self._show_achievements_overlay()
                return

        # 多人结算界面按钮
        if self.mp_over:
            for x1, y1, x2, y2, action in self.mp_settle_btns:
                if x1 <= cx <= x2 and y1 <= cy <= y2:
                    if action == "replay":
                        self._mp_restart()
                    elif action == "exit_mp":
                        self._mp_exit()
                    elif action == "clear_mp":
                        self._mp_clear_history()
                    return
            return

        # 检测多人模式按钮
        if self.mp_btn_rect:
            x1, y1, x2, y2 = self.mp_btn_rect
            if x1 <= cx <= x2 and y1 <= cy <= y2:
                self._start_multiplayer()
                return

        # 检测退出按钮
        if self.current_level != 0:
            return

        cx, cy = event.x, event.y

        # 检测退出按钮
        if self.exit_btn_rect:
            x1, y1, x2, y2 = self.exit_btn_rect
            if x1 <= cx <= x2 and y1 <= cy <= y2:
                self._on_exit()
                return

        for x1, y1, x2, y2, lv in self.level_cards:
            if x1 <= cx <= x2 and y1 <= cy <= y2:
                if lv in self.unlocked:
                    self._start_level(lv)
                else:
                    self._flash_locked(lv)
                return

    def _flash_locked(self, lv):
        """锁定关卡被点击时闪烁提示"""
        for x1, y1, x2, y2, clv in self.level_cards:
            if clv == lv:
                cx_mid = (x1 + x2) // 2
                cy_mid = (y1 + y2) // 2
                # 短暂显示"需先通关"提示
                self.canvas.delete("lockflash")
                self.canvas.create_text(
                    cx_mid, cy_mid - 10,
                    text="🔒\n需先通关",
                    font=("Microsoft YaHei", 12, "bold"),
                    fill="#ff6b6b", justify="center", tags="lockflash"
                )
                self.root.after(800, lambda: self.canvas.delete("lockflash"))
                break

    # ========== 关卡游戏流程 ==========
    def _start_level(self, level):
        """启动指定关卡"""
        self.current_level = level
        cfg = LEVEL_CONFIG[level]
        self.max_mon = cfg["max_mon"]
        self.unlock_msg = None
        self.unlock_msg_end = 0

        self._cancel_timer()
        self.canvas.delete("all")
        self._grid()
        self._init()
        self.run = True
        self._place("food")
        self._place("bomb")
        self._next_spawn()
        self._bar()
        self._loop()

    def _back_to_select(self):
        """返回选关界面"""
        self._cancel_timer()
        # 保存本关最高分
        if self.current_level > 0:
            if self.score > self.level_best.get(self.current_level, 0):
                self.level_best[self.current_level] = self.score
            if self.score > self.high:
                self.high = self.score
        self._save_progress()
        self._init()
        self._show_level_select()

    def _check_unlock(self):
        """检测是否达成解锁条件（吃到食物后调用）"""
        if self.current_level <= 0:
            return
        if self.score < TARGET_SCORE:
            return
        nxt = self.current_level + 1
        if nxt > TOTAL_LEVELS:
            return  # 已是最后一关
        if nxt in self.unlocked:
            return  # 已解锁过

        # 解锁下一关！
        self.unlocked.add(nxt)
        cfg = LEVEL_CONFIG[nxt]
        self.unlock_msg = f"🎉 {cfg['name']}（{cfg['icon']}）已解锁！"
        self.unlock_msg_end = int(time.time() * 1000) + 2500

        # 更新本关最高分
        if self.score > self.level_best[self.current_level]:
            self.level_best[self.current_level] = self.score

        # 保存进度
        self._save_progress()

    # ========== 存档系统 ==========
    def _load_progress(self):
        """从 saves/progress.json 加载游戏进度"""
        try:
            if not os.path.exists(SAVE_FILE):
                return
            with open(SAVE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            # 加载已解锁关卡
            if "unlocked" in data:
                self.unlocked = set(data["unlocked"])
            # 加载每关最高分
            if "level_best" in data:
                for k, v in data["level_best"].items():
                    lv = int(k)
                    if 1 <= lv <= TOTAL_LEVELS:
                        self.level_best[lv] = max(self.level_best[lv], v)
            # 加载全局最高分
            if "high" in data:
                self.high = data["high"]
        except Exception:
            pass  # 存档损坏则忽略

    def _save_progress(self):
        """保存游戏进度到 saves/progress.json"""
        try:
            if not os.path.exists(SAVE_DIR):
                os.makedirs(SAVE_DIR)
            data = {
                "unlocked": list(self.unlocked),
                "level_best": {str(k): v for k, v in self.level_best.items()},
                "high": self.high,
            }
            with open(SAVE_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception:
            pass  # 保存失败静默忽略

    def _on_exit(self):
        """窗口关闭时保存并退出"""
        # 如果正在游戏中，先保存当前关卡分数
        if self.current_level > 0:
            if self.score > self.level_best.get(self.current_level, 0):
                self.level_best[self.current_level] = self.score
            if self.score > self.high:
                self.high = self.score
        self._save_mp_history()
        self._save_progress()
        self.root.destroy()

    # ========== 多人模式 ==========
    def _start_multiplayer(self):
        """启动多人模式"""
        self.multiplayer = True
        self.mp_over = False
        self.winner = None
        self.max_mon = MP_MAX_MON
        self.current_level = 0
        self.unlock_msg = None
        self.unlock_msg_end = 0
        self.mp_settle_btns = []

        self._cancel_timer()
        self.canvas.delete("all")
        self._grid()
        self._init_multiplayer()
        self.run = True
        self._place("food")
        self._place("food2")       # 第2个食物
        self._place("bomb")
        self._next_spawn()
        self._bar()
        self._loop()

    def _init_multiplayer(self):
        """初始化多人模式游戏状态"""
        self._init()
        # 玩家1 从左侧出发
        cx1, cy1 = GW//4, GH//2
        self.snake = [(cx1-i, cy1) for i in range(INIT_LEN)]
        self.dr = "RIGHT"
        self.ndr = "RIGHT"
        # 玩家2 从右侧出发
        cx2, cy2 = GW*3//4, GH//2
        self.snake2 = [(cx2+i, cy2) for i in range(INIT_LEN)]
        self.dr2 = "LEFT"
        self.ndr2 = "LEFT"
        self.score2 = 0
        self.lives2 = LIVES
        self.kills2 = 0               # P2 炸弹击杀数
        self.inv2 = False
        self.inv_end2 = 0
        self.inv_show2 = True
        self.food2 = None

    def _mp_restart(self):
        """多人模式：再来一次"""
        self._cancel_timer()
        self.canvas.delete("all")
        self._grid()
        self._init_multiplayer()
        self.mp_over = False
        self.winner = None
        self.mp_settle_btns = []
        self.run = True
        self._place("food")
        self._place("food2")
        self._place("bomb")
        self._next_spawn()
        self._bar()
        self._loop()

    def _mp_exit(self):
        """多人模式：退出"""
        self._cancel_timer()
        self._save_mp_history()
        self.multiplayer = False
        self.mp_over = False
        self.winner = None
        self.mp_settle_btns = []
        self._init()
        self._show_level_select()

    def _mp_clear_history(self):
        """清除多人模式历史记录"""
        self.mp_history = {"games": 0, "p1_wins": 0, "p2_wins": 0, "ties": 0,
                           "p1_best": 0, "p2_best": 0}
        self._save_mp_history()
        self._show_mp_settlement()  # 刷新结算界面

    def _check_mp_end(self):
        """检查多人模式是否结束（两人都死亡）"""
        if self.lives <= 0 and self.lives2 <= 0:
            self.run = False
            self.mp_over = True
            self._cancel_timer()
            # 判定赢家
            if self.score > self.score2:
                self.winner = 1
                self.mp_history["p1_wins"] += 1
            elif self.score2 > self.score:
                self.winner = 2
                self.mp_history["p2_wins"] += 1
            else:
                self.winner = 0
                self.mp_history["ties"] += 1
            self.mp_history["games"] += 1
            if self.score > self.mp_history["p1_best"]:
                self.mp_history["p1_best"] = self.score
            if self.score2 > self.mp_history["p2_best"]:
                self.mp_history["p2_best"] = self.score2
            self._save_mp_history()
            self._show_mp_settlement()
            return True
        return False

    def _die2(self):
        """玩家2 掉命"""
        self.lives2 -= 1
        if self.lives2 <= 0:
            self.snake2 = []
            self._check_mp_end()
            return
        old = len(self.snake2)
        cx, cy = GW*3//4, GH//2
        self.snake2 = [(cx+i, cy) for i in range(min(old, GW))]
        self.dr2 = "LEFT"
        self.ndr2 = "LEFT"
        self.inv2 = True
        self.inv_end2 = int(time.time()*1000) + INV_MS
        self.inv_show2 = True

    def _move_snake2(self):
        """玩家2 移动逻辑"""
        if not self.snake2 or self.lives2 <= 0:
            return
        self.dr2 = self.ndr2
        hx, hy = self.snake2[0]
        dx, dy = DIR[self.dr2]
        nx, ny = hx+dx, hy+dy

        if not ok(nx, ny):
            if self.inv2:
                nx %= GW; ny %= GH
            else:
                self._die2()
                return

        nh = (nx, ny)

        # 撞自己
        if nh in self.snake2[:-1]:
            if not self.inv2:
                self._die2()
                return

        # 撞怪物
        if not self.inv2:
            for m in self.mons:
                if nh in m:
                    self._die2()
                    return

        # 撞玩家1蛇身 → 任一方无敌则穿透，否则P2受伤
        if self.snake and nh in self.snake:
            if not self.inv and not self.inv2:
                self._die2()
            return

        self.snake2.insert(0, nh)
        ate = False
        if nh == self.food:
            self.score2 += FOOD_SCORE
            self._place("food")
            ate = True
        if nh == self.food2:
            self.score2 += FOOD_SCORE
            self._place("food2")
            ate = True
        if nh == self.bomb:
            self._kill_one()
            self._place("bomb")
            self.kills2 += 1          # P2 炸弹击杀
            ate = True
        if not ate:
            self.snake2.pop()

    def _check_pvp_head_collision(self):
        """检查两个蛇头是否互撞（同时碰到对方头部）"""
        if not self.snake or not self.snake2:
            return
        if self.lives <= 0 or self.lives2 <= 0:
            return
        h1 = self.snake[0]
        h2 = self.snake2[0]
        if h1 == h2:
            # 两头正面对碰
            if self.inv or self.inv2:
                return  # 任一方无敌 → 双方穿透，不掉血
            # 双方都非无敌 → 各掉一命
            self._die()
            self._die2()
            self._check_mp_end()

    def _show_mp_settlement(self):
        """多人模式结算界面"""
        c = self.canvas
        c.delete("all")
        cw, ch = self.cw, self.ch

        # 背景
        c.create_rectangle(0, 0, cw, ch, fill=CBG, tags="mpsettle")

        # 标题
        if self.winner == 1:
            title = "🏆  玩家一 获胜！"
            title_color = CP1
        elif self.winner == 2:
            title = "🏆  玩家二 获胜！"
            title_color = CP2
        else:
            title = "🤝  平  局！"
            title_color = "#ffd700"

        c.create_text(cw//2, ch*0.12, text=title,
                      font=("Microsoft YaHei", 30, "bold"),
                      fill=title_color, tags="mpsettle")

        # P1 成绩
        p1_x = cw * 0.3
        c.create_text(p1_x, ch*0.32, text="🟢 玩家一 (WASD)",
                      font=("Microsoft YaHei", 16, "bold"), fill=CP1, tags="mpsettle")
        c.create_text(p1_x, ch*0.40, text=f"得分: {self.score}",
                      font=("Microsoft YaHei", 22, "bold"), fill=CTX, tags="mpsettle")
        c.create_text(p1_x, ch*0.47, text=f"蛇长: {len(self.snake)} 格  |  击杀: {self.kills}",
                      font=("Microsoft YaHei", 12), fill=CDM, tags="mpsettle")

        # VS
        c.create_text(cw//2, ch*0.40, text="VS",
                      font=("Microsoft YaHei", 18, "bold"), fill=COV, tags="mpsettle")

        # P2 成绩
        p2_x = cw * 0.7
        c.create_text(p2_x, ch*0.32, text="🔵 玩家二 (方向键)",
                      font=("Microsoft YaHei", 16, "bold"), fill=CP2, tags="mpsettle")
        c.create_text(p2_x, ch*0.40, text=f"得分: {self.score2}",
                      font=("Microsoft YaHei", 22, "bold"), fill=CTX, tags="mpsettle")
        c.create_text(p2_x, ch*0.47, text=f"蛇长: {len(self.snake2)} 格  |  击杀: {self.kills}",
                      font=("Microsoft YaHei", 12), fill=CDM, tags="mpsettle")

        # 按钮
        btn_w, btn_h = 170, 38
        gap = 25
        total_btn_w = btn_w * 2 + gap
        btn_start_x = (cw - total_btn_w) // 2
        btn_y = int(ch * 0.65)

        # "再来一次" 按钮
        rp_x1 = btn_start_x
        rp_x2 = rp_x1 + btn_w
        rp_y1 = btn_y
        rp_y2 = btn_y + btn_h
        c.create_rectangle(rp_x1, rp_y1, rp_x2, rp_y2,
                           fill=CMP_BTN, outline=CHD, width=2, tags="mpsettle")
        c.create_text((rp_x1+rp_x2)//2, (rp_y1+rp_y2)//2,
                      text="🔄  再 来 一 次",
                      font=("Microsoft YaHei", 12, "bold"), fill=CHD, tags="mpsettle")
        self.mp_settle_btns.append((rp_x1, rp_y1, rp_x2, rp_y2, "replay"))

        # "退出多人游戏" 按钮
        ex_x1 = rp_x2 + gap
        ex_x2 = ex_x1 + btn_w
        ex_y1 = btn_y
        ex_y2 = btn_y + btn_h
        c.create_rectangle(ex_x1, ex_y1, ex_x2, ex_y2,
                           fill="#3d1111", outline="#ff4757", width=2, tags="mpsettle")
        c.create_text((ex_x1+ex_x2)//2, (ex_y1+ex_y2)//2,
                      text="🚪  退 出 多 人",
                      font=("Microsoft YaHei", 12, "bold"), fill="#ff6b6b", tags="mpsettle")
        self.mp_settle_btns.append((ex_x1, ex_y1, ex_x2, ex_y2, "exit_mp"))

        # 历史记录
        hist_y = int(ch * 0.78)
        h = self.mp_history
        hist_text = (f"📊 历史记录 | 总局数: {h['games']} | "
                     f"P1胜: {h['p1_wins']} | P2胜: {h['p2_wins']} | "
                     f"平局: {h['ties']} | "
                     f"P1最佳: {h['p1_best']} | P2最佳: {h['p2_best']}")
        c.create_text(cw//2, hist_y, text=hist_text,
                      font=("Microsoft YaHei", 9), fill=CDM, tags="mpsettle")

        # "清除记录" 小按钮
        clr_w, clr_h = 100, 26
        clr_x1 = (cw - clr_w) // 2
        clr_y1 = hist_y + 20
        clr_x2 = clr_x1 + clr_w
        clr_y2 = clr_y1 + clr_h
        c.create_rectangle(clr_x1, clr_y1, clr_x2, clr_y2,
                           fill="#2a1a1a", outline="#884444", width=1, tags="mpsettle")
        c.create_text((clr_x1+clr_x2)//2, (clr_y1+clr_y2)//2,
                      text="🗑 清除记录",
                      font=("Microsoft YaHei", 9), fill="#cc6666", tags="mpsettle")
        self.mp_settle_btns.append((clr_x1, clr_y1, clr_x2, clr_y2, "clear_mp"))

        self._bar()

    # ========== 多人模式存档 ==========
    def _save_mp_history(self):
        """保存多人模式历史"""
        try:
            if not os.path.exists(SAVE_DIR):
                os.makedirs(SAVE_DIR)
            mp_file = os.path.join(SAVE_DIR, "multiplayer.json")
            with open(mp_file, "w", encoding="utf-8") as f:
                json.dump(self.mp_history, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _load_mp_history(self):
        """加载多人模式历史"""
        try:
            mp_file = os.path.join(SAVE_DIR, "multiplayer.json")
            if not os.path.exists(mp_file):
                return
            with open(mp_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            for k in self.mp_history:
                if k in data:
                    self.mp_history[k] = data[k]
        except Exception:
            pass

    # ========== 成就存档 ==========
    def _save_achievements(self):
        """保存成就进度"""
        try:
            if not os.path.exists(SAVE_DIR):
                os.makedirs(SAVE_DIR)
            ach_file = os.path.join(SAVE_DIR, "achievements.json")
            data = {"kills": self.ach_kills, "fruits": self.ach_fruits,
                    "mon_deaths": self.ach_mon_deaths}
            with open(ach_file, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _load_achievements(self):
        """加载成就进度"""
        try:
            ach_file = os.path.join(SAVE_DIR, "achievements.json")
            if not os.path.exists(ach_file):
                return
            with open(ach_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            self.ach_kills = data.get("kills", 0)
            self.ach_fruits = data.get("fruits", 0)
            self.ach_mon_deaths = data.get("mon_deaths", 0)
            self._ach_loaded = True
        except Exception:
            pass

    def _show_achievements_overlay(self):
        """在选关界面上叠加成就详情（点击任意处关闭）"""
        c = self.canvas
        cw, ch = self.cw, self.ch

        # 半透明背景
        c.create_rectangle(0, 0, cw, ch, fill=CBG, stipple="gray50",
                           tags="achoverlay")
        # 白色弹窗
        ow, oh = 420, 280
        ox1 = (cw - ow) // 2
        oy1 = (ch - oh) // 2
        ox2 = ox1 + ow
        oy2 = oy1 + oh
        c.create_rectangle(ox1, oy1, ox2, oy2, fill="#1e1e3a",
                           outline="#ffd700", width=2, tags="achoverlay")

        c.create_text(cw // 2, oy1 + 30,
                      text="🏆  成 就 系 统",
                      font=("Microsoft YaHei", 20, "bold"),
                      fill="#ffd700", tags="achoverlay")

        items = [
            ("🏆 怪物杀手", self.ach_kills, self.ach_thresholds["kills"],
             "累计使用炸弹击杀怪物"),
            ("🍎 果子王", self.ach_fruits, self.ach_thresholds["fruits"],
             "累计吃到果子"),
            ("💀 怪物收藏家", self.ach_mon_deaths, self.ach_thresholds["mon_deaths"],
             "累计让怪物撞到玩家或自撞而死"),
        ]
        for idx, (name, val, target, desc) in enumerate(items):
            yy = oy1 + 70 + idx * 55
            pct = min(100, int(val / max(1, target) * 100))
            done = pct >= 100
            bar_w = int(240 * pct / 100)
            bar_color = "#ffd700" if done else "#4da6ff"

            c.create_text(ox1 + 20, yy, anchor="w",
                          text=f"{name}", font=("Microsoft YaHei", 12, "bold"),
                          fill="#ffd700" if done else CTX, tags="achoverlay")
            c.create_text(ox1 + 20, yy + 18, anchor="w",
                          text=desc, font=("Microsoft YaHei", 8),
                          fill=CDM, tags="achoverlay")
            # 进度条背景
            c.create_rectangle(ox1 + 160, yy + 2, ox1 + 400, yy + 16,
                               fill="#333355", outline="", tags="achoverlay")
            # 进度条
            if bar_w > 0:
                c.create_rectangle(ox1 + 160, yy + 2, ox1 + 160 + bar_w, yy + 16,
                                   fill=bar_color, outline="", tags="achoverlay")
            # 数值
            c.create_text(ox1 + 280, yy + 9,
                          text=f"{val}/{target}  {'✅' if done else f'{pct}%'}",
                          font=("Microsoft YaHei", 9, "bold"),
                          fill=bar_color, tags="achoverlay")

        c.create_text(cw // 2, oy2 - 20,
                      text="💡 仅统计单人关卡模式  |  点击任意处关闭",
                      font=("Microsoft YaHei", 9), fill=CDM, tags="achoverlay")

        # 点击任意处关闭
        self._ach_overlay_active = True
        self.root.after(100, lambda: self.canvas.bind(
            "<Button-1>", self._close_ach_overlay))

    def _close_ach_overlay(self, event=None):
        """关闭成就详情弹窗"""
        if not getattr(self, '_ach_overlay_active', False):
            return
        self._ach_overlay_active = False
        self.canvas.delete("achoverlay")
        # 恢复选关界面点击绑定
        self.canvas.bind("<Button-1>", self._on_click)

    # ========== 开始 / 循环 ==========
    def _start(self):
        # 选关界面下Space无效（多人模式除外）
        if self.current_level == 0 and not self.multiplayer:
            return
        if self.run and not self.paused:
            return
        # 如果游戏已结束，重新挑战
        self._cancel_timer()
        self.canvas.delete("msg", "pmsg")  # 清除结束/暂停画面
        if self.multiplayer:
            self._mp_restart()
        else:
            self._init()
            self.run = True
            self._place("food")
            self._place("bomb")
            self._next_spawn()
            self._bar()
            self._loop()

    def _loop(self):
        if not self.run or self.over:
            return
        now = int(time.time() * 1000)

        if not self.paused:
            # --- P1 无敌计时 ---
            if self.inv:
                if now >= self.inv_end:
                    self.inv = False
                else:
                    self.inv_show = ((self.inv_end - now) // BLINK) % 2 == 0

            # --- P2 无敌计时（多人模式） ---
            if self.multiplayer and self.inv2:
                if now >= self.inv_end2:
                    self.inv2 = False
                else:
                    self.inv_show2 = ((self.inv_end2 - now) // BLINK) % 2 == 0

            self._move_snake()
            if self.multiplayer:
                if not self.mp_over:
                    self._move_snake2()
                    self._check_pvp_head_collision()
                if self.mp_over:
                    self._draw(); self._bar(); return
            if self.over:
                self._end(); return

            self._move_mons()
            if self.over or self.mp_over:
                if self.mp_over:
                    self._draw(); self._bar(); return
                self._end(); return

            if len(self.mons) < self.max_mon and now >= self.spawn_at:
                self._spawn_mon()
                self._next_spawn()

            self._draw()

        self._bar()
        if not self.over and not self.mp_over:
            self._tid = self.root.after(SPEED, self._loop)

    def _cancel_timer(self):
        if self._tid:
            try:
                self.root.after_cancel(self._tid)
            except Exception:
                pass
            self._tid = None

    # ========== 蛇移动 ==========
    def _move_snake(self):
        # 多人模式：如果P1已阵亡则跳过
        if self.multiplayer and (not self.snake or self.lives <= 0):
            return
        self.dr = self.ndr
        hx, hy = self.snake[0]
        dx, dy = DIR[self.dr]
        nx, ny = hx+dx, hy+dy

        # 撞墙 → 无敌时穿墙传送
        if not ok(nx, ny):
            if self.inv:
                nx %= GW; ny %= GH
            else:
                self._die()
                if self.over: return
                return

        nh = (nx, ny)

        # 撞自己
        if nh in self.snake[:-1]:
            if not self.inv:
                self._die()
                if self.over: return
                return

        # 撞怪物
        if not self.inv:
            for m in self.mons:
                if nh in m:
                    self._die()
                    if self.over: return
                    return

        # 多人模式：撞玩家2蛇身 → 任一方无敌则穿透，否则P1受伤
        if self.multiplayer and self.snake2:
            if nh in self.snake2:
                if not self.inv and not self.inv2:
                    self._die()
                    if self.over: return
                return

        self.snake.insert(0, nh)
        ate_food = False
        if nh == self.food:
            self.score += FOOD_SCORE
            self._place("food")
            ate_food = True
        if self.multiplayer and nh == self.food2:
            self.score += FOOD_SCORE
            self._place("food2")
            ate_food = True
        if nh == self.bomb:
            self._kill_one()
            self._place("bomb")
        elif not ate_food:
            self.snake.pop()

        # 吃到食物后检测解锁（仅单人模式）
        if ate_food and not self.multiplayer:
            self._check_unlock()
        # 成就追踪：吃果子（仅单人关卡）
        if ate_food and not self.multiplayer and self.current_level > 0:
            self.ach_fruits += 1
            self._save_achievements()

    # ========== 怪物 ==========
    def _next_spawn(self):
        self.spawn_at = int(time.time()*1000) + random.randint(MON_SPAWN_LO, MON_SPAWN_HI)

    def _spawn_mon(self):
        if len(self.mons) >= self.max_mon:
            return
        occ = self._occ()
        free = [(x,y) for x in range(GW) for y in range(GH) if (x,y) not in occ]
        if not free:
            return
        # 确定活着的蛇头位置（多人模式可能有一方已阵亡）
        if self.multiplayer:
            p1_alive = self.snake and self.lives > 0
            p2_alive = self.snake2 and self.lives2 > 0
            if not p1_alive and not p2_alive:
                return
            sh = self.snake[0] if p1_alive else self.snake2[0]
        else:
            sh = self.snake[0]
        # 优先边缘+远离蛇头
        free.sort(key=lambda p: (-dist(p,sh),
            0 if (p[0]<=1 or p[0]>=GW-2 or p[1]<=1 or p[1]>=GH-2) else 1))
        pool = free[:max(1, len(free)//5)]
        pos = random.choice(pool)

        body = [pos]
        for _, (ddx,ddy) in random.sample(list(DIR.items()), len(DIR)):
            bx, by = pos
            segs = [pos]
            ok2 = True
            for _ in range(MON_LEN-1):
                bx += ddx; by += ddy
                if not ok(bx,by) or (bx,by) in occ:
                    ok2 = False; break
                segs.append((bx,by))
            if ok2:
                body = segs; break
        self.mons.append(body)
        self.mdr.append(random.choice(list(DIR.keys())))

    def _intercept_target(self, sh):
        """预测玩家前进方向，计算绕前堵路的拦截点"""
        pdx, pdy = DIR[self.dr]                  # 玩家当前移动方向
        steps = random.randint(3, 7)             # 预测前方 3~7 格
        px = (sh[0] + pdx * steps) % GW
        py = (sh[1] + pdy * steps) % GH
        return (px, py)

    def _move_mons(self):
        if not self.mons:
            return

        # 构建玩家障碍集（多人模式：无敌玩家不计入，怪物穿透）
        if self.multiplayer:
            p1_alive = self.snake and self.lives > 0
            p2_alive = self.snake2 and self.lives2 > 0
            if not p1_alive and not p2_alive:
                return  # 两人都阵亡
            player_body = set()
            # 无敌玩家的身体不作为障碍物 → 怪物直接穿透，也不会撞死
            if p1_alive and not self.inv:
                player_body |= set(self.snake)
            if p2_alive and not self.inv2:
                player_body |= set(self.snake2)
        else:
            player_body = set(self.snake)

        dead = []  # 本轮死亡的怪物索引（延迟删除避免索引错乱）

        for i in range(len(self.mons)):
            m = self.mons[i]
            mh = m[0]
            cur = self.mdr[i]

            # 每个怪物独立选择追击目标（最近的存活玩家）
            if self.multiplayer:
                p1_alive = self.snake and self.lives > 0
                p2_alive = self.snake2 and self.lives2 > 0
                if p1_alive and p2_alive:
                    sh = self.snake[0] if dist(mh, self.snake[0]) <= dist(mh, self.snake2[0]) else self.snake2[0]
                elif p1_alive:
                    sh = self.snake[0]
                else:
                    sh = self.snake2[0]
            else:
                sh = self.snake[0]

            # 障碍集：只包含玩家蛇身 + 自己的尾巴
            # 其他怪物可穿透（彼此不碰撞）
            occ = player_body | set(m[1:])

            nd = cur
            # === 优先级1：追玩家蛇（协同围猎：最近的追、其余的绕前堵路） ===
            d = dist(mh, sh)
            if d <= CHASE_R:
                # 统计其他也在追击的怪物（用于决定是否绕前拦截）
                other_hunting = [j for j in range(len(self.mons))
                                 if j != i and dist(self.mons[j][0], sh) <= CHASE_R]
                if other_hunting and d > 3 and random.random() < 0.5:
                    # 拦截模式：预测玩家前方位置，绕路堵截
                    intercept = self._intercept_target(sh)
                    cd = self._toward(mh, intercept)
                    nd = cd if self._can(mh, cd, occ) else self._best(mh, intercept, occ)
                else:
                    # 追击模式：直接追玩家
                    cd = self._toward(mh, sh)
                    nd = cd if self._can(mh, cd, occ) else self._best(mh, sh, occ)
            # === 优先级2：找食物吃（索敌范围 = 2× 追人范围） ===
            elif self.food:
                fd = dist(mh, self.food)
                if fd <= FOOD_CHASE_R:
                    cd = self._toward(mh, self.food)
                    nd = cd if self._can(mh, cd, occ) else self._best(mh, self.food, occ)
                elif random.random() < 0.2:
                    nd = self._rdir(mh, occ, [REV.get(cur, cur)])
            elif random.random() < 0.2:
                nd = self._rdir(mh, occ, [REV.get(cur, cur)])

            if not self._can(mh, nd, occ):
                nd = self._rdir(mh, occ)

            if nd is None:
                continue

            dx, dy = DIR[nd]
            nx, ny = mh[0]+dx, mh[1]+dy
            nx %= GW; ny %= GH            # 怪物穿墙

            self.mdr[i] = nd
            m.insert(0, (nx, ny))

            # ---- 怪物死亡判定 ----
            # 撞到玩家蛇身 → 怪物死亡
            if (nx, ny) in player_body:
                dead.append(i)
                continue
            # 自撞（头碰到自己身体） → 怪物死亡
            if (nx, ny) in m[1:]:
                dead.append(i)
                continue

            # ---- 存活：处理食物 / 生长 ----
            if (nx, ny) == self.food:
                self._place("food")       # 吃到果子 → 不 pop，身体 +1
            else:
                m.pop()

        # 倒序删除死亡怪物
        mon_deaths_this_tick = 0
        for i in sorted(dead, reverse=True):
            if i < len(self.mons):
                del self.mons[i]
            if i < len(self.mdr):
                del self.mdr[i]
            self.kills += 1
            mon_deaths_this_tick += 1
        # 成就追踪：怪物撞玩家/自撞死亡（仅单人关卡）
        if mon_deaths_this_tick > 0 and not self.multiplayer and self.current_level > 0:
            self.ach_mon_deaths += mon_deaths_this_tick
            self._save_achievements()
            # 成就追踪：炸弹击杀（仅单人关卡）
            if not self.multiplayer and self.current_level > 0:
                self.ach_kills += 1
                self._save_achievements()

    def _toward(self, fm, to):
        # 考虑穿墙的最短路径方向
        dx = to[0]-fm[0]; dy = to[1]-fm[1]
        if abs(dx) > GW//2: dx = -dx//abs(dx)*(GW-abs(dx))
        if abs(dy) > GH//2: dy = -dy//abs(dy)*(GH-abs(dy))
        if abs(dx) >= abs(dy):
            return "RIGHT" if dx>0 else "LEFT" if dx<0 else ("DOWN" if dy>0 else "UP")
        return "DOWN" if dy>0 else "UP" if dy<0 else ("RIGHT" if dx>0 else "LEFT")

    def _best(self, h, tgt, obs):
        bd, bv = None, 9999
        for dn, (dx,dy) in DIR.items():
            nx, ny = h[0]+dx, h[1]+dy
            if (nx,ny) in obs:
                continue
            v = dist((nx%GW, ny%GH), tgt)
            if v < bv:
                bv = v; bd = dn
        return bd if bd else self._rdir(h, obs)

    def _can(self, h, d, obs):
        dx, dy = DIR[d]
        nx, ny = h[0]+dx, h[1]+dy
        return (nx%GW, ny%GH) not in obs

    def _rdir(self, h, obs, exc=None):
        exc = exc or []
        cand = [d for d in DIR if d not in exc and self._can(h,d,obs)]
        if cand:
            return random.choice(cand)
        for d in DIR:
            if self._can(h,d,obs):
                return d
        return None

    # ========== 炸弹 ==========
    def _kill_one(self):
        if not self.mons:
            return
        hd = self.snake[0]
        bi, bd = 0, 9999
        for i, m in enumerate(self.mons):
            d = dist(m[0], hd)
            if d < bd:
                bd = d; bi = i
        if bi < len(self.mons):
            del self.mons[bi]
            if bi < len(self.mdr):
                del self.mdr[bi]
            self.kills += 1

    # ========== 掉命 / 结束 ==========
    def _die(self):
        self.lives -= 1
        if self.lives <= 0:
            if self.multiplayer:
                self.snake = []
                self._check_mp_end()
            else:
                self._end()
            return
        # 保留积分和长度，重置位置
        old = len(self.snake)
        cx, cy = GW//2, GH//2
        self.snake = [(cx-i, cy) for i in range(min(old, GW))]
        self.dr = "RIGHT"
        self.ndr = "RIGHT"
        self.inv = True
        self.inv_end = int(time.time()*1000) + INV_MS
        self.inv_show = True
        self._place("food")
        self._place("bomb")

    def _end(self):
        self.run = False
        self.over = True
        self._cancel_timer()
        # 更新本关最高分
        if self.current_level > 0:
            if self.score > self.level_best[self.current_level]:
                self.level_best[self.current_level] = self.score
            if self.score > self.high:
                self.high = self.score
        self._save_progress()
        self.canvas.delete("s","f","b","m")
        self._show_over()
        self._bar()

    def _show_over(self):
        c = self.canvas
        c.delete("msg")

        # 关卡信息
        if self.current_level > 0:
            cfg = LEVEL_CONFIG[self.current_level]
            level_text = f"{cfg['icon']} {cfg['name']}"
        else:
            level_text = "—"

        # 状态文字
        if self.current_level > 0 and self.score >= TARGET_SCORE:
            if self.current_level < TOTAL_LEVELS:
                status_text = f"✅ 已达成 {TARGET_SCORE} 分，下一关已解锁！"
                status_color = CHD
            else:
                status_text = "🏆 最终关卡通关！太厉害了！"
                status_color = "#ffd700"
        else:
            if self.current_level < TOTAL_LEVELS:
                need = max(0, TARGET_SCORE - self.score)
                status_text = f"距解锁下一关还差 {need} 分"
            else:
                status_text = f"最终得分: {self.score}"
            status_color = CINV

        c.create_rectangle(0, 0, self.cw, self.ch,
            fill=CBG, stipple="gray50", tags="msg")

        ys = [
            (-72, 26, COV, "💀  游戏结束"),
            (-36, 14, CTX, level_text),
            (-12, 13, status_color, status_text),
            (14, 13, CTX, f"最终得分: {self.score}"),
            (38, 12, CHD, f"蛇身长度: {len(self.snake)} 格"),
            (62, 12, CMH, f"击杀怪物: {self.kills} 只"),
            (92, 11, CDM, "Space 重新挑战  |  R 返回选关"),
        ]
        for y, sz, cl, tx in ys:
            c.create_text(self.cw//2, self.ch//2 + y,
                text=tx, font=("Microsoft YaHei", sz, "bold" if sz > 12 else "normal"),
                fill=cl, tags="msg")

    # ========== 食物 ==========
    def _occ(self):
        o = set(self.snake)
        if self.multiplayer and self.snake2:
            o.update(self.snake2)
        for m in self.mons:
            o.update(m)
        if self.food:
            o.add(self.food)
        if self.multiplayer and self.food2:
            o.add(self.food2)
        if self.bomb:
            o.add(self.bomb)
        return o

    def _place(self, which):
        o = self._occ()
        if len(o) >= TOTAL:
            return
        for _ in range(500):
            x = random.randint(0, GW-1)
            y = random.randint(0, GH-1)
            if (x,y) not in o:
                # 降低边缘刷新概率：离墙越近越容易被拒绝
                edge = min(x, GW-1-x, y, GH-1-y)
                if edge <= 1 and random.random() < (0.7 if edge == 0 else 0.4):
                    continue  # 拒绝此位置，重试
                if which == "food": self.food = (x,y)
                elif which == "food2": self.food2 = (x,y)
                else: self.bomb = (x,y)
                return
        # 回退：线性扫描（也优先内部）
        best = None
        for x in range(GW):
            for y in range(GH):
                if (x,y) not in o:
                    e = min(x, GW-1-x, y, GH-1-y)
                    if best is None or e > best[0]:
                        best = (e, x, y)
        if best:
            if which == "food": self.food = (best[1], best[2])
            elif which == "food2": self.food2 = (best[1], best[2])
            else: self.bomb = (best[1], best[2])

    # ========== 渲染 ==========
    def _draw(self):
        if self.over and not self.multiplayer:
            return
        if self.multiplayer and self.mp_over:
            return  # 结算界面单独绘制
        c = self.canvas
        c.delete("s","s2","f","f2","b","m","unlock")

        # ---- 解锁提示（游戏进行中显示） ----
        now = int(time.time() * 1000)
        if self.unlock_msg and now < self.unlock_msg_end:
            remaining = self.unlock_msg_end - now
            alpha = min(1.0, remaining / 500.0)  # 最后500ms淡出
            r = 255
            g = int(215 * alpha)
            b_val = int(50 * (1 - alpha))
            fill_color = f"#{r:02x}{max(0,min(255,g)):02x}{b_val:02x}"
            c.create_text(self.cw // 2, 35,
                          text=self.unlock_msg,
                          font=("Microsoft YaHei", 16, "bold"),
                          fill=fill_color, tags="unlock")
        elif self.unlock_msg and now >= self.unlock_msg_end:
            self.unlock_msg = None

        # ---- 关卡标题（游戏进行中） ----
        if self.current_level > 0:
            cfg = LEVEL_CONFIG[self.current_level]
            c.create_text(self.cw // 2, 16,
                          text=f"{cfg['icon']} {cfg['name']}",
                          font=("Microsoft YaHei", 10, "bold"),
                          fill=cfg["color"], tags="unlock")

        # 食物
        if self.food:
            fx,fy = self.food
            x1,y1 = fx*CELL+2, fy*CELL+2
            c.create_oval(x1,y1, x1+CELL-4,y1+CELL-4,
                fill=CFD, outline="#ff6b81", width=2, tags="f")

        # 食物2（多人模式）
        if self.multiplayer and self.food2:
            fx,fy = self.food2
            x1,y1 = fx*CELL+2, fy*CELL+2
            c.create_oval(x1,y1, x1+CELL-4,y1+CELL-4,
                fill="#ffa500", outline="#ff6600", width=2, tags="f2")

        # 炸弹
        if self.bomb:
            bx,by = self.bomb
            cx,cy = bx*CELL+CELL//2, by*CELL+CELL//2
            r = CELL//2-3
            c.create_polygon(cx,cy-r, cx+r,cy, cx,cy+r, cx-r,cy,
                fill=CBM, outline=CBO, width=2, tags="b")
            c.create_line(cx,cy-r, cx,cy-r-4, fill="#ffd700", width=2, tags="b")
            c.create_oval(cx-2,cy-r-7, cx+2,cy-r-3, fill="#ff8800", outline="", tags="b")

        # 蛇
        inv = self.inv
        for i, (sx,sy) in enumerate(self.snake):
            x1,y1 = sx*CELL+2, sy*CELL+2
            x2,y2 = x1+CELL-4, y1+CELL-4
            if inv and not self.inv_show:
                if i == 0:
                    c.create_rectangle(x1,y1,x2,y2, fill=CINV,
                        outline="#ffaa00", width=2, stipple="gray50", tags="s")
                continue
            if i == 0:
                hc = CINV if inv else CHD
                ol = "#ffaa00" if inv else "#00ffaa"
                c.create_rectangle(x1,y1,x2,y2, fill=hc, outline=ol, width=2, tags="s")
                es = 4; cx = sx*CELL+CELL//2; cy = sy*CELL+CELL//2
                if self.dr == "RIGHT":   ee = [(cx+3,cy-5),(cx+3,cy+1)]
                elif self.dr == "LEFT":  ee = [(cx-7,cy-5),(cx-7,cy+1)]
                elif self.dr == "UP":    ee = [(cx-5,cy-7),(cx+1,cy-7)]
                else:                    ee = [(cx-5,cy+3),(cx+1,cy+3)]
                for ex,ey in ee:
                    c.create_oval(ex,ey, ex+es,ey+es, fill="white", tags="s")
            else:
                a = max(0.3, 1-i/(len(self.snake)*1.2))
                if inv:
                    cl = f"#{int(255*a):02x}{int(221*a):02x}{int(87*a):02x}"
                else:
                    cl = f"#{0:02x}{int(204*a):02x}{int(106*a):02x}"
                c.create_rectangle(x1,y1,x2,y2, fill=cl, outline="", tags="s")

        # ---- 成就进度（左下角，仅单人关卡） ----
        if not self.multiplayer and self.current_level > 0:
            ach_lines = []
            kp = min(100, int(self.ach_kills / self.ach_thresholds["kills"] * 100))
            fp = min(100, int(self.ach_fruits / self.ach_thresholds["fruits"] * 100))
            mp = min(100, int(self.ach_mon_deaths / self.ach_thresholds["mon_deaths"] * 100))
            ach_lines.append(f"🏆 怪物杀手 {self.ach_kills}/{self.ach_thresholds['kills']} {'✅' if kp>=100 else f'{kp}%'}")
            ach_lines.append(f"🍎 果子王   {self.ach_fruits}/{self.ach_thresholds['fruits']} {'✅' if fp>=100 else f'{fp}%'}")
            ach_lines.append(f"💀 收藏家   {self.ach_mon_deaths}/{self.ach_thresholds['mon_deaths']} {'✅' if mp>=100 else f'{mp}%'}")
            ach_text = "  │  ".join(ach_lines)
            # 红字小提示
            c.create_text(10, self.ch - 14, text=ach_text,
                          font=("Microsoft YaHei", 8), fill="#ff6b6b",
                          anchor="sw", tags="unlock")

        # ---- 玩家2 蛇身（多人模式） ----
        if self.multiplayer and self.snake2:
            inv2 = self.inv2
            for i, (sx,sy) in enumerate(self.snake2):
                x1,y1 = sx*CELL+2, sy*CELL+2
                x2,y2 = x1+CELL-4, y1+CELL-4
                if inv2 and not self.inv_show2:
                    if i == 0:
                        c.create_rectangle(x1,y1,x2,y2, fill=CINV,
                            outline="#ffaa00", width=2, stipple="gray50", tags="s2")
                    continue
                if i == 0:
                    hc = CINV if inv2 else CP2
                    ol = "#ffaa00" if inv2 else CP2B
                    c.create_rectangle(x1,y1,x2,y2, fill=hc, outline=ol, width=2, tags="s2")
                    es = 4; cx = sx*CELL+CELL//2; cy = sy*CELL+CELL//2
                    if self.dr2 == "RIGHT":   ee = [(cx+3,cy-5),(cx+3,cy+1)]
                    elif self.dr2 == "LEFT":  ee = [(cx-7,cy-5),(cx-7,cy+1)]
                    elif self.dr2 == "UP":    ee = [(cx-5,cy-7),(cx+1,cy-7)]
                    else:                     ee = [(cx-5,cy+3),(cx+1,cy+3)]
                    for ex,ey in ee:
                        c.create_oval(ex,ey, ex+es,ey+es, fill="white", tags="s2")
                else:
                    a = max(0.3, 1-i/(len(self.snake2)*1.2))
                    if inv2:
                        cl = f"#{int(255*a):02x}{int(221*a):02x}{int(87*a):02x}"
                    else:
                        cl = f"#{0:02x}{int(166*a):02x}{int(255*a):02x}"
                    c.create_rectangle(x1,y1,x2,y2, fill=cl, outline="", tags="s2")

        # 怪物
        for idx, m in enumerate(self.mons):
            md = self.mdr[idx] if idx < len(self.mdr) else "RIGHT"
            for j, (mx,my) in enumerate(m):
                x1,y1 = mx*CELL+2, my*CELL+2
                x2,y2 = x1+CELL-4, y1+CELL-4
                if j == 0:
                    c.create_rectangle(x1,y1,x2,y2, fill=CMH,
                        outline="#ff4500", width=2, tags="m")
                    es = 3; cx = mx*CELL+CELL//2; cy = my*CELL+CELL//2
                    if md == "RIGHT":   ee = [(cx+2,cy-4),(cx+2,cy+1)]
                    elif md == "LEFT":  ee = [(cx-5,cy-4),(cx-5,cy+1)]
                    elif md == "UP":    ee = [(cx-4,cy-5),(cx+1,cy-5)]
                    else:               ee = [(cx-4,cy+2),(cx+1,cy+2)]
                    for ex,ey in ee:
                        c.create_oval(ex,ey, ex+es,ey+es, fill="#ffcccc", tags="m")
                else:
                    a = max(0.4, 1-j/(len(m)*1.2))
                    cl = f"#{int(231*a):02x}{int(76*a):02x}{int(60*a):02x}"
                    c.create_rectangle(x1,y1,x2,y2, fill=cl, outline="", tags="m")

    # ========== 信息栏 ==========
    def _bar(self):
        if self.multiplayer:
            # ---- 多人模式顶栏（P1-左 | 怪物-正中 | P2-右） ----
            self.sep_r1.config(text="│"); self.sep_r2.config(text="│"); self.sep_r3.config(text="│")
            self.lvl.config(text="🟢 P1", fg=CP1)
            self.lsc.config(text="♥"*self.lives + "♡"*(LIVES-self.lives))
            self.llv.config(text=f"🍎{self.score} 💣{self.kills}")

            self.lmn.config(text=f"👾{len(self.mons)}/{self.max_mon}")

            self.llv2.config(text=f"💣{self.kills2} 🍎{self.score2}")
            self.lsc2.config(text="♥"*self.lives2 + "♡"*(LIVES-self.lives2))
            self.lhi.config(text="🔵 P2")

            # 无敌状态（分开显示在各自玩家侧）
            if self.inv:
                rem = max(0, (self.inv_end - int(time.time()*1000))/1000)
                self.liv.config(text=f"🟢🛡{rem:.1f}s")
            else:
                self.liv.config(text="")
            if self.inv2:
                rem = max(0, (self.inv_end2 - int(time.time()*1000))/1000)
                self.liv2.config(text=f"🛡{rem:.1f}s🔵")
            else:
                self.liv2.config(text="")

        else:
            # ---- 单人模式顶栏 ----
            self.llv2.config(text=""); self.lsc2.config(text=""); self.liv2.config(text="")
            self.sep_r1.config(text=""); self.sep_r2.config(text=""); self.sep_r3.config(text="")

            self.lsc.config(text=f"🍎 {self.score}")
            self.llv.config(text="♥"*self.lives + "♡"*(LIVES-self.lives))
            self.lmn.config(text=f"👾 {len(self.mons)}/{self.max_mon}")
            if self.inv:
                rem = max(0, (self.inv_end - int(time.time()*1000))/1000)
                self.liv.config(text=f"🛡 {rem:.1f}s")
            else:
                self.liv.config(text="")
            if self.score > self.high:
                self.high = self.score
            self.lhi.config(text=f"🏆 {self.high}")

            if self.current_level > 0:
                cfg = LEVEL_CONFIG[self.current_level]
                self.lvl.config(text=f"{cfg['icon']} {cfg['name']}", fg=cfg["color"])
            else:
                self.lvl.config(text="🗺️ 选关", fg=CHD)

    # ========== 暂停 / 重来 ==========
    def _pause(self):
        if not self.run or self.over:
            return
        if not self.multiplayer and self.current_level == 0:
            return
        self.paused = not self.paused
        self.canvas.delete("pmsg")
        if self.paused:
            self.canvas.create_text(self.cw//2, self.ch//2,
                text="⏸  已暂停", font=("Microsoft YaHei",22,"bold"),
                fill=CTX, tags="pmsg")

    def _restart(self):
        """R键：返回选关界面"""
        if self.multiplayer:
            self._mp_exit()
            return
        if self.current_level == 0:
            return  # 已在选关界面
        self._back_to_select()

    # ========== 方向 ==========
    def _dir_p1(self, nd):
        """玩家1 方向（WASD）"""
        if self.multiplayer:
            # 多人模式：控制玩家1
            if nd != REV.get(self.dr, "") and self.run and not self.mp_over:
                self.ndr = nd
        else:
            # 单人模式：同原逻辑
            if self.current_level == 0:
                return
            if nd != REV.get(self.dr, ""):
                self.ndr = nd
                if not self.run:
                    self._start()

    def _dir_arrow(self, nd):
        """方向键：多人模式→玩家2，单人模式→玩家1"""
        if self.multiplayer:
            # 多人模式：控制玩家2
            if nd != REV.get(self.dr2, "") and self.run and not self.mp_over:
                self.ndr2 = nd
        else:
            # 单人模式：控制玩家1
            if self.current_level == 0:
                return
            if nd != REV.get(self.dr, ""):
                self.ndr = nd
                if not self.run:
                    self._start()


if __name__ == "__main__":
    SnakeGame()
