"""
贪吃蛇小游戏 - 优化版
↑↓←→ / WASD 移动 | Space 开始 | P 暂停 | R 重来 | F11 全屏
红果 +10分 | 紫炸弹果 炸掉最近怪物
怪物上限3只 | 3条命 | 无敌穿墙传送
自动适配屏幕分辨率，窗口化全屏运行
"""

import tkinter as tk
import random
import time

# ==================== 常量 ====================
CELL = 20                     # 每格像素（会根据屏幕微调）
GW, GH = 30, 20               # 网格宽高（启动时根据屏幕自动计算）
TOTAL = GW * GH
SPEED = 140
INIT_LEN = 3
FOOD_SCORE = 10

MON_LEN = 3
MAX_MON = 3
MON_SPAWN_LO = 3000
MON_SPAWN_HI = 7000
CHASE_R = 8

LIVES = 3
INV_MS = 3000
BLINK = 150

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

DIR = {"UP": (0,-1), "DOWN": (0,1), "LEFT": (-1,0), "RIGHT": (1,0)}
REV = {"UP":"DOWN", "DOWN":"UP", "LEFT":"RIGHT", "RIGHT":"LEFT"}

def ok(x, y):
    return 0 <= x < GW and 0 <= y < GH

def dist(a, b):
    return abs(a[0]-b[0]) + abs(a[1]-b[1])


class SnakeGame:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("贪吃蛇")

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
        self._init()
        self._grid()
        self._bar()
        self._welcome()

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
        self.lsc = tk.Label(f, text="🍎 0", font=F, fg=CTX, bg="#0f0f23")
        self.lsc.pack(side=tk.LEFT, padx=(10,4))
        tk.Label(f, text="│", font=("Microsoft YaHei",9), fg="#333", bg="#0f0f23").pack(side=tk.LEFT)
        self.llv = tk.Label(f, text="", font=F, fg=CFD, bg="#0f0f23")
        self.llv.pack(side=tk.LEFT, padx=4)
        tk.Label(f, text="│", font=("Microsoft YaHei",9), fg="#333", bg="#0f0f23").pack(side=tk.LEFT)
        self.lmn = tk.Label(f, text="👾 0/3", font=F, fg=CMH, bg="#0f0f23")
        self.lmn.pack(side=tk.LEFT, padx=4)
        tk.Label(f, text="│", font=("Microsoft YaHei",9), fg="#333", bg="#0f0f23").pack(side=tk.LEFT)
        self.liv = tk.Label(f, text="", font=F, fg=CINV, bg="#0f0f23")
        self.liv.pack(side=tk.LEFT, padx=4)
        self.lhi = tk.Label(f, text="🏆 0", font=F, fg="#ffd700", bg="#0f0f23")
        self.lhi.pack(side=tk.RIGHT, padx=10)

    def _botbar(self):
        f = tk.Frame(self.root, bg="#0f0f23", height=22)
        f.pack(fill=tk.X); f.pack_propagate(False)
        tk.Label(f, text="↑↓←→/WASD 移动 | Space 开始 | P 暂停 | R 重来 | F11 全屏",
                 font=("Microsoft YaHei",8), fg=CDM, bg="#0f0f23").pack()

    def _keys(self):
        for k, d in [("<Up>","UP"),("<Down>","DOWN"),("<Left>","LEFT"),("<Right>","RIGHT"),
                     ("<w>","UP"),("<s>","DOWN"),("<a>","LEFT"),("<d>","RIGHT")]:
            self.root.bind(k, lambda e, d=d: self._dir(d))
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
        cx, cy = GW//2, GH//2
        for i in range(INIT_LEN):
            self.snake.append((cx-i, cy))

    def _grid(self):
        for x in range(0, self.cw, CELL):
            self.canvas.create_line(x,0,x,self.ch, fill=CGR, dash=(1,3))
        for y in range(0, self.ch, CELL):
            self.canvas.create_line(0,y,self.cw,y, fill=CGR, dash=(1,3))

    def _welcome(self):
        self.canvas.delete("s","f","b","m","msg")
        self.canvas.create_text(self.cw//2, self.ch//2-15,
            text="🐍  贪 吃 蛇  🐍", font=("Microsoft YaHei",24,"bold"),
            fill=CHD, tags="msg")
        self.canvas.create_text(self.cw//2, self.ch//2+25,
            text="Space 开始游戏", font=("Microsoft YaHei",13),
            fill=CTX, tags="msg")

    # ========== 开始 / 循环 ==========
    def _start(self):
        if self.run and not self.paused:
            return
        self._cancel_timer()
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
            if self.inv:
                if now >= self.inv_end:
                    self.inv = False
                else:
                    self.inv_show = ((self.inv_end - now) // BLINK) % 2 == 0

            self._move_snake()
            if self.over:
                self._end(); return

            self._move_mons()
            if self.over:
                self._end(); return

            if len(self.mons) < MAX_MON and now >= self.spawn_at:
                self._spawn_mon()
                self._next_spawn()

            self._draw()

        self._bar()
        if not self.over:
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

        self.snake.insert(0, nh)
        ate = False
        if nh == self.food:
            self.score += FOOD_SCORE
            self._place("food")
            ate = True
        if nh == self.bomb:
            self._kill_one()
            self._place("bomb")
            ate = True
        if not ate:
            self.snake.pop()

    # ========== 怪物 ==========
    def _next_spawn(self):
        self.spawn_at = int(time.time()*1000) + random.randint(MON_SPAWN_LO, MON_SPAWN_HI)

    def _spawn_mon(self):
        if len(self.mons) >= MAX_MON:
            return
        occ = self._occ()
        free = [(x,y) for x in range(GW) for y in range(GH) if (x,y) not in occ]
        if not free:
            return
        # 优先边缘+远离蛇头
        sh = self.snake[0]
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

    def _move_mons(self):
        if not self.mons:
            return
        sh = self.snake[0]
        occ = set(self.snake)
        for m in self.mons:
            occ.update(m)

        for i in range(len(self.mons)):
            m = self.mons[i]
            mh = m[0]
            cur = self.mdr[i]
            d = dist(mh, sh)

            nd = cur
            if self._ahead(i, mh, cur, 3):
                nd = self._rdir(mh, occ, [cur])
            elif d <= CHASE_R:
                cd = self._toward(mh, sh)
                if self._can(mh, cd, occ):
                    nd = cd
                else:
                    nd = self._best(mh, sh, occ)
            elif random.random() < 0.2:
                nd = self._rdir(mh, occ, [REV.get(cur,cur)])

            if not self._can(mh, nd, occ):
                nd = self._rdir(mh, occ)

            if nd is None:
                continue

            dx, dy = DIR[nd]
            nx, ny = mh[0]+dx, mh[1]+dy
            # 怪物穿墙
            nx %= GW; ny %= GH

            # 增量更新障碍集（修复多怪物重叠bug）
            tail = m[-1]
            occ.discard(tail)
            occ.add((nx, ny))

            self.mdr[i] = nd
            m.insert(0, (nx, ny))
            m.pop()

    def _ahead(self, idx, mh, d, rng):
        dx, dy = DIR[d]
        for s in range(1, rng+1):
            cp = (mh[0]+dx*s, mh[1]+dy*s)
            for j, om in enumerate(self.mons):
                if j != idx and cp in om:
                    return True
        return False

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
        self.canvas.delete("s","f","b","m")
        self._show_over()
        self._bar()

    def _show_over(self):
        self.canvas.delete("msg")
        self.canvas.create_rectangle(0,0,self.cw,self.ch,
            fill=CBG, stipple="gray50", tags="msg")
        ys = [(-50,26,COV,"💀  游戏结束"),
              (-5,14,CTX,f"最终得分: {self.score}"),
              (23,12,CHD,f"蛇身长度: {len(self.snake)} 格"),
              (48,12,CMH,f"击杀怪物: {self.kills} 只"),
              (78,11,CDM,"R 重新开始  |  Space 再来一局")]
        for y,sz,cl,tx in ys:
            self.canvas.create_text(self.cw//2, self.ch//2+y,
                text=tx, font=("Microsoft YaHei",sz,"bold" if sz>12 else "normal"),
                fill=cl, tags="msg")

    # ========== 食物 ==========
    def _occ(self):
        o = set(self.snake)
        for m in self.mons:
            o.update(m)
        if self.food:
            o.add(self.food)
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
            else: self.bomb = (best[1], best[2])

    # ========== 渲染 ==========
    def _draw(self):
        if self.over:
            return
        c = self.canvas
        c.delete("s","f","b","m")

        # 食物
        if self.food:
            fx,fy = self.food
            x1,y1 = fx*CELL+2, fy*CELL+2
            c.create_oval(x1,y1, x1+CELL-4,y1+CELL-4,
                fill=CFD, outline="#ff6b81", width=2, tags="f")

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
        self.lsc.config(text=f"🍎 {self.score}")
        self.llv.config(text="♥"*self.lives + "♡"*(LIVES-self.lives))
        self.lmn.config(text=f"👾 {len(self.mons)}/{MAX_MON}")
        if self.inv:
            rem = max(0, (self.inv_end - int(time.time()*1000))/1000)
            self.liv.config(text=f"🛡 {rem:.1f}s")
        else:
            self.liv.config(text="")
        if self.score > self.high:
            self.high = self.score
        self.lhi.config(text=f"🏆 {self.high}")

    # ========== 暂停 / 重来 ==========
    def _pause(self):
        if not self.run or self.over:
            return
        self.paused = not self.paused
        self.canvas.delete("pmsg")
        if self.paused:
            self.canvas.create_text(self.cw//2, self.ch//2,
                text="⏸  已暂停", font=("Microsoft YaHei",22,"bold"),
                fill=CTX, tags="pmsg")

    def _restart(self):
        self._cancel_timer()
        self.canvas.delete("s","f","b","m","msg","pmsg")
        self._init()
        self._bar()
        self._welcome()

    # ========== 方向 ==========
    def _dir(self, nd):
        if nd != REV.get(self.dr, ""):
            self.ndr = nd
            if not self.run:
                self._start()


if __name__ == "__main__":
    SnakeGame()
