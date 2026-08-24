# ChessUI.py (v1.2 Massive UI overhaul)

import tkinter as tk
from tkinter import ttk, messagebox
import math
import random
import time
import re
from GameLogic import *
from AI import ChessBot, board_hash
from OpponentAI import OpponentAI
from EngineRuntime import (
    persistent_worker,
    generate_pgn,
    generate_series_opening_sequence,
    write_series_stats_file,
    strip_casualties,
    board_to_fen,
)
from enum import Enum
import multiprocessing as mp

class GameMode(Enum):
    HUMAN_VS_BOT   = "bot"
    HUMAN_VS_HUMAN = "human"
    AI_VS_AI       = "ai_vs_ai"

_FEN_CHAR_TO_CLASS = {'p': Pawn, 'n': Knight, 'b': Bishop, 'r': Rook, 'q': Queen, 'k': King}

# ---------------------------------------------------------------------------
# Main application
# ---------------------------------------------------------------------------
class EnhancedChessApp:
    MAIN_AI_NAME     = "AI Bot"
    OPPONENT_AI_NAME = "OP Bot"
    ANALYSIS_AI_NAME = "Analysis"
    slidermaxvalue   = 12
    MAX_GAME_MOVES   = 200
    AI_SERIES_GAMES  = 300

    def __init__(self, master):
        self.master = master
        self.master.title("Standard Chess")
        random.seed()

        # --- COMMUNICATION ---
        self.comm_queue = mp.Queue()

        # --- PERSISTENT WORKER STATE ---
        self.current_task_id   = 0
        self.main_work_queue   = mp.Queue()
        self.op_work_queue     = mp.Queue()
        self.main_cancel_event = mp.Event()
        self.op_cancel_event   = mp.Event()
        self.active_worker_name = None   # 'main' | 'op' | None
        self.analysis_thinking  = False
        self.main_worker        = None   
        self.op_worker          = None
        self._shutting_down     = False

        # --- BOARD / GAME STATE ---
        self.board        = Board()
        self.turn         = "white"
        self.selected     = None
        self.valid_moves  = []
        self.game_over    = False
        self.game_result  = None
        self.dragging     = False
        self.drag_piece_ghost = None
        self.drag_start   = None
        self.is_interactive = True
        self.premove      = None

        # --- DRAWING / ARROWS STATE ---
        self.custom_arrows      = set()
        self.custom_highlights  = set()
        self.rc_start_pos       = None

        self.full_history         = []
        self.history_pointer      = -1
        self.position_counts      = {}
        self.current_opening_sequence = []
        self.square_size          = 75
        self.base_sidebar_width   = 280

        self.game_mode           = tk.StringVar(value=GameMode.HUMAN_VS_BOT.value)
        self.analysis_mode_var   = tk.BooleanVar(value=True)
        self.ai_series_running   = False
        self.ai_series_stats     = {'game_count': 0, 'my_ai_wins': 0, 'op_ai_wins': 0, 'draws': 0}
        self.move_stats          = {}
        self._pending_move_stat  = {}
        
        self.auto_save_stats_var  = tk.BooleanVar(value=True)
        self.show_pv_var          = tk.BooleanVar(value=True)
        self.long_notation_var    = tk.BooleanVar(value=False)
        self.instant_move         = tk.BooleanVar(value=False)
        self.use_opening_book_var = tk.BooleanVar(value=True)
        self.show_tt_fullness_var = tk.BooleanVar(value=False)

        self.current_pv_raw  = []
        self.current_pv_san  = []
        self.last_pv_message = None

        self.white_playing_bot_type = "main"
        self.human_color            = "white"
        self.board_orientation      = "white"
        self.last_move_timestamp    = None
        self.game_started           = False

        self.last_eval_score = 0.0
        self.last_eval_depth = None
        self.last_eval_bar_w = 0
        self.last_eval_bar_h = 0
        
        self.hovered_pv_tag = None

        # --- TIME STATE ---
        self.time_control_seconds = tk.IntVar(value=300)
        self.white_time      = 0.0
        self.black_time      = 0.0
        self.increment       = 0.0
        self.last_clock_tick = None
        self.clock_running   = False
        self.use_clock_var   = tk.BooleanVar(value=True)

        self.COLORS = self.setup_styles()
        self.master.configure(bg=self.COLORS['bg_dark'])
        self.build_ui()
        self.master.bind("<Key>", self.handle_key_press)
        self.master.protocol("WM_DELETE_WINDOW", self._on_close)
        self._start_persistent_workers()
        self.process_comm_queue()
        self.reset_game()

    # ------------------------------------------------------------------ workers
    def _start_persistent_workers(self):
        self.main_worker = mp.Process(
            target=persistent_worker,
            args=(self.main_work_queue, self.comm_queue,
                  self.main_cancel_event, ChessBot),
            daemon=True,
        )
        self.op_worker = mp.Process(
            target=persistent_worker,
            args=(self.op_work_queue, self.comm_queue,
                  self.op_cancel_event, OpponentAI),
            daemon=True,
        )
        self.main_worker.start()
        self.op_worker.start()

    def _on_close(self):
        """Shut down workers and queues so window close can't hang the process."""
        if self._shutting_down:
            return
        self._shutting_down = True
        self.clock_running = False

        try:
            self._stop_ai_process(drain_queue=False, invalidate_task=True)
        except Exception:
            pass

        for event in (self.main_cancel_event, self.op_cancel_event):
            try:
                event.set()
            except Exception:
                pass

        for queue in (self.main_work_queue, self.op_work_queue):
            try:
                queue.put_nowait(None)
            except Exception:
                try:
                    queue.put(None, timeout=0.1)
                except Exception:
                    pass

        for worker in (self.main_worker, self.op_worker):
            if worker is None:
                continue
            try:
                worker.join(timeout=0.4)
            except Exception:
                pass
            if worker.is_alive():
                try:
                    worker.terminate()
                except Exception:
                    pass
                try:
                    worker.join(timeout=0.4)
                except Exception:
                    pass

        for queue in (self.comm_queue, self.main_work_queue, self.op_work_queue):
            try:
                queue.close()
            except Exception:
                pass
            try:
                queue.cancel_join_thread()
            except Exception:
                pass

        try:
            self.master.quit()
        except Exception:
            pass
        self.master.destroy()

    def _message_task_id(self, msg):
        if not isinstance(msg, tuple) or not msg:
            return None
        bare_lengths = {'log': 2, 'eval': 3, 'pv': 5, 'move': 2}
        bare_len = bare_lengths.get(msg[0])
        if bare_len is None or len(msg) != bare_len + 1:
            return None
        task_id = msg[-1]
        return task_id if isinstance(task_id, int) else None

    # ------------------------------------------------------------------ helpers
    def _format_san_display(self, s):
        return s if (self.long_notation_var.get() or not s) else strip_casualties(s)

    def _on_notation_toggle(self):
        self.update_moves_list()
        self._render_pv()

    # ------------------------------------------------------------------ clock helpers
    def _start_clock(self):
        if not self.use_clock_var.get() or self.game_over or self.clock_running:
            return
        self.last_clock_tick = time.time()
        self.clock_running   = True
        self._tick_clock()

    def _pause_clock(self):
        was_running        = self.clock_running
        self.clock_running = False
        return was_running

    def _reset_clock_state(self):
        base = float(self.time_control_seconds.get())
        self.white_time      = base
        self.black_time      = base
        self.increment       = base / 60.0
        self.clock_running   = False
        self.last_clock_tick = None

    # ------------------------------------------------------------------ UI build
    def build_ui(self):
        sw, sh = self.master.winfo_screenwidth(), self.master.winfo_screenheight()
        self.master.geometry(f"{sw}x{sh}+0+0")
        self.master.state('zoomed')

        self.main_frame = ttk.Frame(self.master, style='Left.TFrame')
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # --- LEFT PANEL ---
        self.left_panel = ttk.Frame(self.main_frame, style='Left.TFrame')
        self.left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        self.left_panel.pack_propagate(False)
        ttk.Label(self.left_panel, text="CHESS", style='Header.TLabel',
                  font=('Helvetica', 22, 'bold')).pack(pady=(0, 5))
        self.pv_text = tk.Text(self.left_panel, height=6, bg=self.COLORS['bg_medium'],
                               fg=self.COLORS['text_light'], font=('Helvetica', 10),
                               wrap=tk.WORD, borderwidth=1, relief="solid")
        self.pv_text.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=10)
        self.pv_text.config(state=tk.DISABLED)
        self._build_control_widgets(self.left_panel)

        # --- CENTER PANEL ---
        self.center_panel = ttk.Frame(self.main_frame, style='Right.TFrame')
        self.center_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.board_column = ttk.Frame(self.center_panel, style='Right.TFrame')
        self.board_column.pack(expand=True, fill=tk.BOTH)

        self.eval_frame = ttk.Frame(self.board_column, style='Right.TFrame',
                                    width=COLS * self.square_size, height=58)
        self.eval_frame.pack(side=tk.TOP, anchor=tk.CENTER, pady=(6, 5))
        self.eval_frame.pack_propagate(False)
        self.eval_score_label = ttk.Label(self.eval_frame, text="Even",
                                          style='Status.TLabel', anchor="center")
        self.eval_score_label.pack(side=tk.TOP, pady=(0, 4))
        self.eval_bar_canvas = tk.Canvas(self.eval_frame, width=COLS * self.square_size,
                                         height=20, bg=self.COLORS['bg_light'],
                                         highlightthickness=1,
                                         highlightbackground=self.COLORS['text_dark'])
        self.eval_bar_canvas.pack(side=tk.TOP, anchor=tk.CENTER)
        self.eval_bar_canvas.bind("<Configure>", self.redraw_eval_bar_on_resize)

        self.board_row_frame = ttk.Frame(self.board_column, style='Right.TFrame')
        self.board_row_frame.pack(expand=True, fill=tk.BOTH)
        self.canvas_frame = ttk.Frame(self.board_row_frame, style='Canvas.TFrame')
        self.canvas_frame.pack(expand=True, fill=tk.BOTH)

        self.canvas = tk.Canvas(self.canvas_frame,
                                width=COLS * self.square_size, height=ROWS * self.square_size,
                                bg=self.COLORS['bg_medium'], highlightthickness=0)
        self.board_image    = self.create_board_image()
        self.board_image_id = self.canvas.create_image(0, 0, anchor='nw', tags="board")
        self.canvas.pack(expand=True)

        for attr in ('top_bot_label', 'bottom_bot_label'):
            setattr(self, attr, ttk.Label(
                self.board_row_frame, text="", font=("Helvetica", 11, "bold"),
                background=self.COLORS['bg_medium'], foreground=self.COLORS['text_light'],
                anchor="center", justify=tk.CENTER))

        # Navigation bar
        self.navigation_frame = ttk.Frame(self.center_panel, style='Right.TFrame')
        self.navigation_frame.pack(fill=tk.X, pady=(5, 10))
        self.start_button, self.undo_button, self.redo_button, self.end_button = [
            ttk.Button(self.navigation_frame, text=t, command=c,
                       style='Nav.TButton', state=tk.DISABLED)
            for t, c in [("«", self.go_to_start), ("‹", self.undo_move),
                          ("›", self.redo_move),   ("»", self.go_to_end)]]
        self.navigation_frame.columnconfigure(0, weight=1)
        self.navigation_frame.columnconfigure(5, weight=1)
        for col, btn in enumerate([self.start_button, self.undo_button,
                                    self.redo_button,  self.end_button], start=1):
            btn.grid(row=0, column=col, padx=5)

        # --- RIGHT PANEL ---
        self.right_panel = ttk.Frame(self.main_frame, style='Left.TFrame')
        self.right_panel.pack(side=tk.RIGHT, fill=tk.Y, padx=(10, 0))
        self.right_panel.pack_propagate(False)
        self._build_right_sidebar_widgets(self.right_panel)

        self.main_frame.bind("<Configure>",   self.handle_main_resize)
        self.center_panel.bind("<Configure>", self.handle_board_resize)
        
        # --- INFORMATION SHORTCUT BUTTON ---
        self.info_btn = tk.Button(
            self.master, text="ⓘ", font=("Helvetica", 13, "bold"),
            bg=self.COLORS['bg_dark'], fg=self.COLORS['text_dark'],
            activebackground=self.COLORS['bg_dark'], activeforeground=self.COLORS['text_light'],
            bd=0, relief="flat", cursor="hand2", command=self.show_readme_popup
        )
        self.info_btn.place(in_=self.master, relx=1.0, y=12, x=-20, anchor="ne")
        
        # --- PERMANENT CANVAS EVENT BINDINGS ---
        self.canvas.bind("<Button-1>",        self.on_drag_start)
        self.canvas.bind("<B1-Motion>",       self.on_drag_motion)
        self.canvas.bind("<ButtonRelease-1>", self.on_drag_end)
        
        self.canvas.bind("<Button-3>",        self.on_right_click_start)
        self.canvas.bind("<B3-Motion>",       self.on_right_click_drag)
        self.canvas.bind("<ButtonRelease-3>", self.on_right_click_end)
        
        # Mac OS fallback for right-click support
        self.canvas.bind("<Button-2>",        self.on_right_click_start)
        self.canvas.bind("<B2-Motion>",       self.on_right_click_drag)
        self.canvas.bind("<ButtonRelease-2>", self.on_right_click_end)

    def _build_control_widgets(self, parent):
        gf = ttk.Frame(parent, style='Left.TFrame')
        gf.pack(fill=tk.X, pady=(0, 5))
        ttk.Label(gf, text="GAME MODE", style='Header.TLabel').pack(anchor=tk.W)
        for mode in GameMode:
            ttk.Radiobutton(gf, text=mode.name.replace("_", " ").title(),
                            variable=self.game_mode, value=mode.value,
                            command=self.on_mode_changed,
                            style='Custom.TRadiobutton').pack(anchor=tk.W, pady=(2, 0))

        cf = ttk.Frame(parent, style='Left.TFrame')
        cf.pack(fill=tk.X, pady=5)
        self.controls_frame = cf
        for txt, cmd in [("NEW GAME",        self.reset_game),
                         ("SWAP SIDES",      self.swap_sides),
                         ("CLEAR HASH",      self.clear_hash_manually),
                         ("AI vs OP Series", self.start_ai_series),
                         ("VERIFY PERFT",    self.run_move_checker)]:
            ttk.Button(cf, text=txt, command=cmd, style='Control.TButton').pack(fill=tk.X, pady=3)
        self.flip_view_btn = ttk.Button(cf, text="FLIP VIEW",
                                        command=self.toggle_board_view, style='Control.TButton')
        self.flip_view_btn.pack(fill=tk.X, pady=3)

        ttk.Label(cf, text="Depth:", style='SmallHeader.TLabel').pack(anchor=tk.W, pady=(5, 0))
        self.bot_depth_slider = tk.Scale(cf, from_=1, to=self.slidermaxvalue,
                                         orient=tk.HORIZONTAL, bg=self.COLORS['bg_dark'],
                                         fg=self.COLORS['text_light'],
                                         highlightthickness=0, relief='flat')
        self.bot_depth_slider.set(ChessBot.search_depth)
        self.bot_depth_slider.pack(fill=tk.X, pady=(0, 3))

        for text, var, cmd in [
            ("Use Opening Book",           self.use_opening_book_var, None),
            ("Instant Moves",              self.instant_move,         None),
            ("Analysis Mode (H-vs-H)",     self.analysis_mode_var,    self._update_analysis_after_state_change),
            ("Auto-save Depth Stats",      self.auto_save_stats_var,  None),
            ("Show Engine Lines (PV)",     self.show_pv_var,          self._render_pv),
            ("Show TT Fullness",           self.show_tt_fullness_var, None),
        ]:
            kw = {'command': cmd} if cmd else {}
            ttk.Checkbutton(cf, text=text, variable=var,
                            style='Custom.TCheckbutton', **kw).pack(anchor=tk.W, pady=0)

    def _build_right_sidebar_widgets(self, parent):
        info = ttk.Frame(parent, style='Left.TFrame')
        info.pack(side=tk.TOP, fill=tk.X, pady=(0, 5))
        self.info_frame = info
        self.game_info_label = ttk.Label(info, text="Match Info", style='Header.TLabel')
        self.game_info_label.pack(anchor=tk.W)
        self.turn_label = ttk.Label(info, text="WHITE'S TURN", style='Status.TLabel')
        self.turn_label.pack(fill=tk.X, pady=(5, 5))
        self.tt_fullness_label = ttk.Label(info, text="", style='SmallHeader.TLabel')
        self.tt_fullness_label.pack(anchor=tk.W, pady=(2, 2))
        ttk.Checkbutton(info, text="Use Clock", variable=self.use_clock_var,
                        command=self._toggle_clock).pack(anchor=tk.W, pady=(2, 2))

        self.clock_frame = ttk.Frame(info, style='Left.TFrame')
        self.clock_frame.pack(fill=tk.X, pady=(5, 5))
        self.black_clock_lbl = tk.Label(self.clock_frame, text="00:00.0",
                                        font=('Courier', 18, 'bold'),
                                        bg=self.COLORS['bg_medium'],
                                        fg=self.COLORS['text_light'], pady=2)
        self.black_clock_lbl.pack(side=tk.TOP, fill=tk.X, pady=1)
        self.white_clock_lbl = tk.Label(self.clock_frame, text="00:00.0",
                                        font=('Courier', 18, 'bold'),
                                        bg=self.COLORS['bg_light'],
                                        fg=self.COLORS['text_light'], pady=2)
        self.white_clock_lbl.pack(side=tk.BOTTOM, fill=tk.X, pady=1)

        self.time_control_frame = ttk.Frame(info, style='Left.TFrame')
        self.time_control_frame.pack(fill=tk.X, pady=(5, 5))
        self.time_control_label = ttk.Label(self.time_control_frame,
                                            text="Time Control: 05:00",
                                            style='SmallHeader.TLabel')
        self.time_control_label.pack(anchor=tk.W)
        self.time_control_slider = tk.Scale(
            self.time_control_frame, from_=10, to=600, orient=tk.HORIZONTAL,
            bg=self.COLORS['bg_dark'], fg=self.COLORS['text_light'],
            highlightthickness=0, relief='flat', showvalue=False,
            variable=self.time_control_seconds,
            command=lambda _=None: self._update_time_control_label())
        self.time_control_slider.set(int(self.time_control_seconds.get()))
        self.time_control_slider.pack(fill=tk.X, pady=(2, 2))
        self.time_control_slider.bind("<ButtonRelease-1>", lambda e: self.reset_game())

        self.bottom_tools_frame = ttk.Frame(parent, style='Left.TFrame')
        self.bottom_tools_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(0, 10))
        self.fen_entry = self._create_import_export_widget(
            self.bottom_tools_frame, "FEN String:", self.load_fen_from_entry, self.copy_fen_to_clipboard)
        self.pgn_entry = self._create_import_export_widget(
            self.bottom_tools_frame, "PGN Record:", self.load_pgn_from_entry, self.copy_pgn_to_clipboard)

        self.scoreboard_label = ttk.Label(parent, text="", font=("Helvetica", 11),
                                          justify=tk.LEFT, background=self.COLORS['bg_dark'],
                                          foreground=self.COLORS['text_light'])
        self.scoreboard_label.pack(side=tk.BOTTOM, fill=tk.X, pady=(5, 5))

        ttk.Label(parent, text="Move History", style='SmallHeader.TLabel').pack(side=tk.TOP, anchor=tk.W)
        self.tree_frame = tk.Frame(parent, bg=self.COLORS['bg_medium'])
        self.tree_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True, pady=(2, 10))
        hdr = tk.Frame(self.tree_frame, bg=self.COLORS['bg_light'])
        hdr.pack(fill=tk.X)
        tk.Label(hdr, text=" #  " + "White".center(14) + "Black".center(14),
                 bg=self.COLORS['bg_light'], fg=self.COLORS['text_light'],
                 font=('Courier', 11, 'bold'), anchor=tk.W).pack(side=tk.LEFT, fill=tk.X)
        self.moves_text = tk.Text(self.tree_frame, font=('Courier', 11),
                                  bg=self.COLORS['bg_medium'], fg=self.COLORS['text_light'],
                                  borderwidth=0, highlightthickness=0,
                                  state=tk.DISABLED, cursor="arrow", wrap=tk.NONE)
        sb = ttk.Scrollbar(self.tree_frame, orient=tk.VERTICAL, command=self.moves_text.yview)
        self.moves_text.configure(yscrollcommand=sb.set)
        self.moves_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)

        # Global event delegation (fixes the lambda tag_bind memory leak)
        self.pv_text.bind("<Motion>", self._on_pv_text_motion)
        self.pv_text.bind("<Leave>", self._on_pv_text_leave)
        
        self.moves_text.bind("<Button-1>", self._on_moves_text_click)
        self.moves_text.bind("<Motion>", self._on_moves_text_motion)
        self.moves_text.bind("<Leave>", lambda e: self.moves_text.config(cursor="arrow"))

    def _create_import_export_widget(self, parent, label, load_cmd, copy_cmd):
        frame = ttk.Frame(parent, style='Left.TFrame')
        frame.pack(fill=tk.X, pady=(2, 2))
        ttk.Label(frame, text=label, style='SmallHeader.TLabel').pack(anchor=tk.W)
        entry = ttk.Entry(frame, font=('Courier', 10), style='TEntry')
        entry.pack(fill=tk.X, pady=(2, 2))
        bf = ttk.Frame(frame, style='Left.TFrame')
        bf.pack(fill=tk.X)
        prefix = label.split()[0]
        ttk.Button(bf, text=f"Load {prefix}", command=load_cmd,
                   style='Control.TButton').pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        ttk.Button(bf, text=f"Copy {prefix}", command=copy_cmd,
                   style='Control.TButton').pack(side=tk.RIGHT, fill=tk.X, expand=True, padx=(2, 0))
        return entry

    def setup_styles(self):
        style = ttk.Style()
        style.theme_use('clam')
        C = {'bg_dark':    '#1a1a2e', 'bg_medium':  '#16213e', 'bg_light':   '#0f3460',
             'accent':     '#e94560', 'text_light': '#ffffff', 'text_dark':  '#a2a2a2',
             'warning':    '#FF8C00'}

        style.configure('.',             background=C['bg_dark'],   foreground=C['text_light'])
        style.configure('TFrame',        background=C['bg_dark'])
        style.configure('Left.TFrame',   background=C['bg_dark'])
        style.configure('Right.TFrame',  background=C['bg_medium'])
        style.configure('Canvas.TFrame', background=C['bg_medium'])

        style.configure('Header.TLabel',      background=C['bg_dark'],  foreground=C['text_light'], font=('Helvetica', 14, 'bold'), padding=(0, 5))
        style.configure('SmallHeader.TLabel', background=C['bg_dark'],  foreground=C['text_light'], font=('Helvetica', 12, 'bold'), padding=(0, 1))
        style.configure('Status.TLabel',      background=C['bg_light'], foreground=C['text_light'], font=('Helvetica', 14, 'bold'), padding=(6, 4), relief='solid', borderwidth=1)

        style.configure('Nav.TButton', background=C['bg_light'], foreground=C['text_light'],
                        font=('Helvetica', 16, 'bold'), padding=(10, 5), borderwidth=0)
        style.map('Nav.TButton', background=[('active', C['bg_light']), ('pressed', C['bg_medium'])],
                                 foreground=[('disabled', C['text_dark'])])

        for name, bg, pressed in [('Control', C['accent'], '#d13550'),
                                   ('Flipped', C['warning'], '#E07B00')]:
            style.configure(f'{name}.TButton', background=bg, foreground=C['text_light'],
                            font=('Helvetica', 11, 'bold'), padding=(8, 4), borderwidth=0)
            style.map(f'{name}.TButton', background=[('active', bg), ('pressed', pressed)])

        for name in ('Custom.TRadiobutton', 'Custom.TCheckbutton'):
            style.configure(name, background=C['bg_dark'], foreground=C['text_light'],
                            font=('Helvetica', 11))
            style.map(name, background=[('active', C['bg_dark'])],
                      indicatorcolor=[('selected', C['accent'])])

        style.configure('TEntry', fieldbackground='#FFFFFF', foreground='#000000', insertcolor='#000000')
        return C

    # ------------------------------------------------------------------ resize
    def handle_main_resize(self, event):
        w = max(240, int(event.width * 0.20))
        if w != self.left_panel.winfo_width():
            self.left_panel.config(width=w)
            self.right_panel.config(width=w + 20)

    def handle_board_resize(self, event):
        eval_h = max(self.eval_frame.winfo_height(), self.eval_frame.winfo_reqheight())
        nav_h  = max(self.navigation_frame.winfo_height(), self.navigation_frame.winfo_reqheight())
        vw, vh = event.width - 40, event.height - eval_h - nav_h - 35
        if vw <= 1 or vh <= 1:
            return
        new_sq = min(vw // COLS, vh // ROWS)
        bw = COLS * self.square_size
        self.eval_frame.config(width=bw)
        self.eval_bar_canvas.config(width=bw)
        if new_sq != self.square_size and new_sq > 0:
            self.square_size = new_sq
            bw = COLS * self.square_size
            self.canvas.config(width=bw, height=ROWS * self.square_size)
            self.eval_frame.config(width=bw)
            self.eval_bar_canvas.config(width=bw)
            self.board_image = self.create_board_image()
            self.draw_board()
        self._position_side_labels()

    def handle_key_press(self, event):
        if isinstance(event.widget, (tk.Entry, tk.Text)):
            return
        if self.is_ai_thinking() and not self.analysis_thinking:
            return
        action = {'Left': self.undo_move, 'Right': self.redo_move,
                  'Home': self.go_to_start, 'End': self.go_to_end}.get(event.keysym)
        if action:
            action()

    def redraw_eval_bar_on_resize(self, event):
        self.draw_eval_bar(self.last_eval_score, self.last_eval_depth)

    def _analysis_output_enabled(self):
        return bool(getattr(self, 'analysis_mode_var', None) and self.analysis_mode_var.get())

    def _clear_analysis_output(self):
        self.last_eval_score = 0.0
        self.last_eval_depth = None
        self.current_pv_raw  = []
        self.current_pv_san  = []
        self.last_pv_message = None
        self.draw_eval_bar(0)
        self.eval_score_label.config(text="Even")
        if hasattr(self, 'pv_text'):
            self.pv_text.config(state=tk.NORMAL)
            self.pv_text.delete(1.0, tk.END)
            self.pv_text.config(state=tk.DISABLED)

    def _sync_analysis_output_visibility(self):
        if self._analysis_output_enabled():
            if not self.eval_frame.winfo_manager():
                self.eval_frame.pack(side=tk.TOP, anchor=tk.CENTER, pady=(6, 5),
                                     before=self.board_row_frame)
            self._render_pv()
        else:
            self.eval_frame.pack_forget()
            self.pv_text.pack_forget()

    # ------------------------------------------------------------------ flip / swap / mode
    def _update_flip_view_button_style(self):
        mode = self.game_mode.get()
        warn = (mode == GameMode.HUMAN_VS_BOT.value and self.board_orientation != self.human_color) or \
               (mode != GameMode.HUMAN_VS_BOT.value and self.board_orientation == "black")
        self.flip_view_btn.configure(style='Flipped.TButton' if warn else 'Control.TButton')

    def toggle_board_view(self):
        self.board_orientation = "black" if self.board_orientation == "white" else "white"
        self._update_flip_view_button_style()
        self.update_bot_labels()
        self.draw_board()

    def on_mode_changed(self):
        self._stop_ai_process()
        mode = self.game_mode.get()
        if mode == GameMode.HUMAN_VS_BOT.value:
            self.board_orientation = self.human_color
            if not self.game_over and self.turn != self.human_color:
                self.master.after(self._get_ai_move_delay(), self._make_game_ai_move)
        elif mode == GameMode.AI_VS_AI.value:
            if not self.game_over:
                self.master.after(self._get_ai_move_delay(), self._make_game_ai_move)
        else:
            self._update_analysis_after_state_change()
        self._update_flip_view_button_style()
        self.update_ui_after_state_change()

    def swap_sides(self):
        self._stop_ai_process()
        if self.game_mode.get() == GameMode.HUMAN_VS_BOT.value:
            self.human_color       = "black" if self.human_color == "white" else "white"
            self.board_orientation = self.human_color
            self._update_flip_view_button_style()
            self.update_ui_after_state_change()
            if not self.game_over and self.turn != self.human_color:
                print(f"Swapped sides. AI ({self.turn}) taking over...")
                self.master.after(self._get_ai_move_delay(), self._make_game_ai_move)

    def _reset_game_state_vars(self):
        self.full_history    = [(self.board.clone(), self.turn, None)]
        self.history_pointer = 0
        self.position_counts = {board_hash(self.board, self.turn): 1}
        self.game_over       = False
        self.game_result     = None
        self.premove         = None
        self.last_eval_score = 0.0
        self.last_eval_depth = None
        self.draw_eval_bar(0)
        self.current_pv_raw  = []
        self.last_pv_message = None
        self.custom_arrows.clear()
        self.custom_highlights.clear()
        self.rc_start_pos = None
        if hasattr(self, 'pv_text'):
            self.pv_text.config(state=tk.NORMAL)
            self.pv_text.delete(1.0, tk.END)
            self.pv_text.config(state=tk.DISABLED)

    # ------------------------------------------------------------------ FEN / PGN
    def get_current_fen(self):
        return board_to_fen(self.board, self.turn)

    def copy_fen_to_clipboard(self):
        fen = self.get_current_fen()
        self.fen_entry.delete(0, tk.END)
        self.fen_entry.insert(0, fen)
        self.master.clipboard_clear()
        self.master.clipboard_append(fen)

    def load_fen_from_entry(self):
        fen = self.fen_entry.get().strip()
        if not fen:
            return
        parts = fen.split()
        self._stop_ai_process()
        self.board = Board(setup=False)
        r = c = 0
        for ch in parts[0]:
            if ch == '/':
                r += 1; c = 0
            elif ch.isdigit():
                c += int(ch)
            else:
                pc = _FEN_CHAR_TO_CLASS.get(ch.lower())
                if pc:
                    self.board.add_piece(pc("white" if ch.isupper() else "black"), r, c)
                c += 1
        self.turn = "white" if (parts[1] if len(parts) > 1 else 'w').lower() == 'w' else "black"

        # Parse Castling Rights
        self.board.castling_rights = 0
        if len(parts) > 2 and parts[2] != '-':
            if 'K' in parts[2]: self.board.castling_rights |= CASTLE_WK
            if 'Q' in parts[2]: self.board.castling_rights |= CASTLE_WQ
            if 'k' in parts[2]: self.board.castling_rights |= CASTLE_BK
            if 'q' in parts[2]: self.board.castling_rights |= CASTLE_BQ

        # Parse En Passant
        self.board.ep_square = None
        if len(parts) > 3 and parts[3] != '-':
            ep_str = parts[3].lower()
            if len(ep_str) == 2 and ep_str[0] in 'abcdefgh' and ep_str[1] in '12345678':
                self.board.ep_square = (8 - int(ep_str[1]), ord(ep_str[0]) - ord('a'))

        # Parse Halfmove clock
        self.board.halfmove_clock = int(parts[4]) if len(parts) > 4 and parts[4].isdigit() else 0

        # --- CHESS LEGALITY CHECK ---
        if not self.board.white_king_pos or not self.board.black_king_pos:
            messagebox.showerror("Invalid FEN", "Illegal Position: Both Kings must be present on the board.")
            self.reset_game(schedule_ai=False)
            return

        passive_color = "black" if self.turn == "white" else "white"
        if is_in_check(self.board, passive_color):
            messagebox.showerror("Invalid FEN", f"Illegal Position: The side not to move ({passive_color}) is already in check.")
            self.reset_game(schedule_ai=False)
            return
        # ----------------------------

        self.game_started = True
        self._reset_clock_state()
        self.render_clocks()
        self._reset_game_state_vars()
        status, winner = get_game_state(self.board, self.turn, self.position_counts,
                                        self.history_pointer, self.MAX_GAME_MOVES)
        if status != "ongoing":
            self.game_over   = True
            self.game_result = (status, winner)
        self.board_orientation = self.human_color
        self._update_flip_view_button_style()
        self.update_ui_after_state_change()
        self._update_analysis_after_state_change()
        if not self.game_over and self.game_mode.get() == GameMode.HUMAN_VS_BOT.value \
                and self.turn != self.human_color:
            self.master.after(self._get_ai_move_delay(), self._make_game_ai_move)

    def get_current_pgn(self):
        return generate_pgn(self.full_history, self.game_result)

    def copy_pgn_to_clipboard(self):
        pgn = self.get_current_pgn()
        self.pgn_entry.delete(0, tk.END)
        self.pgn_entry.insert(0, pgn)
        self.master.clipboard_clear()
        self.master.clipboard_append(pgn)

    def load_pgn_from_entry(self):
        pgn_text = self.pgn_entry.get().strip()
        if not pgn_text:
            return
        self.reset_game(schedule_ai=False)
        self._pause_clock()
        self.last_clock_tick = None
        for res in ["1-0", "0-1", "1/2-1/2", "*"]:
            pgn_text = pgn_text.replace(res, "")
        pgn_text = re.sub(r'\d+\.+', '', pgn_text).replace(',', ' ')
        while pgn_text.strip():
            pgn_text = pgn_text.strip()
            san_map  = {}
            for m in get_all_legal_moves(self.board, self.turn):
                child = self.board.clone()
                child.make_move(m[0], m[1])
                san_map[format_move_san(self.board, child, m)] = m
            matched_move = matched_san = None
            for san in sorted(san_map, key=len, reverse=True):
                if pgn_text.startswith(san) and \
                        (len(pgn_text) == len(san) or pgn_text[len(san)].isspace()):
                    matched_move = san_map[san]
                    matched_san  = san
                    break
            if matched_move:
                self.board.make_move(matched_move[0], matched_move[1])
                self.execute_move_and_check_state(self.turn, matched_move)
                pgn_text = pgn_text[len(matched_san):]
                if self.game_over:
                    break
            else:
                messagebox.showwarning("PGN Error", f"Could not parse: {pgn_text[:20]}...")
                break
        self.last_clock_tick = time.time()

    # ------------------------------------------------------------------ move history UI
    def update_moves_list(self):
        self.moves_text.config(state=tk.NORMAL)
        self.moves_text.delete(1.0, tk.END)
        for tag in self.moves_text.tag_names():
            if tag.startswith("ply_"):
                self.moves_text.tag_delete(tag)

        formatted  = []
        start_turn = self.full_history[0][1]
        for i in range(1, len(self.full_history)):
            m = self.full_history[i][2]
            if m:
                formatted.append(format_move_san(self.full_history[i-1][0], self.full_history[i][0], m))

        pairs = []
        if start_turn == 'black' and formatted:
            pairs.append(["...", formatted[0]])
            formatted = formatted[1:]
        for i in range(0, len(formatted), 2):
            pairs.append([formatted[i], formatted[i+1] if i+1 < len(formatted) else ""])

        for i, pair in enumerate(pairs):
            self.moves_text.insert(tk.END, f"{i+1}.".ljust(4), "num")
            w_ptr = (i * 2) + 1 if start_turn == 'white' else (i * 2)
            b_ptr = w_ptr + 1
            w_tag, b_tag = f"ply_{w_ptr}", f"ply_{b_ptr}"
            self.moves_text.insert(tk.END, self._format_san_display(pair[0]).center(14), w_tag)
            self.moves_text.insert(
                tk.END,
                self._format_san_display(pair[1]).center(14) if pair[1] else " " * 14,
                b_tag if pair[1] else "")
            self.moves_text.insert(tk.END, "\n")

        self.moves_text.tag_configure("num", foreground=self.COLORS['text_dark'])
        for tag in self.moves_text.tag_names():
            if tag.startswith("ply_"):
                self.moves_text.tag_configure(tag, background=self.COLORS['bg_medium'],
                                              foreground=self.COLORS['text_light'])
        if self.history_pointer > 0:
            atag = f"ply_{self.history_pointer}"
            self.moves_text.tag_configure(atag, background=self.COLORS['accent'],
                                          foreground=self.COLORS['text_light'])
            try:
                self.moves_text.see(f"{atag}.first")
            except tk.TclError:
                pass
        self.moves_text.config(state=tk.DISABLED)

    # ------------------------------------------------------------------ core gameplay
    def execute_move_and_check_state(self, player_who_moved, move):
        if self.use_clock_var.get() and not self.game_over and self.increment:
            if player_who_moved == 'white':
                self.white_time += self.increment
            else:
                self.black_time += self.increment
            self.render_clocks()
        self.switch_turn()
        self._start_clock()
        if self.history_pointer < len(self.full_history) - 1:
            self.full_history = self.full_history[:self.history_pointer + 1]
            self.position_counts.clear()
            for board, turn, _ in self.full_history:
                h = board_hash(board, turn)
                self.position_counts[h] = self.position_counts.get(h, 0) + 1
        self.full_history.append((self.board.clone(), self.turn, move))
        self.history_pointer += 1
        key = board_hash(self.board, self.turn)
        self.position_counts[key] = self.position_counts.get(key, 0) + 1
        status, winner = get_game_state(self.board, self.turn, self.position_counts,
                                        self.history_pointer, self.MAX_GAME_MOVES)
        if status != "ongoing":
            self.game_over   = True
            self.game_result = (status, winner)
        self.update_ui_after_state_change()
        if self.game_over:
            print(f"Game Over! Result: {self.game_result[0]}")
            self._stop_ai_process()
            if self.game_mode.get() == GameMode.AI_VS_AI.value and self.ai_series_running:
                self.process_ai_series_result()

    def _execute_ai_move(self, the_move):
        if self.game_over:
            return
        if the_move:
            self.board.make_move(the_move[0], the_move[1])
            self.execute_move_and_check_state(self.turn, the_move)

            # Auto-execute premove if legal, otherwise instantly clear visual highlight
            if not self.game_over and self.game_mode.get() == GameMode.HUMAN_VS_BOT.value and self.turn == self.human_color:
                if self.premove:
                    pm = self.premove
                    self.premove = None
                    if pm in get_all_legal_moves(self.board, self.turn):
                        self.board.make_move(pm[0], pm[1])
                        self.execute_move_and_check_state(self.turn, pm)
                        if not self.game_over and self.turn != self.human_color:
                            self.set_interactivity(False)
                            self.master.after(self._get_ai_move_delay(), self._make_game_ai_move)
                    else:
                        # Premove became illegal — redraw board immediately so highlight vanishes
                        self.draw_board()

            if not self.game_over and self.game_mode.get() == GameMode.AI_VS_AI.value:
                self.master.after(self._get_ai_move_delay(), self._make_game_ai_move)
        else:
            print("AI reported no valid move.")
            
        self._stop_ai_process()
        self.update_bot_labels()
        self.set_interactivity(True)

    def _get_premove_destinations(self, piece, start_pos):
        """Returns all geometrically reachable squares for a piece on an open board."""
        sr, sc = start_pos
        sq = sr * 8 + sc
        pz = piece.z_idx
        dests = []

        if pz == 0:  # Pawn
            p_dir = -1 if piece.color == 'white' else 1
            # 1-step forward
            if 0 <= sr + p_dir < 8:
                dests.append((sr + p_dir, sc))
            # 2-steps forward from starting rank
            if sr == piece.starting_row and 0 <= sr + 2 * p_dir < 8:
                dests.append((sr + 2 * p_dir, sc))
            # Diagonal captures / en-passant
            for dc in (-1, 1):
                if 0 <= sr + p_dir < 8 and 0 <= sc + dc < 8:
                    dests.append((sr + p_dir, sc + dc))

        elif pz == 1:  # Knight
            dests.extend(KNIGHT_ATTACKS_FROM[(sr, sc)])

        elif pz == 2:  # Bishop (all diagonals regardless of blockers)
            for ray in RAYS_DIAGONAL[sq]:
                dests.extend(ray)

        elif pz == 3:  # Rook (all orthogonals regardless of blockers)
            for ray in RAYS_ORTHOGONAL[sq]:
                dests.extend(ray)

        elif pz == 4:  # Queen (all rays regardless of blockers)
            for ray in RAYS_ALL[sq]:
                dests.extend(ray)

        elif pz == 5:  # King (1-step in any direction + castling target squares)
            dests.extend(KING_ATTACKS_FROM[(sr, sc)])
            if sc == 4 and (sr == 0 or sr == 7):
                dests.extend([(sr, 2), (sr, 6)])

        return dests

    def on_drag_start(self, event):
        cleared_custom = False
        if self.custom_arrows or self.custom_highlights:
            self.custom_arrows.clear()
            self.custom_highlights.clear()
            cleared_custom = True

        if self.premove:
            self.premove = None
            cleared_custom = True

        if self.game_over:
            if cleared_custom: self.draw_board()
            return

        r, c = self.canvas_to_board(event.x, event.y)
        if r == -1 or not self.board.grid[r][c]:
            if cleared_custom: self.draw_board()
            return

        piece = self.board.grid[r][c]
        mode = self.game_mode.get()

        # Check if this is a premove drag (opponent's turn in Bot mode)
        is_premove = (mode == GameMode.HUMAN_VS_BOT.value and self.turn != self.human_color) or \
                     (self.is_ai_thinking() and not self.analysis_thinking)

        if is_premove:
            if piece.color != self.human_color:
                if cleared_custom: self.draw_board()
                return
            self.selected = (r, c)
            self.drag_start = (r, c)
            self.dragging = True
            # Only show dots on currently reachable squares
            all_pseudo = get_all_pseudo_legal_moves(self.board, self.human_color)
            self.valid_moves_for_highlight = [e for s, e in all_pseudo if s == self.selected]
            # But allow dropping anywhere along the piece's full open-board geometry
            dests = self._get_premove_destinations(piece, (r, c))
            self.valid_moves = [(self.selected, d) for d in dests]
            self.drag_piece_ghost = self.canvas.create_text(
                event.x, event.y, text=piece.symbol(),
                font=("Arial Unicode MS", int(self.square_size * 0.7)),
                fill=piece.color, tags="drag_ghost")
            self.draw_board()
            self.canvas.tag_raise("drag_ghost")
            return

        if piece.color != self.turn:
            if cleared_custom: self.draw_board()
            return

        self.selected  = (r, c)
        self.drag_start = (r, c)
        self.dragging  = True
        self.valid_moves = get_all_legal_moves(self.board, self.turn)
        self.valid_moves_for_highlight = [e for s, e in self.valid_moves if s == self.selected]
        self.drag_piece_ghost = self.canvas.create_text(
            event.x, event.y, text=piece.symbol(),
            font=("Arial Unicode MS", int(self.square_size * 0.7)),
            fill=self.turn, tags="drag_ghost")
        self.draw_board()
        self.canvas.tag_raise("drag_ghost")

    def on_drag_motion(self, event):
        if self.dragging:
            self.canvas.coords(self.drag_piece_ghost, event.x, event.y)

    def on_drag_end(self, event):
        if not self.dragging:
            self.valid_moves = []
            self.valid_moves_for_highlight = []
            self.selected = None
            self.draw_board()
            return
            
        self.dragging = False
        self.canvas.delete("drag_ghost")
        row, col = self.canvas_to_board(event.x, event.y)
        if row == -1 or not self.drag_start:
            self.drag_start = None
            self.selected = None
            self.valid_moves = []
            self.valid_moves_for_highlight = []
            self.draw_board()
            return
            
        start_pos, end_pos = self.drag_start, (row, col)
        mode = self.game_mode.get()

        is_premove = (mode == GameMode.HUMAN_VS_BOT.value and self.turn != self.human_color) or \
                     (self.is_ai_thinking() and not self.analysis_thinking)

        # Enforce piece movement rules for premoves
        if is_premove:
            if (start_pos, end_pos) in self.valid_moves:
                self.premove = (start_pos, end_pos)
            self.drag_start = None
            self.selected = None
            self.valid_moves = []
            self.valid_moves_for_highlight = []
            self.draw_board()
            return

        # Regular move (validate against current board state legal moves)
        current_legal = get_all_legal_moves(self.board, self.turn)
        if (start_pos, end_pos) in current_legal:
            promo_cls = self.check_and_prompt_promotion(start_pos, end_pos)
            if promo_cls is False:  # User cancelled/closed promotion dialog
                self.drag_start = None
                self.selected = None
                self.valid_moves = []
                self.valid_moves_for_highlight = []
                self.draw_board()
                return

            self._apply_move_with_promotion(start_pos, end_pos, promo_cls)
            self.execute_move_and_check_state(self.turn, (start_pos, end_pos))
            if not self.game_over:
                if mode == GameMode.HUMAN_VS_BOT.value and self.turn != self.human_color:
                    self.drag_start = None
                    self.selected = None
                    self.valid_moves = []
                    self.valid_moves_for_highlight = []
                    self.set_interactivity(False)
                    self.master.after(self._get_ai_move_delay(), self._make_game_ai_move)
                    return
                elif mode == GameMode.HUMAN_VS_HUMAN.value:
                    self._update_analysis_after_state_change()
                    
        self.drag_start = None
        self.selected = None
        self.valid_moves = []
        self.valid_moves_for_highlight = []
        self.update_ui_after_state_change()
        self.set_interactivity(True)

    # ------------------------------------------------------------------ Promotion & Rules Verification
    def check_and_prompt_promotion(self, start_pos, end_pos):
        """Checks if human pawn moved to back rank and requests promotion choice."""
        piece = self.board.grid[start_pos[0]][start_pos[1]]
        if isinstance(piece, Pawn):
            target_rank = 0 if piece.color == "white" else 7
            if end_pos[0] == target_rank:
                return self._show_promotion_dialog(piece.color)
        return None

    def _show_promotion_dialog(self, color):
        """Displays modal popup to pick Queen, Rook, Bishop, or Knight."""
        dialog = tk.Toplevel(self.master)
        dialog.title("Pawn Promotion")
        dialog.configure(bg=self.COLORS['bg_dark'])
        dialog.transient(self.master)
        dialog.grab_set()
        dialog.resizable(False, False)

        dialog.update_idletasks()
        dw, dh = 340, 115
        mx = self.master.winfo_x() + (self.master.winfo_width() - dw) // 2
        my = self.master.winfo_y() + (self.master.winfo_height() - dh) // 2
        dialog.geometry(f"{dw}x{dh}+{mx}+{my}")

        ttk.Label(dialog, text="Choose piece to promote to:", style='Header.TLabel').pack(pady=(8, 4))

        promo_frame = ttk.Frame(dialog, style='Left.TFrame')
        promo_frame.pack(pady=5)

        chosen = [Queen]

        choices = [
            ("Queen", Queen, "♕" if color == "white" else "♛"),
            ("Rook", Rook, "♖" if color == "white" else "♜"),
            ("Bishop", Bishop, "♗" if color == "white" else "♝"),
            ("Knight", Knight, "♘" if color == "white" else "♞"),
        ]

        for name, cls, sym in choices:
            btn = tk.Button(
                promo_frame, text=f"{sym}\n{name}", font=("Helvetica", 10, "bold"),
                bg=self.COLORS['bg_light'], fg=self.COLORS['text_light'],
                activebackground=self.COLORS['accent'], activeforeground="#ffffff",
                relief="flat", width=6,
                command=lambda c=cls: [chosen.__setitem__(0, c), dialog.destroy()]
            )
            btn.pack(side=tk.LEFT, padx=4)

        dialog.protocol("WM_DELETE_WINDOW", lambda: [chosen.__setitem__(0, False), dialog.destroy()])
        self.master.wait_window(dialog)
        return chosen[0]

    def _apply_move_with_promotion(self, start_pos, end_pos, promo_cls):
        """Executes move on board, applying promotion type if selected."""
        try:
            self.board.make_move(start_pos, end_pos, promo_cls)
        except TypeError:
            self.board.make_move(start_pos, end_pos)
            if promo_cls:
                self.board.grid[end_pos[0]][end_pos[1]] = promo_cls(self.turn)

    def run_move_checker(self):
        """Validates starting position legal move count against standard chess rules."""
        test_board = Board()
        d1_moves = get_all_legal_moves(test_board, "white")
        d1_count = len(d1_moves)

        # Depth 2 Perft calculation (20 x 20 = 400 expected)
        d2_count = 0
        for m in d1_moves:
            b_clone = test_board.clone()
            b_clone.make_move(m[0], m[1])
            d2_moves = get_all_legal_moves(b_clone, "black")
            d2_count += len(d2_moves)

        d1_expected = 20
        d2_expected = 400
        d1_pass = (d1_count == d1_expected)
        d2_pass = (d2_count == d2_expected)

        details = (
            f"--- START POSITION PERFT CHECK ---\n"
            f"Depth 1 Legal Moves: {d1_count} (Expected: {d1_expected}) -> {'PASS [OK]' if d1_pass else 'FAIL [MISMATCH]'}\n"
            f"Depth 2 Legal Moves: {d2_count} (Expected: {d2_expected}) -> {'PASS [OK]' if d2_pass else 'FAIL [MISMATCH]'}\n\n"
            f"Depth 1 Moves Breakdown ({d1_count} total):\n"
        )
        for i, m in enumerate(d1_moves, 1):
            child = test_board.clone()
            child.make_move(m[0], m[1])
            san = format_move_san(test_board, child, m)
            details += f"  {i:2d}. {san.ljust(6)} ({m[0]} -> {m[1]})\n"

        print("\n" + details)
        if d1_pass and d2_pass:
            messagebox.showinfo(
                "Perft Rules Check Passed",
                f"Standard Chess Rule Verification: SUCCESS!\n\n"
                f"Depth 1: {d1_count}/{d1_expected} legal moves\n"
                f"Depth 2: {d2_count}/{d2_expected} legal moves"
            )
        else:
            messagebox.showerror(
                "Perft Rules Check Failed",
                f"MISMATCH DETECTED against standard chess!\n\n"
                f"Depth 1: {d1_count} (Expected: {d1_expected})\n"
                f"Depth 2: {d2_count} (Expected: {d2_expected})\n\n"
                f"See terminal log for details."
            )

    # ------------------------------------------------------------------ Right-Click Drawings
    def on_right_click_start(self, event):
        if self.premove:
            self.premove = None
            self.draw_board()
        r, c = self.canvas_to_board(event.x, event.y)
        if r != -1:
            self.rc_start_pos = (r, c)
            
    def on_right_click_drag(self, event):
        if not getattr(self, 'rc_start_pos', None):
            return
            
        self.canvas.delete("rc_ghost")
        r, c = self.canvas_to_board(event.x, event.y)
        if r == -1: 
            return
            
        if (r, c) != self.rc_start_pos:
            self._draw_arrow(self.rc_start_pos[0], self.rc_start_pos[1], r, c, tags="rc_ghost")

    def on_right_click_end(self, event):
        if not getattr(self, 'rc_start_pos', None): 
            return
            
        self.canvas.delete("rc_ghost")
        r, c = self.canvas_to_board(event.x, event.y)
        if r != -1:
            if (r, c) == self.rc_start_pos:
                if (r, c) in self.custom_highlights:
                    self.custom_highlights.remove((r, c))
                else:
                    self.custom_highlights.add((r, c))
            else:
                arrow = (self.rc_start_pos, (r, c))
                if arrow in self.custom_arrows:
                    self.custom_arrows.remove(arrow)
                else:
                    self.custom_arrows.add(arrow)
                    
        self.rc_start_pos = None
        self.draw_board()

    def _draw_highlight(self, r, c, tags):
        x, y = self.board_to_canvas(r, c)
        # Semi-transparent red highlight with slightly darker solid border
        self.canvas.create_rectangle(
            x, y, x + self.square_size, y + self.square_size,
            fill="#ff4444", stipple="gray50", outline="#cc0000", width=2, tags=tags)

    def _draw_arrow(self, r1, c1, r2, c2, tags):
        x1, y1 = self.board_to_canvas(r1, c1)
        x2, y2 = self.board_to_canvas(r2, c2)
        cx1, cy1 = x1 + self.square_size // 2, y1 + self.square_size // 2
        cx2, cy2 = x2 + self.square_size // 2, y2 + self.square_size // 2
        
        d = math.hypot(cx2 - cx1, cy2 - cy1)
        if d == 0: 
            return
            
        # Add gaps from exact center so it respects the piece location nicely
        gap = self.square_size * 0.3
        
        if d > gap * 2:
            theta = math.atan2(cy2 - cy1, cx2 - cx1)
            start_x = cx1 + math.cos(theta) * gap
            start_y = cy1 + math.sin(theta) * gap
            end_x = cx2 - math.cos(theta) * gap
            end_y = cy2 - math.sin(theta) * gap
            
            aw = max(3, self.square_size // 7)
            
            self.canvas.create_line(
                start_x, start_y, end_x, end_y, 
                arrow=tk.LAST, fill="#ffaa00", width=aw,
                arrowshape=(aw * 2.5, aw * 3, aw * 1.2), 
                capstyle=tk.ROUND, joinstyle=tk.ROUND, tags=tags)

    # ------------------------------------------------------------------ resets and modes
    def clear_hash_manually(self):
        self._force_clear_hash = True
        self._stop_ai_process(invalidate_task=True)
        print("--- Transposition Table & History Cleared ---")
        if self.analysis_mode_var.get() and self.game_mode.get() == GameMode.HUMAN_VS_HUMAN.value:
            self._update_analysis_after_state_change()

    def reset_game(self, schedule_ai=True):
        self._force_clear_hash = True
        if self.game_mode.get() != GameMode.AI_VS_AI.value:
            self.ai_series_running = False
        self._stop_ai_process()
        self.board               = Board()
        self.turn                = "white"
        self.game_started        = False
        self.last_move_timestamp = time.time()
        self.selected            = None
        self.valid_moves         = []
        self._reset_game_state_vars()
        self._reset_clock_state()
        self._update_time_control_label()
        self.render_clocks()
        self._toggle_clock()
        self.fen_entry.delete(0, tk.END)
        self.pgn_entry.delete(0, tk.END)
        self.game_started = True
        mode, delay = self.game_mode.get(), self._get_ai_move_delay()
        if mode == GameMode.AI_VS_AI.value:
            self.white_playing_bot_type = "op" if (
                self.ai_series_running and self.ai_series_stats['game_count'] % 2 == 1) else "main"
            self.board_orientation = "white" if self.white_playing_bot_type == "main" else "black"
            if self.ai_series_running:
                self.apply_series_opening_move()
            if not self.game_over and schedule_ai:
                self.master.after(delay, self._make_game_ai_move)
        elif mode == GameMode.HUMAN_VS_BOT.value:
            self.board_orientation = self.human_color
            if self.turn != self.human_color and schedule_ai:
                self.master.after(delay, self._make_game_ai_move)
        else:
            self.board_orientation = "white"
        self.update_ui_after_state_change()
        self._update_analysis_after_state_change()

    def _make_game_ai_move(self):
        if self.game_over:
            return
        print(f"\n--- Turn {self.history_pointer + 1} ({self.turn.capitalize()}) ---")
        self.last_move_timestamp = time.time()
        mode      = self.game_mode.get()
        bot_class = bot_name = None
        if mode == GameMode.HUMAN_VS_BOT.value:
            if self.turn != self.human_color:
                bot_class, bot_name = ChessBot, self.MAIN_AI_NAME
        elif mode == GameMode.AI_VS_AI.value:
            main_color  = "white" if self.white_playing_bot_type == "main" else "black"
            bot_class, bot_name = (ChessBot, self.MAIN_AI_NAME) if self.turn == main_color \
                               else (OpponentAI, self.OPPONENT_AI_NAME)
        if bot_class:
            self._start_ai_process(bot_class, bot_name, self.bot_depth_slider.get())

    def update_ui_after_state_change(self):
        # Preserve active drag state if user is currently holding a piece mid-turn change
        if self.dragging and self.drag_start:
            r, c = self.drag_start
            piece = self.board.grid[r][c]
            if piece and piece.color == self.turn:
                # Piece still exists and it is now our turn: update valid moves to current position
                self.valid_moves = get_all_legal_moves(self.board, self.turn)
                self.valid_moves_for_highlight = [e for s, e in self.valid_moves if s == self.selected]
            else:
                # Piece was captured by the incoming move: cancel drag
                self.dragging = False
                self.drag_start = None
                self.selected = None
                self.valid_moves = []
                self.valid_moves_for_highlight = []
                if self.drag_piece_ghost:
                    self.canvas.delete("drag_ghost")
                    self.drag_piece_ghost = None
        else:
            self.selected                  = None
            self.valid_moves               = []
            self.valid_moves_for_highlight = []

        self.custom_arrows.clear()
        self.custom_highlights.clear()
        self.update_turn_label()
        self.update_game_info_label()
        self.update_bot_labels()
        self.update_moves_list()
        self.draw_board()
        if self.dragging and self.drag_piece_ghost:
            self.canvas.tag_raise("drag_ghost")
        self.update_navigation_buttons()

    def _navigate_history(self, target_index):
        if self.game_mode.get() == GameMode.AI_VS_AI.value:
            return
        new_index = max(0, min(target_index, len(self.full_history) - 1))
        if new_index != self.history_pointer:
            self.history_pointer = new_index
            self._load_state_from_history()

    def _load_state_from_history(self):
        self._stop_ai_process()
        was_running = self._pause_clock()
        board_state, turn_state, _ = self.full_history[self.history_pointer]
        self.board       = board_state.clone()
        self.turn        = turn_state
        self.game_over   = False
        self.game_result = None
        self.position_counts.clear()
        for i in range(self.history_pointer + 1):
            b, t, _ = self.full_history[i]
            h = board_hash(b, t)
            self.position_counts[h] = self.position_counts.get(h, 0) + 1
        status, winner = get_game_state(self.board, self.turn, self.position_counts,
                                        self.history_pointer, self.MAX_GAME_MOVES)
        if status != "ongoing":
            self.game_over   = True
            self.game_result = (status, winner)
        if was_running and self.history_pointer == len(self.full_history) - 1 and not self.game_over:
            self.last_clock_tick = time.time()
            self.clock_running   = True
            self._tick_clock()
        self.update_ui_after_state_change()
        self._update_analysis_after_state_change()

    def update_game_info_label(self):
        text = {GameMode.HUMAN_VS_BOT.value:  f"Human vs {self.MAIN_AI_NAME}",
                GameMode.AI_VS_AI.value:       f"{self.MAIN_AI_NAME} vs {self.OPPONENT_AI_NAME}",
                GameMode.HUMAN_VS_HUMAN.value: "Human vs Human Analysis"}.get(self.game_mode.get())
        self.game_info_label.config(text=text)

    # ------------------------------------------------------------------ board drawing
    def create_board_image(self):
        if self.square_size <= 0:
            return None
        img = tk.PhotoImage(width=COLS * self.square_size, height=ROWS * self.square_size)
        C1, C2 = "#D2B48C", "#8B5A2B"
        for r in range(ROWS):
            for c in range(COLS):
                x1, y1 = c * self.square_size, r * self.square_size
                img.put(C1 if (r + c) % 2 == 0 else C2,
                        to=(x1, y1, x1 + self.square_size, y1 + self.square_size))
        return img

    def draw_board(self):
        if not self.board_image:
            return
            
        self.canvas.itemconfig(self.board_image_id, image=self.board_image)
        self.canvas.delete("highlight", "piece", "check_highlight", "border_highlight", "custom_highlight", "custom_arrow")
        
        mode = self.game_mode.get()
        warn = (mode == GameMode.HUMAN_VS_BOT.value and self.board_orientation != self.human_color) or \
               (mode != GameMode.HUMAN_VS_BOT.value and self.board_orientation == "black")
        if warn:
            w, h = COLS * self.square_size, ROWS * self.square_size
            self.canvas.create_rectangle(2, 2, w - 2, h - 2, outline=self.COLORS['warning'],
                                         width=4, tags="border_highlight")
                                         
        # Selected square highlight (instant visual feedback on click/drag)
        if self.selected:
            sx, sy = self.board_to_canvas(*self.selected)
            self.canvas.create_rectangle(
                sx, sy, sx + self.square_size, sy + self.square_size,
                fill="#8338ec" if (self.turn != self.human_color and self.game_mode.get() == GameMode.HUMAN_VS_BOT.value) else "#3a86ff",
                stipple="gray50", outline="", tags="highlight"
            )

        # Queued premove start and end square highlights
        if self.premove:
            for pr, pc in self.premove:
                px, py = self.board_to_canvas(pr, pc)
                self.canvas.create_rectangle(
                    px, py, px + self.square_size, py + self.square_size,
                    fill="#8338ec", stipple="gray50", outline="#c77dff", width=2, tags="highlight"
                )

        # Destination dots
        dot_color = "#8338ec" if (self.turn != self.human_color and self.game_mode.get() == GameMode.HUMAN_VS_BOT.value) else "#1E90FF"
        for r_m, c_m in getattr(self, 'valid_moves_for_highlight', []):
            x1, y1 = self.board_to_canvas(r_m, c_m)
            rd      = self.square_size // 5
            cx, cy  = x1 + self.square_size // 2, y1 + self.square_size // 2
            self.canvas.create_oval(cx - rd, cy - rd, cx + rd, cy + rd,
                                    fill=dot_color, outline="", tags="highlight")
                                    
        for r, c in self.custom_highlights:
            self._draw_highlight(r, c, tags="custom_highlight")
                                    
        for r in range(ROWS):
            for c in range(COLS):
                piece = self.board.grid[r][c]
                if not piece:
                    continue
                if isinstance(piece, King):
                    is_lost = (self.game_over and self.game_result
                               and self.game_result[0] in ("checkmate", "timeout")
                               and self.game_result[1] != piece.color)
                    clr = "darkred" if is_lost else ("red" if is_in_check(self.board, piece.color) else None)
                    if clr:
                        x1, y1 = self.board_to_canvas(r, c)
                        if is_lost:
                            self.canvas.create_rectangle(
                                x1, y1, x1 + self.square_size, y1 + self.square_size,
                                fill="#8B0000", stipple="gray50", outline="#FF0000", width=3, tags="check_highlight")
                        else:
                            self.canvas.create_rectangle(
                                x1, y1, x1 + self.square_size, y1 + self.square_size,
                                outline=clr, width=4, tags="check_highlight")
                            
                if (r, c) != self.drag_start:
                    x, y  = self.board_to_canvas(r, c)
                    cx    = x + self.square_size // 2
                    cy    = y + self.square_size // 2 + 2
                    font  = ("Arial Unicode MS", int(self.square_size * 0.67))
                    sym   = piece.symbol()
                    self.canvas.create_text(cx + 1, cy + 1, text=sym, font=font,
                                            fill="#888888", tags="piece")
                    self.canvas.create_text(cx, cy, text=sym, font=font,
                                            fill="#000000" if piece.color == "black" else "#FFFFFF",
                                            tags="piece")
                                            
        # Draw custom arrows over pieces
        for (r1, c1), (r2, c2) in self.custom_arrows:
            self._draw_arrow(r1, c1, r2, c2, tags="custom_arrow")
            
        self._position_side_labels()

    def _position_side_labels(self):
        if not hasattr(self, "canvas"):
            return
        self.board_row_frame.update_idletasks()
        cx, cy  = self.canvas.winfo_x(), self.canvas.winfo_y()
        label_w = min(max(96, int(self.square_size * 1.9)), max(1, cx - 10))
        if label_w < 20:
            self.top_bot_label.place_forget()
            self.bottom_bot_label.place_forget()
            return
        for lbl in (self.top_bot_label, self.bottom_bot_label):
            lbl.config(wraplength=max(1, label_w - 6), anchor="center", justify=tk.CENTER)
        lx = 2 + max(0, (max(3, cx - 8) - 2 - label_w) // 2)
        bh = ROWS * self.square_size
        self.top_bot_label   .place(in_=self.board_row_frame, x=lx, y=cy + 4,      width=label_w, anchor="nw")
        self.bottom_bot_label.place(in_=self.board_row_frame, x=lx, y=cy + bh - 4, width=label_w, anchor="sw")

    def draw_eval_bar(self, eval_score, depth=None):
        score = eval_score / 100.0
        w, h  = self.eval_bar_canvas.winfo_width(), self.eval_bar_canvas.winfo_height()
        if w <= 1 or h <= 1:
            return
        if w != self.last_eval_bar_w or h != self.last_eval_bar_h:
            self.eval_bar_canvas.delete("gradient")
            for x_px in range(w):
                i = int(255 * x_px / (w - 1))
                self.eval_bar_canvas.create_line(x_px, 0, x_px, h,
                                                 fill=f"#{i:02x}{i:02x}{i:02x}", tags="gradient")
            self.last_eval_bar_w, self.last_eval_bar_h = w, h
        self.eval_bar_canvas.delete("marker")
        mx = int(((max(-1.0, min(1.0, math.tanh(score / 10.0))) + 1) / 2.0) * w)
        self.eval_bar_canvas.create_line(mx,   0, mx,   h, fill="#FF0000", width=3, tags="marker")
        self.eval_bar_canvas.create_line(w//2, 0, w//2, h, fill="#00FF00", width=2, tags="marker")
        sfx = f" (D{depth})" if depth is not None else ""
        self.eval_score_label.config(text=f"Even{sfx}" if abs(score) < 0.05
                                     else f"{'+' if score > 0 else ''}{score:.2f}{sfx}")

    # ------------------------------------------------------------------ comm queue / PV
    def process_comm_queue(self):
        if self._shutting_down:
            return
        try:
            while not self.comm_queue.empty():
                msg  = self.comm_queue.get_nowait()
                kind = msg[0]
                msg_task_id = self._message_task_id(msg)
                if msg_task_id is not None and msg_task_id != self.current_task_id:
                    continue
                if kind == 'log':
                    print(msg[1])
                    tt_m = re.search(r'TT=(\d+/1000)', msg[1])
                    if tt_m and self.show_tt_fullness_var.get():
                        self.tt_fullness_label.config(text=f"TT Occupancy: {tt_m.group(1)}")
                    else:
                        self.tt_fullness_label.config(text="")

                    if self.auto_save_stats_var.get() and self.game_mode.get() == GameMode.AI_VS_AI.value:
                        m = re.search(
                            r'>\s*(.*?)\s*\(D(\d+|TB)\):.*?Eval[=:]\s*([+-]?[\d.]+).*?'
                            r'Nodes(?:Total)?[=:]\s*(\d+).*?KNPS[=:]\s*([\d.]+).*?Time[=:]\s*([\d.]+)s',
                            msg[1])
                        if m:
                            self._pending_move_stat[m.group(1)] = {
                                'depth': m.group(2),
                                'eval':  float(m.group(3)),
                                'nodes': int(m.group(4)),
                                'knps':  float(m.group(5)),
                                'time':  float(m.group(6)),
                            }
                elif kind == 'eval':
                    self.last_eval_score, self.last_eval_depth = msg[1], msg[2]
                    if self._analysis_output_enabled():
                        self.draw_eval_bar(msg[1], msg[2])
                elif kind == 'pv':
                    self.last_pv_message = msg
                    if self._analysis_output_enabled():
                        self._render_pv()
                elif kind == 'move':
                    # Only accept the move if it matches the current generation ID
                    if self.active_worker_name is not None and msg_task_id == self.current_task_id:
                        if self.auto_save_stats_var.get() and self.game_mode.get() == GameMode.AI_VS_AI.value:
                            for bot, stat in self._pending_move_stat.items():
                                self.move_stats.setdefault(bot, []).append(stat)
                            self._pending_move_stat.clear()
                        self.active_worker_name = None
                        self.analysis_thinking  = False
                        self._execute_ai_move(msg[1])
        except Exception:
            pass
        finally:
            if not self._shutting_down:
                try:
                    self.master.after(20, self.process_comm_queue)
                except Exception:
                    pass

    def _render_pv(self):
        if not self._analysis_output_enabled() or \
                not getattr(self, 'show_pv_var', None) or not self.show_pv_var.get():
            self.pv_text.pack_forget()
            return
        self.pv_text.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=10)
        msg = getattr(self, 'last_pv_message', None)
        if not msg:
            return
        score, depth, pv_san_list, pv_raw = msg[1], msg[2], msg[3], msg[4]
        self.current_pv_raw = pv_raw
        self.current_pv_san = pv_san_list
        if score > 990000:
            sd = f"+M{(1000000 - score + 1) // 2}"
        elif score < -990000:
            sd = f"-M{(score + 1000000 + 1) // 2}"
        else:
            sd = f"{score / 100:+.2f}"
        self.pv_text.config(state=tk.NORMAL)
        self.pv_text.delete(1.0, tk.END)
        self.pv_text.insert(tk.END, f"[{sd}] (D{depth}):\n")
        for i, (san, _) in enumerate(zip(pv_san_list, pv_raw)):
            tag = f"pv_move_{i}"
            self.pv_text.insert(tk.END, self._format_san_display(san) + " ", tag)
        self.pv_text.config(state=tk.DISABLED)

    # ------------------------------------------------------------------ AI process
    def _start_ai_process(self, bot_class, bot_name, search_depth):
        """Submit a task to the appropriate persistent worker."""
        if self.active_worker_name is not None:
            return   

        time_left = (self.white_time if self.turn == 'white' else self.black_time) \
                    if self.use_clock_var.get() else None
        inc = self.increment if self.use_clock_var.get() else None

        self.current_task_id += 1  # Increment task generation

        task = {
            'board':            self.board.clone(),
            'color':            self.turn,
            'position_counts':  self.position_counts.copy(),
            'bot_name':         bot_name,
            'ply_count':        self.history_pointer,
            'game_mode':        self.game_mode.get(),
            'search_depth':     search_depth,
            'time_left':        time_left,
            'increment':        inc,
            'use_opening_book': self.use_opening_book_var.get(),
            'show_tt_fullness': self.show_tt_fullness_var.get(),
            'clear_hash':       getattr(self, '_force_clear_hash', False),
            'task_id':          self.current_task_id
        }
        self._force_clear_hash = False  # Reset flag after consuming

        self.analysis_thinking = (bot_name == self.ANALYSIS_AI_NAME)

        if bot_class is ChessBot:
            self.active_worker_name = 'main'
            self.main_work_queue.put(task)
        else:
            self.active_worker_name = 'op'
            self.op_work_queue.put(task)

        if not self.analysis_thinking:
            self.set_interactivity(False)
        self.update_bot_labels()

    def _stop_ai_process(self, drain_queue=True, invalidate_task=True):
        """Cancel the current task (worker stays alive)."""
        if self.active_worker_name == 'main':
            self.main_cancel_event.set()
        elif self.active_worker_name == 'op':
            self.op_cancel_event.set()

        if invalidate_task:
            self.current_task_id += 1

        self.active_worker_name = None
        self.analysis_thinking  = False

        # Drain any messages already in the queue from the cancelled task.
        if drain_queue:
            while not self.comm_queue.empty():
                try:
                    self.comm_queue.get_nowait()
                except Exception:
                    break

        if not self._shutting_down and self.game_mode.get() == GameMode.HUMAN_VS_HUMAN.value and not self.analysis_mode_var.get():
            self.last_eval_score, self.last_eval_depth = 0.0, None
            self.draw_eval_bar(0)
            self.eval_score_label.config(text="Even")

        if not self._shutting_down:
            self.set_interactivity(True)
            self.update_bot_labels()

    def _update_analysis_after_state_change(self):
        self._sync_analysis_output_visibility()
        if not self.analysis_mode_var.get():
            if self.analysis_thinking:
                self._stop_ai_process()
            self._clear_analysis_output()
            return

        if self.game_mode.get() == GameMode.HUMAN_VS_HUMAN.value:
            self._stop_ai_process()

        if self.game_mode.get() == GameMode.HUMAN_VS_HUMAN.value and not self.game_over:
            fullmove = (self.history_pointer + 1) // 2 + 1
            print(f"\n--- Analysis: Move {fullmove}, Ply {self.history_pointer}, {self.turn.capitalize()} ---")
            self.master.after(50, lambda: self._start_ai_process(ChessBot, self.ANALYSIS_AI_NAME, 99))

    # ------------------------------------------------------------------ misc helpers
    def _update_time_control_label(self):
        t = int(self.time_control_seconds.get())
        self.time_control_label.config(text=f"Time Control: {t // 60:02d}:{t % 60:02d}")

    def _toggle_clock(self):
        if self.use_clock_var.get():
            self.clock_frame.pack(after=self.turn_label, fill=tk.X, pady=(5, 5))
            self.time_control_frame.pack(after=self.clock_frame, fill=tk.X, pady=(5, 5))
            self._update_time_control_label()
            self.render_clocks()
            if self.game_started and not self.game_over and self.history_pointer > 0:
                self._start_clock()
        else:
            self.clock_frame.pack_forget()
            self.time_control_frame.pack_forget()
            self._pause_clock()
            self.last_clock_tick = None

    def _get_ai_move_delay(self):
        return 0 if self.use_clock_var.get() else (4 if self.instant_move.get() else 20)

    def render_clocks(self):
        if not self.use_clock_var.get():
            return

        def fmt(t):
            t = max(0, t)
            return f"{int(t) // 60:02d}:{int(t) % 60:02d}.{int((t - int(t)) * 10)}"

        self.white_clock_lbl.config(text=f"W: {fmt(self.white_time)}")
        self.black_clock_lbl.config(text=f"B: {fmt(self.black_time)}")
        if not self.game_over:
            self.white_clock_lbl.config(
                bg=self.COLORS['accent']     if self.turn == 'white' else self.COLORS['bg_light'],
                fg=self.COLORS['text_light'] if self.turn == 'white' else self.COLORS['text_dark'])
            self.black_clock_lbl.config(
                bg=self.COLORS['accent']     if self.turn == 'black' else self.COLORS['bg_medium'],
                fg=self.COLORS['text_light'] if self.turn == 'black' else self.COLORS['text_dark'])
        else:
            is_timeout = (self.game_result and self.game_result[0] == "timeout")
            timed_out_color = ('white' if self.white_time <= 0 else 'black') if is_timeout else None
            self.white_clock_lbl.config(
                bg="#8B0000" if timed_out_color == 'white' else self.COLORS['bg_light'],
                fg="#FFFFFF" if timed_out_color == 'white' else self.COLORS['text_dark'])
            self.black_clock_lbl.config(
                bg="#8B0000" if timed_out_color == 'black' else self.COLORS['bg_medium'],
                fg="#FFFFFF" if timed_out_color == 'black' else self.COLORS['text_dark'])

    def _tick_clock(self):
        if not self.use_clock_var.get() or not self.clock_running or self.game_over:
            self.clock_running = False
            return
        now              = time.time()
        elapsed          = now - self.last_clock_tick
        self.last_clock_tick = now
        if self.turn == 'white':
            self.white_time -= elapsed
        else:
            self.black_time -= elapsed
        timed_out = (self.turn == 'white' and self.white_time <= 0) or \
                    (self.turn == 'black' and self.black_time  <= 0)
        if timed_out:
            if self.turn == 'white': self.white_time = 0
            else:                    self.black_time  = 0
            self.handle_timeout(self.turn)
            return
        self.render_clocks()
        self.master.after(25, self._tick_clock)

    def handle_timeout(self, color):
        self.game_over     = True
        self.clock_running = False
        self.game_result   = ('timeout', 'black' if color == 'white' else 'white')
        self.update_ui_after_state_change()
        print("Game Over! Result: timeout")
        self._stop_ai_process()
        if self.game_mode.get() == GameMode.AI_VS_AI.value and self.ai_series_running:
            self.process_ai_series_result()

    def update_turn_label(self):
        if self.game_result:
            res, winner = self.game_result
            if res == "timeout":
                loser = "White" if winner == "black" else "Black"
                self.turn_label.config(
                    text=f"⌛ OUT OF TIME: {loser.upper()} LOST",
                    background="#8B0000", foreground="#FFFFFF")
            elif res == "checkmate":
                self.turn_label.config(
                    text=f"★ CHECKMATE: {winner.upper()} WINS",
                    background="#8B0000", foreground="#FFFFFF")
            else:
                res_text = res.upper().replace('_', ' ')
                self.turn_label.config(
                    text=f"GAME OVER: {res_text}",
                    background=self.COLORS['bg_light'], foreground=self.COLORS['text_light'])
        else:
            self.turn_label.config(
                text=f"TURN: {self.turn.upper()}",
                background=self.COLORS['bg_light'], foreground=self.COLORS['text_light'])

    def update_bot_labels(self):
        mode = self.game_mode.get()
        if mode == GameMode.AI_VS_AI.value:
            wl = self.MAIN_AI_NAME     if self.white_playing_bot_type == "main" else self.OPPONENT_AI_NAME
            bl = self.OPPONENT_AI_NAME if self.white_playing_bot_type == "main" else self.MAIN_AI_NAME
        elif mode == GameMode.HUMAN_VS_BOT.value:
            wl = "Human" if self.human_color == "white" else self.MAIN_AI_NAME
            bl = "Human" if self.human_color == "black" else self.MAIN_AI_NAME
        else:
            wl, bl = "White", "Black"
        if self.turn == "white":
            wl += "\n(to move)"
        else:
            bl += "\n(to move)"
        bottom, top = (wl, bl) if self.board_orientation == 'white' else (bl, wl)
        self.bottom_bot_label.config(text=bottom)
        self.top_bot_label   .config(text=top)
        self._position_side_labels()

    def set_interactivity(self, on):
        self.is_interactive = on

    def is_ai_thinking(self):
        return self.active_worker_name is not None

    def switch_turn(self):
        if not self.game_over:
            self.turn = "black" if self.turn == "white" else "white"

    def board_to_canvas(self, r, c):
        if self.board_orientation == "black":
            return (COLS - 1 - c) * self.square_size, (ROWS - 1 - r) * self.square_size
        return c * self.square_size, r * self.square_size

    def canvas_to_board(self, x, y):
        if self.board_orientation == "black":
            c = (COLS - 1) - x // self.square_size
            r = (ROWS - 1) - y // self.square_size
        else:
            c = x // self.square_size
            r = y // self.square_size
        return (r, c) if 0 <= r < ROWS and 0 <= c < COLS else (-1, -1)

    def show_readme_popup(self):
        """Creates a dark-themed scrollable popup rendering Zreadme.txt."""
        popup = tk.Toplevel(self.master)
        popup.title("Standard Chess - Rules & Reference")
        popup.geometry("800x700")
        popup.configure(bg=self.COLORS['bg_dark'])
        popup.transient(self.master)
        popup.grab_set()

        # Center popup on master window
        popup.update_idletasks()
        mx = self.master.winfo_x() + (self.master.winfo_width() - 800) // 2
        my = self.master.winfo_y() + (self.master.winfo_height() - 700) // 2
        popup.geometry(f"800x700+{mx}+{my}")

        # Scrollable Text Container Frame
        text_frame = tk.Frame(popup, bg=self.COLORS['bg_medium'])
        text_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=(20, 15))

        scrollbar = ttk.Scrollbar(text_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        text = tk.Text(text_frame, wrap=tk.WORD, yscrollcommand=scrollbar.set,
                       bg=self.COLORS['bg_medium'], fg=self.COLORS['text_light'],
                       insertbackground=self.COLORS['text_light'], relief="flat", bd=0,
                       font=("Helvetica", 11), padx=15, pady=15)
        text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=text.yview)

        # Custom Styling Tags for a styled markdown look
        text.tag_config("title", foreground=self.COLORS['accent'], font=("Helvetica", 18, "bold"), spacing1=10, spacing2=5)
        text.tag_config("h2", foreground=self.COLORS['text_light'], font=("Helvetica", 14, "bold"), spacing1=15, spacing2=5)
        text.tag_config("h3", foreground=self.COLORS['text_light'], font=("Helvetica", 12, "bold"), spacing1=10, spacing2=5)
        text.tag_config("code", font=("Courier", 10), background=self.COLORS['bg_light'], foreground="#00ffcc")
        text.tag_config("bold", font=("Helvetica", 11, "bold"))
        text.tag_config("normal", font=("Helvetica", 11), spacing3=4)

        # Read the file
        try:
            with open("Zreadme.txt", "r", encoding="utf-8") as f:
                readme_text = f.read()
        except FileNotFoundError:
            readme_text = "# Error\nCould not find `Zreadme.txt` in the current directory."

        # Parse and insert text
        lines = readme_text.split('\n')
        in_code_block = False

        for line in lines:
            if line.startswith("```"):
                in_code_block = not in_code_block
                text.insert(tk.END, "\n")
                continue
            
            if in_code_block:
                text.insert(tk.END, line + "\n", "code")
                continue

            if line.startswith("# "):
                text.insert(tk.END, line[2:] + "\n", "title")
            elif line.startswith("## "):
                text.insert(tk.END, line[3:] + "\n", "h2")
            elif line.startswith("### "):
                text.insert(tk.END, line[4:] + "\n", "h3")
            elif line.startswith("---"):
                text.insert(tk.END, "─" * 60 + "\n", "normal")
            else:
                # Parse inline bold and code tags within standard sentences
                parts = re.split(r'(`[^`]+`)', line)
                for part in parts:
                    if part.startswith('`') and part.endswith('`'):
                        text.insert(tk.END, part[1:-1], "code")
                    else:
                        sub_parts = re.split(r'(\*\*[^*]+\*\*)', part)
                        for sub_part in sub_parts:
                            if sub_part.startswith('**') and sub_part.endswith('**'):
                                text.insert(tk.END, sub_part[2:-2], "bold")
                            else:
                                text.insert(tk.END, sub_part, "normal")
                text.insert(tk.END, "\n")

        text.config(state=tk.DISABLED)

        # Got It button
        close_btn = ttk.Button(popup, text="Close", command=popup.destroy, style='Control.TButton')
        close_btn.pack(pady=(0, 15))

        # Bind Escape to close
        popup.bind("<Escape>", lambda e: popup.destroy())

    def undo_move(self):   self._navigate_history(self.history_pointer - 1)
    def redo_move(self):   self._navigate_history(self.history_pointer + 1)
    def go_to_start(self): self._navigate_history(0)
    def go_to_end(self):   self._navigate_history(len(self.full_history) - 1)

    def update_navigation_buttons(self):
        if self.game_mode.get() == GameMode.AI_VS_AI.value:
            for b in (self.start_button, self.undo_button, self.redo_button, self.end_button):
                b.config(state=tk.DISABLED)
            return
        can_back = self.history_pointer > 0
        can_fwd  = self.history_pointer < len(self.full_history) - 1
        self.start_button.config(state=tk.NORMAL if can_back else tk.DISABLED)
        self.undo_button .config(state=tk.NORMAL if can_back else tk.DISABLED)
        self.redo_button .config(state=tk.NORMAL if can_fwd  else tk.DISABLED)
        self.end_button  .config(state=tk.NORMAL if can_fwd  else tk.DISABLED)

    # ------------------------------------------------------------------ AI series
    def process_ai_series_result(self):
        self.ai_series_stats['game_count'] += 1
        _, wc = self.game_result
        if wc:
            main_color = 'white' if self.white_playing_bot_type == 'main' else 'black'
            self.ai_series_stats['my_ai_wins' if wc == main_color else 'op_ai_wins'] += 1
        else:
            self.ai_series_stats['draws'] += 1
        self.update_scoreboard()
        if self.auto_save_stats_var.get():
            self.save_depth_stats_to_file()
        if self.ai_series_running and self.ai_series_stats['game_count'] < self.AI_SERIES_GAMES:
            self.master.after(1000, self.reset_game)
        else:
            self.ai_series_running = False
            self.turn_label.config(text="AI SERIES COMPLETE!")

    def start_ai_series(self):
        self._stop_ai_process()
        self.game_mode.set(GameMode.AI_VS_AI.value)
        self.ai_series_stats          = {'game_count': 0, 'my_ai_wins': 0, 'op_ai_wins': 0, 'draws': 0}
        self.move_stats               = {}
        self._pending_move_stat       = {}
        self.ai_series_running        = True
        self.current_opening_sequence = []
        self.update_scoreboard()
        self.reset_game()

    def apply_series_opening_move(self):
        if self.ai_series_stats['game_count'] % 2 == 0:
            print("\n--- Generating new 2-ply opening sequence ---")
            self.current_opening_sequence = generate_series_opening_sequence(self.board, num_plies=2)
        self._pause_clock()
        for move in self.current_opening_sequence:
            child = self.board.clone()
            child.make_move(move[0], move[1])
            print(f"Opening: {format_move_san(self.board, child, move)}")
            self.board.make_move(move[0], move[1])
            self.execute_move_and_check_state(self.turn, move)
            if self.game_over:
                break
        self.last_clock_tick = time.time()
        self.clock_running   = False

    def update_scoreboard(self):
        if self.game_mode.get() == GameMode.AI_VS_AI.value and self.ai_series_running:
            s = self.ai_series_stats
            self.scoreboard_label.config(text=(
                f"{self.MAIN_AI_NAME} vs {self.OPPONENT_AI_NAME} "
                f"({s['game_count']}/{self.AI_SERIES_GAMES} games)\n"
                f"  {self.MAIN_AI_NAME}: {s['my_ai_wins']}  "
                f"{self.OPPONENT_AI_NAME}: {s['op_ai_wins']}  Draws: {s['draws']}"))
        else:
            self.scoreboard_label.config(text="")

    def save_depth_stats_to_file(self):
        import os
        out_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "AI_Series_Results.txt")
        write_series_stats_file(
            out_path=out_path,
            move_stats=self.move_stats,
            series_stats=self.ai_series_stats,
            main_name=self.MAIN_AI_NAME,
            op_name=self.OPPONENT_AI_NAME,
            use_clock=self.use_clock_var.get(),
            time_control_sec=self.time_control_seconds.get(),
            increment=self.increment,
            fixed_depth=self.bot_depth_slider.get(),
            total_series_games=self.AI_SERIES_GAMES,
        )

    # ------------------------------------------------------------------ Delegated Events
    def _on_pv_text_motion(self, event):
        index = self.pv_text.index(f"@{event.x},{event.y}")
        tags = self.pv_text.tag_names(index)
        pv_tag = next((t for t in tags if t.startswith("pv_move_")), None)
        
        if pv_tag != self.hovered_pv_tag:
            if self.hovered_pv_tag:
                self.on_pv_hover_leave(None, self.hovered_pv_tag)
            self.hovered_pv_tag = pv_tag
            if pv_tag:
                idx = int(pv_tag.split("_")[2])
                self.on_pv_hover_enter(event, idx, pv_tag)

    def _on_pv_text_leave(self, event):
        if self.hovered_pv_tag:
            self.on_pv_hover_leave(None, self.hovered_pv_tag)
            self.hovered_pv_tag = None

    def _on_moves_text_click(self, event):
        if self.game_mode.get() == GameMode.AI_VS_AI.value: return
        index = self.moves_text.index(f"@{event.x},{event.y}")
        for tag in self.moves_text.tag_names(index):
            if tag.startswith("ply_"):
                self._navigate_history(int(tag.split("_")[1]))
                break

    def _on_moves_text_motion(self, event):
        index = self.moves_text.index(f"@{event.x},{event.y}")
        if any(t.startswith("ply_") for t in self.moves_text.tag_names(index)):
            self.moves_text.config(cursor="hand2")
        else:
            self.moves_text.config(cursor="arrow")

    # ------------------------------------------------------------------ PV hover mini-board
    def on_pv_hover_enter(self, event, move_idx, tag):
        self.pv_text.tag_config(tag, background=self.COLORS['accent'],
                                foreground=self.COLORS['text_light'])
        if getattr(self, 'pv_tooltip', None):
            self.pv_tooltip.destroy()
        self.pv_tooltip = tk.Toplevel(self.master)
        self.pv_tooltip.wm_overrideredirect(True)
        self.pv_tooltip.wm_geometry(f"+{event.x_root + 15}+{event.y_root - ROWS * 25 - 20}")
        self.tt_sq_size = 25
        self.tt_canvas  = tk.Canvas(self.pv_tooltip,
                                    width=COLS * self.tt_sq_size, height=ROWS * self.tt_sq_size,
                                    bg=self.COLORS['bg_medium'], highlightthickness=2,
                                    highlightbackground=self.COLORS['accent'])
        self.tt_canvas.pack()
        tt_sim = self.board.clone()
        for i in range(move_idx + 1):
            tt_sim.make_move(*self.current_pv_raw[i])
        self._draw_tt_board_static(tt_sim, self.current_pv_raw[move_idx])

    def on_pv_hover_leave(self, event, tag):
        self.pv_text.tag_config(tag, background="", foreground="")
        if getattr(self, 'pv_tooltip', None):
            self.pv_tooltip.destroy()
            self.pv_tooltip = None

    def _draw_tt_board_static(self, sim_board, last_move):
        self.tt_canvas.delete("all")
        sq     = self.tt_sq_size
        C1, C2 = "#D2B48C", "#8B5A2B"
        flipped_last_move = None
        if last_move:
            if self.board_orientation == "black":
                flipped_last_move = [((ROWS - 1 - r), (COLS - 1 - c)) for r, c in last_move]
            else:
                flipped_last_move = last_move
        
        for r in range(ROWS):
            for c in range(COLS):
                dr = (ROWS - 1 - r) if self.board_orientation == "black" else r
                dc = (COLS - 1 - c) if self.board_orientation == "black" else c
                x1, y1 = dc * sq, dr * sq
                self.tt_canvas.create_rectangle(x1, y1, x1 + sq, y1 + sq,
                                                fill=C1 if (r + c) % 2 == 0 else C2, outline="")
                if flipped_last_move and (dr, dc) in flipped_last_move:
                    self.tt_canvas.create_rectangle(x1, y1, x1 + sq, y1 + sq,
                                                    fill="#F0E68C", stipple="gray50", outline="")
                piece = sim_board.grid[r][c]
                if piece:
                    font = ("Arial Unicode MS", int(sq * 0.7))
                    sym  = piece.symbol()
                    self.tt_canvas.create_text(x1 + sq // 2 + 1, y1 + sq // 2 + 2,
                                               text=sym, font=font, fill="#888888")
                    self.tt_canvas.create_text(x1 + sq // 2, y1 + sq // 2 + 1,
                                               text=sym, font=font,
                                               fill="#000" if piece.color == "black" else "#FFF")


if __name__ == "__main__":
    mp.freeze_support()
    root = tk.Tk()
    app  = EnhancedChessApp(root)
    root.mainloop()