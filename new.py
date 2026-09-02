# ChessUI.py (v2.1 Tuple of 2 used)

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
from MoveChecker import launch_move_checker_dialog
from enum import Enum
import multiprocessing as mp

class GameMode(Enum):
    HUMAN_VS_BOT   = "bot"
    HUMAN_VS_HUMAN = "human"
    AI_VS_AI       = "ai_vs_ai"

_FEN_CHAR_TO_CLASS = {'p': Pawn, 'n': Knight, 'b': Bishop, 'r': Rook, 'q': Queen, 'k': King}

class EnhancedChessApp:
    MAIN_AI_NAME     = "AI Bot"
    OPPONENT_AI_NAME = "OP Bot"
    ANALYSIS_AI_NAME = "Analysis"
    slidermaxvalue   = 12
    MAX_GAME_MOVES   = 200 # Kept for legacy compatibility, but logic allows None
    AI_SERIES_GAMES  = 300

    def __init__(self, master):
        self.master = master
        self.master.title("Standard Chess")
        random.seed()

        self.comm_queue = mp.Queue()

        self.current_task_id   = 0
        self.main_work_queue   = mp.Queue()
        self.op_work_queue     = mp.Queue()
        self.main_cancel_event = mp.Event()
        self.op_cancel_event   = mp.Event()
        self.active_worker_name = None   
        self.analysis_thinking  = False
        self.main_worker        = None   
        self.op_worker          = None
        self._shutting_down     = False

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

    def _format_san_display(self, s):
        return s if (self.long_notation_var.get() or not s) else strip_casualties(s)

    def _on_notation_toggle(self):
        self.update_moves_list()
        self._render_pv()

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

    def build_ui(self):
        sw, sh = self.master.winfo_screenwidth(), self.master.winfo_screenheight()
        self.master.geometry(f"{sw}x{sh}+0+0")
        try:
            self.master.state('zoomed')
        except tk.TclError:
            try:
                self.master.attributes('-zoomed', True)
            except tk.TclError:
                pass

        self.main_frame = ttk.Frame(self.master, style='Left.TFrame')
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

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

        self.right_panel = ttk.Frame(self.main_frame, style='Left.TFrame')
        self.right_panel.pack(side=tk.RIGHT, fill=tk.Y, padx=(10, 0))
        self.right_panel.pack_propagate(False)
        self._build_right_sidebar_widgets(self.right_panel)

        self.main_frame.bind("<Configure>",   self.handle_main_resize)
        self.center_panel.bind("<Configure>", self.handle_board_resize)
        
        self.info_btn = tk.Button(
            self.master, text="ⓘ", font=("Helvetica", 13, "bold"),
            bg=self.COLORS['bg_dark'], fg=self.COLORS['text_dark'],
            activebackground=self.COLORS['bg_dark'], activeforeground=self.COLORS['text_light'],
            bd=0, relief="flat", cursor="hand2", command=self.show_readme_popup
        )
        self.info_btn.place(in_=self.master, relx=1.0, y=12, x=-20, anchor="ne")
        
        self.canvas.bind("<Button-1>",        self.on_drag_start)
        self.canvas.bind("<B1-Motion>",       self.on_drag_motion)
        self.canvas.bind("<ButtonRelease-1>", self.on_drag_end)
        
        self.canvas.bind("<Button-3>",        self.on_right_click_start)
        self.canvas.bind("<B3-Motion>",       self.on_right_click_drag)
        self.canvas.bind("<ButtonRelease-3>", self.on_right_click_end)
        
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
        elif mode == GameMode.HUMAN_VS_HUMAN.value:
            self.board_orientation = "white"
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

    def get_current_fen(self):
        fullmove = (self.history_pointer // 2) + 1 if self.history_pointer >= 0 else 1
        return board_to_fen(self.board, self.turn, fullmove=fullmove)

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

        self.board.castling_rights = 0
        if len(parts) > 2:
            if parts[2] != '-':
                if 'K' in parts[2]: self.board.castling_rights |= CASTLE_WK
                if 'Q' in parts[2]: self.board.castling_rights |= CASTLE_WQ
                if 'k' in parts[2]: self.board.castling_rights |= CASTLE_BK
                if 'q' in parts[2]: self.board.castling_rights |= CASTLE_BQ
        else:
            # Only the standard start position defaults to KQkq if flags were omitted
            if parts[0] == "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR":
                self.board.castling_rights = 15

        # Parse En Passant
        self.board.ep_square = None
        if len(parts) > 3 and parts[3] != '-':
            ep_str = parts[3].lower()
            valid_ep_rank = '6' if self.turn == 'white' else '3'
            if len(ep_str) == 2 and ep_str[0] in 'abcdefgh' and ep_str[1] == valid_ep_rank:
                self.board.ep_square = (8 - int(ep_str[1]), ord(ep_str[0]) - ord('a'))

        self.board.halfmove_clock = int(parts[4]) if len(parts) > 4 and parts[4].isdigit() else 0

        if not self.board.white_king_pos or not self.board.black_king_pos:
            messagebox.showerror("Invalid FEN", "Illegal Position: Both Kings must be present on the board.")
            self.reset_game(schedule_ai=False)
            return

        passive_color = "black" if self.turn == "white" else "white"
        if is_in_check(self.board, passive_color):
            messagebox.showerror("Invalid FEN", f"Illegal Position: The side not to move ({passive_color}) is already in check.")
            self.reset_game(schedule_ai=False)
            return

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

            if not self.game_over and self.game_mode.get() == GameMode.HUMAN_VS_BOT.value and self.turn == self.human_color:
                if self.premove:
                    pm = self.premove
                    self.premove = None
                    start_pos, end_pos = pm[0], pm[1]
                    promo_cls = pm[2] if len(pm) > 2 else Queen
                    legal_moves = get_all_legal_moves(self.board, self.turn)
                    if any(m[0] == start_pos and m[1] == end_pos for m in legal_moves):
                        self._apply_move_with_promotion(start_pos, end_pos, promo_cls)
                        self.execute_move_and_check_state(self.turn, (start_pos, end_pos, promo_cls))
                        if not self.game_over and self.turn != self.human_color:
                            self.set_interactivity(False)
                            self.master.after(self._get_ai_move_delay(), self._make_game_ai_move)
                    else:
                        self.draw_board()

            if not self.game_over and self.game_mode.get() == GameMode.AI_VS_AI.value:
                self.master.after(self._get_ai_move_delay(), self._make_game_ai_move)
        else:
            print("AI reported no valid move.")
            
        self._stop_ai_process()
        self.update_bot_labels()
        self.set_interactivity(True)

    def _get_premove_destinations(self, piece, start_pos):
        sr, sc = start_pos
        sq = sr * 8 + sc
        pz = piece.z_idx
        dests = []

        if pz == 0:
            p_dir = -1 if piece.color == 'white' else 1
            if 0 <= sr + p_dir < 8:
                dests.append((sr + p_dir, sc))
            if sr == piece.starting_row and 0 <= sr + 2 * p_dir < 8:
                dests.append((sr + 2 * p_dir, sc))
            for dc in (-1, 1):
                if 0 <= sr + p_dir < 8 and 0 <= sc + dc < 8:
                    dests.append((sr + p_dir, sc + dc))

        elif pz == 1:
            dests.extend(KNIGHT_ATTACKS_FROM[(sr, sc)])

        elif pz == 2:
            for ray in RAYS_DIAGONAL[sq]:
                dests.extend(ray)

        elif pz == 3:
            for ray in RAYS_ORTHOGONAL[sq]:
                dests.extend(ray)

        elif pz == 4:
            for ray in RAYS_ALL[sq]:
                dests.extend(ray)

        elif pz == 5:
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

        mode = self.game_mode.get()
        if mode == GameMode.AI_VS_AI.value:
            if cleared_custom: self.draw_board()
            return

        r, c = self.canvas_to_board(event.x, event.y)
        if r == -1 or not self.board.grid[r][c]:
            if cleared_custom: self.draw_board()
            return

        piece = self.board.grid[r][c]

        is_premove = (mode == GameMode.HUMAN_VS_BOT.value and self.turn != self.human_color) or \
                     (self.is_ai_thinking() and not self.analysis_thinking)

        if is_premove:
            if piece.color != self.human_color:
                if cleared_custom: self.draw_board()
                return
            self.selected = (r, c)
            self.drag_start = (r, c)
            self.dragging = True
            all_pseudo = get_all_pseudo_legal_moves(self.board, self.human_color)
            self.valid_moves_for_highlight = [m[1] for m in all_pseudo if m[0] == self.selected]
            dests = self._get_premove_destinations(piece, (r, c))
            self.valid_moves = [(self.selected, d, None) for d in dests]
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
        self.valid_moves_for_highlight = [m[1] for m in self.valid_moves if m[0] == self.selected]
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
            if any(m[0] == start_pos and m[1] == end_pos for m in self.valid_moves):
                promo_cls = self.check_and_prompt_promotion(start_pos, end_pos)
                if promo_cls is not False:
                    self.premove = (start_pos, end_pos, promo_cls)
            self.drag_start = None
            self.selected = None
            self.valid_moves = []
            self.valid_moves_for_highlight = []
            self.draw_board()
            return

        current_legal = get_all_legal_moves(self.board, self.turn)
        matched_move = next((m for m in current_legal if m[0] == start_pos and m[1] == end_pos), None)
        if matched_move is not None:
            promo_cls = self.check_and_prompt_promotion(start_pos, end_pos)
            if promo_cls is False:
                self.drag_start = None
                self.selected = None
                self.valid_moves = []
                self.valid_moves_for_highlight = []
                self.draw_board()
                return

            actual_promo = promo_cls if promo_cls is not None else matched_move[2]
            move_tuple = (start_pos, end_pos, actual_promo)
            self._apply_move_with_promotion(start_pos, end_pos, actual_promo)
            self.execute_move_and_check_state(self.turn, move_tuple)
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

    def check_and_prompt_promotion(self, start_pos, end_pos):
        piece = self.board.grid[start_pos[0]][start_pos[1]]
        if isinstance(piece, Pawn):
            target_rank = 0 if piece.color == "white" else 7
            if end_pos[0] == target_rank:
                return self._show_promotion_dialog(piece.color)
        return None

    def _show_promotion_dialog(self, color):
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
        try:
            self.board.make_move(start_pos, end_pos, promo_cls)
        except TypeError:
            self.board.make_move(start_pos, end_pos)
            if promo_cls:
                self.board.grid[end_pos[0]][end_pos[1]] = promo_cls(self.turn)

    def run_move_checker(self):
        depth = int(self.bot_depth_slider.get())
        # Compare the actual board arrangement, not just castling/turn flags.
        # The old check falsely matched Kiwipete (KQkq, white to move, no ep).
        is_start_pos = (self.get_current_fen().split()[0] ==
                        "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR")
        
        launch_move_checker_dialog(
            self.master, 
            self.board.clone(), 
            self.turn, 
            depth, 
            self.COLORS, 
            is_start_pos
        )

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
        if self.dragging and self.drag_start:
            r, c = self.drag_start
            piece = self.board.grid[r][c]
            if piece and piece.color == self.turn:
                self.valid_moves = get_all_legal_moves(self.board, self.turn)
                self.valid_moves_for_highlight = [m[1] for m in self.valid_moves if m[0] == self.selected]
            else:
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
                                         
        if self.selected:
            sx, sy = self.board_to_canvas(*self.selected)
            self.canvas.create_rectangle(
                sx, sy, sx + self.square_size, sy + self.square_size,
                fill="#8338ec" if (self.turn != self.human_color and self.game_mode.get() == GameMode.HUMAN_VS_BOT.value) else "#3a86ff",
                stipple="gray50", outline="", tags="highlight"
            )

        # Queued premove start and end square highlights
        if self.premove:
            for pr, pc in (self.premove[0], self.premove[1]):
                px, py = self.board_to_canvas(pr, pc)
                self.canvas.create_rectangle(
                    px, py, px + self.square_size, py + self.square_size,
                    fill="#8338ec", stipple="gray50", outline="#c77dff", width=2, tags="highlight"
                )

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
        self.eval_score_label.config(text=f"Even{sfx}" if abs(score) < 0.005
                                     else f"{'+' if score > 0 else ''}{score:.2f}{sfx}")

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

    def _start_ai_process(self, bot_class, bot_name, search_depth):
        if self.active_worker_name is not None:
            return   

        is_analysis = (bot_name == self.ANALYSIS_AI_NAME)
        time_left = ((self.white_time if self.turn == 'white' else self.black_time) \
                    if self.use_clock_var.get() else None) if not is_analysis else None
        inc = (self.increment if self.use_clock_var.get() else None) if not is_analysis else None

        self.current_task_id += 1

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
        self._force_clear_hash = False

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
        if self.active_worker_name == 'main':
            self.main_cancel_event.set()
        elif self.active_worker_name == 'op':
            self.op_cancel_event.set()

        if invalidate_task:
            self.current_task_id += 1

        self.active_worker_name = None
        self.analysis_thinking  = False

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
        opp_color = 'black' if color == 'white' else 'white'
        if is_insufficient_material(self.board):
            self.game_result = ('timeout_draw', None)
        else:
            self.game_result = ('timeout', opp_color)
        self.update_ui_after_state_change()
        print(f"Game Over! Result: {self.game_result[0]}")
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
            elif res == "timeout_draw":
                self.turn_label.config(
                    text="⌛ TIMEOUT: DRAW (INSUFFICIENT MATERIAL)",
                    background=self.COLORS['bg_light'], foreground=self.COLORS['text_light'])
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
        popup = tk.Toplevel(self.master)
        popup.title("Standard Chess - Rules & Reference")
        popup.geometry("800x700")
        popup.configure(bg=self.COLORS['bg_dark'])
        popup.transient(self.master)
        popup.grab_set()

        popup.update_idletasks()
        mx = self.master.winfo_x() + (self.master.winfo_width() - 800) // 2
        my = self.master.winfo_y() + (self.master.winfo_height() - 700) // 2
        popup.geometry(f"800x700+{mx}+{my}")

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

        text.tag_config("title", foreground=self.COLORS['accent'], font=("Helvetica", 18, "bold"), spacing1=10, spacing2=5)
        text.tag_config("h2", foreground=self.COLORS['text_light'], font=("Helvetica", 14, "bold"), spacing1=15, spacing2=5)
        text.tag_config("h3", foreground=self.COLORS['text_light'], font=("Helvetica", 12, "bold"), spacing1=10, spacing2=5)
        text.tag_config("code", font=("Courier", 10), background=self.COLORS['bg_light'], foreground="#00ffcc")
        text.tag_config("bold", font=("Helvetica", 11, "bold"))
        text.tag_config("normal", font=("Helvetica", 11), spacing3=4)

        try:
            with open("Zreadme.txt", "r", encoding="utf-8") as f:
                readme_text = f.read()
        except FileNotFoundError:
            readme_text = "# Error\nCould not find `Zreadme.txt` in the current directory."

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

        close_btn = ttk.Button(popup, text="Close", command=popup.destroy, style='Control.TButton')
        close_btn.pack(pady=(0, 15))

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
            m = self.current_pv_raw[i]
            promo = m[2] if len(m) > 2 and m[2] is not None else Queen
            tt_sim.make_move(m[0], m[1], promo)
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
            # Only unpack the coordinate pairs (start, end), ignoring promo
            squares = last_move[:2]
            if self.board_orientation == "black":
                flipped_last_move = [((ROWS - 1 - r), (COLS - 1 - c)) for r, c in squares]
            else:
                flipped_last_move = squares
        
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

# GameLogic.py (v1.4 - Improvements to performance)

ROWS, COLS = 8, 8
SQUARE_SIZE = 75
BOARD_COLOR_1 = "#D2B48C"
BOARD_COLOR_2 = "#8B5A2B"
OPPONENT_COLOR = {'white': 'black', 'black': 'white'}

DIRECTIONS = {
    'king':   ((-1, 0), (1, 0), (0, -1), (0, 1), (-1, -1), (-1, 1), (1, -1), (1, 1)),
    'queen':  ((-1, 0), (1, 0), (0, -1), (0, 1), (-1, -1), (-1, 1), (1, -1), (1, 1)),
    'rook':   ((0, 1), (0, -1), (1, 0), (-1, 0)),
    'bishop': ((-1, -1), (-1, 1), (1, -1), (1, 1)),
    'knight': ((2, 1), (2, -1), (-2, 1), (-2, -1), (1, 2), (1, -2), (-1, 2), (-1, -2)),
}

KNIGHT_ATTACKS_SQ = [None] * 64
KING_ATTACKS_SQ   = [None] * 64
PAWN_ATTACKS_SQ   = {'white': [None] * 64, 'black': [None] * 64}

RAYS_ORTHOGONAL = [None] * 64
RAYS_DIAGONAL   = [None] * 64
RAYS_ALL        = [None] * 64

def _init_tables():
    for r in range(ROWS):
        for c in range(COLS):
            sq = r * 8 + c
            
            # Knight attacks
            k_moves = []
            for dr, dc in DIRECTIONS['knight']:
                nr, nc = r + dr, c + dc
                if 0 <= nr < 8 and 0 <= nc < 8:
                    k_moves.append((nr, nc))
            KNIGHT_ATTACKS_SQ[sq] = tuple(k_moves)

            # King attacks
            kg_moves = []
            for dr, dc in DIRECTIONS['king']:
                nr, nc = r + dr, c + dc
                if 0 <= nr < 8 and 0 <= nc < 8:
                    kg_moves.append((nr, nc))
            KING_ATTACKS_SQ[sq] = tuple(kg_moves)

            # Pawn attacks
            w_pawn_caps = []
            b_pawn_caps = []
            for dc in (-1, 1):
                if 0 <= r + 1 < 8 and 0 <= c + dc < 8:
                    w_pawn_caps.append((r + 1, c + dc))
                if 0 <= r - 1 < 8 and 0 <= c + dc < 8:
                    b_pawn_caps.append((r - 1, c + dc))
            PAWN_ATTACKS_SQ['white'][sq] = tuple(w_pawn_caps)
            PAWN_ATTACKS_SQ['black'][sq] = tuple(b_pawn_caps)

            # Ray attacks
            ortho = []
            diag  = []
            for dr, dc in DIRECTIONS['rook']:
                ray = []
                cr, cc = r + dr, c + dc
                while 0 <= cr < ROWS and 0 <= cc < COLS:
                    ray.append((cr, cc))
                    cr += dr; cc += dc
                ortho.append(tuple(ray))
            for dr, dc in DIRECTIONS['bishop']:
                ray = []
                cr, cc = r + dr, c + dc
                while 0 <= cr < ROWS and 0 <= cc < COLS:
                    ray.append((cr, cc))
                    cr += dr; cc += dc
                diag.append(tuple(ray))
            RAYS_ORTHOGONAL[sq] = tuple(ortho)
            RAYS_DIAGONAL[sq]   = tuple(diag)
            RAYS_ALL[sq]        = tuple(ortho + diag)

_init_tables()

KNIGHT_ATTACKS_FROM = {(sq // 8, sq % 8): KNIGHT_ATTACKS_SQ[sq] for sq in range(64)}
KING_ATTACKS_FROM   = {(sq // 8, sq % 8): KING_ATTACKS_SQ[sq] for sq in range(64)}


def _clone_piece_fast(piece):
    cls       = piece.__class__
    new_piece = cls.__new__(cls)
    new_piece.color          = piece.color
    new_piece.opponent_color = piece.opponent_color
    new_piece.pos            = piece.pos
    new_piece._list_pos      = piece._list_pos
    if cls is Pawn:
        new_piece.direction    = piece.direction
        new_piece.starting_row = piece.starting_row
        new_piece.promo_rank   = piece.promo_rank
    return new_piece


# -----------------------------------------------------------------------
# Piece classes
# -----------------------------------------------------------------------
class Piece:
    __slots__ = ('color', 'opponent_color', 'pos', '_list_pos', '_z_list_pos')

    def __init__(self, color):
        self.color          = color
        self.opponent_color = "black" if color == "white" else "white"
        self.pos            = None
        self._list_pos      = -1
        self._z_list_pos    = -1

    def symbol(self): return "?"

class King(Piece):
    __slots__ = ()
    z_idx = 5
    def symbol(self): return "♔" if self.color == "white" else "♚"

class Queen(Piece):
    __slots__ = ()
    z_idx = 4
    def symbol(self): return "♕" if self.color == "white" else "♛"

class Rook(Piece):
    __slots__ = ()
    z_idx = 3
    def symbol(self): return "♖" if self.color == "white" else "♜"

class Bishop(Piece):
    __slots__ = ()
    z_idx = 2
    def symbol(self): return "♗" if self.color == "white" else "♝"

class Knight(Piece):
    __slots__ = ()
    z_idx = 1
    def symbol(self): return "♘" if self.color == "white" else "♞"

class Pawn(Piece):
    __slots__ = ('direction', 'starting_row', 'promo_rank')
    z_idx = 0
    def __init__(self, color):
        super().__init__(color)
        self.direction    = -1 if color == "white" else 1
        self.starting_row = 6  if color == "white" else 1
        self.promo_rank   = 0  if color == "white" else 7

    def symbol(self): return "♙" if self.color == "white" else "♟"


# -----------------------------------------------------------------------
# Board
# -----------------------------------------------------------------------
CASTLE_WK = 1
CASTLE_WQ = 2
CASTLE_BK = 4
CASTLE_BQ = 8

class Board:
    def __init__(self, setup=True):
        self.grid             = [[None] * COLS for _ in range(ROWS)]
        self.white_king_pos   = None
        self.black_king_pos   = None
        self.white_pieces     = []
        self.black_pieces     = []
        self.piece_counts_z   = {'white': [0] * 6, 'black': [0] * 6}
        self.castling_rights  = 15  # 1111 binary: WK, WQ, BK, BQ
        self.ep_square        = None
        self.halfmove_clock   = 0
        if setup:
            self._setup_initial_board()

    def _setup_initial_board(self):
        pieces = {
            0: [(0, Rook), (1, Knight), (2, Bishop), (3, Queen), (4, King),
                (5, Bishop), (6, Knight), (7, Rook)],
            1: [(i, Pawn) for i in range(8)],
            6: [(i, Pawn) for i in range(8)],
            7: [(0, Rook), (1, Knight), (2, Bishop), (3, Queen), (4, King),
                (5, Bishop), (6, Knight), (7, Rook)],
        }
        for r, piece_list in pieces.items():
            color = "black" if r < 2 else "white"
            for c, piece_class in piece_list:
                self.add_piece(piece_class(color), r, c)

    def _list_append(self, piece):
        lst             = self.white_pieces if piece.color == 'white' else self.black_pieces
        piece._list_pos = len(lst)
        lst.append(piece)

    def _list_remove(self, piece):
        idx = piece._list_pos
        if idx < 0:
            return
        lst            = self.white_pieces if piece.color == 'white' else self.black_pieces
        last           = lst[-1]
        lst[idx]       = last
        last._list_pos = idx
        lst.pop()
        piece._list_pos = -1

    def add_piece(self, piece, r, c):
        if self.grid[r][c] is not None:
            self.remove_piece(r, c)
        self.grid[r][c] = piece
        piece.pos       = (r, c)
        self._list_append(piece)
        self.piece_counts_z[piece.color][piece.z_idx] += 1
        if type(piece) is King:
            if piece.color == 'white': self.white_king_pos = (r, c)
            else:                      self.black_king_pos = (r, c)

    def remove_piece(self, r, c):
        piece = self.grid[r][c]
        if not piece:
            return
        self._list_remove(piece)
        self.piece_counts_z[piece.color][piece.z_idx] -= 1
        if type(piece) is King:
            if piece.color == 'white': self.white_king_pos = None
            else:                      self.black_king_pos = None
        piece.pos       = None
        self.grid[r][c] = None

    def move_piece(self, start, end):
        piece = self.grid[start[0]][start[1]]
        if not piece:
            return
        piece.pos = end
        if type(piece) is King:
            if piece.color == 'white': self.white_king_pos = end
            else:                      self.black_king_pos = end
        self.grid[start[0]][start[1]] = None
        self.grid[end[0]][end[1]]     = piece

    def find_king_pos(self, color):
        return self.white_king_pos if color == 'white' else self.black_king_pos

    def clone(self):
        new_board                 = Board.__new__(Board)
        new_board.grid            = [[None] * COLS for _ in range(ROWS)]
        new_board.white_king_pos  = self.white_king_pos
        new_board.black_king_pos  = self.black_king_pos
        new_board.castling_rights = self.castling_rights
        new_board.ep_square       = self.ep_square
        new_board.halfmove_clock  = self.halfmove_clock

        white_pieces = [_clone_piece_fast(p) for p in self.white_pieces]
        black_pieces = [_clone_piece_fast(p) for p in self.black_pieces]
        new_board.white_pieces = white_pieces
        new_board.black_pieces = black_pieces

        grid = new_board.grid
        for p in white_pieces: r, c = p.pos; grid[r][c] = p
        for p in black_pieces: r, c = p.pos; grid[r][c] = p

        pcz = self.piece_counts_z
        new_board.piece_counts_z = {
            'white': pcz['white'].copy(),
            'black': pcz['black'].copy(),
        }
        return new_board

    def make_move(self, start, end, promo_cls=Queen):
        return self.make_move_track(start, end, promo_cls)

    def make_move_track(self, start, end, promo_cls=Queen):
        sr, sc = start
        er, ec = end
        moving_piece = self.grid[sr][sc]
        target_piece = self.grid[er][ec]
        mc           = moving_piece.color
        mp_z         = moving_piece.z_idx

        old_castling = self.castling_rights
        old_ep       = self.ep_square
        old_halfmove = self.halfmove_clock

        removed = []
        added   = []
        special = 0

        if mp_z == 0 or target_piece is not None:
            self.halfmove_clock = 0
        else:
            self.halfmove_clock += 1

        # En Passant capture
        if mp_z == 0 and (er, ec) == self.ep_square and target_piece is None and sc != ec:
            ep_victim = self.grid[sr][ec]
            if ep_victim is not None:
                removed.append((ep_victim, sr, ec))
                self.remove_piece(sr, ec)
            special = 2
        elif target_piece is not None:
            removed.append((target_piece, er, ec))
            self.remove_piece(er, ec)

        # Castling move
        if mp_z == 5 and abs(ec - sc) == 2:
            special = 1
            if ec == 6: # Kingside
                self.move_piece((sr, 7), (sr, 5))
            elif ec == 2: # Queenside
                self.move_piece((sr, 0), (sr, 3))

        self.move_piece(start, end)

        # Promotion
        if mp_z == 0 and er == moving_piece.promo_rank:
            special = 3
            p_to_add = promo_cls if promo_cls is not None else Queen
            removed.append((moving_piece, er, ec))
            self.remove_piece(er, ec)
            promoted_piece = p_to_add(mc)
            self.add_piece(promoted_piece, er, ec)
            added.append((promoted_piece, er, ec))

        # Update En Passant square
        if mp_z == 0 and abs(er - sr) == 2:
            self.ep_square = ((sr + er) // 2, sc)
        else:
            self.ep_square = None

        # Update Castling Rights
        if mp_z == 5:
            if mc == 'white': self.castling_rights &= ~(CASTLE_WK | CASTLE_WQ)
            else:             self.castling_rights &= ~(CASTLE_BK | CASTLE_BQ)
        elif mp_z == 3:
            if (sr, sc) == (7, 7): self.castling_rights &= ~CASTLE_WK
            elif (sr, sc) == (7, 0): self.castling_rights &= ~CASTLE_WQ
            elif (sr, sc) == (0, 7): self.castling_rights &= ~CASTLE_BK
            elif (sr, sc) == (0, 0): self.castling_rights &= ~CASTLE_BQ

        if target_piece and target_piece.z_idx == 3:
            if (er, ec) == (7, 7): self.castling_rights &= ~CASTLE_WK
            elif (er, ec) == (7, 0): self.castling_rights &= ~CASTLE_WQ
            elif (er, ec) == (0, 7): self.castling_rights &= ~CASTLE_BK
            elif (er, ec) == (0, 0): self.castling_rights &= ~CASTLE_BQ

        return (start, end, moving_piece, removed, added, old_castling, old_ep, old_halfmove, special, self.castling_rights, self.ep_square)

    def unmake_move(self, record_tuple):
        start, end, moving_piece, removed, added, old_castling, old_ep, old_halfmove, special = record_tuple[:9]
        self.castling_rights = old_castling
        self.ep_square       = old_ep
        self.halfmove_clock  = old_halfmove

        for p, r, c in added:
            self.remove_piece(r, c)

        if special == 3:
            self.add_piece(moving_piece, start[0], start[1])
        else:
            self.move_piece(end, start)

        if special == 1:
            sr = start[0]
            if end[1] == 6:
                self.move_piece((sr, 5), (sr, 7))
            elif end[1] == 2:
                self.move_piece((sr, 3), (sr, 0))

        for p, r, c in removed:
            if p is not moving_piece:
                self.add_piece(p, r, c)


# -----------------------------------------------------------------------
# Global game logic
# -----------------------------------------------------------------------
def is_square_attacked(board, r, c, attacking_color):
    grid = board.grid
    sq = r * 8 + c

    # 1. Pawn Attacks (Flat Table)
    for pr, pc in PAWN_ATTACKS_SQ[attacking_color][sq]:
        p = grid[pr][pc]
        if p and p.z_idx == 0 and p.color == attacking_color:
            return True

    # 2. Knight Attacks (Flat Table)
    for kr, kc in KNIGHT_ATTACKS_SQ[sq]:
        p = grid[kr][kc]
        if p and p.z_idx == 1 and p.color == attacking_color:
            return True

    # 3. King Attacks (Flat Table)
    for kr, kc in KING_ATTACKS_SQ[sq]:
        p = grid[kr][kc]
        if p and p.z_idx == 5 and p.color == attacking_color:
            return True

    # 4. Orthogonal (Rook/Queen)
    sq = r * 8 + c
    for ray in RAYS_ORTHOGONAL[sq]:
        for cr, cc in ray:
            p = grid[cr][cc]
            if p:
                if p.color == attacking_color and (p.z_idx == 3 or p.z_idx == 4):
                    return True
                break

    # 5. Diagonal (Bishop/Queen)
    for ray in RAYS_DIAGONAL[sq]:
        for cr, cc in ray:
            p = grid[cr][cc]
            if p:
                if p.color == attacking_color and (p.z_idx == 2 or p.z_idx == 4):
                    return True
                break

    return False

def is_in_check(board, color):
    kpos = board.find_king_pos(color)
    if not kpos: return True
    return is_square_attacked(board, kpos[0], kpos[1], OPPONENT_COLOR[color])

def get_all_pseudo_legal_moves(board, color):
    moves = []
    grid = board.grid
    opp = OPPONENT_COLOR[color]
    pieces = board.white_pieces if color == 'white' else board.black_pieces

    for p in pieces:
        r, c = p.pos
        sq = r * 8 + c
        pz = p.z_idx

        if pz == 0: # Pawn
            dr = -1 if color == 'white' else 1
            promo_r = p.promo_rank
            if 0 <= r + dr < 8 and grid[r + dr][c] is None:
                if r + dr == promo_r:
                    for p_cls in (Queen, Rook, Bishop, Knight):
                        moves.append(((r, c), (r + dr, c), p_cls))
                else:
                    moves.append(((r, c), (r + dr, c), None))
                    if r == p.starting_row and grid[r + 2 * dr][c] is None:
                        moves.append(((r, c), (r + 2 * dr, c), None))
            for dc in (-1, 1):
                cr, cc = r + dr, c + dc
                if 0 <= cr < 8 and 0 <= cc < 8:
                    target = grid[cr][cc]
                    if target and target.color == opp:
                        if cr == promo_r:
                            for p_cls in (Queen, Rook, Bishop, Knight):
                                moves.append(((r, c), (cr, cc), p_cls))
                        else:
                            moves.append(((r, c), (cr, cc), None))
                    elif (cr, cc) == board.ep_square:
                        moves.append(((r, c), (cr, cc), None))

        elif pz == 1: # Knight
            for kr, kc in KNIGHT_ATTACKS_SQ[sq]:
                target = grid[kr][kc]
                if target is None or target.color == opp:
                    moves.append(((r, c), (kr, kc), None))

        elif pz == 2: # Bishop
            for ray in RAYS_DIAGONAL[sq]:
                for cr, cc in ray:
                    target = grid[cr][cc]
                    if target is None: moves.append(((r, c), (cr, cc), None))
                    else:
                        if target.color == opp: moves.append(((r, c), (cr, cc), None))
                        break

        elif pz == 3: # Rook
            for ray in RAYS_ORTHOGONAL[sq]:
                for cr, cc in ray:
                    target = grid[cr][cc]
                    if target is None: moves.append(((r, c), (cr, cc), None))
                    else:
                        if target.color == opp: moves.append(((r, c), (cr, cc), None))
                        break

        elif pz == 4: # Queen
            for ray in RAYS_ALL[sq]:
                for cr, cc in ray:
                    target = grid[cr][cc]
                    if target is None: moves.append(((r, c), (cr, cc), None))
                    else:
                        if target.color == opp: moves.append(((r, c), (cr, cc), None))
                        break

        elif pz == 5: # King
            for kr, kc in KING_ATTACKS_SQ[sq]:
                target = grid[kr][kc]
                if target is None or target.color == opp:
                    moves.append(((r, c), (kr, kc), None))

            # Castling
            if color == 'white' and r == 7 and c == 4 and not is_in_check(board, 'white'):
                if (board.castling_rights & CASTLE_WK) and grid[7][5] is None and grid[7][6] is None:
                    if not is_square_attacked(board, 7, 5, 'black') and not is_square_attacked(board, 7, 6, 'black'):
                        moves.append(((7, 4), (7, 6), None))
                if (board.castling_rights & CASTLE_WQ) and grid[7][3] is None and grid[7][2] is None and grid[7][1] is None:
                    if not is_square_attacked(board, 7, 3, 'black') and not is_square_attacked(board, 7, 2, 'black'):
                        moves.append(((7, 4), (7, 2), None))
            elif color == 'black' and r == 0 and c == 4 and not is_in_check(board, 'black'):
                if (board.castling_rights & CASTLE_BK) and grid[0][5] is None and grid[0][6] is None:
                    if not is_square_attacked(board, 0, 5, 'white') and not is_square_attacked(board, 0, 6, 'white'):
                        moves.append(((0, 4), (0, 6), None))
                if (board.castling_rights & CASTLE_BQ) and grid[0][3] is None and grid[0][2] is None and grid[0][1] is None:
                    if not is_square_attacked(board, 0, 3, 'white') and not is_square_attacked(board, 0, 2, 'white'):
                        moves.append(((0, 4), (0, 2), None))

    return moves

def get_pseudo_legal_captures(board, color):
    """High-speed capture-only generator for Quiescence Search."""
    moves = []
    grid = board.grid
    opp = OPPONENT_COLOR[color]
    pieces = board.white_pieces if color == 'white' else board.black_pieces

    for p in pieces:
        r, c = p.pos
        sq = r * 8 + c
        pz = p.z_idx

        if pz == 0: # Pawn
            dr = -1 if color == 'white' else 1
            promo_r = p.promo_rank
            # Forward promotion (tactical)
            if 0 <= r + dr < 8 and grid[r + dr][c] is None and r + dr == promo_r:
                for p_cls in (Queen, Rook, Bishop, Knight):
                    moves.append(((r, c), (r + dr, c), p_cls))
            # Diagonal captures
            for dc in (-1, 1):
                cr, cc = r + dr, c + dc
                if 0 <= cr < 8 and 0 <= cc < 8:
                    target = grid[cr][cc]
                    if target and target.color == opp:
                        if cr == promo_r:
                            for p_cls in (Queen, Rook, Bishop, Knight):
                                moves.append(((r, c), (cr, cc), p_cls))
                        else:
                            moves.append(((r, c), (cr, cc), None))
                    elif (cr, cc) == board.ep_square:
                        moves.append(((r, c), (cr, cc), None))

        elif pz == 1: # Knight
            for kr, kc in KNIGHT_ATTACKS_SQ[sq]:
                target = grid[kr][kc]
                if target and target.color == opp:
                    moves.append(((r, c), (kr, kc), None))

        elif pz == 2: # Bishop
            for ray in RAYS_DIAGONAL[sq]:
                for cr, cc in ray:
                    target = grid[cr][cc]
                    if target is not None:
                        if target.color == opp:
                            moves.append(((r, c), (cr, cc), None))
                        break

        elif pz == 3: # Rook
            for ray in RAYS_ORTHOGONAL[sq]:
                for cr, cc in ray:
                    target = grid[cr][cc]
                    if target is not None:
                        if target.color == opp:
                            moves.append(((r, c), (cr, cc), None))
                        break

        elif pz == 4: # Queen
            for ray in RAYS_ALL[sq]:
                for cr, cc in ray:
                    target = grid[cr][cc]
                    if target is not None:
                        if target.color == opp:
                            moves.append(((r, c), (cr, cc), None))
                        break

        elif pz == 5: # King
            for kr, kc in KING_ATTACKS_SQ[sq]:
                target = grid[kr][kc]
                if target and target.color == opp:
                    moves.append(((r, c), (kr, kc), None))

    return moves

def _is_square_attacked_ignoring_square(board, r, c, attacking_color, ignore_pos):
    grid = board.grid
    ir, ic = ignore_pos
    original = grid[ir][ic]
    grid[ir][ic] = None
    try:
        return is_square_attacked(board, r, c, attacking_color)
    finally:
        grid[ir][ic] = original

def _compute_check_and_pins(board, color):
    opp  = OPPONENT_COLOR[color]
    kpos = board.find_king_pos(color)
    if not kpos:
        return (0, 0), [], {}
    kr, kc = kpos
    grid = board.grid
    sq = kr * 8 + kc

    checkers = []

    # Pawn checks (Flat Table)
    for pr, pc in PAWN_ATTACKS_SQ[opp][sq]:
        p = grid[pr][pc]
        if p and p.z_idx == 0 and p.color == opp:
            checkers.append((p, pr, pc))

    # Knight checks (Flat Table)
    for kr2, kc2 in KNIGHT_ATTACKS_SQ[sq]:
        p = grid[kr2][kc2]
        if p and p.z_idx == 1 and p.color == opp:
            checkers.append((p, kr2, kc2))

    pinned = {}

    def _scan_rays(rays, slider_idxs):
        for ray in rays:
            blocker = None
            seen = []
            for cr, cc in ray:
                seen.append((cr, cc))
                p = grid[cr][cc]
                if p is None:
                    continue
                if blocker is None:
                    if p.color == color:
                        blocker = (p, cr, cc)
                        continue
                    else:
                        if p.z_idx in slider_idxs:
                            checkers.append((p, cr, cc))
                        break
                else:
                    if p.color == opp and p.z_idx in slider_idxs:
                        pinned[(blocker[1], blocker[2])] = frozenset(seen)
                    break

    # Execute ray scans at the function level (4 spaces indent)
    _scan_rays(RAYS_ORTHOGONAL[sq], (3, 4))  # Rook, Queen
    _scan_rays(RAYS_DIAGONAL[sq],   (2, 4))  # Bishop, Queen

    return kpos, checkers, pinned

def _generate_legal_moves(board, color, captures_only=False):
    kpos, checkers, pinned = _compute_check_and_pins(board, color)
    if not kpos or (kpos == (0, 0) and not checkers and not pinned and not board.find_king_pos(color)):
        return

    grid = board.grid
    opp = OPPONENT_COLOR[color]
    kr, kc = kpos
    num_checkers = len(checkers)

    if num_checkers >= 2:
        for tr, tc in KING_ATTACKS_SQ[kr * 8 + kc]:
            target = grid[tr][tc]
            if target is None or target.color == opp:
                if captures_only and (target is None or target.color != opp):
                    continue
                if not _is_square_attacked_ignoring_square(board, tr, tc, opp, kpos):
                    yield ((kr, kc), (tr, tc), None)
        return

    block_squares = None
    checker_sq = None
    if num_checkers == 1:
        checker_piece, ccr, ccc = checkers[0]
        checker_sq = (ccr, ccc)
        if checker_piece.z_idx in (2, 3, 4):
            dr = (ccr > kr) - (ccr < kr)
            dc = (ccc > kc) - (ccc < kc)
            block_squares = set()
            r, c = kr + dr, kc + dc
            while (r, c) != (ccr, ccc):
                block_squares.add((r, c))
                r += dr
                c += dc
            block_squares.add((ccr, ccc))
        else:
            block_squares = {(ccr, ccc)}

    move_source = get_pseudo_legal_captures(board, color) if captures_only else get_all_pseudo_legal_moves(board, color)

    for m in move_source:
        (sr, sc), (tr, tc) = m[0], m[1]
        promo = m[2] if len(m) > 2 else None
        piece = grid[sr][sc]
        if not piece:
            continue

        if piece.z_idx == 5:  # King
            if abs(tc - sc) == 2:
                if not captures_only:
                    yield ((sr, sc), (tr, tc), None)
                continue

            if _is_square_attacked_ignoring_square(board, tr, tc, opp, kpos):
                continue
            yield ((sr, sc), (tr, tc), None)
            continue

        if num_checkers == 1 and (tr, tc) not in block_squares:
            is_ep_of_checker = (piece.z_idx == 0 and (tr, tc) == board.ep_square
                                 and checker_sq == (sr, tc))
            if not is_ep_of_checker:
                continue

        pin_ray = pinned.get((sr, sc))
        if pin_ray is not None and (tr, tc) not in pin_ray:
            continue

        if piece.z_idx == 0 and (tr, tc) == board.ep_square and sc != tc:
            rec = board.make_move_track((sr, sc), (tr, tc))
            still_in_check = is_in_check(board, color)
            board.unmake_move(rec)
            if still_in_check:
                continue

        yield ((sr, sc), (tr, tc), promo)

def get_all_legal_moves(board, color):
    return list(_generate_legal_moves(board, color, captures_only=False))

def get_all_legal_captures(board, color):
    return list(_generate_legal_moves(board, color, captures_only=True))

def has_legal_moves(board, color):
    for _ in _generate_legal_moves(board, color):
        return True
    return False

def is_insufficient_material(board):
    pcz_w = board.piece_counts_z['white']
    pcz_b = board.piece_counts_z['black']
    if pcz_w[0] > 0 or pcz_b[0] > 0 or pcz_w[3] > 0 or pcz_b[3] > 0 or pcz_w[4] > 0 or pcz_b[4] > 0:
        return False

    w_count, b_count = len(board.white_pieces), len(board.black_pieces)
    if w_count == 1 and b_count == 1:
        return True
    if (w_count <= 2 and b_count == 1) or (b_count <= 2 and w_count == 1):
        return True
    if w_count == 2 and b_count == 2:
        if pcz_w[2] == 1 and pcz_b[2] == 1:
            w_b_pos = next(p.pos for p in board.white_pieces if p.z_idx == 2)
            b_b_pos = next(p.pos for p in board.black_pieces if p.z_idx == 2)
            if (w_b_pos[0] + w_b_pos[1]) % 2 == (b_b_pos[0] + b_b_pos[1]) % 2:
                return True
        elif (pcz_w[1] == 1 and pcz_b[1] == 1) or (pcz_w[2] == 1 and pcz_b[1] == 1) or (pcz_w[1] == 1 and pcz_b[2] == 1):
            return True
    return False

_board_hash_fn = None
def _get_board_hash():
    global _board_hash_fn
    if _board_hash_fn is None:
        from EngineRuntime import board_hash
        _board_hash_fn = board_hash
    return _board_hash_fn

def get_game_state(board, turn_to_move, position_counts, ply_count=0, max_moves=None):
    in_chk = is_in_check(board, turn_to_move)
    if not has_legal_moves(board, turn_to_move):
        if in_chk:
            winner = 'black' if turn_to_move == 'white' else 'white'
            return ("checkmate", winner)
        else:
            return ("stalemate", None)

    if is_insufficient_material(board):
        return ("insufficient_material", None)

    if board.halfmove_clock >= 100:
        return ("50_move_rule", None)

    try:
        bh_fn = _get_board_hash()
        if position_counts.get(bh_fn(board, turn_to_move), 0) >= 3:
            return ("repetition", None)
    except ImportError:
        pass

    if max_moves is not None and ply_count >= max_moves:
        return ("move_limit", None)

    return "ongoing", None

# --- Fast Static Exchange Evaluation (SEE) ---
_SEE_VALUES = [100, 320, 330, 500, 950, 20000]

def _attackers_to_square(board, r, c, color, occupied_override=None):
    grid = board.grid
    attackers = []
    sq = r * 8 + c

    def get_piece(pr, pc):
        if occupied_override and (pr, pc) in occupied_override:
            return occupied_override[(pr, pc)]
        return grid[pr][pc]

    for pr, pc in PAWN_ATTACKS_SQ[color][sq]:
        p = get_piece(pr, pc)
        if p and p.z_idx == 0 and p.color == color:
            attackers.append((_SEE_VALUES[0], pr, pc, 0))

    for kr, kc in KNIGHT_ATTACKS_SQ[sq]:
        p = get_piece(kr, kc)
        if p and p.z_idx == 1 and p.color == color:
            attackers.append((_SEE_VALUES[1], kr, kc, 1))

    for kr, kc in KING_ATTACKS_SQ[sq]:
        p = get_piece(kr, kc)
        if p and p.z_idx == 5 and p.color == color:
            attackers.append((_SEE_VALUES[5], kr, kc, 5))

    for ray in RAYS_ORTHOGONAL[sq]:
        for cr, cc in ray:
            p = get_piece(cr, cc)
            if p:
                if p.color == color and (p.z_idx == 3 or p.z_idx == 4):
                    attackers.append((_SEE_VALUES[p.z_idx], cr, cc, p.z_idx))
                break

    for ray in RAYS_DIAGONAL[sq]:
        for cr, cc in ray:
            p = get_piece(cr, cc)
            if p:
                if p.color == color and (p.z_idx == 2 or p.z_idx == 4):
                    attackers.append((_SEE_VALUES[p.z_idx], cr, cc, p.z_idx))
                break

    return attackers

def static_exchange_eval(board, move, moving_piece, target_piece):
    if target_piece is None:
        if moving_piece.z_idx == 0 and move[1] == board.ep_square:
            return _SEE_VALUES[0]
        return 0

    (sr, sc), (tr, tc) = move[0], move[1]
    grid = board.grid
    occupied_override = {(sr, sc): None, (tr, tc): moving_piece}

    def attackers_live(color):
        return _attackers_to_square(board, tr, tc, color, occupied_override)

    gains = [_SEE_VALUES[target_piece.z_idx]]
    side_to_move = moving_piece.opponent_color
    current_attacker_value = _SEE_VALUES[moving_piece.z_idx]

    while True:
        attackers = attackers_live(side_to_move)
        if not attackers:
            break
        attackers.sort(key=lambda a: a[0])
        value, fr, fc, fz = attackers[0]

        gains.append(current_attacker_value - gains[-1])

        moving_p = occupied_override.get((fr, fc), grid[fr][fc])
        occupied_override[(fr, fc)] = None
        occupied_override[(tr, tc)] = moving_p
        current_attacker_value = value
        side_to_move = 'black' if side_to_move == 'white' else 'white'

    result = gains[-1]
    for i in range(len(gains) - 2, -1, -1):
        result = gains[i] - max(0, result)
    return result

def fast_approximate_material_swing(board, move, moving_piece, target_piece, piece_values_list):
    if target_piece is not None:
        # Fast MVV-LVA fast-path: capturing equal/higher value piece is always tactical
        if piece_values_list[target_piece.z_idx] >= piece_values_list[moving_piece.z_idx]:
            return piece_values_list[target_piece.z_idx] - piece_values_list[moving_piece.z_idx], True
        see = static_exchange_eval(board, move, moving_piece, target_piece)
        return see, (see >= 0)

    if moving_piece.z_idx == 0 and move[1] == board.ep_square:
        return piece_values_list[0], True

    if moving_piece.z_idx == 0 and move[1][0] == moving_piece.promo_rank:
        return piece_values_list[4] - piece_values_list[0], True

    return 0, False

def format_move(move):
    if not move: return "None"
    (r1, c1), (r2, c2) = move[:2]
    return f"{'abcdefgh'[c1]}{'87654321'[r1]}-{'abcdefgh'[c2]}{'87654321'[r2]}"

def format_move_san(board_before, board_after, move):
    if not move: return "None"
    start_pos, end_pos = move[0], move[1]
    p = board_before.grid[start_pos[0]][start_pos[1]]
    if not p: return format_move(move)

    if p.z_idx == 5 and abs(end_pos[1] - start_pos[1]) == 2:
        san = "O-O" if end_pos[1] == 6 else "O-O-O"
    else:
        chars = {Pawn: '', Knight: 'N', Bishop: 'B', Rook: 'R', Queen: 'Q', King: 'K'}
        files = 'abcdefgh'
        ranks = '87654321'
        is_cap = (board_before.grid[end_pos[0]][end_pos[1]] is not None) or (p.z_idx == 0 and end_pos == board_before.ep_square)

        if p.z_idx == 0:
            san = f"{files[start_pos[1]]}x{files[end_pos[1]]}{ranks[end_pos[0]]}" if is_cap else f"{files[end_pos[1]]}{ranks[end_pos[0]]}"
            if end_pos[0] == p.promo_rank:
                promoted_piece = board_after.grid[end_pos[0]][end_pos[1]]
                promo_char = chars.get(type(promoted_piece), 'Q') if promoted_piece else 'Q'
                san += f"={promo_char}"
        else:
            p_char = chars[type(p)]
            disambig = ""
            if p.z_idx != 0 and p.z_idx != 5:
                other_candidates = [
                    m[0] for m in get_all_legal_moves(board_before, p.color)
                    if m[1] == end_pos and m[0] != start_pos
                    and type(board_before.grid[m[0][0]][m[0][1]]) is type(p)
                ]
                if other_candidates:
                    same_file = any(pos[1] == start_pos[1] for pos in other_candidates)
                    same_rank = any(pos[0] == start_pos[0] for pos in other_candidates)
                    if not same_file:
                        disambig = files[start_pos[1]]
                    elif not same_rank:
                        disambig = ranks[start_pos[0]]
                    else:
                        disambig = f"{files[start_pos[1]]}{ranks[start_pos[0]]}"

            san = f"{p_char}{disambig}{'x' if is_cap else ''}{files[end_pos[1]]}{ranks[end_pos[0]]}"

    opp = 'black' if p.color == 'white' else 'white'
    if not has_legal_moves(board_after, opp):
        san += "#" if is_in_check(board_after, opp) else ""
    elif is_in_check(board_after, opp):
        san += "+"

    return san

# AI.py (v2.0 - Lean Eval, SEE Move Ordering, Capture-Only QSearch and bottleneck removed)

import time
import random
from operator import itemgetter
from GameLogic import *
from EngineRuntime import (
    OPENING_BOOK,
    ZOBRIST_TURN,
    SearchCancelledException,
    TT_FLAG_EXACT,
    TT_FLAG_LOWERBOUND,
    TT_FLAG_UPPERBOUND,
    board_hash,
    board_to_fen,
    build_flat_pst_tables,
    calc_time_check_mask,
    format_bot_move,
    get_pv_data,
    incremental_hash,
    update_bot_runtime_state,
)

# --- EVALUATION CONSTANTS ---
MG_PIECE_VALUES = {
    Pawn: 100,
    Knight: 320,
    Bishop: 330,
    Rook: 500,
    Queen: 950,
    King: 20000
}

EG_PIECE_VALUES = {
    Pawn: 110,
    Knight: 300,
    Bishop: 340,
    Rook: 550,
    Queen: 920,
    King: 20000
}

ORDERING_VALUES = [
    MG_PIECE_VALUES[Pawn],
    MG_PIECE_VALUES[Knight],
    MG_PIECE_VALUES[Bishop],
    MG_PIECE_VALUES[Rook],
    MG_PIECE_VALUES[Queen],
    MG_PIECE_VALUES[King]
]

INITIAL_PHASE_MATERIAL = (MG_PIECE_VALUES[Knight] * 4 + MG_PIECE_VALUES[Bishop] * 4 +
                          MG_PIECE_VALUES[Rook] * 4 + MG_PIECE_VALUES[Queen] * 2)

class ChessBot:
    search_depth = 6
    MATE_SCORE = 1000000
    DRAW_SCORE = 0

    MAX_Q_SEARCH_DEPTH = 12
    LMR_DEPTH_THRESHOLD = 3
    LMR_MOVE_COUNT_THRESHOLD = 4
    NMP_MIN_DEPTH = 3
    NMP_BASE_REDUCTION = 2
    NMP_DEPTH_DIVISOR = 6
    USE_NULL_MOVE_PRUNING = True

    USE_FUTILITY_PRUNING = True
    FUTILITY_MARGIN = 350

    USE_REVERSE_FUTILITY_PRUNING = True
    RFP_MAX_DEPTH = 2
    RFP_MARGIN_PER_DEPTH = 150

    USE_IIR = True
    IIR_MIN_DEPTH = 4

    TT_SIZE      = 1 << 22   # ~4.19M slots
    TT_MASK      = TT_SIZE - 1
    EVAL_TT_SIZE = 1 << 21   # ~2.10M slots
    EVAL_TT_MASK = EVAL_TT_SIZE - 1

    BONUS_PV_MOVE = 10_000_000
    BONUS_CAPTURE = 8_000_000
    BONUS_KILLER_1 = 4_000_000
    BONUS_KILLER_2 = 3_000_000
    ASP_WINDOW_INIT = 60
    ASP_MAX_RETRIES = 3

    TIME_BUFFER_SEC = 0.40
    TIME_BUFFER_PCT = 0.05
    MIN_MOVE_TIME = 0.03
    TIME_DIVISOR_BASE = 45
    TIME_DIVISOR_HEALTH_WEIGHT = 20
    TIME_INCREMENT_WEIGHT = 0.8
    TIME_MAX_MULTIPLIER = 3.0

    MAX_EXTENSION_DEPTH = 16

    TEMPO_BONUS = 20
    EVAL_CASTLING_RIGHTS = 15
    EVAL_DEV_BONUS = 10
    EVAL_BISHOP_PAIR = 25
    EVAL_ROOK_ON_7TH = 25
    EVAL_ROOK_OPEN_FILE = 20
    EVAL_ROOK_SEMI_OPEN = 10
    EVAL_PAWN_DEFENDED = 10
    EVAL_PAWN_SHIELD = 10
    EVAL_PASSED_PAWN_RANK = [0, 5, 10, 20, 35, 60, 100, 0]

    def __init__(self, board, color, position_counts, comm_queue, cancellation_event,
                 bot_name=None, ply_count=0, game_mode="bot",
                 time_left=None, increment=None, use_opening_book=True,
                 show_tt_fullness=False):
        self.show_tt_fullness = show_tt_fullness

        self.board = board
        self.color = color
        self.opponent_color = 'black' if color == 'white' else 'white'
        self.position_counts = position_counts
        self.comm_queue = comm_queue
        self.cancellation_event = cancellation_event
        self.ply_count = ply_count
        self.game_mode = game_mode

        self.time_left = time_left
        self.increment = increment
        self.stop_time = None
        
        if time_left:
             allocated = (self.time_left / 30.0) + (self.increment * 0.8)
             self.time_check_mask = self._calc_time_check_mask(allocated)
        else:
             self.time_check_mask = 511

        self.use_opening_book = use_opening_book

        if bot_name is None:
            self.bot_name = "OP Bot" if self.__class__.__name__ == "OpponentAI" else "AI Bot"
        else:
            self.bot_name = bot_name

        self._initialize_search_state()

    def _initialize_search_state(self):
        self.tt_keys   = [0] * self.TT_SIZE
        self.tt_scores = [0] * self.TT_SIZE
        self.tt_depths = [-1] * self.TT_SIZE
        self.tt_flags  = [0] * self.TT_SIZE
        self.tt_moves  = [None] * self.TT_SIZE
        self.tt_ages   = [0] * self.TT_SIZE
        self.tt_filled = 0

        self.eval_tt_keys = [0] * self.EVAL_TT_SIZE
        self.eval_tt_vals = [0] * self.EVAL_TT_SIZE
        self.eval_tt_occ  = bytearray(self.EVAL_TT_SIZE)

        self.current_age = 0
        self.nodes_searched = 0
        self.used_heuristic_eval = False
        self.tb_hits = 0
        self.killer_moves = [[None, None] for _ in range(256)]
        self.history_heuristic_table = [[[0 for _ in range(64)] for _ in range(64)] for _ in range(2)]
        self.counter_moves = [[[None for _ in range(64)] for _ in range(64)] for _ in range(2)]
        self.continuation_history = [[[[[0] * 64 for _ in range(6)] for _ in range(64)] for _ in range(6)] for _ in range(2)]

    def update_state(self, board, color, position_counts, comm_queue, cancellation_event, bot_name, ply_count, game_mode, **kwargs):
        update_bot_runtime_state(
            self, board, color, position_counts, comm_queue, cancellation_event,
            bot_name, ply_count, game_mode, **kwargs
        )

    def _tt_probe(self, hash_val):
        idx = hash_val & self.TT_MASK
        if self.tt_depths[idx] != -1 and self.tt_keys[idx] == hash_val:
            return idx
        return -1

    def _peek_eval_tt(self, hash_val):
        idx = hash_val & self.EVAL_TT_MASK
        if self.eval_tt_occ[idx] and self.eval_tt_keys[idx] == hash_val:
            return self.eval_tt_vals[idx]
        return None

    def _get_cached_static_eval(self, board, turn, hash_val):
        idx = hash_val & self.EVAL_TT_MASK
        if self.eval_tt_occ[idx] and self.eval_tt_keys[idx] == hash_val:
            return self.eval_tt_vals[idx]
        val = self.evaluate_board(board, turn)
        self.eval_tt_keys[idx] = hash_val
        self.eval_tt_vals[idx] = val
        self.eval_tt_occ[idx]  = 1
        return val

    def _store_tt(self, hash_val, score, depth, flag, move):
        idx = hash_val & self.TT_MASK
        stored_depth = self.tt_depths[idx]
        same_position = (stored_depth != -1 and self.tt_keys[idx] == hash_val)

        if stored_depth == -1 or self.tt_ages[idx] < self.current_age or depth >= stored_depth:
            if stored_depth == -1:
                self.tt_filled += 1
            self.tt_keys[idx]   = hash_val
            self.tt_scores[idx] = score
            self.tt_depths[idx] = depth
            self.tt_flags[idx]  = flag
            
            if move is not None:
                self.tt_moves[idx] = move
            elif same_position:
                pass
            else:
                self.tt_moves[idx] = None
                
            self.tt_ages[idx]   = self.current_age

    def _report_log(self, message):   self.comm_queue.put(('log', message))
    def _report_eval(self, score, depth): self.comm_queue.put(('eval', score if self.color == 'white' else -score, depth))
    def _report_move(self, move):     self.comm_queue.put(('move', move))

    def _calc_time_check_mask(self, allocated):
        return calc_time_check_mask(allocated)

    def _search_time_budget(self, time_left, increment):
        buffer = max(self.TIME_BUFFER_SEC, time_left * self.TIME_BUFFER_PCT, increment * 1.5)
        clock_ceiling = max(0.0, time_left - buffer)
        buffer_health = max(0.0, min(1.0, clock_ceiling / time_left)) if time_left > 0 else 0.0

        divisor = self.TIME_DIVISOR_BASE - (self.TIME_DIVISOR_HEALTH_WEIGHT * buffer_health)
        optimum_time = (time_left / divisor) + (increment * self.TIME_INCREMENT_WEIGHT)
        optimum_time = max(self.MIN_MOVE_TIME, optimum_time)
        optimum_time = min(optimum_time, clock_ceiling)

        max_time = min(clock_ceiling, optimum_time * self.TIME_MAX_MULTIPLIER)
        max_time = max(max_time, min(self.MIN_MOVE_TIME, clock_ceiling))
        return optimum_time, max_time

    def _format_move(self, board_before, move):
        return format_bot_move(self, board_before, move)

    def _run_depth_iteration(self, depth, root_moves, root_hash, pv_move,
                             prev_iter_score=None, alpha_floor=None):
        iter_nodes       = 0
        iter_tb_hits     = 0
        any_heuristic_eval = False
        use_aspiration   = (alpha_floor is None and prev_iter_score is not None and depth >= 2)

        if use_aspiration:
            window      = self.ASP_WINDOW_INIT
            alpha_bound = prev_iter_score - window
            beta_bound  = prev_iter_score + window
            retries     = 0
            while True:
                best_score, best_move = self._search_at_depth(
                    depth, root_moves, root_hash, pv_move,
                    aspiration_window=(alpha_bound, beta_bound))
                iter_nodes   += self.nodes_searched
                iter_tb_hits += self.tb_hits
                if self.used_heuristic_eval: any_heuristic_eval = True

                if self.cancellation_event.is_set() or (self.stop_time and time.time() > self.stop_time):
                    raise SearchCancelledException()

                if best_score <= alpha_bound:
                    alpha_bound -= window; window *= 2; retries += 1
                elif best_score >= beta_bound:
                    beta_bound  += window; window *= 2; retries += 1
                else:
                    break

                if retries >= self.ASP_MAX_RETRIES:
                    best_score, best_move = self._search_at_depth(
                        depth, root_moves, root_hash, pv_move, alpha_floor=alpha_floor)
                    iter_nodes   += self.nodes_searched
                    iter_tb_hits += self.tb_hits
                    if self.used_heuristic_eval: any_heuristic_eval = True
                    break
        else:
            best_score, best_move = self._search_at_depth(
                depth, root_moves, root_hash, pv_move, alpha_floor=alpha_floor)
            iter_nodes       = self.nodes_searched
            iter_tb_hits     = self.tb_hits
            if self.used_heuristic_eval: any_heuristic_eval = True

        self.nodes_searched    = iter_nodes
        self.tb_hits           = iter_tb_hits
        self.used_heuristic_eval = any_heuristic_eval
        return best_score, best_move

    def _age_history_table(self):
        for c_idx in range(2):
            ht = self.history_heuristic_table[c_idx]
            for from_sq in range(64):
                row = ht[from_sq]
                ht[from_sq] = [(v * 7) // 8 for v in row]

    def _get_pv_data(self, max_depth, root_move):
        return get_pv_data(self, max_depth, root_move)

    def make_move(self):
        try:
            self._age_history_table()

            # 1. Check Opening Book
            if self.use_opening_book and self.ply_count <= 16:
                fen = board_to_fen(self.board, self.color)
                if fen in OPENING_BOOK:
                    book_options = OPENING_BOOK[fen]
                    weights = [opt["weight"] for opt in book_options]
                    chosen = random.choices(book_options, weights=weights, k=1)[0]
                    move_tuple = (tuple(chosen["move"][0]), tuple(chosen["move"][1]), None)
                    abs_score = chosen['score']
                    rel_score = abs_score if self.color == 'white' else -abs_score
                    self._report_log(f"  > {self.bot_name} (Book): {chosen['san']}")
                    self._report_eval(rel_score, "Book")
                    self.comm_queue.put(('pv', abs_score, "Book", [chosen['san']], [move_tuple]))
                    self._report_move(move_tuple)
                    return

            root_moves = get_all_legal_moves(self.board, self.color)
            if not root_moves:
                self._report_move(None)
                return

            if len(root_moves) == 1:
                self._report_log(f"  > {self.bot_name} (Forced): {self._format_move(self.board, root_moves[0])}")
                self.comm_queue.put(('pv', 0, "Forced", [self._format_move(self.board, root_moves[0])], [root_moves[0]]))
                self._report_move(root_moves[0])
                return

            best_move_overall  = root_moves[0]
            prev_iter_score    = None
            prev_iter_duration = None
            total_nodes        = 0
            root_hash          = board_hash(self.board, self.color)

            search_start_time = time.time()
            if self.time_left is not None and self.increment is not None:
                optimum_time, max_time = self._search_time_budget(self.time_left, self.increment)
                self.stop_time = search_start_time + max_time
                target_depth = 64
            else:
                self.stop_time = None
                optimum_time = float('inf')
                max_time = float('inf')
                target_depth = self.search_depth

            for current_depth in range(1, target_depth + 1):
                iter_start_time = time.time()
                best_score_this_iter, best_move_this_iter = self._run_depth_iteration(
                    current_depth, root_moves, root_hash, best_move_overall, prev_iter_score=prev_iter_score)

                if self.cancellation_event.is_set():
                    raise SearchCancelledException()

                if self.stop_time and time.time() > self.stop_time:
                    best_move_overall = best_move_this_iter
                    break

                best_move_overall = best_move_this_iter
                prev_iter_score   = best_score_this_iter
                total_nodes      += self.nodes_searched
                iter_duration     = time.time() - iter_start_time
                knps              = (self.nodes_searched / iter_duration / 1000) if iter_duration > 0 else 0

                eval_for_ui = best_score_this_iter if self.color == 'white' else -best_score_this_iter
                tt_str = f", TT={int((self.tt_filled / self.TT_SIZE) * 1000)}/1000" if getattr(self, 'show_tt_fullness', False) else ""
                self._report_log(f"  > {self.bot_name} (D{current_depth}): {self._format_move(self.board, best_move_this_iter)}, Eval={eval_for_ui/100:+.2f}, NodesTotal={total_nodes}, KNPS={knps:.1f}{tt_str}, Time={iter_duration:.2f}s")
                self._report_eval(best_score_this_iter, current_depth)

                pv_str, pv_raw = self._get_pv_data(current_depth, best_move_this_iter)
                self.comm_queue.put(('pv', eval_for_ui, current_depth, pv_str, pv_raw))

                if best_score_this_iter > self.MATE_SCORE - 2000: break

                if self.stop_time:
                    time_used = time.time() - search_start_time
                    if time_used > optimum_time:
                        break

                    if prev_iter_duration and prev_iter_duration > 0:
                        effective_branching = iter_duration / prev_iter_duration
                        effective_branching = max(1.5, min(effective_branching, 6.0))
                    else:
                        effective_branching = 4.0

                    predicted_next_duration = iter_duration * effective_branching
                    time_remaining_to_max   = self.stop_time - time.time()

                    if predicted_next_duration > time_remaining_to_max * 0.85:
                        break

                prev_iter_duration = iter_duration

            self._report_move(best_move_overall)
        except SearchCancelledException:
            if self.cancellation_event.is_set():
                self._report_move(None)
            else:
                self._report_move(best_move_overall)

    def ponder_indefinitely(self):
        try:
            self.stop_time = None
            self._age_history_table()
            if is_insufficient_material(self.board): return

            root_moves = get_all_legal_moves(self.board, self.color)
            if not root_moves: return

            best_move_overall = root_moves[0]
            root_hash         = board_hash(self.board, self.color)
            prev_iter_score   = None
            total_nodes       = 0

            for current_depth in range(1, 100):
                if self.cancellation_event.is_set(): raise SearchCancelledException()
                iter_start_time = time.time()
                best_score_this_iter, best_move_this_iter = self._run_depth_iteration(
                    current_depth, root_moves, root_hash, best_move_overall,
                    prev_iter_score=prev_iter_score)

                if not self.cancellation_event.is_set():
                    best_move_overall = best_move_this_iter
                    prev_iter_score   = best_score_this_iter
                    total_nodes      += self.nodes_searched
                    iter_duration     = time.time() - iter_start_time
                    knps              = (self.nodes_searched / iter_duration / 1000) if iter_duration > 0 else 0

                    eval_for_ui = best_score_this_iter if self.color == 'white' else -best_score_this_iter
                    tt_str = f", TT={int((self.tt_filled / self.TT_SIZE) * 1000)}/1000" if getattr(self, 'show_tt_fullness', False) else ""
                    self._report_log(f"  > {self.bot_name} (D{current_depth}): {self._format_move(self.board, best_move_this_iter)}, Eval={eval_for_ui/100:+.2f}, NodesTotal={total_nodes}, KNPS={knps:.1f}{tt_str}, Time={iter_duration:.2f}s")
                    self._report_eval(best_score_this_iter, current_depth)

                    pv_str, pv_raw = self._get_pv_data(current_depth, best_move_this_iter)
                    self.comm_queue.put(('pv', eval_for_ui, current_depth, pv_str, pv_raw))
                else:
                    raise SearchCancelledException()
        except SearchCancelledException:
            pass

    def _search_at_depth(self, depth, root_moves, root_hash, pv_move, alpha_floor=None, aspiration_window=None):
        self.nodes_searched    = 0
        self.used_heuristic_eval = False
        self.tb_hits           = 0

        if alpha_floor is not None:
            best_score_this_iter  = alpha_floor
            best_move_this_iter   = pv_move if pv_move in root_moves else (root_moves[0] if root_moves else None)
            alpha = alpha_floor
            beta  = float('inf')
        elif aspiration_window is not None:
            best_score_this_iter, best_move_this_iter = -float('inf'), None
            alpha, beta = aspiration_window
        else:
            best_score_this_iter, best_move_this_iter = -float('inf'), None
            alpha = -float('inf')
            beta  =  float('inf')

        orig_alpha = alpha
        orig_beta = beta

        ordered_root_moves = self.order_moves(self.board, root_moves, 0, pv_move, self.color)
        board = self.board

        for move in ordered_root_moves:
            if self.cancellation_event.is_set(): raise SearchCancelledException()

            promo      = move[2] if len(move) > 2 and move[2] is not None else Queen
            record     = board.make_move_track(move[0], move[1], promo)
            child_hash = incremental_hash(root_hash, record)

            search_path = {root_hash}
            try:
                mp = record[2]
                next_prev_tuple = (move, mp.z_idx)

                if alpha_floor is not None:
                    probe_score = -self.negamax(
                        board, depth - 1, -(alpha_floor + 1), -alpha_floor,
                        self.opponent_color, 1, search_path,
                        current_hash=child_hash, prev_move_tuple=next_prev_tuple)
                    if probe_score <= alpha_floor:
                        continue
                    score = -self.negamax(
                        board, depth - 1, -beta, -alpha,
                        self.opponent_color, 1, search_path,
                        current_hash=child_hash, prev_move_tuple=next_prev_tuple)
                else:
                    score = -self.negamax(
                        board, depth - 1, -beta, -alpha,
                        self.opponent_color, 1, search_path,
                        current_hash=child_hash, prev_move_tuple=next_prev_tuple)
            finally:
                board.unmake_move(record)

            if score > best_score_this_iter:
                best_score_this_iter = score
                best_move_this_iter  = move
            if best_score_this_iter > alpha:
                alpha = best_score_this_iter

        if best_move_this_iter is not None:
            if best_score_this_iter <= orig_alpha:
                tt_flag = TT_FLAG_UPPERBOUND
            elif best_score_this_iter >= orig_beta:
                tt_flag = TT_FLAG_LOWERBOUND
            else:
                tt_flag = TT_FLAG_EXACT
            self._store_tt(root_hash, best_score_this_iter, depth, tt_flag, best_move_this_iter)

        return best_score_this_iter, best_move_this_iter

    def negamax(self, board, depth, alpha, beta, turn, ply, search_path, current_hash=None, prev_move_tuple=None, extensions=0):
        self.nodes_searched += 1
        if (self.nodes_searched & self.time_check_mask) == 0:
            if self.cancellation_event.is_set() or (self.stop_time and time.time() > self.stop_time):
                raise SearchCancelledException()

        total_pieces = len(board.white_pieces) + len(board.black_pieces)

        hash_val = current_hash if current_hash is not None else board_hash(board, turn)
        if ply > 0:
            if hash_val in self.position_counts:
                return self.DRAW_SCORE
            if hash_val in search_path:
                return self.DRAW_SCORE

        if is_insufficient_material(board) or board.halfmove_clock >= 100:
            return self.DRAW_SCORE

        original_alpha = alpha
        tt_idx = self._tt_probe(hash_val)
        hash_move = self.tt_moves[tt_idx] if tt_idx != -1 else None

        if ply > 0 and tt_idx != -1 and self.tt_depths[tt_idx] >= depth:
            tt_score = self.tt_scores[tt_idx]
            if tt_score >  self.MATE_SCORE - 1000: tt_score -= ply
            elif tt_score < -self.MATE_SCORE + 1000: tt_score += ply

            self.used_heuristic_eval = True

            tt_flag = self.tt_flags[tt_idx]
            if tt_flag == TT_FLAG_EXACT:
                return tt_score
            elif tt_flag == TT_FLAG_LOWERBOUND:
                if tt_score > alpha: alpha = tt_score
            elif tt_flag == TT_FLAG_UPPERBOUND:
                if tt_score < beta: beta = tt_score
            if alpha >= beta: return tt_score

        if depth <= 0: return self.qsearch(board, alpha, beta, turn, ply, current_hash=hash_val)

        opponent_turn    = 'black' if turn == 'white' else 'white'
        is_in_check_flag = is_in_check(board, turn)
        static_eval      = None

        if is_in_check_flag and ply < self.MAX_EXTENSION_DEPTH:
            depth      += 1
            extensions += 1

        path_added = False
        if hash_val not in search_path:
            search_path.add(hash_val)
            path_added = True

        try:
            if (self.USE_REVERSE_FUTILITY_PRUNING and depth <= self.RFP_MAX_DEPTH and
                    not is_in_check_flag and ply > 0 and abs(beta) < self.MATE_SCORE - 1000
                    and total_pieces > 6):
                static_eval = self._peek_eval_tt(hash_val)
                if static_eval is not None:
                    rfp_margin = self.RFP_MARGIN_PER_DEPTH * depth
                    if static_eval - rfp_margin >= beta:
                        return static_eval - rfp_margin

            if (self.USE_NULL_MOVE_PRUNING and depth >= self.NMP_MIN_DEPTH and
                    ply > 0 and not is_in_check_flag and abs(beta) < self.MATE_SCORE - 1000
                    and total_pieces > 6):
                pc = board.piece_counts_z
                if (pc['white'][1] + pc['white'][2] + pc['white'][3] + pc['white'][4] > 0 and
                        pc['black'][1] + pc['black'][2] + pc['black'][3] + pc['black'][4] > 0):
                    self.used_heuristic_eval = True
                    if static_eval is None:
                        static_eval = self._get_cached_static_eval(board, turn, hash_val)
                    if static_eval >= beta:
                        reduction = self.NMP_BASE_REDUCTION + (depth // self.NMP_DEPTH_DIVISOR)
                        null_hash = hash_val ^ ZOBRIST_TURN
                        saved_ep = board.ep_square
                        if saved_ep:
                            board.ep_square = None
                            from EngineRuntime import ZOBRIST_EP
                            null_hash ^= ZOBRIST_EP[saved_ep[1]]
                        try:
                            score = -self.negamax(board, depth - 1 - reduction, -beta, -beta + 1,
                                                opponent_turn, ply + 1, search_path,
                                                null_hash, None, extensions)
                        finally:
                            board.ep_square = saved_ep
                        if score >= beta: 
                            return score if score < self.MATE_SCORE - 1000 else beta

            futility_prune = False
            if (self.USE_FUTILITY_PRUNING and depth == 1 and not is_in_check_flag and
                    abs(alpha) < self.MATE_SCORE - 1000 and total_pieces > 6):
                self.used_heuristic_eval = True
                if static_eval is None:
                    static_eval = self._get_cached_static_eval(board, turn, hash_val)
                if static_eval + self.FUTILITY_MARGIN < alpha:
                    futility_prune = True

            legal_moves = get_all_legal_moves(board, turn)

            if self.USE_IIR and depth >= self.IIR_MIN_DEPTH and not hash_move and not is_in_check_flag:
                depth -= 1
            
            if prev_move_tuple:
                (pr1, pc1), (pr2, pc2) = prev_move_tuple[0][:2]
                c_move = self.counter_moves[0 if turn == 'white' else 1][pr1 * 8 + pc1][pr2 * 8 + pc2]
            else:
                c_move = None

            ordered_entries = self.order_moves(board, legal_moves, ply, hash_move, turn,
                                            return_meta=True, counter_move=c_move, prev_move_tuple=prev_move_tuple)
            best_move_for_node = None
            legal_moves_count  = 0
            quiet_moves_tried  = []
            history_table      = self.history_heuristic_table[0 if turn == 'white' else 1]
            best_score         = -float('inf')

            for move, meta in ordered_entries:
                is_good_tactic, moving_piece = meta
                f_sq = move[0][0] * 8 + move[0][1]
                t_sq = move[1][0] * 8 + move[1][1]

                promo      = move[2] if len(move) > 2 and move[2] is not None else Queen
                record     = board.make_move_track(move[0], move[1], promo)
                child_hash = incremental_hash(hash_val, record)

                legal_moves_count += 1
                if not is_good_tactic: quiet_moves_tried.append((move, moving_piece))

                if futility_prune and not is_good_tactic and legal_moves_count > 1:
                    if not is_in_check(board, opponent_turn):
                        board.unmake_move(record)
                        continue

                reduction = 0
                is_castling = (moving_piece.z_idx == 5 and abs(move[1][1] - move[0][1]) == 2)
                if (depth >= self.LMR_DEPTH_THRESHOLD and
                        legal_moves_count > self.LMR_MOVE_COUNT_THRESHOLD and
                        not is_in_check_flag and not is_good_tactic and not is_castling):
                    reduction = 1 + (depth // 6) + (legal_moves_count // 12)

                    # Avoid list allocations in the hot loop
                    is_killer = False
                    if ply < len(self.killer_moves):
                        k0, k1 = self.killer_moves[ply]
                        is_killer = (k0 is not None and move[:2] == k0[:2]) or \
                                    (k1 is not None and move[:2] == k1[:2])

                    if is_killer or (c_move and move[:2] == c_move[:2]):
                        reduction -= 1
                        
                    # 10_000 correctly matches the 2,000,000 gravity table scale
                    if history_table[f_sq][t_sq] > 10_000:
                        reduction -= 1
                        
                    reduction = max(0, min(reduction, depth - 2))

                search_depth_child = depth - 1 - reduction
                next_prev_tuple = (move, moving_piece.z_idx)

                if legal_moves_count == 1:
                    score = -self.negamax(board, search_depth_child, -beta, -alpha,
                                        opponent_turn, ply + 1, search_path, child_hash, next_prev_tuple, extensions)
                else:
                    score = -self.negamax(board, search_depth_child, -(alpha + 1), -alpha,
                                        opponent_turn, ply + 1, search_path, child_hash, next_prev_tuple, extensions)
                    if score > alpha:
                        if reduction > 0 or score < beta:
                            score = -self.negamax(board, depth - 1, -beta, -alpha,
                                                opponent_turn, ply + 1, search_path, child_hash, next_prev_tuple, extensions)

                board.unmake_move(record)

                if score > best_score:
                    best_score = score
                    if score > alpha:
                        alpha, best_move_for_node = score, move

                if best_score >= beta:
                    if not is_good_tactic:
                        if ply < len(self.killer_moves) and self.killer_moves[ply][0] != move:
                            self.killer_moves[ply][1], self.killer_moves[ply][0] = \
                                self.killer_moves[ply][0], move
                        if prev_move_tuple:
                            (pr1, pc1), (pr2, pc2) = prev_move_tuple[0][:2]
                            self.counter_moves[0 if turn == 'white' else 1][pr1 * 8 + pc1][pr2 * 8 + pc2] = move
                        
                        if moving_piece:
                            c_idx = 0 if turn == 'white' else 1
                            bonus = depth * depth
                            ht    = self.history_heuristic_table[c_idx]
                            
                            ht[f_sq][t_sq] += bonus - (ht[f_sq][t_sq] * bonus) // 2_000_000
                            
                            if prev_move_tuple:
                                prev_move, prev_pt_idx = prev_move_tuple
                                pr, pc = prev_move[1]
                                prev_to_sq  = pr * 8 + pc
                                mp_idx      = moving_piece.z_idx
                                
                                ch_table = self.continuation_history[c_idx][prev_pt_idx][prev_to_sq][mp_idx]
                                ch_table[t_sq] += bonus - (ch_table[t_sq] * bonus) // 64_000
                            
                            for f_move, f_mp in quiet_moves_tried:
                                if f_move != move:
                                    (fr1, fc1), (fr2, fc2) = f_move[:2]
                                    ff = fr1 * 8 + fc1
                                    ft = fr2 * 8 + fc2
                                    ht[ff][ft] -= bonus + (ht[ff][ft] * bonus) // 2_000_000
                                    
                                    if prev_move_tuple:
                                        prev_move, prev_pt_idx = prev_move_tuple
                                        pr, pc = prev_move[1]
                                        prev_to_sq = pr * 8 + pc
                                        f_mp_idx = f_mp.z_idx
                                        ch_table = self.continuation_history[c_idx][prev_pt_idx][prev_to_sq][f_mp_idx]
                                        ch_table[ft] -= bonus + (ch_table[ft] * bonus) // 64_000

                    sto = best_score
                    if sto >  self.MATE_SCORE - 1000: sto = best_score + ply
                    elif sto < -self.MATE_SCORE + 1000: sto = best_score - ply
                    self._store_tt(hash_val, sto, depth, TT_FLAG_LOWERBOUND, move)
                    return best_score

            if legal_moves_count == 0:
                return -self.MATE_SCORE + ply

            sto = best_score
            if sto >  self.MATE_SCORE - 1000: sto = best_score + ply
            elif sto < -self.MATE_SCORE + 1000: sto = best_score - ply
            flag = TT_FLAG_EXACT if best_score > original_alpha else TT_FLAG_UPPERBOUND
            self._store_tt(hash_val, sto, depth, flag, best_move_for_node)
            return best_score

        finally:
            if path_added: search_path.discard(hash_val)

    def qsearch(self, board, alpha, beta, turn, ply, current_hash=None):
        self.nodes_searched += 1
        if (self.nodes_searched & self.time_check_mask) == 0:
            if self.cancellation_event.is_set() or (self.stop_time and time.time() > self.stop_time):
                raise SearchCancelledException()

        hash_val = current_hash if current_hash is not None else board_hash(board, turn)
        if ply > 0 and hash_val in self.position_counts:
            return self.DRAW_SCORE

        tt_idx = self._tt_probe(hash_val)
        if tt_idx != -1:
            tt_score = self.tt_scores[tt_idx]
            if tt_score > self.MATE_SCORE - 1000: tt_score -= ply
            elif tt_score < -self.MATE_SCORE + 1000: tt_score += ply
            tt_flag = self.tt_flags[tt_idx]
            if tt_flag == TT_FLAG_EXACT: return tt_score
            if tt_flag == TT_FLAG_LOWERBOUND and tt_score >= beta: return tt_score
            if tt_flag == TT_FLAG_UPPERBOUND and tt_score <= alpha: return tt_score

        if is_insufficient_material(board): return self.DRAW_SCORE

        if ply >= self.MAX_Q_SEARCH_DEPTH:
            self.used_heuristic_eval = True
            return self._get_cached_static_eval(board, turn, hash_val)

        self.used_heuristic_eval = True
        is_in_check_flag = is_in_check(board, turn)
        best_score = -float('inf')
        opponent_turn = 'black' if turn == 'white' else 'white'
        tt_move = self.tt_moves[tt_idx] if tt_idx != -1 else None
        grid = board.grid

        if is_in_check_flag:
            candidate_moves = get_all_legal_moves(board, turn)
            scored_moves = []
            for move in candidate_moves:
                (r1, c1), (r2, c2) = move[:2]
                moving_piece = grid[r1][c1]
                target_piece = grid[r2][c2]
                swing, _ = fast_approximate_material_swing(board, move, moving_piece, target_piece, ORDERING_VALUES)
                score = swing * 10 - moving_piece.z_idx
                if tt_move and move[:2] == tt_move[:2]: score += 1_000_000
                scored_moves.append((score, move))
            scored_moves.sort(key=itemgetter(0), reverse=True)

            legal_moves_count = 0
            for score, move in scored_moves:
                promo = move[2] if len(move) > 2 and move[2] is not None else Queen
                record = board.make_move_track(move[0], move[1], promo)
                legal_moves_count += 1
                child_hash = incremental_hash(hash_val, record)
                search_score = -self.qsearch(board, -beta, -alpha, opponent_turn, ply + 1, current_hash=child_hash)
                board.unmake_move(record)

                if search_score > best_score:
                    best_score = search_score
                    if search_score > alpha: alpha = search_score
                if best_score >= beta: return best_score

            if legal_moves_count == 0:
                return -self.MATE_SCORE + ply
            return best_score

        # Not in check: Generate ONLY captures and tactical promotions (2x speedup!)
        stand_pat = self._get_cached_static_eval(board, turn, hash_val)
        best_score = stand_pat
        if stand_pat >= beta: return stand_pat
        if stand_pat > alpha: alpha = stand_pat

        promising_moves = get_all_legal_captures(board, turn)
        scored_moves = []

        for move in promising_moves:
            (r1, c1), (r2, c2) = move[:2]
            moving_piece = grid[r1][c1]
            target_piece = grid[r2][c2]

            swing, is_tactic = fast_approximate_material_swing(board, move, moving_piece, target_piece, ORDERING_VALUES)
            if not is_tactic: continue
            if stand_pat + swing + 200 < alpha: continue

            score = swing * 10 - moving_piece.z_idx
            if tt_move and move[:2] == tt_move[:2]: score += 1_000_000
            scored_moves.append((score, move))

        scored_moves.sort(key=itemgetter(0), reverse=True)

        for score, move in scored_moves:
            promo = move[2] if len(move) > 2 and move[2] is not None else Queen
            record = board.make_move_track(move[0], move[1], promo)
            child_hash = incremental_hash(hash_val, record)
            search_score = -self.qsearch(board, -beta, -alpha, opponent_turn, ply + 1, current_hash=child_hash)
            board.unmake_move(record)

            if search_score > best_score:
                best_score = search_score
                if search_score > alpha: alpha = search_score
            if best_score >= beta: return best_score

        return best_score

    def order_moves(self, board, moves, ply, hash_move, turn, return_meta=False, counter_move=None, prev_move_tuple=None):
        if not moves: return []
        scored_moves = []
        killers = self.killer_moves[ply] if ply < len(self.killer_moves) else [None, None]
        c_idx = 0 if turn == 'white' else 1
        history_table = self.history_heuristic_table[c_idx]

        grid = board.grid
        k1 = killers[0] if killers else None
        k2 = killers[1] if killers else None

        for move in moves:
            (r1, c1), (r2, c2) = move[:2]
            moving_piece = grid[r1][c1]
            target_piece = grid[r2][c2]

            swing, is_good_tactic = fast_approximate_material_swing(board, move, moving_piece, target_piece, ORDERING_VALUES)

            if hash_move and move[:2] == hash_move[:2]:
                score = self.BONUS_PV_MOVE
            elif target_piece is not None or is_good_tactic:
                if swing > 0:
                    score = self.BONUS_CAPTURE + (swing * 100) - moving_piece.z_idx
                elif swing == 0:
                    score = 6_000_000 - moving_piece.z_idx
                else:
                    score = -1_000_000 + swing  # Bad capture: rank below quiet moves
            elif k1 and move[:2] == k1[:2]:
                score = self.BONUS_KILLER_1
            elif k2 and move[:2] == k2[:2]:
                score = self.BONUS_KILLER_2
            elif counter_move and move[:2] == counter_move[:2]:
                score = 2_000_000
            else:
                score = history_table[r1 * 8 + c1][r2 * 8 + c2]
                if prev_move_tuple and moving_piece:
                    prev_move, prev_pt_idx = prev_move_tuple
                    pr, pc = prev_move[1]
                    prev_to_sq = pr * 8 + pc
                    score += self.continuation_history[c_idx][prev_pt_idx][prev_to_sq][moving_piece.z_idx][r2 * 8 + c2]

            scored_moves.append((score, move, is_good_tactic, moving_piece))

        scored_moves.sort(key=itemgetter(0), reverse=True)

        if return_meta:
            return [(item[1], (item[2], item[3])) for item in scored_moves]
        else:
            return [item[1] for item in scored_moves]

    def evaluate_board(self, board, turn_to_move):
        if is_insufficient_material(board):
            return self.DRAW_SCORE

        pc_wz = board.piece_counts_z['white']
        pc_bz = board.piece_counts_z['black']

        scores_mg = [0, 0]
        scores_eg = [0, 0]

        phase_material_score = (
            (pc_wz[1] + pc_bz[1]) * MG_PIECE_VALUES[Knight] +
            (pc_wz[2] + pc_bz[2]) * MG_PIECE_VALUES[Bishop] +
            (pc_wz[3] + pc_bz[3]) * MG_PIECE_VALUES[Rook] +
            (pc_wz[4] + pc_bz[4]) * MG_PIECE_VALUES[Queen]
        )

        piece_lists = [board.white_pieces, board.black_pieces]
        grid = board.grid

        w_pawn_files = [0] * 8
        b_pawn_files = [0] * 8
        for p in board.white_pieces:
            if p.z_idx == 0: w_pawn_files[p.pos[1]] += 1
        for p in board.black_pieces:
            if p.z_idx == 0: b_pawn_files[p.pos[1]] += 1

        for color_idx in (0, 1):
            pieces   = piece_lists[color_idx]
            is_white = (color_idx == 0)
            my_pawn_files  = w_pawn_files if is_white else b_pawn_files
            opp_pawn_files = b_pawn_files if is_white else w_pawn_files
            pst_mg   = FLAT_PST_MG_WHITE if is_white else FLAT_PST_MG_BLACK
            pst_eg   = FLAT_PST_EG_WHITE if is_white else FLAT_PST_EG_BLACK
            home_rank = 7 if is_white else 0
            seventh_rank = 1 if is_white else 6

            for piece in pieces:
                z    = piece.z_idx
                r, c = piece.pos
                sq   = r * 8 + c

                scores_mg[color_idx] += pst_mg[z][sq]
                scores_eg[color_idx] += pst_eg[z][sq]

                # 1. Pawns (Passed & Defended)
                if z == 0:
                    advancement = (7 - r) if is_white else r

                    # Passed pawn
                    is_passed = True
                    for fc in range(max(0, c - 1), min(8, c + 2)):
                        opp_pieces = board.black_pieces if is_white else board.white_pieces
                        for opp_p in opp_pieces:
                            if opp_p.z_idx == 0 and opp_p.pos[1] == fc:
                                if (is_white and opp_p.pos[0] < r) or (not is_white and opp_p.pos[0] > r):
                                    is_passed = False
                                    break
                        if not is_passed: break
                    if is_passed and advancement < len(self.EVAL_PASSED_PAWN_RANK):
                        scores_eg[color_idx] += self.EVAL_PASSED_PAWN_RANK[advancement]

                    # Defended by friendly pawn
                    p_def_r = r + 1 if is_white else r - 1
                    if 0 <= p_def_r < 8:
                        if (c > 0 and grid[p_def_r][c - 1] and grid[p_def_r][c - 1].z_idx == 0 and grid[p_def_r][c - 1].color == piece.color) or \
                           (c < 7 and grid[p_def_r][c + 1] and grid[p_def_r][c + 1].z_idx == 0 and grid[p_def_r][c + 1].color == piece.color):
                            scores_mg[color_idx] += self.EVAL_PAWN_DEFENDED

                # 2. Minor Piece Development
                elif z == 1 or z == 2:
                    if r != home_rank:
                        scores_mg[color_idx] += self.EVAL_DEV_BONUS

                # 3. Rooks (7th rank & Open files)
                elif z == 3:
                    if r == seventh_rank:
                        scores_mg[color_idx] += self.EVAL_ROOK_ON_7TH
                        scores_eg[color_idx] += self.EVAL_ROOK_ON_7TH

                    if my_pawn_files[c] == 0:
                        if opp_pawn_files[c] == 0:
                            scores_mg[color_idx] += self.EVAL_ROOK_OPEN_FILE
                            scores_eg[color_idx] += self.EVAL_ROOK_OPEN_FILE
                        else:
                            scores_mg[color_idx] += self.EVAL_ROOK_SEMI_OPEN
                            scores_eg[color_idx] += self.EVAL_ROOK_SEMI_OPEN

                # 4. Castled King Pawn Shield
                elif z == 5:
                    if (is_white and r == 7 and (c == 6 or c == 2)) or (not is_white and r == 0 and (c == 6 or c == 2)):
                        shield_r = 6 if is_white else 1
                        shield_intact = 0
                        for sc in range(max(0, c - 1), min(8, c + 2)):
                            sp = grid[shield_r][sc]
                            if sp and sp.z_idx == 0 and sp.color == piece.color:
                                shield_intact += 1
                        scores_mg[color_idx] += shield_intact * self.EVAL_PAWN_SHIELD

            # Bishop pair
            if board.piece_counts_z['white' if is_white else 'black'][2] >= 2:
                scores_mg[color_idx] += self.EVAL_BISHOP_PAIR
                scores_eg[color_idx] += self.EVAL_BISHOP_PAIR

            # Castling rights retention
            c_rights = board.castling_rights
            if is_white and (c_rights & (CASTLE_WK | CASTLE_WQ)):
                scores_mg[color_idx] += self.EVAL_CASTLING_RIGHTS
            elif not is_white and (c_rights & (CASTLE_BK | CASTLE_BQ)):
                scores_mg[color_idx] += self.EVAL_CASTLING_RIGHTS

            # Doubled pawns
            for count in my_pawn_files:
                if count > 1:
                    penalty = (count - 1) * 15
                    scores_mg[color_idx] -= penalty
                    scores_eg[color_idx] -= penalty

        phase     = min(256, (phase_material_score * 256) // INITIAL_PHASE_MATERIAL) if INITIAL_PHASE_MATERIAL > 0 else 0
        inv_phase = 256 - phase

        mg_score    = scores_mg[0] - scores_mg[1]
        eg_score    = scores_eg[0] - scores_eg[1]
        final_score = (mg_score * phase + eg_score * inv_phase) >> 8

        eval_side = final_score if turn_to_move == 'white' else -final_score
        return eval_side + self.TEMPO_BONUS


# --- Standard Chess Piece-Square Tables ---
pawn_pst = [
    [  0,   0,   0,   0,   0,   0,   0,   0],
    [ 50,  50,  50,  50,  50,  50,  50,  50],
    [ 10,  10,  20,  30,  30,  20,  10,  10],
    [  5,   5,  15,  35,  35,  15,   5,   5],
    [  0,   0,  10,  30,  30,  10,   0,   0],
    [  5,  -5, -10,   0,   0, -10,  -5,   5],
    [  5,  10,  10, -25, -25,  10,  10,   5],
    [  0,   0,   0,   0,   0,   0,   0,   0]
]

pawn_endgame_pst = [
    [  0,   0,   0,   0,   0,   0,   0,   0],
    [ 80,  80,  80,  80,  80,  80,  80,  80],
    [ 50,  50,  50,  50,  50,  50,  50,  50],
    [ 30,  30,  30,  35,  35,  30,  30,  30],
    [ 20,  20,  20,  25,  25,  20,  20,  20],
    [ 10,  10,  10,  15,  15,  10,  10,  10],
    [  5,   5,   5,   5,   5,   5,   5,   5],
    [  0,   0,   0,   0,   0,   0,   0,   0]
]

knight_pst = [
    [-50, -40, -30, -30, -30, -30, -40, -50],
    [-40, -20,   0,   0,   0,   0, -20, -40],
    [-30,   0,  10,  15,  15,  10,   0, -30],
    [-30,   5,  15,  20,  20,  15,   5, -30],
    [-30,   0,  15,  20,  20,  15,   0, -30],
    [-30,   5,  10,  15,  15,  10,   5, -30],
    [-40, -20,   0,   5,   5,   0, -20, -40],
    [-50, -40, -30, -30, -30, -30, -40, -50]
]

bishop_pst = [
    [-20, -10, -10, -10, -10, -10, -10, -20],
    [-10,   0,   0,   0,   0,   0,   0, -10],
    [-10,   0,   5,  10,  10,   5,   0, -10],
    [-10,   5,   5,  10,  10,   5,   5, -10],
    [-10,   0,  10,  10,  10,  10,   0, -10],
    [-10,  10,  10,  10,  10,  10,  10, -10],
    [-10,   5,   0,   0,   0,   0,   5, -10],
    [-20, -10, -10, -10, -10, -10, -10, -20]
]

rook_pst = [
    [  0,   0,   0,   0,   0,   0,   0,   0],
    [  5,  10,  10,  10,  10,  10,  10,   5],
    [ -5,   0,   0,   0,   0,   0,   0,  -5],
    [ -5,   0,   0,   0,   0,   0,   0,  -5],
    [ -5,   0,   0,   0,   0,   0,   0,  -5],
    [ -5,   0,   0,   0,   0,   0,   0,  -5],
    [ -5,   0,   0,   0,   0,   0,   0,  -5],
    [  0,   0,   0,   5,   5,   0,   0,   0]
]

queen_pst = [
    [-20, -10, -10,  -5,  -5, -10, -10, -20],
    [-10,   0,   0,   0,   0,   0,   0, -10],
    [-10,   0,   5,   5,   5,   5,   0, -10],
    [ -5,   0,   5,   5,   5,   5,   0,  -5],
    [  0,   0,   5,   5,   5,   5,   0,  -5],
    [-10,   5,   5,   5,   5,   5,   0, -10],
    [-10,   0,   5,   0,   0,   0,   0, -10],
    [-20, -10, -10,  -5,  -5, -10, -10, -20]
]

king_midgame_pst = [
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-20, -30, -30, -40, -40, -30, -20, -20],
    [-10, -20, -20, -20, -20, -20, -20, -10],
    [ 20,  20,   5,   5,   5,   5,  20,  20],
    [ 20,  25,  15,  15,  15,  15,  25,  20]
]

king_endgame_pst = [
    [-50, -40, -30, -20, -20, -30, -40, -50],
    [-30, -20, -10,   0,   0, -10, -20, -30],
    [-30, -10,  20,  30,  30,  20, -10, -30],
    [-30, -10,  30,  40,  40,  30, -10, -30],
    [-30, -10,  30,  40,  40,  30, -10, -30],
    [-30, -10,  20,  30,  30,  20, -10, -30],
    [-30, -30,   0,   0,   0,   0, -30, -30],
    [-50, -30, -30, -30, -30, -30, -30, -50]
]

PIECE_SQUARE_TABLES = {
    Pawn:           pawn_pst,
    'pawn_endgame': pawn_endgame_pst,
    Knight:         knight_pst,
    Bishop:         bishop_pst,
    Rook:           rook_pst,
    Queen:          queen_pst,
    'king_midgame': king_midgame_pst,
    'king_endgame': king_endgame_pst,
}

FLAT_PST_MG_WHITE, FLAT_PST_MG_BLACK, FLAT_PST_EG_WHITE, FLAT_PST_EG_BLACK = build_flat_pst_tables(
    MG_PIECE_VALUES, EG_PIECE_VALUES, PIECE_SQUARE_TABLES
)

# MoveChecker.py (v2 - Use full fens)

import os
import time
import threading
import multiprocessing as mp
import tkinter as tk
from tkinter import ttk, messagebox
from GameLogic import get_all_legal_moves, format_move_san, Queen
from EngineRuntime import board_to_fen

PARALLEL_MIN_DEPTH = 3

def _perft_rec(board, turn, depth):
    if depth == 0:
        return 1
    if depth == 1:
        return len(get_all_legal_moves(board, turn))
    total = 0
    opp = 'black' if turn == 'white' else 'white'
    for m in get_all_legal_moves(board, turn):
        promo = m[2] if len(m) > 2 and m[2] is not None else Queen
        rec = board.make_move_track(m[0], m[1], promo)
        total += _perft_rec(board, opp, depth - 1)
        board.unmake_move(rec)
    return total

def _perft_task_wrapper(args):
    child_board, opp_turn, remaining_depth = args
    return _perft_rec(child_board, opp_turn, remaining_depth)

def launch_move_checker_dialog(master, board, turn, depth, colors, is_start_pos=False):
    # Canonical Chess Programming Wiki (CPW) reference Perft positions
    # Keyed by 4-field normalized FEN: <piece placement> <turn> <castling> <ep>
    PERFT_POSITIONS = {
        # Position 1 — Initial Standard Starting Position
        "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -": {
            "name": "Start Position",
            "counts": {
                1: 20, 2: 400, 3: 8902, 4: 197281, 5: 4865609,
                6: 119060324, 7: 3195901860, 8: 84997849941,
            }
        },
        # Position 2 — Kiwipete (Peter Ellis) - Castling & Pin Stress Test
        "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq -": {
            "name": "Position 2 (Kiwipete)",
            "counts": {
                1: 48, 2: 2039, 3: 97862, 4: 4085603, 5: 193690690, 6: 8031647685,
            }
        },
        # Position 3 — Endgame En Passant Discovered Check Torture Test
        "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - -": {
            "name": "Position 3 (EP Discovered Check)",
            "counts": {
                1: 14, 2: 191, 3: 2812, 4: 43238, 5: 674624, 6: 11030083, 7: 178633661,
            }
        },
        # Position 4 — Complex Promotions, Pins & Skewers
        "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq -": {
            "name": "Position 4 (Promotions & Pins)",
            "counts": {
                1: 6, 2: 264, 3: 9467, 4: 422333, 5: 15833292, 6: 706045033,
            }
        },
        # Position 4 Mirrored — Black to Move
        "r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ -": {
            "name": "Position 4 Mirrored (Black)",
            "counts": {
                1: 6, 2: 264, 3: 9467, 4: 422333, 5: 15833292, 6: 706045033,
            }
        },
        # Position 5 — Discovered Checks & Underpromotions
        "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ -": {
            "name": "Position 5 (Discovered Checks)",
            "counts": {
                1: 44, 2: 1486, 3: 62379, 4: 2103487, 5: 89941194,
            }
        },
        # Position 6 — Edwards / Talkchess Middlegame
        "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - -": {
            "name": "Position 6 (Middlegame)",
            "counts": {
                1: 46, 2: 2079, 3: 89890, 4: 3894594, 5: 164075551, 6: 6923051137,
            }
        },
    }

    dialog = tk.Toplevel(master)
    dialog.title(f"Perft Runner (Depth {depth})")
    dialog.configure(bg=colors['bg_dark'])
    dialog.geometry("460x250")
    dialog.resizable(False, False)
    dialog.transient(master)
    dialog.grab_set()

    dialog.update_idletasks()
    mx = master.winfo_x() + (master.winfo_width() - 460) // 2
    my = master.winfo_y() + (master.winfo_height() - 250) // 2
    dialog.geometry(f"460x250+{mx}+{my}")

    ttk.Label(dialog, text=f"Computing Perft Depth {depth}...", style='Header.TLabel').pack(pady=(12, 4))
    status_lbl = ttk.Label(dialog, text="Initializing search...", style='SmallHeader.TLabel')
    status_lbl.pack(pady=2)

    progress_var = tk.DoubleVar(value=0.0)
    progress_bar = ttk.Progressbar(dialog, variable=progress_var, maximum=100.0, length=400)
    progress_bar.pack(pady=8)

    stats_lbl = tk.Label(
        dialog, text="Nodes: 0  |  Time: 0.0s  |  Speed: 0.0 KNPS",
        bg=colors['bg_dark'], fg=colors['text_light'], font=('Courier', 10)
    )
    stats_lbl.pack(pady=4)

    cancel_event = threading.Event()
    pool_holder = {}

    def on_cancel():
        cancel_event.set()
        pool = pool_holder.get('pool')
        if pool:
            try:
                pool.terminate()
                pool.join()
            except Exception:
                pass
        dialog.destroy()

    cancel_btn = ttk.Button(dialog, text="Cancel", command=on_cancel, style='Control.TButton')
    cancel_btn.pack(pady=(6, 0))
    dialog.protocol("WM_DELETE_WINDOW", on_cancel)

    def worker():
        root_moves = get_all_legal_moves(board, turn)
        total_root_moves = len(root_moves)
        if total_root_moves == 0:
            master.after(0, lambda: [dialog.destroy(), messagebox.showinfo("Perft Complete", "No legal moves.")])
            return

        opp = 'black' if turn == 'white' else 'white'
        t0 = time.time()

        sans = [None] * total_root_moves
        child_boards = [None] * total_root_moves
        for idx, m in enumerate(root_moves):
            child = board.clone()
            promo = m[2] if len(m) > 2 and m[2] is not None else Queen
            child.make_move(m[0], m[1], promo)
            sans[idx] = format_move_san(board, child, m)
            child_boards[idx] = child

        divide_results = [None] * total_root_moves
        total_nodes = 0
        completed = 0

        if depth < PARALLEL_MIN_DEPTH:
            for idx in range(total_root_moves):
                if cancel_event.is_set():
                    return
                sub_nodes = _perft_rec(child_boards[idx], opp, depth - 1)
                divide_results[idx] = (sans[idx], root_moves[idx], sub_nodes)
                total_nodes += sub_nodes
                completed += 1
                elapsed = max(0.001, time.time() - t0)
                knps = (total_nodes / elapsed / 1000) if elapsed > 0 else 0
                pct = (completed / total_root_moves) * 100.0
                master.after(0, lambda p=pct, s=sans[idx], i=completed, tot=total_root_moves,
                             n=total_nodes, el=elapsed, k=knps: [
                    progress_var.set(p),
                    status_lbl.config(text=f"Exploring branch {s} ({i}/{tot})..."),
                    stats_lbl.config(text=f"Nodes: {n:,}  |  Time: {el:.1f}s  |  Speed: {k:.1f} KNPS")
                ])
        else:
            num_workers = min(os.cpu_count() or 4, total_root_moves)
            pool = mp.Pool(processes=num_workers)
            pool_holder['pool'] = pool

            tasks = [(child_boards[i], opp, depth - 1) for i in range(total_root_moves)]
            async_results = [pool.apply_async(_perft_task_wrapper, (t,)) for t in tasks]

            for idx, res in enumerate(async_results):
                while not res.ready():
                    if cancel_event.is_set():
                        pool.terminate()
                        pool.join()
                        return
                    time.sleep(0.02)

                sub_nodes = res.get()
                divide_results[idx] = (sans[idx], root_moves[idx], sub_nodes)
                total_nodes += sub_nodes
                completed += 1

                elapsed = max(0.001, time.time() - t0)
                knps = (total_nodes / elapsed / 1000) if elapsed > 0 else 0
                pct = (completed / total_root_moves) * 100.0

                master.after(0, lambda p=pct, s=sans[idx], i=completed, tot=total_root_moves,
                             n=total_nodes, el=elapsed, k=knps: [
                    progress_var.set(p),
                    status_lbl.config(text=f"Exploring branch {s} ({i}/{tot})..."),
                    stats_lbl.config(text=f"Nodes: {n:,}  |  Time: {el:.1f}s  |  Speed: {k:.1f} KNPS")
                ])

            pool.close()
            pool.join()
            pool_holder.pop('pool', None)

        if cancel_event.is_set():
            return

        elapsed = max(0.001, time.time() - t0)
        knps = (total_nodes / elapsed / 1000) if elapsed > 0 else 0
        
        # Match normalized 4-part FEN (<piece placement> <turn> <castling> <ep>)
        full_fen = board_to_fen(board, turn)
        fen_parts = full_fen.split()
        norm_fen = " ".join(fen_parts[:4])
        
        ref_entry = PERFT_POSITIONS.get(norm_fen)
        if not ref_entry:
            # Fallback to piece-placement-only key matching if shorthand was used
            ref_entry = next((v for k, v in PERFT_POSITIONS.items() if k.split()[0] == fen_parts[0]), None)

        pos_name = ref_entry["name"] if ref_entry else "Custom Position"
        expected = ref_entry["counts"].get(depth) if ref_entry else None
        is_pass = (total_nodes == expected) if expected is not None else True

        log_lines = [
            f"\n--- PERFT: {pos_name} (Depth {depth}, Turn: {turn.capitalize()}) ---",
            f"FEN: {full_fen}",
            f"Time: {elapsed:.3f}s | Speed: {knps:.1f} KNPS | Total Nodes: {total_nodes:,}"
        ]
        if expected is not None:
            status_str = "PASS [OK]" if is_pass else f"FAIL [Expected: {expected:,}]"
            log_lines.append(f"Standard Chess Reference Comparison: {status_str}")
        else:
            log_lines.append("No reference table for this position — count unverified.")

        log_lines.append("\nPerft Divide (Branch Leaf Counts):")
        for i, (san, m, cnt) in enumerate(divide_results, 1):
            log_lines.append(f"  {i:2d}. {san.ljust(8)} ({m[0]} -> {m[1]}): {cnt:,}")

        print("\n".join(log_lines))

        def finish_ui():
            try:
                dialog.destroy()
            except Exception:
                pass

            if expected is not None:
                if is_pass:
                    messagebox.showinfo(
                        f"Perft Depth {depth} Passed",
                        f"SUCCESS: {pos_name} Depth {depth} verified!\n\n"
                        f"Total Nodes: {total_nodes:,} / {expected:,}\n"
                        f"Time: {elapsed:.3f}s ({knps:.1f} KNPS)"
                    )
                else:
                    messagebox.showerror(
                        f"Perft Depth {depth} Failed",
                        f"MISMATCH DETECTED: {pos_name} at Depth {depth}!\n\n"
                        f"Actual Nodes: {total_nodes:,}\n"
                        f"Expected: {expected:,}\n\n"
                        f"See console divide log for details."
                    )
            else:
                messagebox.showinfo(
                    f"Perft Depth {depth} Complete",
                    f"Custom Position Perft Complete (Depth {depth}):\n\n"
                    f"Total Nodes: {total_nodes:,}\n"
                    f"Time: {elapsed:.3f}s ({knps:.1f} KNPS)"
                )

        master.after(0, finish_ui)

    threading.Thread(target=worker, daemon=True).start()

# EngineRuntime.py (v1.8 - Allow for 3 tuple)

import glob
import inspect
import json
import multiprocessing as mp
import os
import random
import re
import traceback
from collections import namedtuple

from GameLogic import (
    ROWS, COLS, Pawn, Knight, Bishop, Rook, Queen, King, Board,
    format_move_san, get_all_legal_moves,
)

OPTIONAL_BOT_KWARGS = (
    "time_left",
    "increment",
    "use_opening_book",
    "show_tt_fullness",
)

# ---------------------------------------------------------------------------
# Zobrist hashing
# ---------------------------------------------------------------------------
ZOBRIST_ARRAY  = None
ZOBRIST_TURN   = None
ZOBRIST_CASTLE = None
ZOBRIST_EP     = None

def initialize_zobrist_table():
    global ZOBRIST_ARRAY, ZOBRIST_TURN, ZOBRIST_CASTLE, ZOBRIST_EP
    if ZOBRIST_ARRAY is not None:
        return
    random.seed(42)
    ZOBRIST_ARRAY = [[[[random.getrandbits(64) for _ in range(8)] for _ in range(8)]
                      for _ in range(6)] for _ in range(2)]
    ZOBRIST_TURN   = random.getrandbits(64)
    ZOBRIST_CASTLE = [random.getrandbits(64) for _ in range(16)]
    ZOBRIST_EP     = [random.getrandbits(64) for _ in range(8)]
    random.seed()

initialize_zobrist_table()

def board_hash(board, turn):
    h = 0
    arr = ZOBRIST_ARRAY

    for piece in board.white_pieces:
        r, c = piece.pos
        h ^= arr[0][piece.z_idx][r][c]
    for piece in board.black_pieces:
        r, c = piece.pos
        h ^= arr[1][piece.z_idx][r][c]

    if turn == "black":
        h ^= ZOBRIST_TURN

    h ^= ZOBRIST_CASTLE[board.castling_rights]
    if board.ep_square:
        h ^= ZOBRIST_EP[board.ep_square[1]]
    return h

def incremental_hash(parent_hash, record_tuple):
    start, end, mp_piece, removed, added, old_c, old_ep, _, special, new_c, new_ep = record_tuple
    h = parent_hash ^ ZOBRIST_TURN
    arr = ZOBRIST_ARRAY
    c_idx = 0 if mp_piece.color == "white" else 1

    h ^= arr[c_idx][mp_piece.z_idx][start[0]][start[1]]

    if special == 3 and added:
        promoted_piece = added[0][0]
        h ^= arr[c_idx][promoted_piece.z_idx][end[0]][end[1]]
    elif special != 3:
        h ^= arr[c_idx][mp_piece.z_idx][end[0]][end[1]]

    for p, r, c in removed:
        if p is not None and p is not mp_piece:
            pc_idx = 0 if p.color == "white" else 1
            h ^= arr[pc_idx][p.z_idx][r][c]

    if special == 1:
        sr = start[0]
        if end[1] == 6:
            h ^= arr[c_idx][3][sr][7] ^ arr[c_idx][3][sr][5]
        elif end[1] == 2:
            h ^= arr[c_idx][3][sr][0] ^ arr[c_idx][3][sr][3]

    if old_c != new_c:
        h ^= ZOBRIST_CASTLE[old_c] ^ ZOBRIST_CASTLE[new_c]

    if old_ep != new_ep:
        if old_ep:
            h ^= ZOBRIST_EP[old_ep[1]]
        if new_ep:
            h ^= ZOBRIST_EP[new_ep[1]]

    return h

# ---------------------------------------------------------------------------
# Opening book / FEN helpers
# ---------------------------------------------------------------------------
_CLS_TO_CHAR = {Pawn: "P", Knight: "N", Bishop: "B", Rook: "R", Queen: "Q", King: "K"}
OPENING_BOOK = {}

def board_to_fen(board, turn, fullmove=1):
    fen = ""
    for r in range(ROWS):
        empty = 0
        for c in range(COLS):
            piece = board.grid[r][c]
            if piece is None:
                empty += 1
            else:
                if empty:
                    fen += str(empty)
                    empty = 0
                ch = _CLS_TO_CHAR[type(piece)]
                fen += ch if piece.color == "white" else ch.lower()
        if empty:
            fen += str(empty)
        if r < ROWS - 1:
            fen += "/"

    t_str = " w " if turn == "white" else " b "
    c_str = ""
    if board.castling_rights & 1: c_str += "K"
    if board.castling_rights & 2: c_str += "Q"
    if board.castling_rights & 4: c_str += "k"
    if board.castling_rights & 8: c_str += "q"
    if not c_str: c_str = "-"

    ep_str = "-"
    if board.ep_square:
        ep_str = f"{'abcdefgh'[board.ep_square[1]]}{'87654321'[board.ep_square[0]]}"

    return f"{fen}{t_str}{c_str} {ep_str} {board.halfmove_clock} {fullmove}"

def _find_opening_book_files():
    base_dir = os.path.dirname(os.path.abspath(__file__))
    patterns = (
        os.path.join(base_dir, "opening books", "opening_book*.json"),
        os.path.join(base_dir, "opening_book*.json"),
    )
    seen = set()
    matches = []
    for pattern in patterns:
        for path in glob.glob(pattern):
            norm = os.path.normcase(os.path.abspath(path))
            if norm in seen:
                continue
            seen.add(norm)
            matches.append(path)
    return sorted(
        matches,
        key=lambda path: (os.path.getmtime(path), os.path.basename(path)),
        reverse=True,
    )

for _book_filename in _find_opening_book_files():
    try:
        with open(_book_filename, "r", encoding="utf-8") as f:
            OPENING_BOOK = json.load(f)
        break
    except Exception as e:
        print(f"Opening book not found or invalid at {_book_filename}: {e}")

# ---------------------------------------------------------------------------
# Common bot lifecycle helpers
# ---------------------------------------------------------------------------
class SearchCancelledException(Exception):
    pass

def calc_time_check_mask(allocated):
    if allocated <= 0.15: return 15
    if allocated <= 0.30: return 31
    if allocated <= 0.60: return 63
    if allocated <= 1.20: return 127
    if allocated <= 2.50: return 255
    return 511

def update_bot_runtime_state(bot, board, color, position_counts, comm_queue,
                             cancellation_event, bot_name, ply_count, game_mode,
                             **kwargs):
    bot.board = board
    bot.color = color
    bot.opponent_color = "black" if color == "white" else "white"
    bot.position_counts = position_counts
    bot.comm_queue = comm_queue
    bot.cancellation_event = cancellation_event
    bot.bot_name = bot_name
    bot.ply_count = ply_count
    bot.game_mode = game_mode
    bot.stop_time = None

    bot.time_left = kwargs.get("time_left")
    bot.increment = kwargs.get("increment")
    bot.use_opening_book = kwargs.get("use_opening_book", True)
    bot.show_tt_fullness = kwargs.get("show_tt_fullness", False)

    if bot.time_left:
        allocated = (bot.time_left / 30.0) + (bot.increment * 0.8)
        bot.time_check_mask = calc_time_check_mask(allocated)
    else:
        bot.time_check_mask = 511

    bot.current_age += 1

def accepted_bot_kwargs(bot_class, values):
    accepted_params = set(inspect.signature(bot_class.__init__).parameters)
    return {k: values[k] for k in OPTIONAL_BOT_KWARGS
            if k in values and k in accepted_params}

def run_bot_turn(bot):
    if bot.search_depth == 99:
        bot.ponder_indefinitely()
    else:
        bot.make_move()

def run_ai_process(board, color, position_counts, comm_queue, cancellation_event,
                   bot_class, bot_name, search_depth, ply_count, game_mode,
                   time_left=None, increment=None, use_opening_book=True,
                   show_tt_fullness=False):
    values = {
        "time_left": time_left,
        "increment": increment,
        "use_opening_book": use_opening_book,
        "show_tt_fullness": show_tt_fullness,
    }
    bot = bot_class(board, color, position_counts, comm_queue, cancellation_event,
                    bot_name, ply_count, game_mode,
                    **accepted_bot_kwargs(bot_class, values))
    bot.search_depth = search_depth
    run_bot_turn(bot)

# ---------------------------------------------------------------------------
# Persistent worker
# ---------------------------------------------------------------------------
class TaskQueueWrapper:
    def __init__(self, real_queue, task_id):
        self.real_queue = real_queue
        self.task_id = task_id

    def put(self, item):
        if isinstance(item, tuple) and item and item[0] in {"move", "log", "eval", "pv"}:
            self.real_queue.put(item + (self.task_id,))
        else:
            self.real_queue.put(item)

class EngineWorker:
    def __init__(self, bot_class):
        self.bot_class = bot_class
        self.bot = None

    def handle_task(self, task, comm_queue, cancel_event):
        cancel_event.clear()
        wrapped_comm = TaskQueueWrapper(comm_queue, task.get("task_id", -1))

        values = {
            "time_left": task.get("time_left"),
            "increment": task.get("increment"),
            "use_opening_book": task.get("use_opening_book", True),
            "show_tt_fullness": task.get("show_tt_fullness", False),
        }
        filtered_kwargs = accepted_bot_kwargs(self.bot_class, values)

        if self.bot is None or task.get("clear_hash", False):
            self.bot = self.bot_class(
                task["board"], task["color"], task["position_counts"],
                wrapped_comm, cancel_event, task["bot_name"],
                task["ply_count"], task["game_mode"], **filtered_kwargs
            )
        else:
            self.bot.update_state(
                task["board"], task["color"], task["position_counts"],
                wrapped_comm, cancel_event, task["bot_name"],
                task["ply_count"], task["game_mode"], **filtered_kwargs
            )

        self.bot.search_depth = task["search_depth"]
        run_bot_turn(self.bot)

def _jit_warmup(bot_class):
    try:
        dummy_bot = bot_class(
            Board(), 'white', {}, mp.Queue(), mp.Event(),
            bot_name="__warmup__", ply_count=0, game_mode="bot",
            use_opening_book=False,  # Force JIT to compile search/eval, not just book lookup
        )
        dummy_bot.search_depth = 4
        dummy_bot.make_move()
    except Exception:
        pass

def persistent_worker(work_queue, comm_queue, cancel_event, bot_class):
    worker = EngineWorker(bot_class)
    _jit_warmup(bot_class)

    while True:
        task = work_queue.get()
        if task is None:
            break

        try:
            worker.handle_task(task, comm_queue, cancel_event)
        except Exception:
            traceback.print_exc()
            TaskQueueWrapper(comm_queue, task.get("task_id", -1)).put(("move", None))

# ---------------------------------------------------------------------------
# PGN, Opening Sequence & Statistics Handlers
# ---------------------------------------------------------------------------
_CASUALTIES_RE = re.compile(r'\s*\(.*?\)')

def strip_casualties(san_str):
    return _CASUALTIES_RE.sub('', san_str) if san_str else ""

def generate_pgn(full_history, game_result=None):
    if not full_history: return ""
    moves = []
    start_turn = full_history[0][1]
    for i in range(1, len(full_history)):
        m = full_history[i][2]
        if m:
            moves.append(format_move_san(full_history[i-1][0], full_history[i][0], m))
    pgn, move_num = "", 1
    if start_turn == 'black' and moves:
        pgn += f"{move_num}... {moves[0]} "
        moves = moves[1:]
        move_num += 1
    for i in range(0, len(moves), 2):
        w, b = moves[i], moves[i+1] if i+1 < len(moves) else None
        pgn += f"{move_num}. {w} {b} " if b else f"{move_num}. {w} "
        move_num += 1
    if game_result:
        r = game_result[1]
        pgn += "1-0" if r == 'white' else "0-1" if r == 'black' else "1/2-1/2"
    else:
        pgn += "*"
    return pgn.strip()

def generate_series_opening_sequence(board, num_plies=2):
    opening_sequence = []
    temp_board = board.clone()
    temp_turn = "white"
    for _ in range(num_plies):
        moves = get_all_legal_moves(temp_board, temp_turn)
        if not moves:
            break
        move = random.choice(moves)
        opening_sequence.append(move)
        promo = move[2] if len(move) > 2 and move[2] is not None else Queen
        temp_board.make_move(move[0], move[1], promo)
        temp_turn = "black" if temp_turn == "white" else "white"
    return opening_sequence

def write_series_stats_file(out_path, move_stats, series_stats, main_name, op_name, use_clock, time_control_sec, increment, fixed_depth, total_series_games):
    if not move_stats: return
    
    def _summarise(stats):
        if not stats: return None
        n = len(stats)
        num_d = sorted(int(x['depth']) for x in stats if x['depth'].isdigit())
        def trimmed_mean(lst):
            if not lst: return None
            cut = max(1, int(len(lst) * 0.16))
            trimmed = lst[cut:-cut] if len(lst) > cut * 2 else lst
            return sum(trimmed) / len(trimmed)
        return {
            'n': n,
            't_avg': sum(x['time'] for x in stats) / n,
            't_max': max(x['time'] for x in stats),
            'n_avg': sum(x['nodes'] for x in stats) / n,
            'kn': sum(x['knps'] for x in stats) / n,
            'd_med': trimmed_mean(num_d),
            'd_max': max(num_d) if num_d else None,
        }
        
    try:
        with open(out_path, "w") as f:
            mode_str = f"Clock ({int(time_control_sec)}s + {increment:.1f}s inc)" if use_clock else f"Fixed depth {fixed_depth}"
            s = series_stats
            ma = _summarise(move_stats.get(main_name, []))
            oa = _summarise(move_stats.get(op_name, []))

            f.write(f"AI Series Results  |  {mode_str}  |  {s['game_count']} / {total_series_games} games\n")
            f.write(f"{main_name} {s['my_ai_wins']}  {op_name} {s['op_ai_wins']}  Draws {s['draws']}\n\n")

            if not ma or not oa:
                f.write("(insufficient data)\n")
                return

            def row(label, a_str, b_str, d_str):
                f.write(f"{label}\t{a_str}\t{b_str}\t{d_str}\n")

            def diff_str(a, b, fmt):
                d = a - b
                return ("+" if d > 0 else "") + format(d, fmt)

            f.write(f"\t{main_name}\t{op_name}\tDiff\n")
            row("Moves", f"{ma['n']:,}", f"{oa['n']:,}", "")
            if use_clock and ma['d_med'] is not None and oa['d_med'] is not None:
                row("Avg depth (68%)", f"{ma['d_med']:.1f}", f"{oa['d_med']:.1f}", diff_str(ma['d_med'], oa['d_med'], ".1f"))
                row("Max depth", f"{ma['d_max']}", f"{oa['d_max']}", diff_str(ma['d_max'], oa['d_max'], "d"))
            row("Avg nodes", f"{ma['n_avg']:,.0f}", f"{oa['n_avg']:,.0f}", diff_str(ma['n_avg'], oa['n_avg'], ",.0f"))
            row("Avg time (s)", f"{ma['t_avg']:.3f}", f"{oa['t_avg']:.3f}", diff_str(ma['t_avg'], oa['t_avg'], ".3f"))
            row("Max time (s)", f"{ma['t_max']:.3f}", f"{oa['t_max']:.3f}", diff_str(ma['t_max'], oa['t_max'], ".3f"))
            row("Avg KNPS", f"{ma['kn']:.1f}", f"{oa['kn']:.1f}", diff_str(ma['kn'], oa['kn'], ".1f"))
    except Exception as e:
        print(f"Failed to save stats: {e}")

TTEntry = namedtuple('TTEntry', ['score', 'depth', 'flag', 'best_move', 'age'])
TT_FLAG_EXACT, TT_FLAG_LOWERBOUND, TT_FLAG_UPPERBOUND = 0, 1, 2

def format_bot_move(bot, board_before, move):
    if not move: return "None"
    child = board_before.clone()
    promo = move[2] if len(move) > 2 and move[2] is not None else Queen
    child.make_move(move[0], move[1], promo)
    return format_move_san(board_before, child, move)

def get_pv_data(bot, max_depth, root_move):
    if not root_move: return [], []

    pv_san  = []
    pv_raw  = []
    current_board = bot.board.clone()
    current_turn  = bot.color
    current_ply   = bot.ply_count
    seen_hashes = set()
    move = root_move

    for i in range(max_depth):
        if not move: break

        p = current_board.grid[move[0][0]][move[0][1]]
        if not p or p.color != current_turn: break

        legal_moves = get_all_legal_moves(current_board, current_turn)
        if move not in legal_moves: break

        san      = format_bot_move(bot, current_board, move)
        move_num = (current_ply // 2) + 1
        if current_turn == 'white':
            pv_san.append(f"{move_num}. {san}")
        else:
            pv_san.append(f"{move_num}... {san}" if i == 0 else san)

        pv_raw.append(move)
        promo = move[2] if len(move) > 2 and move[2] is not None else Queen
        current_board.make_move(move[0], move[1], promo)
        current_turn = 'black' if current_turn == 'white' else 'white'
        current_ply += 1

        h = board_hash(current_board, current_turn)
        if h in seen_hashes: break
        seen_hashes.add(h)

        tt_idx = bot._tt_probe(h)
        if tt_idx == -1 or not bot.tt_moves[tt_idx]:
            break
        move = bot.tt_moves[tt_idx]

    return pv_san, pv_raw

def build_flat_pst_tables(mg_values, eg_values, piece_square_tables):
    flat_mg_w = [None] * 6
    flat_mg_b = [None] * 6
    flat_eg_w = [None] * 6
    flat_eg_b = [None] * 6

    for pt in [Pawn, Knight, Bishop, Rook, Queen, King]:
        z = pt.z_idx
        flat_mg_w[z] = [0] * 64
        flat_mg_b[z] = [0] * 64
        flat_eg_w[z] = [0] * 64
        flat_eg_b[z] = [0] * 64

        mg_val = mg_values[pt]
        eg_val = eg_values[pt]

        if pt == Pawn:
            mg_table = piece_square_tables[Pawn]
            eg_table = piece_square_tables['pawn_endgame']
        elif pt == King:
            mg_table = piece_square_tables['king_midgame']
            eg_table = piece_square_tables['king_endgame']
        else:
            mg_table = piece_square_tables[pt]
            eg_table = piece_square_tables[pt]

        for r in range(8):
            for c in range(8):
                sq_w = r * 8 + c
                sq_b = (7 - r) * 8 + c
                flat_mg_w[z][sq_w] = mg_val + mg_table[r][c]
                flat_mg_b[z][sq_b] = mg_val + mg_table[r][c]
                flat_eg_w[z][sq_w] = eg_val + eg_table[r][c]
                flat_eg_b[z][sq_b] = eg_val + eg_table[r][c]

    return flat_mg_w, flat_mg_b, flat_eg_w, flat_eg_b

