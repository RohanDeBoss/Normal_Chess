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