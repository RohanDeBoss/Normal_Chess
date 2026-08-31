# AI.py (v1.8 - Evaluation update)

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
                if (depth >= self.LMR_DEPTH_THRESHOLD and
                        legal_moves_count > self.LMR_MOVE_COUNT_THRESHOLD and
                        not is_in_check_flag and not is_good_tactic):
                    reduction = 1 + (depth // 6) + (legal_moves_count // 12)

                    if (ply < len(self.killer_moves) and move[:2] in [k[:2] for k in self.killer_moves[ply] if k]) or (c_move and move[:2] == c_move[:2]):
                        reduction -= 1
                        
                    if history_table[f_sq][t_sq] > 500:
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

        # Not in check
        stand_pat = self._get_cached_static_eval(board, turn, hash_val)
        best_score = stand_pat
        if stand_pat >= beta: return stand_pat
        if stand_pat > alpha: alpha = stand_pat

        promising_moves = get_all_legal_moves(board, turn)
        scored_moves = []

        for move in promising_moves:
            (r1, c1), (r2, c2) = move[:2]
            moving_piece = grid[r1][c1]
            target_piece = grid[r2][c2]

            # Only search tactical captures with SEE >= 0
            if target_piece is None and not (moving_piece.z_idx == 0 and (move[1] == board.ep_square or move[1][0] == moving_piece.promo_rank)):
                continue

            swing, is_tactic = fast_approximate_material_swing(board, move, moving_piece, target_piece, ORDERING_VALUES)
            if not is_tactic: continue  # Prunes losing exchanges (SEE < 0)
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
            opp_color = 'black' if is_white else 'white'
            mob_mg = 0
            mob_eg = 0

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

                    # Defended by another friendly pawn behind it
                    p_def_r = r + 1 if is_white else r - 1
                    if 0 <= p_def_r < 8:
                        if (c > 0 and grid[p_def_r][c - 1] and grid[p_def_r][c - 1].z_idx == 0 and grid[p_def_r][c - 1].color == piece.color) or \
                           (c < 7 and grid[p_def_r][c + 1] and grid[p_def_r][c + 1].z_idx == 0 and grid[p_def_r][c + 1].color == piece.color):
                            scores_mg[color_idx] += self.EVAL_PAWN_DEFENDED

                # 2. Knights (Development & Mobility)
                elif z == 1:
                    if r != home_rank:
                        scores_mg[color_idx] += self.EVAL_DEV_BONUS
                    safe_sqs = 0
                    for kr, kc in KNIGHT_ATTACKS_FROM[(r, c)]:
                        target = grid[kr][kc]
                        if target is None or target.color == opp_color: safe_sqs += 1
                    mob_mg += safe_sqs * 4
                    mob_eg += safe_sqs * 4

                # 3. Bishops (Development & Mobility)
                elif z == 2:
                    if r != home_rank:
                        scores_mg[color_idx] += self.EVAL_DEV_BONUS
                    safe_sqs = 0
                    for ray in RAYS_DIAGONAL[sq]:
                        for cr, cc in ray:
                            target = grid[cr][cc]
                            if target is None: safe_sqs += 1
                            else:
                                if target.color == opp_color: safe_sqs += 1
                                break
                    mob_mg += safe_sqs * 4
                    mob_eg += safe_sqs * 4

                # 4. Rooks (7th Rank, Open Files & Mobility)
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

                    safe_sqs = 0
                    for ray in RAYS_ORTHOGONAL[sq]:
                        for cr, cc in ray:
                            target = grid[cr][cc]
                            if target is None: safe_sqs += 1
                            else:
                                if target.color == opp_color: safe_sqs += 1
                                break
                    mob_mg += safe_sqs * 2
                    mob_eg += safe_sqs * 4

                # 5. Queens (Mobility)
                elif z == 4:
                    safe_sqs = 0
                    for ray in RAYS_ALL[sq]:
                        for cr, cc in ray:
                            target = grid[cr][cc]
                            if target is None: safe_sqs += 1
                            else:
                                if target.color == opp_color: safe_sqs += 1
                                break
                    mob_mg += safe_sqs * 1
                    mob_eg += safe_sqs * 2

                # 6. King (Pawn Shield for Castled King)
                elif z == 5:
                    if (is_white and r == 7 and (c == 6 or c == 2)) or (not is_white and r == 0 and (c == 6 or c == 2)):
                        shield_r = 6 if is_white else 1
                        shield_intact = 0
                        for sc in range(max(0, c - 1), min(8, c + 2)):
                            sp = grid[shield_r][sc]
                            if sp and sp.z_idx == 0 and sp.color == piece.color:
                                shield_intact += 1
                        scores_mg[color_idx] += shield_intact * self.EVAL_PAWN_SHIELD

            # Global color bonuses
            scores_mg[color_idx] += mob_mg // 2
            scores_eg[color_idx] += mob_eg // 2

            if board.piece_counts_z['white' if is_white else 'black'][2] >= 2:
                scores_mg[color_idx] += self.EVAL_BISHOP_PAIR
                scores_eg[color_idx] += self.EVAL_BISHOP_PAIR

            c_rights = board.castling_rights
            if is_white and (c_rights & (CASTLE_WK | CASTLE_WQ)):
                scores_mg[color_idx] += self.EVAL_CASTLING_RIGHTS
            elif not is_white and (c_rights & (CASTLE_BK | CASTLE_BQ)):
                scores_mg[color_idx] += self.EVAL_CASTLING_RIGHTS

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