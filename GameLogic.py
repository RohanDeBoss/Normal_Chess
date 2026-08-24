# GameLogic.py (v72.0 - Standard Chess Rules)


# -----------------------------------------------------------------------
# Global constants
# z_idx reference: 0=Pawn 1=Knight 2=Bishop 3=Rook 4=Queen 5=King
# -----------------------------------------------------------------------
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

KNIGHT_ATTACKS_FROM = {
    (r, c): tuple(
        (r + dr, c + dc) for dr, dc in DIRECTIONS['knight']
        if 0 <= r + dr < ROWS and 0 <= c + dc < COLS
    )
    for r in range(ROWS) for c in range(COLS)
}

KING_ATTACKS_FROM = {
    (r, c): tuple(
        (r + dr, c + dc) for dr, dc in DIRECTIONS['king']
        if 0 <= r + dr < ROWS and 0 <= c + dc < COLS
    )
    for r in range(ROWS) for c in range(COLS)
}

RAYS_ORTHOGONAL = [None] * 64
RAYS_DIAGONAL   = [None] * 64
RAYS_ALL        = [None] * 64

def _init_rays():
    for r in range(ROWS):
        for c in range(COLS):
            sq = r * COLS + c
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

_init_rays()


def _clone_piece_fast(piece):
    cls       = piece.__class__
    new_piece = cls.__new__(cls)
    new_piece.color          = piece.color
    new_piece.opponent_color = piece.opponent_color
    new_piece.pos            = piece.pos
    new_piece._list_pos      = piece._list_pos   # preserve index in new board's list
    if cls is Pawn:
        new_piece.direction    = piece.direction
        new_piece.starting_row = piece.starting_row
        new_piece.promo_rank   = piece.promo_rank
    return new_piece


# -----------------------------------------------------------------------
# Piece classes
# -----------------------------------------------------------------------
class Piece:
    def __init__(self, color):
        self.color          = color
        self.opponent_color = "black" if color == "white" else "white"
        self.pos            = None
        self._list_pos      = -1
        self._z_list_pos    = -1

    def symbol(self): return "?"

class King(Piece):
    z_idx = 5
    def symbol(self): return "♔" if self.color == "white" else "♚"

class Queen(Piece):
    z_idx = 4
    def symbol(self): return "♕" if self.color == "white" else "♛"

class Rook(Piece):
    z_idx = 3
    def symbol(self): return "♖" if self.color == "white" else "♜"

class Bishop(Piece):
    z_idx = 2
    def symbol(self): return "♗" if self.color == "white" else "♝"

class Knight(Piece):
    z_idx = 1
    def symbol(self): return "♘" if self.color == "white" else "♞"

class Pawn(Piece):
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
# Castling Bitmasks: White-King = 1, White-Queen = 2, Black-King = 4, Black-Queen = 8
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
        self.pieces_by_z      = {'white': [[] for _ in range(6)], 'black': [[] for _ in range(6)]}
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

    # ---- O(1) piece-list helpers ------------------------------------------

    def _list_append(self, piece):
        """Append to the colour list and record the resulting index."""
        lst             = self.white_pieces if piece.color == 'white' else self.black_pieces
        piece._list_pos = len(lst)
        lst.append(piece)
        
        z_lst             = self.pieces_by_z[piece.color][piece.z_idx]
        piece._z_list_pos = len(z_lst)
        z_lst.append(piece)

    def _list_remove(self, piece):
        """
        O(1) swap-and-pop removal.  Swaps piece with the last element so the
        list stays compact, then pops the tail.  Safe to call on a piece that
        is already absent (_list_pos == -1) — treated as a no-op.
        """
        idx = piece._list_pos
        if idx < 0:
            return
        lst            = self.white_pieces if piece.color == 'white' else self.black_pieces
        last           = lst[-1]
        lst[idx]       = last
        last._list_pos = idx
        lst.pop()
        piece._list_pos = -1
        
        z_idx = piece._z_list_pos
        if z_idx >= 0:
            z_lst = self.pieces_by_z[piece.color][piece.z_idx]
            if z_lst:
                z_last = z_lst[-1]
                z_lst[z_idx] = z_last
                z_last._z_list_pos = z_idx
                z_lst.pop()
            piece._z_list_pos = -1

    # ---- Board mutation primitives ----------------------------------------

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
        new_board.pieces_by_z  = {'white': [[] for _ in range(6)], 'black': [[] for _ in range(6)]}
        
        for p in white_pieces:
            z_lst = new_board.pieces_by_z['white'][p.z_idx]
            p._z_list_pos = len(z_lst)
            z_lst.append(p)
            
        for p in black_pieces:
            z_lst = new_board.pieces_by_z['black'][p.z_idx]
            p._z_list_pos = len(z_lst)
            z_lst.append(p)

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
            removed.append((moving_piece, er, ec))
            self.remove_piece(er, ec)
            promoted_piece = promo_cls(mc)
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

    # 1. Pawn Attacks
    p_dir = 1 if attacking_color == 'white' else -1
    for dc in (-1, 1):
        pr, pc = r + p_dir, c + dc
        if 0 <= pr < 8 and 0 <= pc < 8:
            p = grid[pr][pc]
            if p and p.z_idx == 0 and p.color == attacking_color:
                return True

    # 2. Knight Attacks
    for kr, kc in KNIGHT_ATTACKS_FROM[(r, c)]:
        p = grid[kr][kc]
        if p and p.z_idx == 1 and p.color == attacking_color:
            return True

    # 3. King Attacks
    for kr, kc in KING_ATTACKS_FROM[(r, c)]:
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
    kpos = board.white_king_pos if color == 'white' else board.black_king_pos
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
            if 0 <= r + dr < 8 and grid[r + dr][c] is None:
                moves.append(((r, c), (r + dr, c)))
                if r == p.starting_row and grid[r + 2 * dr][c] is None:
                    moves.append(((r, c), (r + 2 * dr, c)))
            for dc in (-1, 1):
                cr, cc = r + dr, c + dc
                if 0 <= cr < 8 and 0 <= cc < 8:
                    target = grid[cr][cc]
                    if target and target.color == opp:
                        moves.append(((r, c), (cr, cc)))
                    elif (cr, cc) == board.ep_square:
                        moves.append(((r, c), (cr, cc)))

        elif pz == 1: # Knight
            for kr, kc in KNIGHT_ATTACKS_FROM[(r, c)]:
                target = grid[kr][kc]
                if target is None or target.color == opp:
                    moves.append(((r, c), (kr, kc)))

        elif pz == 2: # Bishop
            for ray in RAYS_DIAGONAL[sq]:
                for cr, cc in ray:
                    target = grid[cr][cc]
                    if target is None: moves.append(((r, c), (cr, cc)))
                    else:
                        if target.color == opp: moves.append(((r, c), (cr, cc)))
                        break

        elif pz == 3: # Rook
            for ray in RAYS_ORTHOGONAL[sq]:
                for cr, cc in ray:
                    target = grid[cr][cc]
                    if target is None: moves.append(((r, c), (cr, cc)))
                    else:
                        if target.color == opp: moves.append(((r, c), (cr, cc)))
                        break

        elif pz == 4: # Queen
            for ray in RAYS_ALL[sq]:
                for cr, cc in ray:
                    target = grid[cr][cc]
                    if target is None: moves.append(((r, c), (cr, cc)))
                    else:
                        if target.color == opp: moves.append(((r, c), (cr, cc)))
                        break

        elif pz == 5: # King
            for kr, kc in KING_ATTACKS_FROM[(r, c)]:
                target = grid[kr][kc]
                if target is None or target.color == opp:
                    moves.append(((r, c), (kr, kc)))

            # Castling
            if color == 'white' and r == 7 and c == 4 and not is_in_check(board, 'white'):
                if (board.castling_rights & CASTLE_WK) and grid[7][5] is None and grid[7][6] is None:
                    if not is_square_attacked(board, 7, 5, 'black') and not is_square_attacked(board, 7, 6, 'black'):
                        moves.append(((7, 4), (7, 6)))
                if (board.castling_rights & CASTLE_WQ) and grid[7][3] is None and grid[7][2] is None and grid[7][1] is None:
                    if not is_square_attacked(board, 7, 3, 'black') and not is_square_attacked(board, 7, 2, 'black'):
                        moves.append(((7, 4), (7, 2)))
            elif color == 'black' and r == 0 and c == 4 and not is_in_check(board, 'black'):
                if (board.castling_rights & CASTLE_BK) and grid[0][5] is None and grid[0][6] is None:
                    if not is_square_attacked(board, 0, 5, 'white') and not is_square_attacked(board, 0, 6, 'white'):
                        moves.append(((0, 4), (0, 6)))
                if (board.castling_rights & CASTLE_BQ) and grid[0][3] is None and grid[0][2] is None and grid[0][1] is None:
                    if not is_square_attacked(board, 0, 3, 'white') and not is_square_attacked(board, 0, 2, 'white'):
                        moves.append(((0, 4), (0, 2)))

    return moves

def get_all_legal_moves(board, color):
    legal_moves = []
    for m in get_all_pseudo_legal_moves(board, color):
        rec = board.make_move_track(m[0], m[1])
        if not is_in_check(board, color):
            legal_moves.append(m)
        board.unmake_move(rec)
    return legal_moves

def has_legal_moves(board, color):
    for m in get_all_pseudo_legal_moves(board, color):
        rec = board.make_move_track(m[0], m[1])
        legal = not is_in_check(board, color)
        board.unmake_move(rec)
        if legal: return True
    return False

def is_insufficient_material(board):
    pcz_w = board.piece_counts_z['white']
    pcz_b = board.piece_counts_z['black']
    if pcz_w[0] > 0 or pcz_b[0] > 0 or pcz_w[3] > 0 or pcz_b[3] > 0 or pcz_w[4] > 0 or pcz_b[4] > 0:
        return False
    if len(board.white_pieces) == 1 and len(board.black_pieces) == 1:
        return True
    if (len(board.white_pieces) <= 2 and len(board.black_pieces) == 1) or \
       (len(board.black_pieces) <= 2 and len(board.white_pieces) == 1):
        return True
    return False

_board_hash_fn = None
def _get_board_hash():
    global _board_hash_fn
    if _board_hash_fn is None:
        from EngineRuntime import board_hash
        _board_hash_fn = board_hash
    return _board_hash_fn

def get_game_state(board, turn_to_move, position_counts, ply_count, max_moves):
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

    if ply_count >= max_moves:
        return ("move_limit", None)

    return "ongoing", None

def fast_approximate_material_swing(board, move, moving_piece, target_piece, piece_values_list):
    swing = 0
    is_tactic = False
    my_z = moving_piece.z_idx

    if target_piece is not None:
        swing += piece_values_list[target_piece.z_idx]
        is_tactic = True
    elif my_z == 0 and move[1] == board.ep_square:
        swing += piece_values_list[0]
        is_tactic = True

    if my_z == 0 and move[1][0] == moving_piece.promo_rank:
        swing += piece_values_list[4] - piece_values_list[0]
        is_tactic = True

    return swing, is_tactic

def format_move(move):
    if not move: return "None"
    (r1, c1), (r2, c2) = move
    return f"{'abcdefgh'[c1]}{'87654321'[r1]}-{'abcdefgh'[c2]}{'87654321'[r2]}"

def format_move_san(board_before, board_after, move):
    if not move: return "None"
    start_pos, end_pos = move
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
                san += "=Q"
        else:
            p_char = chars[type(p)]
            same_pieces = [other for other in (board_before.white_pieces if p.color == 'white' else board_before.black_pieces)
                           if type(other) is type(p) and other.pos != start_pos]
            disambig = ""
            ambiguous = [other for other in same_pieces if move in [((other.pos), end_pos) for other in same_pieces]]
            if ambiguous:
                same_file = any(o.pos[1] == start_pos[1] for o in ambiguous)
                same_rank = any(o.pos[0] == start_pos[0] for o in ambiguous)
                if not same_file: disambig = files[start_pos[1]]
                elif not same_rank: disambig = ranks[start_pos[0]]
                else: disambig = f"{files[start_pos[1]]}{ranks[start_pos[0]]}"

            san = f"{p_char}{disambig}{'x' if is_cap else ''}{files[end_pos[1]]}{ranks[end_pos[0]]}"

    opp = 'black' if p.color == 'white' else 'white'
    if not has_legal_moves(board_after, opp):
        san += "#" if is_in_check(board_after, opp) else ""
    elif is_in_check(board_after, opp):
        san += "+"

    return san