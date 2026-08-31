# GameLogic.py (v1.3 - High Performance Standard Chess Rules & Capture-Only Movegen)

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
        k = self.white_king_pos if color == 'white' else self.black_king_pos
        if k is not None and self.grid[k[0]][k[1]] and self.grid[k[0]][k[1]].z_idx == 5:
            return k
        for r in range(ROWS):
            for c in range(COLS):
                p = self.grid[r][c]
                if p and p.z_idx == 5 and p.color == color:
                    if color == 'white': self.white_king_pos = (r, c)
                    else:                self.black_king_pos = (r, c)
                    return (r, c)
        return None

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
            for kr, kc in KNIGHT_ATTACKS_FROM[(r, c)]:
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
            for kr, kc in KING_ATTACKS_FROM[(r, c)]:
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
            for kr, kc in KNIGHT_ATTACKS_FROM[(r, c)]:
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
            for kr, kc in KING_ATTACKS_FROM[(r, c)]:
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

    # Pawn checks
    p_dir = 1 if opp == 'white' else -1
    for dc in (-1, 1):
        pr, pc = kr + p_dir, kc + dc
        if 0 <= pr < 8 and 0 <= pc < 8:
            p = grid[pr][pc]
            if p and p.z_idx == 0 and p.color == opp:
                checkers.append((p, pr, pc))

    # Knight checks
    for kr2, kc2 in KNIGHT_ATTACKS_FROM[(kr, kc)]:
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
        for tr, tc in KING_ATTACKS_FROM[(kr, kc)]:
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

def _attackers_to_square(board, r, c, color):
    grid = board.grid
    attackers = []

    p_dir = 1 if color == 'white' else -1
    for dc in (-1, 1):
        pr, pc = r + p_dir, c + dc
        if 0 <= pr < 8 and 0 <= pc < 8:
            p = grid[pr][pc]
            if p and p.z_idx == 0 and p.color == color:
                attackers.append((_SEE_VALUES[0], pr, pc, 0))

    for kr, kc in KNIGHT_ATTACKS_FROM[(r, c)]:
        p = grid[kr][kc]
        if p and p.z_idx == 1 and p.color == color:
            attackers.append((_SEE_VALUES[1], kr, kc, 1))

    for kr, kc in KING_ATTACKS_FROM[(r, c)]:
        p = grid[kr][kc]
        if p and p.z_idx == 5 and p.color == color:
            attackers.append((_SEE_VALUES[5], kr, kc, 5))

    sq = r * 8 + c
    for ray in RAYS_ORTHOGONAL[sq]:
        for cr, cc in ray:
            p = grid[cr][cc]
            if p:
                if p.color == color and (p.z_idx == 3 or p.z_idx == 4):
                    attackers.append((_SEE_VALUES[p.z_idx], cr, cc, p.z_idx))
                break

    for ray in RAYS_DIAGONAL[sq]:
        for cr, cc in ray:
            p = grid[cr][cc]
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
        raw = _attackers_to_square(board, tr, tc, color)
        return [a for a in raw if (a[1], a[2]) not in occupied_override or occupied_override[(a[1], a[2])] is not None]

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

        occupied_override[(fr, fc)] = None
        occupied_override[(tr, tc)] = grid[fr][fc]
        current_attacker_value = value
        side_to_move = 'black' if side_to_move == 'white' else 'white'

    result = gains[-1]
    for i in range(len(gains) - 2, -1, -1):
        result = gains[i] - max(0, result)
    return result

def fast_approximate_material_swing(board, move, moving_piece, target_piece, piece_values_list):
    if target_piece is not None or (moving_piece.z_idx == 0 and move[1] == board.ep_square):
        see = static_exchange_eval(board, move, moving_piece, target_piece)
        is_tactic = (see >= 0)
        return see, is_tactic

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