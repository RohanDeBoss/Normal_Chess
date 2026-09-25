"""FEN parsing and position validation, shared by the game and test tools."""

from GameLogic import (
    Board, Pawn, Knight, Bishop, Rook, Queen, King,
    CASTLE_WK, CASTLE_WQ, CASTLE_BK, CASTLE_BQ, is_in_check,
)


class FenError(ValueError):
    """Raised when a FEN cannot describe a legal standard-chess position."""


_FEN_PIECES = {
    "p": Pawn, "n": Knight, "b": Bishop,
    "r": Rook, "q": Queen, "k": King,
}
_CASTLING_ORDER = "KQkq"
_CASTLING_DATA = {
    "K": (CASTLE_WK, (7, 4), King, "white", (7, 7), Rook),
    "Q": (CASTLE_WQ, (7, 4), King, "white", (7, 0), Rook),
    "k": (CASTLE_BK, (0, 4), King, "black", (0, 7), Rook),
    "q": (CASTLE_BQ, (0, 4), King, "black", (0, 0), Rook),
}


def _is_piece(board, square, piece_type, color):
    piece = board.grid[square[0]][square[1]]
    return type(piece) is piece_type and piece.color == color


def parse_fen(fen):
    """Return ``(board, turn, fullmove)`` or raise :class:`FenError`.

    One-field shorthand remains accepted for the board editor.  The returned
    board is fully constructed before validation completes, so callers never
    need to partially mutate their current game on invalid input.
    """
    if not isinstance(fen, str) or not fen.strip():
        raise FenError("Enter a FEN position.")

    fields = fen.split()
    if not 1 <= len(fields) <= 6:
        raise FenError("A FEN must contain between 1 and 6 fields.")

    placement = fields[0]
    turn_field = fields[1].lower() if len(fields) > 1 else "w"
    castling = fields[2] if len(fields) > 2 else (
        "KQkq" if placement == "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR" else "-"
    )
    ep_field = fields[3].lower() if len(fields) > 3 else "-"
    halfmove_field = fields[4] if len(fields) > 4 else "0"
    fullmove_field = fields[5] if len(fields) > 5 else "1"

    if turn_field not in ("w", "b"):
        raise FenError("The active-colour field must be `w` or `b`.")
    turn = "white" if turn_field == "w" else "black"

    ranks = placement.split("/")
    if len(ranks) != 8:
        raise FenError("Piece placement must contain exactly 8 ranks.")

    board = Board(setup=False)
    kings = {"white": 0, "black": 0}
    pawns = {"white": 0, "black": 0}

    for row, rank in enumerate(ranks):
        col = 0
        for char in rank:
            if char.isdigit():
                width = int(char)
                if not 1 <= width <= 8:
                    raise FenError(f"Invalid empty-square count `{char}` in rank {8 - row}.")
                col += width
                continue

            piece_type = _FEN_PIECES.get(char.lower())
            if piece_type is None:
                raise FenError(f"Invalid FEN piece character `{char}`.")
            if col >= 8:
                raise FenError(f"Rank {8 - row} contains more than 8 squares.")

            color = "white" if char.isupper() else "black"
            board.add_piece(piece_type(color), row, col)
            if piece_type is King:
                kings[color] += 1
            elif piece_type is Pawn:
                pawns[color] += 1
                if row in (0, 7):
                    raise FenError("Pawns cannot be on the first or eighth rank.")
            col += 1

        if col != 8:
            raise FenError(f"Rank {8 - row} contains {col} squares, not 8.")

    if kings != {"white": 1, "black": 1}:
        raise FenError("A legal position must contain exactly one king of each colour.")
    if pawns["white"] > 8 or pawns["black"] > 8:
        raise FenError("Neither side can have more than eight pawns.")

    if castling != "-":
        canonical = "".join(flag for flag in _CASTLING_ORDER if flag in castling)
        if castling != canonical:
            raise FenError("Castling rights must be `KQkq` in canonical order, or `-`.")

        board.castling_rights = 0
        for flag in castling:
            bit, king_sq, king_type, color, rook_sq, rook_type = _CASTLING_DATA[flag]
            if not _is_piece(board, king_sq, king_type, color) or \
                    not _is_piece(board, rook_sq, rook_type, color):
                raise FenError(f"Castling right `{flag}` has no matching king and rook.")
            board.castling_rights |= bit
    else:
        board.castling_rights = 0

    board.ep_square = None
    if ep_field != "-":
        if len(ep_field) != 2 or ep_field[0] not in "abcdefgh" or ep_field[1] not in "36":
            raise FenError("En-passant square must be `-` or a square on rank 3 or 6.")
        required_rank = "6" if turn == "white" else "3"
        if ep_field[1] != required_rank:
            raise FenError(f"En-passant square must be on rank {required_rank} for this side to move.")

        ep_row = 8 - int(ep_field[1])
        ep_col = ord(ep_field[0]) - ord("a")
        pawn_row = 3 if turn == "white" else 4
        pawn_color = "black" if turn == "white" else "white"
        if not _is_piece(board, (pawn_row, ep_col), Pawn, pawn_color):
            raise FenError("En-passant square has no pawn that could have advanced two squares.")
        if board.grid[ep_row][ep_col] is not None:
            raise FenError("En-passant square must be empty.")
        board.ep_square = (ep_row, ep_col)

    if not halfmove_field.isdigit():
        raise FenError("Halfmove clock must be a non-negative integer.")
    if not fullmove_field.isdigit() or int(fullmove_field) < 1:
        raise FenError("Fullmove number must be a positive integer.")
    board.halfmove_clock = int(halfmove_field)

    passive_color = "black" if turn == "white" else "white"
    if is_in_check(board, passive_color):
        raise FenError(f"The side not to move ({passive_color}) may not already be in check.")

    return board, turn, int(fullmove_field)
