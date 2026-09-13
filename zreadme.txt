This is a project.
Its a modified clone of Jungle chess.
Its regular chess.

## Engine: Pure Search Mode (ChessBot / AI.py)

Do not re-enable USE_NULL_MOVE_PRUNING, USE_FUTILITY_PRUNING, or
USE_REVERSE_FUTILITY_PRUNING, and do not restore the old delta-pruning
skip in qsearch's capture loop. These four discard a move outright with
no mechanism to ever revisit it, so they can silently throw away the true
best move.

USE_LMR and USE_IIR stay on. Both reduce search depth but verify
themselves: LMR immediately re-searches at full depth if the reduced
score beats alpha, and IIR's reduction only fires when no TT move exists
yet, so the next iterative-deepening pass searches that node at full
depth anyway. Neither one permanently loses a move.

Quiescence search still only searches captures (plus all legal replies
when in check) instead of every quiet move — that's normal quiescence
search, not one of the unsound heuristics above.