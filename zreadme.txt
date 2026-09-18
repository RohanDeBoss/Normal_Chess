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

## Testing Methodology (AI.py vs OpponentAI.py)

AI.py is the candidate engine under test. OpponentAI.py is the current baseline.
Matches run head-to-head series via ChessUI.py under clock conditions.

When a change set in AI.py proves stronger over a full test series, it is
intentionally copied into OpponentAI.py to establish a new baseline. Do not
treat OpponentAI.py sharing code with a previous version of AI.py as an error
or a methodology break; this is intentional baseline promotion.

Subsequent test series measure marginal gains against this newly promoted
baseline, not cumulative progress against older legacy versions. Always check the
version header at the top of each file to see what is currently being tested.