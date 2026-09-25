This is a regular-chess project descended from Jungle Chess.

## Engine: Almost-Pure Search Mode

The engine deliberately uses null-move pruning. `USE_NULL_MOVE_PRUNING` stays
enabled unless a measured regression or a future variant rule specifically
requires otherwise. It has zugzwang protection and is part of the intended
almost-pure search design.

`USE_LMR`, `USE_IIR`, and futility reduction stay enabled. They reduce work
but leave the engine able to verify promising moves with a stronger search.

Keep reverse futility pruning disabled and do not restore the old qsearch
delta-pruning skip. Those permanently discard moves and are outside this
engine's search policy. Quiescence considers captures, promotions, and every
legal evasion while in check.

## Validation and Regression Tests

Validation and regression tools live in the `tests` folder. Open their separate
window with:

```text
python tests/ui.py
```

It runs canonical perft and a deterministic 20-position node bench. Create a
bench baseline once with **Write Bench Baseline**, inspect
`tests/bench_baseline.json`, and commit it. Later bench runs must keep every count
identical.

## AI versus Opponent Series

Use **AI vs OP Series** in the main game UI for Elo testing. It plays one game
at a time, alternates the engines' colours, reuses each random opening for the
next colour-swapped game, and displays live W/D/L, score, Elo, and a 95%
confidence margin in the sidebar. No concurrent match games are used.

Under **AI Series Stop**, the **Max games** and **Confidence** checkboxes work
independently. By default both are enabled: 1,000 games and 95% confidence.
The series stops as soon as either enabled limit is reached, but only after a
complete colour-swapped pair of games. This ensures neither AI gains an
unmatched White-game advantage. An odd maximum entered manually is rounded up
to the next even number. Untick either limit to ignore it; untick both for an
unlimited series.

Confidence mode needs at least 10 scored games, then stops once the
normal-approximate evidence reaches the selected percentage that either AI.py
or OpponentAI.py is stronger. This prevents an inconclusive series from running
forever when the candidate is weaker. Like the game limit, confidence is only
checked after a complete pair.

AI.py is the candidate engine and OpponentAI.py is the baseline. When a
candidate is convincingly stronger, copying it into OpponentAI.py is intentional
baseline promotion.
