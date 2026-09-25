"""GUI-independent correctness and deterministic search regression tests."""

import json
import threading
import time
from pathlib import Path

from AI import ChessBot
from EngineRuntime import board_hash
from GameLogic import Board, Queen, get_all_legal_moves
from tests.position_validation import parse_fen


PERFT_POSITIONS = {
    "Start Position": (
        "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -",
        {1: 20, 2: 400, 3: 8902, 4: 197281, 5: 4865609},
    ),
    "Kiwipete": (
        "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq -",
        {1: 48, 2: 2039, 3: 97862, 4: 4085603},
    ),
    "EP Discovered Check": (
        "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - -",
        {1: 14, 2: 191, 3: 2812, 4: 43238},
    ),
    "Promotions and Pins": (
        "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq -",
        {1: 6, 2: 264, 3: 9467, 4: 422333},
    ),
    "Promotions and Pins, mirrored": (
        "r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ -",
        {1: 6, 2: 264, 3: 9467, 4: 422333},
    ),
    "Discovered Checks": (
        "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ -",
        {1: 44, 2: 1486, 3: 62379, 4: 2103487},
    ),
    "Middlegame": (
        "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - -",
        {1: 46, 2: 2079, 3: 89890, 4: 3894594},
    ),
}

# The initial board plus nineteen prefixes of a fixed Ruy Lopez line.
BENCH_LINE = (
    "e2e4", "e7e5", "g1f3", "b8c6", "f1b5", "a7a6", "b5a4", "g8f6",
    "e1g1", "f8e7", "f1e1", "b7b5", "a4b3", "d7d6", "c2c3", "e8g8",
    "h2h3", "c6b8", "d2d4",
)


class _MoveSink:
    def __init__(self):
        self.move = None

    def put(self, message):
        if isinstance(message, tuple) and message and message[0] == "move":
            self.move = message[1]


def perft(board, turn, depth):
    if depth == 0:
        return 1
    moves = get_all_legal_moves(board, turn)
    if depth == 1:
        return len(moves)

    total = 0
    next_turn = "black" if turn == "white" else "white"
    for move in moves:
        promotion = move[2] if len(move) > 2 and move[2] is not None else Queen
        record = board.make_move_track(move[0], move[1], promotion)
        total += perft(board, next_turn, depth - 1)
        board.unmake_move(record)
    return total


def run_perft(max_depth=3, report=print):
    """Run all canonical positions through ``max_depth`` and return success."""
    failed = False
    started = time.perf_counter()
    for name, (fen, counts) in PERFT_POSITIONS.items():
        board, turn, _ = parse_fen(fen)
        for depth, expected in counts.items():
            if depth > max_depth:
                continue
            actual = perft(board, turn, depth)
            passed = actual == expected
            report(f"{'PASS' if passed else 'FAIL'}  {name}, depth {depth}: "
                   f"{actual:,} {'=' if passed else '!='} {expected:,}")
            failed |= not passed
    report(f"Perft {'FAILED' if failed else 'PASSED'} in {time.perf_counter() - started:.2f}s.")
    return not failed


def _square(text):
    return 8 - int(text[1]), ord(text[0]) - ord("a")


def _bench_position(ply_count):
    board = Board()
    turn = "white"
    for uci in BENCH_LINE[:ply_count]:
        start, end = _square(uci[:2]), _square(uci[2:4])
        move = next((candidate for candidate in get_all_legal_moves(board, turn)
                     if candidate[0] == start and candidate[1] == end), None)
        if move is None:
            raise RuntimeError(f"Invalid fixed bench move `{uci}` at ply {ply_count}.")
        promotion = move[2] if len(move) > 2 and move[2] is not None else Queen
        board.make_move(move[0], move[1], promotion)
        turn = "black" if turn == "white" else "white"
    return board, turn


def collect_bench(depth):
    nodes = {}
    for ply_count in range(20):
        board, turn = _bench_position(ply_count)
        sink = _MoveSink()
        bot = ChessBot(
            board, turn, {board_hash(board, turn): 1}, sink, threading.Event(),
            bot_name="Bench", ply_count=ply_count, game_mode="bench",
            use_opening_book=False,
        )
        bot.search_depth = depth
        bot.make_move()
        if sink.move is None:
            raise RuntimeError(f"Bench engine returned no move at position {ply_count}.")
        nodes[f"ply_{ply_count:02d}"] = bot.nodes_searched
    return nodes


def run_bench(depth=4, baseline_path=None, write_baseline=False, report=print):
    """Create or compare a reviewed, deterministic node-count baseline."""
    baseline_path = Path(baseline_path) if baseline_path else Path(__file__).with_name("bench_baseline.json")
    actual = collect_bench(depth)
    payload = {"depth": depth, "nodes": actual}

    if write_baseline:
        baseline_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        report(f"Wrote baseline: {baseline_path}")
        report(f"Total nodes: {sum(actual.values()):,}")
        return True

    if not baseline_path.exists():
        report(f"FAIL  Missing baseline: {baseline_path}")
        return False

    expected_payload = json.loads(baseline_path.read_text(encoding="utf-8"))
    expected = expected_payload.get("nodes", {})
    failed = expected_payload.get("depth") != depth
    if failed:
        report(f"FAIL  Baseline depth is {expected_payload.get('depth')}; requested depth is {depth}.")

    for name, node_count in actual.items():
        expected_nodes = expected.get(name)
        passed = node_count == expected_nodes
        report(f"{'PASS' if passed else 'FAIL'}  {name}: {node_count:,}" +
               ("" if passed else f" != {expected_nodes:,}"))
        failed |= not passed

    report(f"Bench {'FAILED' if failed else 'PASSED'} — total nodes: {sum(actual.values()):,}")
    return not failed
