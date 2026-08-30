# MoveChecker.py (v1.1 - parallel Perft via ProcessPoolExecutor across root moves)
#
# Changelog vs v1.0:
#   - Perft used to run all root moves sequentially on one background
#     thread. Every root move's subtree is fully independent (no shared
#     alpha-beta bounds, no shared mutable state once the move's
#     applied), so it's an embarrassingly parallel problem: dividing
#     the root moves across a ProcessPoolExecutor scales throughput
#     with core count instead of running on a single core.
#   - _perft_rec() and the per-root-move task function were pulled out
#     to module level so they're picklable/importable by worker
#     processes — a closure defined inside launch_move_checker_dialog()
#     can't be sent to a ProcessPoolExecutor.
#   - Below depth 3, falls back to the old sequential loop: spinning up
#     a process pool costs more in startup time than a depth-1/2 Perft
#     (tens to low-hundreds of nodes) takes to run outright.
#   - The Cancel button now also forcibly terminates any worker
#     processes already mid-computation (see _shutdown_executor_now),
#     since a ProcessPoolExecutor can't cooperatively cancel a task
#     that's already running.
#   - The outer dialog/thread architecture (background thread submits
#     work, polls for completions, posts UI updates via master.after)
#     is unchanged.

import os
import time
import threading
from concurrent.futures import ProcessPoolExecutor, as_completed
import tkinter as tk
from tkinter import ttk, messagebox
from GameLogic import get_all_legal_moves, format_move_san

# Below this requested depth, a Perft run is cheap enough (tens to a few
# hundred nodes) that sequential execution beats paying process-pool
# startup cost.
PARALLEL_MIN_DEPTH = 3


def _perft_rec(board, turn, depth):
    """Plain recursive perft counter. Runs inside a worker process, one
    call per root move's subtree — no cancellation checks here, since
    cancelling a subtree that's already been dispatched to a worker
    process means terminating that process (see _shutdown_executor_now),
    not a cooperative check inside the recursion."""
    if depth == 0:
        return 1
    if depth == 1:
        return len(get_all_legal_moves(board, turn))
    total = 0
    opp = 'black' if turn == 'white' else 'white'
    for m in get_all_legal_moves(board, turn):
        rec = board.make_move_track(m[0], m[1])
        total += _perft_rec(board, opp, depth - 1)
        board.unmake_move(rec)
    return total


def _perft_subtree_task(child_board, opp_turn, remaining_depth):
    """The unit of work sent to each worker process: count leaves under
    one already-applied root move. Module-level (not a closure) so
    ProcessPoolExecutor can pickle and import it in the child process."""
    return _perft_rec(child_board, opp_turn, remaining_depth)


def _shutdown_executor_now(executor):
    """shutdown(wait=False, cancel_futures=True) only cancels futures that
    haven't started running yet — it can't stop a worker process that's
    already mid-recursion. For a Cancel button that actually cancels, we
    additionally terminate any still-alive worker processes directly.
    This reaches into a private attribute (_processes); there's no public
    API for "kill running work right now" on ProcessPoolExecutor, and an
    orphaned worker process burning CPU after the user hit Cancel is worse
    than depending on that attribute."""
    try:
        executor.shutdown(wait=False, cancel_futures=True)
    except Exception:
        pass
    try:
        for proc in list(executor._processes.values()):
            if proc.is_alive():
                proc.terminate()
    except Exception:
        pass


def _sequential_root_results(child_boards, opp, depth):
    """Depth < PARALLEL_MIN_DEPTH fallback: same computation, single process."""
    for idx in range(len(child_boards)):
        yield idx, _perft_subtree_task(child_boards[idx], opp, depth - 1)


def _parallel_root_results(child_boards, opp, depth, max_workers, executor_holder, cancel_event):
    """depth >= PARALLEL_MIN_DEPTH path: one task per root move, spread
    across a process pool. Yields (idx, sub_nodes) as each completes —
    NOT in root-move order, since faster subtrees finish first."""
    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        executor_holder['executor'] = executor
        future_to_idx = {
            executor.submit(_perft_subtree_task, child_boards[idx], opp, depth - 1): idx
            for idx in range(len(child_boards))
        }
        for future in as_completed(future_to_idx):
            if cancel_event.is_set():
                break
            idx = future_to_idx[future]
            try:
                sub_nodes = future.result()
            except Exception:
                sub_nodes = 0
            yield idx, sub_nodes
    executor_holder.pop('executor', None)


def launch_move_checker_dialog(master, board, turn, depth, colors, is_start_pos):
    """Runs an asynchronous, non-blocking Perft test with a live progress dialog.
    Root moves are dispatched to a process pool (depth >= PARALLEL_MIN_DEPTH)
    so subtree counts run in parallel across CPU cores instead of one at a time."""

    START_POS_PERFT = {
        1:  20,
        2:  400,
        3:  8902,
        4:  197281,
        5:  4865609,
        6:  119060324,
        7:  3195901860,
        8:  84997849941,
        9:  2439530234167,
        10: 69352859712417,
        11: 2097651003696556,
        12: 62854969295001380
    }

    dialog = tk.Toplevel(master)
    dialog.title(f"Perft Runner (Depth {depth})")
    dialog.configure(bg=colors['bg_dark'])
    dialog.geometry("440x240")
    dialog.resizable(False, False)
    dialog.transient(master)
    dialog.grab_set()

    dialog.update_idletasks()
    mx = master.winfo_x() + (master.winfo_width() - 440) // 2
    my = master.winfo_y() + (master.winfo_height() - 240) // 2
    dialog.geometry(f"440x240+{mx}+{my}")

    ttk.Label(dialog, text=f"Computing Perft Depth {depth}...", style='Header.TLabel').pack(pady=(12, 4))
    status_lbl = ttk.Label(dialog, text="Initializing search...", style='SmallHeader.TLabel')
    status_lbl.pack(pady=2)

    progress_var = tk.DoubleVar(value=0.0)
    progress_bar = ttk.Progressbar(dialog, variable=progress_var, maximum=100.0, length=380)
    progress_bar.pack(pady=8)

    stats_lbl = tk.Label(
        dialog, text="Nodes: 0  |  Time: 0.0s  |  Speed: 0.0 KNPS",
        bg=colors['bg_dark'], fg=colors['text_light'], font=('Courier', 10)
    )
    stats_lbl.pack(pady=4)

    cancel_event = threading.Event()
    executor_holder = {}   # populated only while a process pool is live, so on_cancel can reach it

    def on_cancel():
        cancel_event.set()
        executor = executor_holder.get('executor')
        if executor is not None:
            _shutdown_executor_now(executor)
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

        # One independent, already-move-applied board per root move, plus
        # its SAN label computed up front. `board` itself is never mutated
        # here (each root move gets its own clone), so it can be used
        # directly as SAN's "board_before" reference for every move.
        sans         = [None] * total_root_moves
        child_boards = [None] * total_root_moves
        for idx, m in enumerate(root_moves):
            child = board.clone()
            child.make_move(m[0], m[1])
            sans[idx] = format_move_san(board, child, m)
            child_boards[idx] = child

        divide_results = [None] * total_root_moves
        total_nodes = 0
        completed = 0

        if depth < PARALLEL_MIN_DEPTH:
            results_iter = _sequential_root_results(child_boards, opp, depth)
        else:
            max_workers = os.cpu_count() or 4
            results_iter = _parallel_root_results(
                child_boards, opp, depth, max_workers, executor_holder, cancel_event)

        for idx, sub_nodes in results_iter:
            if cancel_event.is_set():
                return

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

        if cancel_event.is_set():
            return

        elapsed = max(0.001, time.time() - t0)
        knps = (total_nodes / elapsed / 1000) if elapsed > 0 else 0
        expected = START_POS_PERFT.get(depth) if is_start_pos else None
        is_pass = (total_nodes == expected) if expected is not None else True

        # Print divide results to terminal, in original root-move order
        # (task completion order is nondeterministic under the pool).
        log_lines = [
            f"\n--- PERFT (Depth {depth}, Turn: {turn.capitalize()}) ---",
            f"Time: {elapsed:.3f}s | Speed: {knps:.1f} KNPS | Total Nodes: {total_nodes:,}"
        ]
        if expected is not None:
            status_str = "PASS [OK]" if is_pass else f"FAIL [Expected: {expected:,}]"
            log_lines.append(f"Standard Chess Reference Comparison: {status_str}")

        log_lines.append("\nPerft Divide (Branch Leaf Counts):")
        for i, (san, m, cnt) in enumerate(divide_results, 1):
            log_lines.append(f"  {i:2d}. {san.ljust(6)} ({m[0]} -> {m[1]}): {cnt:,}")

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
                        f"SUCCESS: Standard Chess Perft Depth {depth} verified!\n\n"
                        f"Total Nodes: {total_nodes:,} / {expected:,}\n"
                        f"Time: {elapsed:.3f}s ({knps:.1f} KNPS)"
                    )
                else:
                    messagebox.showerror(
                        f"Perft Depth {depth} Failed",
                        f"MISMATCH DETECTED at Depth {depth}!\n\n"
                        f"Actual Nodes: {total_nodes:,}\n"
                        f"Expected: {expected:,}\n\n"
                        f"See console divide log for details."
                    )
            else:
                messagebox.showinfo(
                    f"Perft Depth {depth} Complete",
                    f"Position Perft Complete (Depth {depth}):\n\n"
                    f"Total Nodes: {total_nodes:,}\n"
                    f"Time: {elapsed:.3f}s ({knps:.1f} KNPS)"
                )

        master.after(0, finish_ui)

    threading.Thread(target=worker, daemon=True).start()