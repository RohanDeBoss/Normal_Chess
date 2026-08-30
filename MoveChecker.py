# MoveChecker.py

import tkinter as tk
from tkinter import ttk, messagebox
import threading
import time
from GameLogic import get_all_legal_moves, format_move_san

def launch_move_checker_dialog(master, board, turn, depth, colors, is_start_pos):
    """Runs an asynchronous, non-blocking Perft test with a live progress dialog."""
    
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

    def on_cancel():
        cancel_event.set()
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

        def _perft_rec(b, current_turn, d):
            if cancel_event.is_set():
                return 0
            if d == 0:
                return 1
            if d == 1:
                return len(get_all_legal_moves(b, current_turn))
            total = 0
            opp = 'black' if current_turn == 'white' else 'white'
            for m in get_all_legal_moves(b, current_turn):
                if cancel_event.is_set():
                    return 0
                rec = b.make_move_track(m[0], m[1])
                total += _perft_rec(b, opp, d - 1)
                b.unmake_move(rec)
            return total

        t0 = time.time()
        total_nodes = 0
        divide_results = []
        opp = 'black' if turn == 'white' else 'white'

        for idx, m in enumerate(root_moves, 1):
            if cancel_event.is_set():
                return

            child = board.clone()
            rec = board.make_move_track(m[0], m[1])
            san = format_move_san(child, board, m)

            elapsed = max(0.001, time.time() - t0)
            knps = (total_nodes / elapsed / 1000) if elapsed > 0 else 0
            pct = ((idx - 1) / total_root_moves) * 100.0

            master.after(0, lambda p=pct, s=san, i=idx, tot=total_root_moves, n=total_nodes, el=elapsed, k=knps: [
                progress_var.set(p),
                status_lbl.config(text=f"Exploring branch {s} ({i}/{tot})..."),
                stats_lbl.config(text=f"Nodes: {n:,}  |  Time: {el:.1f}s  |  Speed: {k:.1f} KNPS")
            ])

            if depth == 1:
                sub_nodes = 1
            else:
                sub_nodes = _perft_rec(board, opp, depth - 1)

            board.unmake_move(rec)
            if cancel_event.is_set():
                return

            total_nodes += sub_nodes
            divide_results.append((san, m, sub_nodes))

        elapsed = max(0.001, time.time() - t0)
        knps = (total_nodes / elapsed / 1000) if elapsed > 0 else 0
        expected = START_POS_PERFT.get(depth) if is_start_pos else None
        is_pass = (total_nodes == expected) if expected is not None else True

        # Print divide results to terminal
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

        if not cancel_event.is_set():
            master.after(0, finish_ui)

    threading.Thread(target=worker, daemon=True).start()