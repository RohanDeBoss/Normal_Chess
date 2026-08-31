# MoveChecker.py (v2 - Use full fens)

import os
import time
import threading
import multiprocessing as mp
import tkinter as tk
from tkinter import ttk, messagebox
from GameLogic import get_all_legal_moves, format_move_san, Queen
from EngineRuntime import board_to_fen

PARALLEL_MIN_DEPTH = 3

def _perft_rec(board, turn, depth):
    if depth == 0:
        return 1
    if depth == 1:
        return len(get_all_legal_moves(board, turn))
    total = 0
    opp = 'black' if turn == 'white' else 'white'
    for m in get_all_legal_moves(board, turn):
        promo = m[2] if len(m) > 2 and m[2] is not None else Queen
        rec = board.make_move_track(m[0], m[1], promo)
        total += _perft_rec(board, opp, depth - 1)
        board.unmake_move(rec)
    return total

def _perft_task_wrapper(args):
    child_board, opp_turn, remaining_depth = args
    return _perft_rec(child_board, opp_turn, remaining_depth)

def launch_move_checker_dialog(master, board, turn, depth, colors, is_start_pos=False):
    # Canonical Chess Programming Wiki (CPW) reference Perft positions
    # Keyed by 4-field normalized FEN: <piece placement> <turn> <castling> <ep>
    PERFT_POSITIONS = {
        # Position 1 — Initial Standard Starting Position
        "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -": {
            "name": "Start Position",
            "counts": {
                1: 20, 2: 400, 3: 8902, 4: 197281, 5: 4865609,
                6: 119060324, 7: 3195901860, 8: 84997849941,
            }
        },
        # Position 2 — Kiwipete (Peter Ellis) - Castling & Pin Stress Test
        "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq -": {
            "name": "Position 2 (Kiwipete)",
            "counts": {
                1: 48, 2: 2039, 3: 97862, 4: 4085603, 5: 193690690, 6: 8031647685,
            }
        },
        # Position 3 — Endgame En Passant Discovered Check Torture Test
        "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - -": {
            "name": "Position 3 (EP Discovered Check)",
            "counts": {
                1: 14, 2: 191, 3: 2812, 4: 43238, 5: 674624, 6: 11030083, 7: 178633661,
            }
        },
        # Position 4 — Complex Promotions, Pins & Skewers
        "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq -": {
            "name": "Position 4 (Promotions & Pins)",
            "counts": {
                1: 6, 2: 264, 3: 9467, 4: 422333, 5: 15833292, 6: 706045033,
            }
        },
        # Position 4 Mirrored — Black to Move
        "r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ -": {
            "name": "Position 4 Mirrored (Black)",
            "counts": {
                1: 6, 2: 264, 3: 9467, 4: 422333, 5: 15833292, 6: 706045033,
            }
        },
        # Position 5 — Discovered Checks & Underpromotions
        "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ -": {
            "name": "Position 5 (Discovered Checks)",
            "counts": {
                1: 44, 2: 1486, 3: 62379, 4: 2103487, 5: 89941194,
            }
        },
        # Position 6 — Edwards / Talkchess Middlegame
        "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - -": {
            "name": "Position 6 (Middlegame)",
            "counts": {
                1: 46, 2: 2079, 3: 89890, 4: 3894594, 5: 164075551, 6: 6923051137,
            }
        },
    }

    dialog = tk.Toplevel(master)
    dialog.title(f"Perft Runner (Depth {depth})")
    dialog.configure(bg=colors['bg_dark'])
    dialog.geometry("460x250")
    dialog.resizable(False, False)
    dialog.transient(master)
    dialog.grab_set()

    dialog.update_idletasks()
    mx = master.winfo_x() + (master.winfo_width() - 460) // 2
    my = master.winfo_y() + (master.winfo_height() - 250) // 2
    dialog.geometry(f"460x250+{mx}+{my}")

    ttk.Label(dialog, text=f"Computing Perft Depth {depth}...", style='Header.TLabel').pack(pady=(12, 4))
    status_lbl = ttk.Label(dialog, text="Initializing search...", style='SmallHeader.TLabel')
    status_lbl.pack(pady=2)

    progress_var = tk.DoubleVar(value=0.0)
    progress_bar = ttk.Progressbar(dialog, variable=progress_var, maximum=100.0, length=400)
    progress_bar.pack(pady=8)

    stats_lbl = tk.Label(
        dialog, text="Nodes: 0  |  Time: 0.0s  |  Speed: 0.0 KNPS",
        bg=colors['bg_dark'], fg=colors['text_light'], font=('Courier', 10)
    )
    stats_lbl.pack(pady=4)

    cancel_event = threading.Event()
    pool_holder = {}

    def on_cancel():
        cancel_event.set()
        pool = pool_holder.get('pool')
        if pool:
            try:
                pool.terminate()
                pool.join()
            except Exception:
                pass
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

        sans = [None] * total_root_moves
        child_boards = [None] * total_root_moves
        for idx, m in enumerate(root_moves):
            child = board.clone()
            promo = m[2] if len(m) > 2 and m[2] is not None else Queen
            child.make_move(m[0], m[1], promo)
            sans[idx] = format_move_san(board, child, m)
            child_boards[idx] = child

        divide_results = [None] * total_root_moves
        total_nodes = 0
        completed = 0

        if depth < PARALLEL_MIN_DEPTH:
            for idx in range(total_root_moves):
                if cancel_event.is_set():
                    return
                sub_nodes = _perft_rec(child_boards[idx], opp, depth - 1)
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
        else:
            num_workers = min(os.cpu_count() or 4, total_root_moves)
            pool = mp.Pool(processes=num_workers)
            pool_holder['pool'] = pool

            tasks = [(child_boards[i], opp, depth - 1) for i in range(total_root_moves)]
            async_results = [pool.apply_async(_perft_task_wrapper, (t,)) for t in tasks]

            for idx, res in enumerate(async_results):
                while not res.ready():
                    if cancel_event.is_set():
                        pool.terminate()
                        pool.join()
                        return
                    time.sleep(0.02)

                sub_nodes = res.get()
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

            pool.close()
            pool.join()
            pool_holder.pop('pool', None)

        if cancel_event.is_set():
            return

        elapsed = max(0.001, time.time() - t0)
        knps = (total_nodes / elapsed / 1000) if elapsed > 0 else 0
        
        # Match normalized 4-part FEN (<piece placement> <turn> <castling> <ep>)
        full_fen = board_to_fen(board, turn)
        fen_parts = full_fen.split()
        norm_fen = " ".join(fen_parts[:4])
        
        ref_entry = PERFT_POSITIONS.get(norm_fen)
        if not ref_entry:
            # Fallback to piece-placement-only key matching if shorthand was used
            ref_entry = next((v for k, v in PERFT_POSITIONS.items() if k.split()[0] == fen_parts[0]), None)

        pos_name = ref_entry["name"] if ref_entry else "Custom Position"
        expected = ref_entry["counts"].get(depth) if ref_entry else None
        is_pass = (total_nodes == expected) if expected is not None else True

        log_lines = [
            f"\n--- PERFT: {pos_name} (Depth {depth}, Turn: {turn.capitalize()}) ---",
            f"FEN: {full_fen}",
            f"Time: {elapsed:.3f}s | Speed: {knps:.1f} KNPS | Total Nodes: {total_nodes:,}"
        ]
        if expected is not None:
            status_str = "PASS [OK]" if is_pass else f"FAIL [Expected: {expected:,}]"
            log_lines.append(f"Standard Chess Reference Comparison: {status_str}")
        else:
            log_lines.append("No reference table for this position — count unverified.")

        log_lines.append("\nPerft Divide (Branch Leaf Counts):")
        for i, (san, m, cnt) in enumerate(divide_results, 1):
            log_lines.append(f"  {i:2d}. {san.ljust(8)} ({m[0]} -> {m[1]}): {cnt:,}")

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
                        f"SUCCESS: {pos_name} Depth {depth} verified!\n\n"
                        f"Total Nodes: {total_nodes:,} / {expected:,}\n"
                        f"Time: {elapsed:.3f}s ({knps:.1f} KNPS)"
                    )
                else:
                    messagebox.showerror(
                        f"Perft Depth {depth} Failed",
                        f"MISMATCH DETECTED: {pos_name} at Depth {depth}!\n\n"
                        f"Actual Nodes: {total_nodes:,}\n"
                        f"Expected: {expected:,}\n\n"
                        f"See console divide log for details."
                    )
            else:
                messagebox.showinfo(
                    f"Perft Depth {depth} Complete",
                    f"Custom Position Perft Complete (Depth {depth}):\n\n"
                    f"Total Nodes: {total_nodes:,}\n"
                    f"Time: {elapsed:.3f}s ({knps:.1f} KNPS)"
                )

        master.after(0, finish_ui)

    threading.Thread(target=worker, daemon=True).start()