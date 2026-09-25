"""Standalone UI for validation, perft, and deterministic bench testing."""

import queue
import sys
import threading
import tkinter as tk
from tkinter import ttk
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from tests.headless import run_bench, run_perft


class TesterApp:
    def __init__(self, master):
        self.master = master
        master.title("Chess Engine Test Lab")
        master.minsize(760, 520)
        self.output_queue = queue.Queue()
        self.running = False

        controls = ttk.Frame(master, padding=12)
        controls.pack(fill=tk.X)

        self.depth = tk.IntVar(value=4)
        ttk.Label(controls, text="Test depth").grid(row=0, column=0, sticky="w")
        ttk.Spinbox(controls, from_=1, to=15, textvariable=self.depth, width=6).grid(row=0, column=1, padx=(6, 18))

        self.perft_button = ttk.Button(controls, text="Run Perft", command=self.start_perft)
        self.perft_button.grid(row=1, column=0, sticky="ew", pady=(12, 0))
        self.bench_button = ttk.Button(controls, text="Run Bench", command=self.start_bench)
        self.bench_button.grid(row=1, column=1, sticky="ew", padx=(8, 0), pady=(12, 0))
        self.baseline_button = ttk.Button(controls, text="Write Bench Baseline", command=self.write_baseline)
        self.baseline_button.grid(row=1, column=2, sticky="ew", padx=(8, 0), pady=(12, 0))

        self.output = tk.Text(master, wrap=tk.WORD, font=("Consolas", 10), state=tk.DISABLED)
        self.output.pack(fill=tk.BOTH, expand=True, padx=12, pady=(0, 12))
        master.after(50, self.drain_output)

    def log(self, message):
        self.output_queue.put(message)

    def drain_output(self):
        try:
            while True:
                self.output.config(state=tk.NORMAL)
                self.output.insert(tk.END, self.output_queue.get_nowait() + "\n")
                self.output.see(tk.END)
                self.output.config(state=tk.DISABLED)
        except queue.Empty:
            pass
        self.master.after(50, self.drain_output)

    def set_running(self, value):
        self.running = value
        state = tk.DISABLED if value else tk.NORMAL
        for button in (self.perft_button, self.bench_button, self.baseline_button):
            button.config(state=state)

    def start_task(self, label, action):
        if self.running:
            return
        self.set_running(True)
        self.log(f"\n--- {label} ---")

        def worker():
            try:
                action()
            except Exception as error:
                self.log(f"FAIL  {type(error).__name__}: {error}")
            finally:
                self.master.after(0, lambda: self.set_running(False))

        threading.Thread(target=worker, daemon=True).start()

    def start_perft(self):
        self.start_task("PERFT", lambda: run_perft(self.depth.get(), self.log))

    def start_bench(self):
        self.start_task("BENCH", lambda: run_bench(self.depth.get(), report=self.log))

    def write_baseline(self):
        self.start_task("WRITE BENCH BASELINE", lambda: run_bench(
            self.depth.get(), write_baseline=True, report=self.log
        ))

if __name__ == "__main__":
    root = tk.Tk()
    TesterApp(root)
    root.mainloop()
