#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# measure.py INPUT ROUNDS NAME=PROGRAM...: runs each program on the input, in turn, ROUNDS times,
# and prints for each the best wall time, the CPU time of that run and the peak memory.
import os, subprocess, sys, time
inp, rounds = sys.argv[1], int(sys.argv[2])
progs = [a.split("=", 1) for a in sys.argv[3:]]
best = {}
for _ in range(rounds):
    for name, prog in progs:
        with open(inp, "rb") as f, open(os.devnull, "wb") as out:
            t0 = time.perf_counter()
            p = subprocess.Popen([prog], stdin=f, stdout=out)
            _, status, ru = os.wait4(p.pid, 0)
            wall = time.perf_counter() - t0
        if status != 0:
            sys.exit(f"{name} failed")
        cur = (wall, ru.ru_utime + ru.ru_stime, ru.ru_maxrss / 1024)
        if name not in best or wall < best[name][0]:
            best[name] = cur
print(f"{'build':12s} {'time s':>8s} {'cpu s':>8s} {'peak MiB':>9s}")
for name, _ in progs:
    w, c, m = best[name]
    print(f"{name:12s} {w:8.3f} {c:8.3f} {m:9.1f}")
