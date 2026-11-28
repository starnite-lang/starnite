#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Functions that yield against the loops they stand for (iter.stn), and against Rust's iterators,
# static and behind Box<dyn Iterator> (iter.rs): the best wall time of five runs as nanoseconds
# per value, and the peak memory. Rust is left out when rustc is not there.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
(cd "$repo" && "$repo/_build/default/compiler/main.exe" build --release "$here/iter.stn" -o "$out/starnite")
rust=0
if command -v rustc >/dev/null 2>&1; then rustc -C opt-level=3 -C overflow-checks=on -o "$out/rust" "$here/iter.rs" 2>/dev/null && rust=1; fi
python3 - "$out" "$rust" <<'PY'
import os, subprocess, sys, time
out, rust = sys.argv[1], sys.argv[2] == "1"
cases = [("starnite", c) for c in ("loop", "iter", "loop3", "iter3", "array")]
if rust: cases += [("rust", c) for c in ("iter-static", "iter-dyn", "iter3-static", "iter3-dyn")]
sums = {}
print(f"{'build':9s} {'case':13s} {'ns per value':>13s} {'peak MiB':>9s}")
for exe, case in cases:
    best = None
    for _ in range(5):
        r, w = os.pipe(); os.write(w, case.encode()); os.close(w)
        t0 = time.perf_counter()
        p = subprocess.Popen([os.path.join(out, exe)], stdin=r, stdout=subprocess.PIPE); os.close(r)
        text = p.stdout.read().strip(); _, status, ru = os.wait4(p.pid, 0)
        wall = time.perf_counter() - t0
        if status != 0: sys.exit(f"{exe} {case} failed")
        if best is None or wall < best[0]: best = (wall, ru.ru_maxrss / 1024)
    sums.setdefault("3" in case or case == "array", set()).add(text)
    print(f"{exe:9s} {case:13s} {best[0] / 200e6 * 1e9:13.2f} {best[1]:9.1f}")
if any(len(v) != 1 for v in sums.values()): sys.exit("the cases disagree on a sum")
PY
