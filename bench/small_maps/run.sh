#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Many small maps (small_maps.stn), with this checkout and with a baseline one, for maps of 2, 5,
# 8, 9 and 16 entries: the best wall time of five runs, and the peak memory.
# usage: run.sh BASE
set -euo pipefail
base=$(realpath "$1")
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
(cd "$base" && "$base/_build/default/compiler/main.exe" build --release "$here/small_maps.stn" -o "$out/previous")
(cd "$repo" && "$repo/_build/default/compiler/main.exe" build --release "$here/small_maps.stn" -o "$out/starnite")
python3 - "$out" <<'PY'
import os, subprocess, sys, time
out = sys.argv[1]
print(f"{'keys':>4s} {'previous s':>11s} {'starnite s':>11s} {'ratio':>6s} {'previous MiB':>13s} {'starnite MiB':>13s} {'ratio':>6s}")
for keys in (2, 5, 8, 9, 16):
    res = {}
    for name in ("previous", "starnite"):
        best = None; text = None
        for _ in range(5):
            r, w = os.pipe(); os.write(w, f"{keys}\n".encode()); os.close(w)
            t0 = time.perf_counter()
            p = subprocess.Popen([os.path.join(out, name)], stdin=r, stdout=subprocess.PIPE)
            os.close(r)
            got = p.stdout.read(); _, status, ru = os.wait4(p.pid, 0)
            wall = time.perf_counter() - t0
            if status != 0: sys.exit(f"{name} failed")
            if best is None or wall < best[0]: best = (wall, ru.ru_maxrss / 1024)
            text = got
        res[name] = (best, text)
    if res["previous"][1] != res["starnite"][1]: sys.exit(f"keys {keys}: the two print different things")
    (pt, pm), (st, sm) = res["previous"][0], res["starnite"][0]
    print(f"{keys:4d} {pt:11.3f} {st:11.3f} {st/pt:6.2f} {pm:13.1f} {sm:13.1f} {sm/pm:6.2f}")
PY
