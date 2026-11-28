#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# A million JSON lines (write.stn) built as one string and printed once, against written piece by
# piece: the best wall time of five runs and the peak memory of each, and a check that the two
# write the same bytes.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
(cd "$repo" && "$repo/_build/default/compiler/main.exe" build --release "$here/write.stn" -o "$out/write")
python3 - "$out/write" <<'PY'
import hashlib, os, subprocess, sys, time
exe = sys.argv[1]
sums = {}
print(f"{'way':8s} {'seconds':>8s} {'peak MiB':>9s} {'output MiB':>11s}")
for way in ("whole", "pieces"):
    best = None
    for _ in range(5):
        r, w = os.pipe(); os.write(w, way.encode()); os.close(w)
        t0 = time.perf_counter()
        p = subprocess.Popen([exe], stdin=r, stdout=subprocess.PIPE); os.close(r)
        h = hashlib.sha256(); size = 0
        for chunk in iter(lambda: p.stdout.read(1 << 20), b""):
            h.update(chunk); size += len(chunk)
        _, status, ru = os.wait4(p.pid, 0)
        wall = time.perf_counter() - t0
        if status != 0: sys.exit(f"{way} failed")
        if best is None or wall < best[0]: best = (wall, ru.ru_maxrss / 1024)
        sums[way] = h.hexdigest()
    print(f"{way:8s} {best[0]:8.3f} {best[1]:9.1f} {size / 1048576:11.1f}")
if sums["whole"] != sums["pieces"]: sys.exit("the two ways write different bytes")
PY
