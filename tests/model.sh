#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# The model of counting, reuse and destination passing (section 21.4, tests/model/model.ml):
# properties P1 and P2 on random programs, and then the same with a fault put into the model, to
# see that the test would find one.
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
model=${MODEL:-"$root/_build/default/tests/model/model.exe"}
fail=0; pass=0
for seed in 1 2 3; do
    if out=$("$model" --count 5000 --seed $seed); then pass=$((pass + 1)); else echo "FAIL model, seed $seed"; echo "$out" | head -30; fail=$((fail + 1)); fi
done
echo "$out"
# no-dup: a borrowed value is returned without a reference; no-drop: what a function still owns
# is not released when it returns; reuse-shared: a cell something else holds is used again;
# wrong-hole: the destination is moved to the wrong field
for fault in no-dup no-drop reuse-shared wrong-hole; do
    if "$model" --count 5000 --fault $fault > /dev/null; then echo "FAIL the fault $fault went unnoticed"; fail=$((fail + 1)); else pass=$((pass + 1)); fi
done
echo "$pass passed, $fail failed"
[ "$fail" = 0 ]
