#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# Constant stack (sections 9.5 and 9.7). tests/run/destination_passing.stn goes through the
# corpus on a few thousand elements, as deep as the reference interpreter can recurse. This runs
# the same program on a million with the debug and release C builds: a function that returns a
# constructor holding a call of itself must run as a loop, and a list must be released as one, or
# the stack runs out. The expected output is in tests/deep/destination_passing.out.
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
starnite=${STARNITE:-"$root/_build/default/compiler/main.exe"}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0; pass=0
# the compiler checks its own account of what is unique (section 6.2) while it runs here, and a
# release build keeps the tests that account lets it leave out
export STN_CHECK_UNIQUE=1
sed 's/4000/1000000/g; s/1600/400000/' "$here/run/destination_passing.stn" > "$tmp/deep.stn"
for mode in "" --release; do
    "$starnite" run $mode "$tmp/deep.stn" < /dev/null > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out"
    if cmp -s "$tmp/out" "$here/deep/destination_passing.out"; then pass=$((pass + 1))
    else echo "FAIL deep/destination_passing ${mode:-debug}"; diff "$here/deep/destination_passing.out" "$tmp/out" | head -10; fail=$((fail + 1)); fi
done
# releasing structures that are deep where a release cannot loop (section 9.7), all at once and
# a thousand heap blocks at a time
for mode in "" --release; do
    for budget in "" 1000; do
        STN_FREE_BUDGET=$budget "$starnite" run $mode "$here/deep/release.stn" < /dev/null > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out"
        if cmp -s "$tmp/out" "$here/deep/release.out"; then pass=$((pass + 1))
        else echo "FAIL deep/release ${mode:-debug} ${budget:+budget $budget}"; diff "$here/deep/release.out" "$tmp/out" | head -10; fail=$((fail + 1)); fi
    done
done
# a deep copy, asked for and made for a unique parameter, of a list a million long (section 6.2)
for mode in "" --release; do
    "$starnite" run $mode "$here/deep/copy.stn" < /dev/null > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out"
    if cmp -s "$tmp/out" "$here/deep/copy.out"; then pass=$((pass + 1))
    else echo "FAIL deep/copy ${mode:-debug}"; diff "$here/deep/copy.out" "$tmp/out" | head -10; fail=$((fail + 1)); fi
done
# the same of values that are deep along a field a copy cannot loop over, and through arrays,
# maps and structs: the copies nest only so far (section 6.2)
for mode in "" --release; do
    "$starnite" run $mode "$here/deep/copy_shapes.stn" < /dev/null > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out"
    if cmp -s "$tmp/out" "$here/deep/copy_shapes.out"; then pass=$((pass + 1))
    else echo "FAIL deep/copy_shapes ${mode:-debug}"; diff "$here/deep/copy_shapes.out" "$tmp/out" | head -10; fail=$((fail + 1)); fi
done
echo "$pass passed, $fail failed"
[ "$fail" = 0 ]
