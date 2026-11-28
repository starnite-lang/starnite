#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# Functions that yield (section 10.6), checked two ways beyond the corpus. A local of such a
# function stays a C local only when the compiler has shown that no value of it is needed after
# a stop; everything else is kept in the frame. And a for loop over a call of a yielding function
# in sight is written with the function in place of the loop, with no iterator at all, which is
# how the corpus runs these tests. So each tests/run/yield_*.stn is
#   1. built again with STN_NO_FUSE, which makes an iterator for every loop, in debug and release;
#   2. and with STN_GEN_ALL as well, which keeps every local in the frame: the output must be
#      the one in its .out file each time;
#   3. compiled as C, both ways, with only the warnings for a variable read before it is
#      written: a local that a resume jumps past and then reads is one.
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
starnite=${STARNITE:-"$root/_build/default/compiler/main.exe"}
cc=${CC:-cc}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0; pass=0
export STN_CHECK_UNIQUE=1
for f in "$here"/run/yield_*.stn; do
    name=$(basename "$f" .stn)
    for mode in "" --release; do
        STN_NO_FUSE=1 "$starnite" run $mode "$f" < /dev/null > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out"
        if cmp -s "$tmp/out" "$here/run/$name.out"; then pass=$((pass + 1))
        else echo "FAIL yield/$name an iterator for every loop ${mode:-debug}"; diff "$here/run/$name.out" "$tmp/out" | head -10; fail=$((fail + 1)); fi
        STN_NO_FUSE=1 STN_GEN_ALL=1 "$starnite" run $mode "$f" < /dev/null > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out"
        if cmp -s "$tmp/out" "$here/run/$name.out"; then pass=$((pass + 1))
        else echo "FAIL yield/$name every local in the frame ${mode:-debug}"; diff "$here/run/$name.out" "$tmp/out" | head -10; fail=$((fail + 1)); fi
    done
    for fuse in "" 1; do
        STN_NO_FUSE=$fuse "$starnite" emit-c "$f" > "$tmp/$name.c" 2> "$tmp/err" || { echo "FAIL yield/$name emit-c"; head -5 "$tmp/err"; fail=$((fail + 1)); continue; }
        "$cc" -std=c11 -O2 -fno-strict-aliasing -w -Wno-unknown-warning-option -Wuninitialized -Wmaybe-uninitialized -I"$root/runtime" -c "$tmp/$name.c" -o "$tmp/$name.o" 2> "$tmp/warn"
        if grep -q "uninitialized" "$tmp/warn"; then echo "FAIL yield/$name reads a local before it is written"; grep -A3 "uninitialized" "$tmp/warn" | head -12; fail=$((fail + 1))
        else pass=$((pass + 1)); fi
    done
done
echo "$pass passed, $fail failed"
[ "$fail" = 0 ]
