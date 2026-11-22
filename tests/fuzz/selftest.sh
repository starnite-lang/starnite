#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# Checks of the fuzzer itself (section 21.2). Negative fuzzing must find nothing wrong with the
# compiler as it is, every kind of violation being tried. Given a compiler with a fault put in
# on purpose (buggy.sh), the fuzzer must see the fault, and what it shrinks the failing program
# to must be small and still have the fault: the real compiler rejects a violation that was
# shrunk with the code it was made for, and the programs of the other faults run as they do
# with the real compiler. Prints "pass NAME" or "FAIL NAME: why" for each check; the status says
# whether all passed.
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$(dirname "$here")")
starnite=${STARNITE:-"$root/_build/default/compiler/main.exe"}
fuzz=${FUZZ:-"$root/_build/default/tests/fuzz/fuzz.exe"}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0
ok() { printf 'pass %s\n' "$1"; }
bad() { printf 'FAIL %s\n' "$*"; fail=$((fail + 1)); }
lines() { wc -l < "$1" | tr -d ' '; }
# the code of the first diagnostic of a program, by the real compiler
code_of() { "$starnite" check --json "$1" 2>&1 | head -1 | sed -n 's/.*"code":"\([^"]*\)".*/\1/p'; }
# the fuzzer, with a compiler that has a fault: the real one runs under buggy.sh
export REAL_STARNITE=$starnite
with_fault() { fault=$1; shift; BUGGY=$fault STARNITE="$here/buggy.sh" "$fuzz" "$@"; }

# 1. a compiler that is right: all 100 violations are rejected, with the codes they have, and
# none of the kinds was left out
out=$(STARNITE="$starnite" "$fuzz" --negative-only --count 100 --seed 1 2>&1); status=$?
counts=$(printf '%s\n' "$out" | sed -n 's/^  .* \([0-9][0-9]*\), *[0-9][0-9]* made of.*/\1/p')
kinds=$(printf '%s\n' "$counts" | grep -c .)
if [ $status != 0 ] || ! printf '%s\n' "$out" | grep -q '^100 of 100 agreed'; then
    bad "negative fuzzing against the compiler: it did not agree on all of 100 mutations"; printf '%s\n' "$out" | head -20
elif [ "$kinds" -lt 10 ] || printf '%s\n' "$counts" | grep -qx 0; then
    bad "negative fuzzing: a kind of violation was never tried"; printf '%s\n' "$out" | tail -20
else ok "negative fuzzing against the compiler ($kinds kinds of violation)"; fi

# 2. a checker that accepts a use after take: seen, and shrunk to a few lines that the real
# compiler rejects with E0302
d="$tmp/take"
out=$(with_fault accept-take --negative-only --count 80 --seed 1 --shrink --keep "$d" 2>&1); status=$?
n=$(ls "$d"/*.neg.min.stn 2>/dev/null | wc -l | tr -d ' ')
if [ $status != 1 ] || ! printf '%s\n' "$out" | grep -q "was accepted; it should be rejected with E0302"; then
    bad "fault accept-take: the fuzzer did not report an accepted mutation"; printf '%s\n' "$out" | tail -10
elif [ "$n" = 0 ]; then bad "fault accept-take: nothing was shrunk"
else
    all=1
    for m in "$d"/*.neg.min.stn; do
        if [ "$(lines "$m")" -gt 60 ] || [ "$(code_of "$m")" != E0302 ]; then
            bad "fault accept-take: $(basename "$m") has $(lines "$m") lines and is rejected with '$(code_of "$m")'"; all=0
        fi
    done
    [ $all = 1 ] && ok "fault accept-take: $n programs shrunk, each a use after take"
fi

# 3. a checker that says E0303 for E0304: seen, and shrunk to a program that the real compiler
# rejects with E0304
d="$tmp/code"
out=$(with_fault wrong-code --negative-only --count 40 --seed 1 --shrink --keep "$d" 2>&1); status=$?
n=$(ls "$d"/*.neg.min.stn 2>/dev/null | wc -l | tr -d ' ')
if [ $status != 1 ] || ! printf '%s\n' "$out" | grep -q "was rejected with E0303; it should be E0304"; then
    bad "fault wrong-code: the fuzzer did not report the wrong code"; printf '%s\n' "$out" | tail -10
elif [ "$n" = 0 ]; then bad "fault wrong-code: nothing was shrunk"
else
    all=1
    for m in "$d"/*.neg.min.stn; do
        if [ "$(lines "$m")" -gt 20 ] || [ "$(code_of "$m")" != E0304 ]; then
            bad "fault wrong-code: $(basename "$m") has $(lines "$m") lines and is rejected with '$(code_of "$m")'"; all=0
        fi
    done
    [ $all = 1 ] && ok "fault wrong-code: $n programs shrunk, each a missing mut marker"
fi

# 4. a C build that prints one line more for a program that sorts: the interpreter and the C build
# differ, and the program is shrunk to one that still sorts, and that the real compiler runs the
# same on both
seed=
for s in $(seq 1 200); do
    if "$fuzz" --print --seed "$s" | grep -q 'sort(mut'; then seed=$s; break; fi
done
if [ -z "$seed" ]; then bad "fault c-output: none of 200 programs sorts"
else
    d="$tmp/cout"
    out=$(with_fault c-output --no-negative --seed "$seed" --count 1 --shrink --keep "$d" 2>&1); status=$?
    m="$d/case$seed.min.stn"
    if [ $status != 1 ] || ! printf '%s\n' "$out" | grep -q "differ"; then
        bad "fault c-output: the fuzzer did not report a difference (seed $seed)"; printf '%s\n' "$out" | tail -10
    elif [ ! -f "$m" ]; then bad "fault c-output: nothing was shrunk (seed $seed)"
    elif [ "$(lines "$m")" -gt 40 ] || ! grep -q 'sort(mut' "$m"; then
        bad "fault c-output: the program has $(lines "$m") lines, and sort: $(grep -c 'sort(mut' "$m")"
    elif ! "$starnite" run --interp "$m" > "$tmp/i.out" 2>&1 || ! "$starnite" run "$m" > "$tmp/c.out" 2>&1 || ! cmp -s "$tmp/i.out" "$tmp/c.out"; then
        bad "fault c-output: the shrunk program does not run alike on the real compiler"
    else ok "fault c-output: $(lines "$d/case$seed.stn") lines shrunk to $(lines "$m")"; fi
fi

# 5. --reduce: a program of 200 lines and more, kept while it compiles and has a main, is a few
# lines of main
"$fuzz" --print --seed 7 > "$tmp/p.stn"
STARNITE="$starnite" "$fuzz" --reduce "$tmp/p.stn" --keeping 'fn main' > "$tmp/r.stn" 2> "$tmp/r.err"; status=$?
if [ $status != 0 ] || [ "$(lines "$tmp/r.stn")" -gt 6 ] || ! grep -q 'fn main' "$tmp/r.stn" || ! "$starnite" check "$tmp/r.stn" > /dev/null 2>&1; then
    bad "--reduce --keeping: exit $status, $(lines "$tmp/r.stn") lines"; cat "$tmp/r.err"
else ok "--reduce --keeping: $(lines "$tmp/p.stn") lines reduced to $(lines "$tmp/r.stn")"; fi

[ $fail = 0 ]
