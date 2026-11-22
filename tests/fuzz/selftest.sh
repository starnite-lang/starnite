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

# 2. a checker that accepts what it rejects with a code: seen, and shrunk to a few lines that the real
# compiler rejects with that code, a use after take and a match that does not cover every case
accepts() {
    code=$1; what=$2
    d="$tmp/accept-$code"
    out=$(with_fault "accept:$code" --negative-only --count 80 --seed 1 --shrink --keep "$d" 2>&1); status=$?
    n=$(ls "$d"/*.neg.min.stn 2>/dev/null | wc -l | tr -d ' ')
    if [ $status != 1 ] || ! printf '%s\n' "$out" | grep -q "was accepted; it should be rejected with $code"; then
        bad "fault accept:$code: the fuzzer did not report an accepted mutation"; printf '%s\n' "$out" | tail -10
    elif [ "$n" = 0 ]; then bad "fault accept:$code: nothing was shrunk"
    else
        all=1
        for m in "$d"/*.neg.min.stn; do
            if [ "$(lines "$m")" -gt 60 ] || [ "$(code_of "$m")" != "$code" ]; then
                bad "fault accept:$code: $(basename "$m") has $(lines "$m") lines and is rejected with '$(code_of "$m")'"; all=0
            fi
        done
        [ $all = 1 ] && ok "fault accept:$code: $n programs shrunk, each $what"
    fi
}
accepts E0302 "a use after take"
accepts E0202 "a match that does not cover every case"

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

# 6. --reduce of a program that imports a module that is next to it: the candidates are tried where
# the module is, so that the program is found to fail and is reduced, in the way it fails, and nothing
# is left in its directory
proj="$tmp/proj"; mkdir "$proj"
cat > "$proj/helpers.stn" <<'STN'
fn twice*(n: Int) -> Int:
    n * 2

fn name*() -> Str:
    "helper"
STN
cat > "$proj/main.stn" <<'STN'
import helpers

fn main():
    var xs: Array[Int] = [3, 1, 2]
    sort(mut xs)
    print(f"{helpers.twice(xs[0])}")
    print("unused")
STN
(cd "$tmp" && with_fault c-output --reduce "$proj/main.stn" > "$tmp/proj.out" 2> "$tmp/proj.err"); status=$?
left=$(ls -A "$proj" | tr '\n' ' ')
if [ $status != 0 ] || ! grep -q 'sort(mut' "$tmp/proj.out" || [ "$(lines "$tmp/proj.out")" -ge "$(lines "$proj/main.stn")" ]; then
    bad "--reduce next to a module: exit $status, $(lines "$tmp/proj.out") lines of $(lines "$proj/main.stn")"; cat "$tmp/proj.err"
elif [ "$left" != "helpers.stn main.stn " ]; then bad "--reduce next to a module left files in its directory: $left"
else ok "--reduce next to a module: $(lines "$proj/main.stn") lines reduced to $(lines "$tmp/proj.out")"; fi

# and by the code a program is rejected with, which a missing module would change
cat > "$proj/main2.stn" <<'STN'
import helpers

fn main():
    print("start")
    let n: Int = helpers.name()
    print(f"{n}")
    print("end")
STN
(cd "$tmp" && STARNITE="$starnite" "$fuzz" --reduce "$proj/main2.stn" --rejected E0201 > "$tmp/proj2.out" 2> "$tmp/proj2.err"); status=$?
cp "$tmp/proj2.out" "$proj/reduced.stn"
if [ $status != 0 ] || [ "$(lines "$tmp/proj2.out")" -ge "$(lines "$proj/main2.stn")" ] || [ "$(code_of "$proj/reduced.stn")" != E0201 ]; then
    bad "--reduce --rejected next to a module: exit $status, $(lines "$tmp/proj2.out") lines of $(lines "$proj/main2.stn"), rejected with '$(code_of "$proj/reduced.stn")'"; cat "$tmp/proj2.err"
else ok "--reduce --rejected next to a module: $(lines "$proj/main2.stn") lines reduced to $(lines "$tmp/proj2.out")"; fi

# 7. a match that a checker accepts although it has an arm too few, reduced while another match has the
# same header and the same arms, and one more: the reduction keeps the match that is the violation
proj="$tmp/proj3"; mkdir "$proj"
cat > "$proj/main.stn" <<'STN'
type Shape = Dot | Box(w: Int) | Named(n: Str)

fn one(s: Shape):
    match s:
        Dot -> print("a")
        Box(w) -> print("b")

fn two(s: Shape):
    match s:
        Dot -> print("a")
        Box(w) -> print("b")
        Named(n) -> print("c")

fn main():
    two(Dot)
STN
(cd "$tmp" && with_fault accept:E0202 --reduce "$proj/main.stn" --keeping-match 'match s:' --arm 'Dot -> print("a")' --arm 'Box(w) -> print("b")' > "$tmp/m.out" 2> "$tmp/m.err"); status=$?
cp "$tmp/m.out" "$proj/reduced.stn"
if [ $status != 0 ] || ! grep -q 'fn one' "$tmp/m.out" || [ "$(code_of "$proj/reduced.stn")" != E0202 ]; then
    bad "--keeping-match: exit $status, the match that is the violation is not kept: rejected with '$(code_of "$proj/reduced.stn")'"; cat "$tmp/m.err" "$tmp/m.out"
else ok "--keeping-match: the match with an arm too few is kept, and rejected with E0202 by the real compiler ($(lines "$proj/main.stn") lines reduced to $(lines "$tmp/m.out"))"; fi

# 8. the name that the reducer tries first for a file of its own is taken, by a file that is there already: the
# reducer tries another, and the file that was there is as it was
proj="$tmp/proj4"; mkdir "$proj"
cat > "$proj/main.stn" <<'STN'
fn main():
    var xs: Array[Int] = [3, 1, 2]
    sort(mut xs)
    print("unused")
STN
echo precious > "$proj/.fuzz-reduce-first-orig.stn"
(cd "$tmp" && FUZZ_SCRATCH_TOKENS=first,second,third with_fault c-output --reduce "$proj/main.stn" > "$tmp/c.out" 2> "$tmp/c.err"); status=$?
left=$(ls -A "$proj" | tr '\n' ' ')
kept=$(cat "$proj/.fuzz-reduce-first-orig.stn" 2>/dev/null)
if [ $status != 0 ] || ! grep -q 'sort(mut' "$tmp/c.out"; then bad "--reduce with its first name taken: exit $status"; cat "$tmp/c.err"
elif [ "$kept" != precious ]; then bad "--reduce with its first name taken changed the file that was there: '$kept'"
elif [ "$left" != ".fuzz-reduce-first-orig.stn main.stn " ]; then bad "--reduce with its first name taken left files, or took one away: $left"
else ok "--reduce with its first name taken: another is made, the file that was there is as it was, nothing is left"; fi

# 9. the compiler does not start: the reducer stops, and leaves nothing next to the input
proj="$tmp/proj5"; mkdir "$proj"
printf '%s\n' 'fn main():' '    print("x")' > "$proj/main.stn"
(cd "$tmp" && STARNITE="$tmp/no-such-compiler" "$fuzz" --reduce "$proj/main.stn" > "$tmp/n.out" 2> "$tmp/n.err"); status=$?
left=$(ls -A "$proj" | tr '\n' ' ')
if [ $status != 2 ]; then bad "--reduce without a compiler: exit $status, not 2"; cat "$tmp/n.err"
elif [ "$left" != "main.stn " ]; then bad "--reduce without a compiler left files next to the input: $left"
else ok "--reduce without a compiler: it stops, and leaves nothing next to the input"; fi

[ $fail = 0 ]
