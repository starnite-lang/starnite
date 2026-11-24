#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# Checks of the fuzzer itself (section 21.2). Negative fuzzing must find nothing wrong with the
# compiler as it is, every kind of violation being tried. Given a compiler with a fault put in
# on purpose (buggy.sh), the fuzzer must see the fault, and what it shrinks the failing program
# to must be small and still have the fault: the real compiler rejects a violation that was
# shrunk with the code it was made for, and the programs of the other faults run as they do
# with the real compiler. The checks do not depend on each other, so they run together. Prints
# "pass NAME" or "FAIL NAME: why" for each, in order; the status says whether all passed.
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$(dirname "$here")")
starnite=${STARNITE:-"$root/_build/default/compiler/main.exe"}
fuzz=${FUZZ:-"$root/_build/default/tests/fuzz/fuzz.exe"}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
ok() { printf 'pass %s\n' "$1"; }
bad() { printf 'FAIL %s\n' "$*"; }
lines() { wc -l < "$1" | tr -d ' '; }
# the code of the first diagnostic of a program, by the real compiler
code_of() { "$starnite" check --json "$1" 2>&1 | head -1 | sed -n 's/.*"code":"\([^"]*\)".*/\1/p'; }
# the fuzzer, with a compiler that has a fault: the real one runs under buggy.sh
export REAL_STARNITE=$starnite
with_fault() { fault=$1; shift; BUGGY=$fault STARNITE="$here/buggy.sh" "$fuzz" "$@"; }

# a compiler that is right: all 100 violations are rejected, with the codes they have, and none of
# the kinds was left out
negative_fuzzing() {
    out=$(STARNITE="$starnite" "$fuzz" --negative-only --count 100 --seed 1 2>&1); status=$?
    counts=$(printf '%s\n' "$out" | sed -n 's/^  .* \([0-9][0-9]*\), *[0-9][0-9]* made of.*/\1/p')
    kinds=$(printf '%s\n' "$counts" | grep -c .)
    if [ $status != 0 ] || ! printf '%s\n' "$out" | grep -q '^100 of 100 agreed'; then
        bad "negative fuzzing against the compiler: it did not agree on all of 100 mutations"; printf '%s\n' "$out" | head -20
    elif [ "$kinds" -lt 10 ] || printf '%s\n' "$counts" | grep -qx 0; then
        bad "negative fuzzing: a kind of violation was never tried"; printf '%s\n' "$out" | tail -20
    else ok "negative fuzzing against the compiler ($kinds kinds of violation)"; fi
}

# a checker that accepts what it rejects with a code: seen, and shrunk to a few lines that the real
# compiler rejects with that code, a use after take and a match that does not cover every case
fault_accept() {
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
fault_accept_take() { fault_accept E0302 "a use after take"; }
fault_accept_match() { fault_accept E0202 "a match that does not cover every case"; }

# a checker that says E0303 for E0304: seen, and shrunk to a program that the real compiler rejects
# with E0304
fault_wrong_code() {
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
}

# a C build that prints one line more for a program that sorts: the interpreter and the C build
# differ, and the program is shrunk to one that still sorts, and that the real compiler runs the
# same on both
fault_c_output() {
    seed=
    for s in $(seq 1 200); do
        if "$fuzz" --print --seed "$s" | grep -q 'sort(mut'; then seed=$s; break; fi
    done
    if [ -z "$seed" ]; then bad "fault c-output: none of 200 programs sorts"; return; fi
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
}

# a compiler that prints one line more for a program that imports a module, and so does not do what
# the same program in one file does: seen, and the program is shrunk to one that is still split, which
# the real compiler runs alike in two files and in one
fault_split() { split_fault split; }
# the same, where the two differ in what a program prints (not in a trap's place, which is left out): the
# difference is on the standard output, byte for byte
fault_split_stdout() { split_fault split-stdout; }
# two programs run alike: the same exit status, the same standard output and the same standard
# error, byte for byte. A shrunk program may end in a trap (status 2). A trap writes one header,
# `trap: KIND at FILE:LINE:COL` (or `trap: stack overflow`, which has no place), as the first line
# of standard error, and then its message. The
# place differs between the two forms, so it is left out of that first line and of nothing else:
# the message is compared as it is, whatever it says. Status 2 without that header first is an
# uncaught exception of the compiler, which begins with a header of its own, and is not alike.
same_run() {
    # the checks run at the same time: the files are the caller's own, named by its third argument
    w="$tmp/same-$3"
    "$starnite" run --interp "$1" > "$w.s.out" 2> "$w.s.err"; s1=$?
    "$starnite" run --interp "$2" > "$w.o.out" 2> "$w.o.err"; s2=$?
    [ "$s1" = "$s2" ] || return 1
    case $s1 in
        0) ;;
        2) for f in s o; do
               first=$(head -n 1 "$w.$f.err")
               # a stack overflow has no place, and is compared as it is
               [ "$first" = 'trap: stack overflow' ] && continue
               # the place is the last `:LINE:COL` of the line; the path before it may hold spaces
               printf '%s\n' "$first" | grep -q '^trap: .* at ..*:[0-9][0-9]*:[0-9][0-9]*$' || return 1
               # the kind of a trap holds no ` at `, so the first one on the line begins the place
               sed '1s/ at .*$//' "$w.$f.err" > "$w.$f.cut" && mv "$w.$f.cut" "$w.$f.err"
           done ;;
        *) return 1 ;;
    esac
    cmp -s "$w.s.out" "$w.o.out" && cmp -s "$w.s.err" "$w.o.err"
}
split_fault() {
    fault=$1
    seed=
    for s in $(seq 1 50); do
        if [ "$("$fuzz" --print --seed "$s" | head -1)" = '# module' ]; then seed=$s; break; fi
    done
    if [ -z "$seed" ]; then bad "fault $fault: none of 50 programs is split across a module"; return; fi
    d="$tmp/split-$fault"
    out=$(with_fault "$fault" --no-negative --seed "$seed" --count 1 --shrink --keep "$d" 2>&1); status=$?
    m="$d/case$seed.min.stn"
    if [ $status != 1 ] || ! printf '%s\n' "$out" | grep -q "split across a module"; then
        bad "fault $fault: the fuzzer did not report a difference (seed $seed)"; printf '%s\n' "$out" | tail -10
    elif [ ! -f "$m" ] || [ "$(head -1 "$m")" != '# module' ]; then bad "fault $fault: the shrunk program is not split (seed $seed)"
    elif [ "$(lines "$m")" -gt 40 ]; then bad "fault $fault: the shrunk program has $(lines "$m") lines"
    elif ! same_run "$d/case$seed.min.split/main.stn" "$m" "$fault"; then
        bad "fault $fault: the real compiler does not run the shrunk program alike in two files and in one"
    else ok "fault $fault: $(lines "$d/case$seed.stn") lines shrunk to $(lines "$m")"; fi
}

# --reduce: programs of a dozen lines, kept while they compile and have a main, are a few lines of main. The
# programs are fixed, so that the result does not depend on what the generator makes of a seed: one that is
# split across a module, which stays split and checks, and an ordinary one
reduce_keeping() {
    cat > "$tmp/p.stn" <<'STN'
# module
fn double(n: Int) -> Int:
    n * 2

fn unused(n: Int) -> Int:
    n + 1

# generated
fn main():
    print(f"{double(2)}")
    print(f"{unused(3)}")
    print("done")
STN
    STARNITE="$starnite" "$fuzz" --reduce "$tmp/p.stn" --keeping 'fn main' > "$tmp/r.stn" 2> "$tmp/r.err"; status=$?
    cp "$tmp/r.stn" "$tmp/r2.stn"
    if [ $status != 0 ] || [ "$(lines "$tmp/r2.stn")" -gt 6 ] || [ "$(head -1 "$tmp/r2.stn")" != '# module' ] || ! grep -q 'fn main' "$tmp/r2.stn" || ! "$starnite" check "$tmp/r2.stn" > /dev/null 2>&1; then
        bad "--reduce --keeping: a program split across a module: exit $status, $(lines "$tmp/r2.stn") lines"; cat "$tmp/r.err"; return
    fi
    cat > "$tmp/q.stn" <<'STN'
fn double(n: Int) -> Int:
    n * 2

fn main():
    print(f"{double(2)}")
    print("done")
STN
    STARNITE="$starnite" "$fuzz" --reduce "$tmp/q.stn" --keeping 'fn main' > "$tmp/q.out" 2> "$tmp/q.err"; status=$?
    cp "$tmp/q.out" "$tmp/q2.stn"
    if [ $status != 0 ] || [ "$(lines "$tmp/q2.stn")" -gt 3 ] || ! grep -q 'fn main' "$tmp/q2.stn" || ! "$starnite" check "$tmp/q2.stn" > /dev/null 2>&1; then
        bad "--reduce --keeping: an ordinary program: exit $status, $(lines "$tmp/q2.stn") lines"; cat "$tmp/q.err"
    else ok "--reduce --keeping: $(lines "$tmp/p.stn") lines reduced to $(lines "$tmp/r2.stn") (split) and $(lines "$tmp/q.stn") to $(lines "$tmp/q2.stn")"; fi
}

# --reduce of a program that imports a module that is next to it: the candidates are tried where the
# module is, so that the program is found to fail and is reduced, in the way it fails, and nothing is
# left in its directory
reduce_next_to_a_module() {
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
}

# and by the code a program is rejected with, which a missing module would change
reduce_rejected_next_to_a_module() {
    proj="$tmp/proj2"; mkdir "$proj"
    cat > "$proj/helpers.stn" <<'STN'
fn name*() -> Str:
    "helper"
STN
    cat > "$proj/main.stn" <<'STN'
import helpers

fn main():
    print("start")
    let n: Int = helpers.name()
    print(f"{n}")
    print("end")
STN
    (cd "$tmp" && STARNITE="$starnite" "$fuzz" --reduce "$proj/main.stn" --rejected E0201 > "$tmp/proj2.out" 2> "$tmp/proj2.err"); status=$?
    cp "$tmp/proj2.out" "$proj/reduced.stn"
    if [ $status != 0 ] || [ "$(lines "$tmp/proj2.out")" -ge "$(lines "$proj/main.stn")" ] || [ "$(code_of "$proj/reduced.stn")" != E0201 ]; then
        bad "--reduce --rejected next to a module: exit $status, $(lines "$tmp/proj2.out") lines of $(lines "$proj/main.stn"), rejected with '$(code_of "$proj/reduced.stn")'"; cat "$tmp/proj2.err"
    else ok "--reduce --rejected next to a module: $(lines "$proj/main.stn") lines reduced to $(lines "$tmp/proj2.out")"; fi
}

# a match that a checker accepts although it has an arm too few, reduced while another match has the same
# header and the same arms, and one more: the reduction keeps the match that is the violation
reduce_keeping_a_match() {
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
}

# the name the reducer tries first for a file of its own is taken by a file that is there already: it tries another
reduce_name_taken() {
    proj="$tmp/proj4"; mkdir "$proj"
    printf '%s\n' 'fn main():' '    var xs: Array[Int] = [3, 1, 2]' '    sort(mut xs)' '    print("unused")' > "$proj/main.stn"
    echo precious > "$proj/.fuzz-reduce-first-orig.stn"
    (cd "$tmp" && FUZZ_SCRATCH_TOKENS=first,second,third with_fault c-output --reduce "$proj/main.stn" > "$tmp/c.out" 2> "$tmp/c.err"); status=$?
    left=$(ls -A "$proj" | tr '\n' ' ')
    kept=$(cat "$proj/.fuzz-reduce-first-orig.stn" 2>/dev/null)
    if [ $status != 0 ] || ! grep -q 'sort(mut' "$tmp/c.out"; then bad "--reduce with its first name taken: exit $status"; cat "$tmp/c.err"
    elif [ "$kept" != precious ]; then bad "--reduce with its first name taken changed the file that was there: '$kept'"
    elif [ "$left" != ".fuzz-reduce-first-orig.stn main.stn " ]; then bad "--reduce with its first name taken left files, or took one away: $left"
    else ok "--reduce with its first name taken: another is made, the file that was there is as it was, nothing is left"; fi
}

# the compiler does not start: the reducer stops, and leaves nothing next to the input
reduce_without_compiler() {
    proj="$tmp/proj5"; mkdir "$proj"
    printf '%s\n' 'fn main():' '    print("x")' > "$proj/main.stn"
    (cd "$tmp" && STARNITE="$tmp/no-such-compiler" "$fuzz" --reduce "$proj/main.stn" > "$tmp/n.out" 2> "$tmp/n.err"); status=$?
    left=$(ls -A "$proj" | tr '\n' ' ')
    if [ $status != 2 ]; then bad "--reduce without a compiler: exit $status, not 2"; cat "$tmp/n.err"
    elif [ "$left" != "main.stn " ]; then bad "--reduce without a compiler left files next to the input: $left"
    else ok "--reduce without a compiler: it stops, and leaves nothing next to the input"; fi
}

# a checker that dies with an exception, and an interpreter that does: the corruption of a program that
# makes them do it is found, and shrunk to the few lines that have it
crashes() {
    fault=$1; where=$2
    d="$tmp/crash-$fault"
    out=$(with_fault "$fault" --crash --count 40 --seed 1 --shrink --keep "$d" 2>&1); status=$?
    n=$(ls "$d"/*.crash.min.stn 2>/dev/null | wc -l | tr -d ' ')
    if [ $status != 1 ] || ! printf '%s\n' "$out" | grep -q "the compiler crashed $where"; then
        bad "fault $fault: the fuzzer did not report a crash $where"; printf '%s\n' "$out" | tail -10
    elif [ "$n" = 0 ]; then bad "fault $fault: nothing was shrunk"
    else
        all=1
        for m in "$d"/*.crash.min.stn; do
            if [ "$(lines "$m")" -gt 40 ] || ! grep -q '^fn main' "$m"; then
                bad "fault $fault: $(basename "$m") has $(lines "$m") lines"; all=0
            fi
        done
        [ $all = 1 ] && ok "fault $fault: a crash $where, $n programs shrunk"
    fi
}
fault_crash() { crashes crash "in the check"; }
fault_crash_run() { crashes crash-run "in run --interp"; }
# the program that the C build made is killed by a signal and prints nothing: the fuzzer runs it itself
# and sees how it ended, which the compiler's output does not say
fault_silent_crash() { crashes silent-crash "in exe"; }

# a SIGKILL that the machine sends is a signal like another, and not the end of a run that took too long
fault_killed() { crashes killed "in exe"; }

# a C compiler that fails and says nothing: the build of a program that checked fails, and it is a crash
fault_cc_fails() { crashes cc-fails "in build"; }

# the build said it succeeded and left no program, and the program that was built ends with the status of the
# debug runtime that finds objects that do not balance: a launch that failed and a status that is not the program's
fault_no_exe() { crashes no-exe "in exe"; }
fault_leak() { crashes leak "in exe"; }
# the status of the program that the build makes of a saved case, built and run under a fault; a program
# split across a module is read from the files next to it (X.stn is X.split/main.stn and fuzzlib.stn)
replay_status() {
    fault=$1; p=$2; w=$(mktemp -d "$tmp/replay.XXXXXX")
    src=$p; [ -d "${p%.stn}.split" ] && src=${p%.stn}.split/main.stn
    if BUGGY=$fault "$here/buggy.sh" build -o "$w/exe" "$src" >/dev/null 2>&1 && [ -x "$w/exe" ]; then
        "$w/exe" >/dev/null 2>&1; echo $?
    else echo 127; fi
    rm -rf "$w"
}
# the shrink keeps the failure it was given: a candidate that no longer leaks but fails to launch is not accepted,
# so the saved program still ends with status 3 when it is built and run again, as the one it came from does
fault_leak_kept() {
    d="$tmp/crash-leak-kept"
    out=$(with_fault leak-then-no-exe --crash --count 40 --seed 1 --shrink --keep "$d" 2>&1); status=$?
    n=$(ls "$d"/*.crash.min.stn 2>/dev/null | wc -l | tr -d ' ')
    if [ $status != 1 ] || [ "$n" = 0 ]; then bad "fault leak-then-no-exe: nothing was shrunk"; printf '%s\n' "$out" | tail -10; return; fi
    all=1
    for m in "$d"/*.crash.min.stn; do
        # replay the saved program and the one it was shrunk from (the files the compiler was given: the .split
        # directory when there is one) under the same fault: both must end with status 3, not 127
        for p in "$m" "${m%.min.stn}.stn"; do
            s=$(replay_status leak-then-no-exe "$p")
            if [ "$s" != 3 ]; then bad "fault leak-then-no-exe: $(basename "$p") ends with status $s, not the leak (3)"; all=0; fi
        done
    done
    [ $all = 1 ] && ok "fault leak-then-no-exe: $n programs shrunk, each still the leak"
}

# The compiler may say that a program uses what it does not support yet (the build of valid code, exit 1, in
# its own words), and that is not a crash. The same words in a C compiler that failed, or in an exception
# that nothing caught, are not that, and are one.
unsupported_is_not_a_crash() {
    out=$(with_fault unsupported --crash --count 40 --seed 1 2>&1); status=$?
    if [ $status != 0 ] || printf '%s\n' "$out" | grep -q 'the compiler crashed'; then
        bad "the compiler's own report of what it does not support yet was taken for a crash (exit $status)"; printf '%s\n' "$out" | tail -10
    else ok "a program that uses what is not supported yet is rejected by the build in the compiler's words, and that is not a crash"; fi
}
fault_cc_says_unsupported() { crashes cc-says-unsupported "in build"; }
fault_exception_unsupported() { crashes exception-unsupported "in build"; }

# not a crash: programs that print what a crash looks like, from the interpreter and from the C build.
# The words are the program's output, and the compiler did nothing wrong.
crash_phrase_is_output() {
    out=$(with_fault phrase --crash --count 40 --seed 1 2>&1); status=$?
    if [ $status != 0 ] || printf '%s\n' "$out" | grep -q 'the compiler crashed'; then
        bad "a program that prints 'Fatal error: exception' was taken for a crash of the compiler (exit $status)"; printf '%s\n' "$out" | tail -10
    else ok "a program that prints the words of a crash is not one"; fi
}

# a program that is not split across a module, with a comment that begins as the header does, is an ordinary
# file: what it imports is found next to it, and it is reduced there
reduce_ordinary_module_comment() {
    proj="$tmp/proj6"; mkdir "$proj"
    printf '%s\n' 'fn twice*(n: Int) -> Int:' '    n * 2' > "$proj/helpers.stn"
    cat > "$proj/main.stn" <<'STN'
# module smoke test: this is not the header of a program split across a module
import helpers

fn main():
    var xs: Array[Int] = [3, 1, 2]
    sort(mut xs)
    print(f"{helpers.twice(xs[0])}")
    print("unused")
STN
    (cd "$tmp" && with_fault c-output --reduce "$proj/main.stn" > "$tmp/o6.out" 2> "$tmp/o6.err"); status=$?
    left=$(ls -A "$proj" | tr '\n' ' ')
    if [ $status != 0 ] || ! grep -q 'sort(mut' "$tmp/o6.out"; then
        bad "--reduce of a file with a comment that begins like the module header: exit $status"; cat "$tmp/o6.err"
    elif [ "$left" != "helpers.stn main.stn " ]; then bad "--reduce of a file with a comment like the module header left files: $left"
    else ok "--reduce of a file with a comment that begins like the module header: it is an ordinary file, and its import is found"; fi
}

# A program that is not split across a module, with the two marker comments of one in it but not at its
# start, can become one while it is reduced (the blank line before them goes). The mode is the input's, and
# the candidates are written in it: a module that is next to the input is not written over.
reduce_keeps_a_sibling_module() {
    proj="$tmp/proj7"; mkdir "$proj"
    printf '%s\n' 'fn keep*() -> Int:' '    1' > "$proj/fuzzlib.stn"
    cp "$proj/fuzzlib.stn" "$tmp/fuzzlib.orig"
    cat > "$proj/main.stn" <<'STN'

# module
# generated
fn main():
    var xs: Array[Int] = [3, 1, 2]
    sort(mut xs)
    print("unused")
STN
    (cd "$tmp" && with_fault c-output --reduce "$proj/main.stn" > "$tmp/o7.out" 2> "$tmp/o7.err"); status=$?
    left=$(ls -A "$proj" | tr '\n' ' ')
    if [ $status != 0 ] || ! grep -q 'sort(mut' "$tmp/o7.out"; then
        bad "--reduce next to a module with the marker comments in a file that is not split: exit $status"; cat "$tmp/o7.err"
    elif ! cmp -s "$proj/fuzzlib.stn" "$tmp/fuzzlib.orig"; then bad "--reduce wrote over the module next to its input"
    elif [ "$left" != "fuzzlib.stn main.stn " ]; then bad "--reduce left files, or took one away: $left"
    else ok "--reduce keeps the module that is next to its input, whatever a candidate looks like"; fi
}

# The checks run together, each as a process of its own. Every one has to end, and to say how: a check that
# was killed, or that stopped before it printed its result, fails the run, and does not drop out of it.
n=0
pids=""
names=""
for check in negative_fuzzing fault_accept_take fault_accept_match fault_wrong_code fault_c_output fault_split fault_split_stdout reduce_keeping reduce_next_to_a_module reduce_ordinary_module_comment reduce_keeps_a_sibling_module reduce_rejected_next_to_a_module reduce_keeping_a_match reduce_name_taken reduce_without_compiler fault_crash fault_crash_run fault_silent_crash fault_killed fault_cc_fails fault_no_exe fault_leak fault_leak_kept unsupported_is_not_a_crash fault_cc_says_unsupported fault_exception_unsupported crash_phrase_is_output; do
    n=$((n + 1))
    # each check runs in a directory of its own: they run at the same time, and a file one of them
    # writes must never be one another reads
    mkdir "$tmp/check.$n"
    (tmp="$tmp/check.$n"; "$check") > "$tmp/result.$n" 2>&1 &
    pids="$pids $!"
    names="$names $check"
done
i=1
for pid in $pids; do
    wait "$pid"; st=$?
    name=$(printf '%s\n' $names | sed -n "${i}p")
    # what a check prints ends with a line of its own: "pass ..." or "FAIL ...", and ends the process well
    if ! grep -q '^\(pass\|FAIL\) ' "$tmp/result.$i"; then
        printf 'FAIL %s: it ended with status %s without a result\n' "$name" "$st" >> "$tmp/result.$i"
    elif [ "$st" != 0 ] && ! grep -q '^FAIL ' "$tmp/result.$i"; then
        printf 'FAIL %s: it ended with status %s\n' "$name" "$st" >> "$tmp/result.$i"
    fi
    i=$((i + 1))
done
i=1
while [ $i -le $n ]; do cat "$tmp/result.$i"; i=$((i + 1)); done > "$tmp/results"
cat "$tmp/results"
! grep -q '^FAIL ' "$tmp/results"
