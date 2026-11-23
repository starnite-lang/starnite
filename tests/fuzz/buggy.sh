#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# A compiler with a fault put in on purpose, for the fuzzer's own tests (selftest.sh): what
# does the fuzzer say about a compiler that is wrong? It runs the real compiler, named by
# REAL_STARNITE, and changes what BUGGY says:
#   c-output     the C build of a program that has `sort(mut` in it prints one line more
#   accept:CODE  the checker accepts a program it rejects with CODE (accept:E0302, a use after take;
#                accept:E0202, a match that does not cover every case)
#   wrong-code   the checker says E0303 where it says E0304 (a mut marker left out)
#   split        both backends print one line more for a program that imports fuzzlib, which
#                the same program in one file does not
#   crash        the checker dies with an exception that nothing caught, for a program that has a main
#   crash-run    the interpreter does, for a program that has a main and checks
#   silent-crash the program that the C build makes of one that has a main is killed by a signal,
#                with nothing printed
#   phrase       not a fault: the programs print `Fatal error: exception Not_found` as their output, which is
#                not a crash of the compiler (the crashes above are written on the standard error, as OCaml does)
real=${REAL_STARNITE:?REAL_STARNITE names the compiler to run}
# the file that `build -o FILE` writes, and a way to put a shell script in its place
exe=; prev=
for a in "$@"; do if [ "$prev" = -o ]; then exe=$a; fi; prev=$a; done
replace_program() { printf '#!/bin/sh\n%s\n' "$1" > "$exe"; chmod +x "$exe"; }
case "${BUGGY:-}" in
c-output)
    if [ "$1" = run ] && [ "$2" != --interp ]; then
        for last; do :; done
        "$real" "$@"; status=$?
        if grep -q 'sort(mut' "$last"; then echo BUG; fi
        exit $status
    fi ;;
accept:*)
    if [ "$1" = check ]; then
        out=$("$real" "$@" 2>&1); status=$?
        case $out in *"${BUGGY#accept:}"*) exit 0 ;; esac
        printf '%s\n' "$out"; exit $status
    fi ;;
wrong-code)
    if [ "$1" = check ]; then
        out=$("$real" "$@" 2>&1); status=$?
        printf '%s\n' "$out" | sed 's/"code":"E0304"/"code":"E0303"/'; exit $status
    fi ;;
split)
    if [ "$1" = run ]; then
        for last; do :; done
        "$real" "$@"; status=$?
        if grep -q '^import fuzzlib' "$last"; then echo BUG; fi
        exit $status
    fi ;;
crash)
    if [ "$1" = check ]; then
        for last; do :; done
        if grep -q '^fn main' "$last"; then echo 'Fatal error: exception Not_found' >&2; exit 2; fi
    fi ;;
crash-run)
    if [ "$1" = run ] && [ "$2" = --interp ]; then
        for last; do :; done
        if grep -q '^fn main' "$last"; then echo 'Fatal error: exception Not_found' >&2; exit 2; fi
    fi ;;
silent-crash)
    # the program that the C build makes is killed by a signal, with nothing printed
    if [ "$1" = build ]; then
        "$real" "$@"; status=$?
        for last; do :; done
        if [ $status = 0 ] && grep -q '^fn main' "$last"; then
            replace_program 'kill -SEGV $$'
        fi
        exit $status
    fi ;;
phrase)
    # not a fault: programs that print what a crash looks like, on the standard output, which the
    # fuzzer must not take for one, from the interpreter and from the C build
    if [ "$1" = run ] && [ "$2" = --interp ]; then
        "$real" "$@"; status=$?
        echo 'Fatal error: exception Not_found'
        exit $status
    fi
    if [ "$1" = build ]; then
        "$real" "$@"; status=$?
        if [ $status = 0 ]; then replace_program 'echo "Fatal error: exception Not_found"'; fi
        exit $status
    fi ;;
esac
exec "$real" "$@"
