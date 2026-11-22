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
real=${REAL_STARNITE:?REAL_STARNITE names the compiler to run}
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
        if grep -q '^fn main' "$last"; then echo 'Fatal error: exception Not_found'; exit 2; fi
    fi ;;
crash-run)
    if [ "$1" = run ] && [ "$2" = --interp ]; then
        for last; do :; done
        if grep -q '^fn main' "$last"; then echo 'Fatal error: exception Not_found'; exit 2; fi
    fi ;;
esac
exec "$real" "$@"
