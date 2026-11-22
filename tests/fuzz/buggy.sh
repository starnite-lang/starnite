#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# A compiler with a fault put in on purpose, for the fuzzer's own tests (selftest.sh): what
# does the fuzzer say about a compiler that is wrong? It runs the real compiler, named by
# REAL_STARNITE, and changes what BUGGY says:
#   c-output     the C build of a program that has `sort(mut` in it prints one line more
#   accept-take  the checker accepts a program it rejects with E0302 (use after take)
#   wrong-code   the checker says E0303 where it says E0304 (a mut marker left out)
real=${REAL_STARNITE:?REAL_STARNITE names the compiler to run}
case "${BUGGY:-}" in
c-output)
    if [ "$1" = run ] && [ "$2" != --interp ]; then
        for last; do :; done
        "$real" "$@"; status=$?
        if grep -q 'sort(mut' "$last"; then echo BUG; fi
        exit $status
    fi ;;
accept-take)
    if [ "$1" = check ]; then
        out=$("$real" "$@" 2>&1); status=$?
        case $out in *E0302*) exit 0 ;; esac
        printf '%s\n' "$out"; exit $status
    fi ;;
wrong-code)
    if [ "$1" = check ]; then
        out=$("$real" "$@" 2>&1); status=$?
        printf '%s\n' "$out" | sed 's/"code":"E0304"/"code":"E0303"/'; exit $status
    fi ;;
esac
exec "$real" "$@"
