#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# Reporting copies (section 9.8): --explain-copies lists the places of tests/copies/copies.stn where
# a write may copy a shared value or a loop raises a count, and --profile-copies counts what
# happens at them when the program runs, in debug and release builds.
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
starnite=${STARNITE:-"$root/_build/default/compiler/main.exe"}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0; pass=0
check() { # name, expected file
    if cmp -s "$tmp/out" "$2"; then pass=$((pass + 1))
    else echo "FAIL copies/$1"; diff "$2" "$tmp/out" | head -10; fail=$((fail + 1)); fi
}
cd "$root" || exit 1
"$starnite" check --explain-copies tests/copies/copies.stn > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out"
check explain "$here/copies/copies.explain"
for mode in "" --release; do
    "$starnite" run $mode --profile-copies tests/copies/copies.stn < /dev/null > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out"
    check "profile ${mode:-debug}" "$here/copies/copies.profile"
done
# a program that copies nothing says so, and the flags change nothing else it prints
"$starnite" run --profile-copies tests/run/basics.stn < /dev/null > "$tmp/out" 2>/dev/null; echo "exit $?" >> "$tmp/out"
check "output unchanged" "$here/run/basics.out"
echo "$pass passed, $fail failed"
[ "$fail" = 0 ]
