#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# The Str layout has fast paths for little-endian targets and byte-wise paths for every other
# (runtime/stn_runtime.h). This runs the string tests of the corpus on the byte-wise paths:
#   1. on this machine, with the fast paths turned off (-DSTN_STR_PORTABLE);
#   2. on a big-endian target, s390x under qemu, when a cross compiler and qemu are installed.
# REQUIRE_BIG_ENDIAN=1 makes the second part an error when they are not (the CI job sets it).
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
starnite=${STARNITE:-"$root/_build/default/compiler/main.exe"}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
tests="strings str_inline_boundary str_views str_argument_order trap_str_argument_order map_set map_set_equality collection_fast_paths main_entry_names"
fail=0; pass=0

# check NAME COMPILER-AND-FLAGS... : build the test's generated C with the command, run it (through
# $runner when set) and compare what it prints and its status with the golden output
check() {
    label=$1; name=$2; shift 2
    if ! (cd "$root" && "$starnite" emit-c "tests/run/$name.stn") > "$tmp/$name.c" 2> "$tmp/err"; then
        echo "FAIL $label/$name: emit-c failed"; cat "$tmp/err"; fail=$((fail + 1)); return
    fi
    if ! "$@" -std=c11 -O1 -w -I"$root/runtime" "$tmp/$name.c" "$root/runtime/stn_runtime.c" -lm -o "$tmp/$name.exe" 2> "$tmp/err"; then
        echo "FAIL $label/$name: the C compiler failed"; head -5 "$tmp/err"; fail=$((fail + 1)); return
    fi
    (cd "$root" && $runner "$tmp/$name.exe" < /dev/null > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out")
    if cmp -s "$tmp/out" "$here/run/$name.out"; then pass=$((pass + 1))
    else echo "FAIL $label/$name: output differs from $name.out"; diff "$here/run/$name.out" "$tmp/out" | head -10; fail=$((fail + 1)); fi
}

runner=
for name in $tests; do check byte-wise "$name" "${CC:-cc}" -DSTN_STR_PORTABLE; done

cross=s390x-linux-gnu-gcc
qemu=$(command -v qemu-s390x-static || command -v qemu-s390x || true)
if command -v "$cross" > /dev/null && [ -n "$qemu" ]; then
    runner=$qemu
    for name in $tests; do check big-endian "$name" "$cross" -static; done
elif [ "${REQUIRE_BIG_ENDIAN:-}" = 1 ]; then
    echo "FAIL: REQUIRE_BIG_ENDIAN is set, but $cross or qemu-s390x is not installed"; fail=$((fail + 1))
else
    echo "skipped the big-endian run: $cross and qemu-s390x are not installed"
fi

# the size arithmetic of strings for a 32-bit size_t, checked on this machine (tests/str_limits.c)
if "${CC:-cc}" -std=c11 -O1 -w -I"$root/runtime" "$here/str_limits.c" -o "$tmp/str_limits.exe" 2> "$tmp/err" && "$tmp/str_limits.exe" > "$tmp/out" 2>&1; then
    pass=$((pass + 1))
else
    echo "FAIL str_limits"; cat "$tmp/err" "$tmp/out" 2> /dev/null | head -10; fail=$((fail + 1))
fi

# a release that STN_FREE_BUDGET put off is taken up by the next allocation of any size
# (tests/release_budget.c)
if "${CC:-cc}" -std=c11 -O1 -w -I"$root/runtime" "$here/release_budget.c" "$root/runtime/stn_runtime.c" -lm -o "$tmp/release_budget.exe" 2> "$tmp/err" && "$tmp/release_budget.exe" > "$tmp/out" 2>&1; then
    pass=$((pass + 1))
else
    echo "FAIL release_budget"; cat "$tmp/err" "$tmp/out" 2> /dev/null | head -10; fail=$((fail + 1))
fi

echo "$pass passed, $fail failed"
[ "$fail" = 0 ]
