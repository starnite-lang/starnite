#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# Conformance corpus (section 21.3). Every program in tests/run runs on the reference
# interpreter, the debug C build and the release C build; all three must agree with
# each other and with the reviewed golden output (section 21.2, oracle 3). The debug
# runtime also checks that counts balance at exit (oracle 2), and both C builds check every value
# the compiler took to be unique (section 6.2).
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
starnite=${STARNITE:-"$root/_build/default/compiler/main.exe"}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0; pass=0
# the compiler checks its own account of what is unique (section 6.2) while it runs here, and a
# release build keeps the tests that account lets it leave out
export STN_CHECK_UNIQUE=1
note() { printf '%s\n' "$*"; }

# runs a program, recording output and exit status
capture() { "$@" > "$tmp/out" 2>&1; echo "exit $?" >> "$tmp/out"; cat "$tmp/out"; }

for f in "$here"/run/*.stn; do
    name=$(basename "$f" .stn)
    rel=${f#"$root/"}
    # a .stdin-dir marker makes standard input a directory, so reading it fails
    input=/dev/null
    if [ -f "$here/run/$name.stdin-dir" ]; then input=$here; fi
    (cd "$root" && capture "$starnite" run --interp "$rel" < "$input") > "$tmp/interp"
    (cd "$root" && capture "$starnite" run "$rel" < "$input") > "$tmp/debug"
    # the release build also makes the tests the compiler left out for values it took to be unique
    (cd "$root" && capture "$starnite" run --release "$rel" < "$input") > "$tmp/release"
    golden="$here/run/$name.out"
    if [ "${UPDATE:-}" = 1 ]; then cp "$tmp/interp" "$golden"; fi
    ok=1
    for k in debug release; do
        if ! cmp -s "$tmp/interp" "$tmp/$k"; then
            note "FAIL run/$name: the $k C build differs from the interpreter"; diff "$tmp/interp" "$tmp/$k" | head -10; ok=0
        fi
    done
    if [ -f "$golden" ] && ! cmp -s "$tmp/interp" "$golden"; then
        note "FAIL run/$name: output differs from $name.out"; diff "$golden" "$tmp/interp" | head -10; ok=0
    elif [ ! -f "$golden" ]; then note "FAIL run/$name: no golden output (run with UPDATE=1 and review)"; ok=0; fi
    if [ $ok = 1 ]; then pass=$((pass + 1)); else fail=$((fail + 1)); fi
done

# one golden test per error code: the first line says "# expect: CODE LINE:COL"
for f in "$here"/errors/*.stn; do
    name=$(basename "$f" .stn)
    want=$(head -1 "$f" | sed 's/^# expect: //')
    got=$(cd "$root" && "$starnite" check --json "${f#"$root/"}" 2>&1 | head -1 |
          sed -n 's/.*"code":"\([^"]*\)".*"line":\([0-9]*\),"col":\([0-9]*\).*/\1 \2:\3/p')
    if [ "$want" = "$got" ]; then pass=$((pass + 1)); else note "FAIL errors/$name: expected '$want', got '$got'"; fail=$((fail + 1)); fi
done

# a program nested deeper than the compiler's own recursion is E0100, with the code in the JSON of --json
# as well as in the text (the fuzzer reads the code from the JSON)
deep="$tmp/deep.stn"
{ printf 'fn main():\n    let x = '; head -c 200000 /dev/zero | tr '\0' '('; printf '1'; head -c 200000 /dev/zero | tr '\0' ')'; printf '\n'; } > "$deep"
got=$("$starnite" check --json "$deep" 2>&1 | head -1 | sed -n 's/.*"code":"\([^"]*\)".*/\1/p')
text=$("$starnite" check "$deep" 2>&1 | head -1)
if [ "$got" = E0100 ] && [ "$text" = 'error[E0100]: the program is nested too deeply to be compiled' ]; then pass=$((pass + 1))
else note "FAIL a program nested too deeply: json code '$got', text '$text'"; fail=$((fail + 1)); fi

# The checks of noalloc and inplace functions (section 9.6, compiler/verify.ml) take any name in
# generated C that they do not know to allocate. STN_VERIFY_NAMES lists such names: there must be
# none in the code of the corpus, or a function would be refused for an allocation it does not make.
unlisted=$(for f in "$here"/run/*.stn; do STN_VERIFY_NAMES=1 "$starnite" emit-c "$f" 2>&1 >/dev/null | grep '^unlisted: '; done | sort -u)
if [ -z "$unlisted" ]; then pass=$((pass + 1)); else note "FAIL names the checks of section 9.6 do not know:"; note "$unlisted"; fail=$((fail + 1)); fi

# test blocks, including rejection tests (section 20.2)
for f in "$here"/unit/*.stn; do
    if (cd "$root" && "$starnite" test "${f#"$root/"}") > "$tmp/unit" 2>&1; then pass=$((pass + 1))
    else note "FAIL unit/$(basename "$f")"; cat "$tmp/unit"; fail=$((fail + 1)); fi
done

# property and snapshot tests that fail (section 20.2): what the runner reports, with each input
# shrunk and its seed, against tests/testing/failing.out
(cd "$root" && "$starnite" test tests/testing/failing.stn) > "$tmp/failing" 2>&1; echo "exit $?" >> "$tmp/failing"
if cmp -s "$tmp/failing" "$here/testing/failing.out"; then pass=$((pass + 1))
else note "FAIL testing/failing"; diff "$here/testing/failing.out" "$tmp/failing" | head -10; fail=$((fail + 1)); fi

# Two tests whose snapshots would share a file: neither may write it, with --update-snapshots
# either. The stored copy is another value than both give, and must still be there afterwards.
cp -r "$here/testing" "$tmp/testing"
(cd "$tmp" && "$starnite" test --update-snapshots testing/failing.stn) > /dev/null 2>&1
if [ "$(cat "$tmp/testing/snapshots/failing/same.snap")" = 7 ]; then pass=$((pass + 1)); else note "FAIL a snapshot shared by two tests was overwritten"; fail=$((fail + 1)); fi

# a run of no cases would pass whatever a property says
if (cd "$root" && "$starnite" test --cases 0 tests/unit/testing_kinds.stn) > "$tmp/cases" 2>&1; then note "FAIL --cases 0 was accepted"; fail=$((fail + 1)); else pass=$((pass + 1)); fi

# bench blocks (section 20.3): the counters of each measure block and its budgets, one of them
# broken, against tests/testing/benches.out
(cd "$root" && "$starnite" test tests/testing/benches.stn) > "$tmp/benches" 2>&1; echo "exit $?" >> "$tmp/benches"
if cmp -s "$tmp/benches" "$here/testing/benches.out"; then pass=$((pass + 1))
else note "FAIL testing/benches"; diff "$here/testing/benches.out" "$tmp/benches" | head -10; fail=$((fail + 1)); fi

# the fuzzer's own checks (tests/fuzz/selftest.sh): negative fuzzing against this compiler, and the
# fuzzer against compilers with a fault put in, to see that it finds it and shrinks the program
fuzz=${FUZZ:-"$root/_build/default/tests/fuzz/fuzz.exe"}
if [ -x "$fuzz" ]; then
    if STARNITE="$starnite" FUZZ="$fuzz" "$here/fuzz/selftest.sh" > "$tmp/selftest" 2>&1; then ok=1; else ok=0; fi
    pass=$((pass + $(grep -c '^pass ' "$tmp/selftest")))
    if [ $ok = 0 ]; then
        cat "$tmp/selftest"
        n=$(grep -c '^FAIL ' "$tmp/selftest"); [ "$n" = 0 ] && n=1
        fail=$((fail + n))
    fi
else note "skipped: the fuzzer's own checks (no $fuzz; dune build makes it)"; fi

note "$pass passed, $fail failed"
[ $fail = 0 ]
