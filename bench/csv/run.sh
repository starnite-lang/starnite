#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# CSV to JSON: the program of tests/run/csv_to_json.stn against the same program in C and in
# Rust, on a generated file. Every build must print the same bytes. An object is a hash map that
# keeps insertion order in Starnite and in csv_to_json_hashmap.rs; csv_to_json.rs and
# csv_to_json.c keep an array of fields and search it, which no hash map of nine keys beats.
# csv_to_json_stream.stn is the same conversion a row at a time: it never holds more than one row.
# usage: run.sh [ROWS] [ROUNDS]
set -euo pipefail
rows=${1:-200000}
rounds=${2:-7}
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cc=${CC:-gcc}
release="-O2 -falign-functions=64 -falign-loops=64"
python3 "$here/gen.py" "$rows" > "$out/input.csv"
(cd "$repo" && "${STARNITE:-$repo/_build/default/compiler/main.exe}" build --release "$here/csv_to_json.stn" -o "$out/starnite")
"$cc" $release -std=c11 -Wall -Wextra -Werror "$here/csv_to_json.c" -o "$out/c-arrays"
"${RUSTC:-rustc}" -C opt-level=3 -C overflow-checks=yes "$here/csv_to_json.rs" -o "$out/rust-arrays" 2>/dev/null
"${RUSTC:-rustc}" -C opt-level=3 -C overflow-checks=yes "$here/csv_to_json_hashmap.rs" -o "$out/rust-hashmap" 2>/dev/null
(cd "$repo" && "${STARNITE:-$repo/_build/default/compiler/main.exe}" build --release "$here/csv_to_json_stream.stn" -o "$out/starnite-stream")
"$out/starnite" < "$out/input.csv" > "$out/want.json"
for b in c-arrays rust-arrays rust-hashmap starnite-stream; do
    "$out/$b" < "$out/input.csv" | cmp -s - "$out/want.json" || { echo "$b prints something else"; exit 1; }
done
echo "$rows rows, $(wc -c < "$out/input.csv") bytes in, $(wc -c < "$out/want.json") bytes out, every build prints the same"
python3 "$here/measure.py" "$out/input.csv" "$rounds" c-arrays="$out/c-arrays" rust-arrays="$out/rust-arrays" rust-hashmap="$out/rust-hashmap" starnite="$out/starnite" starnite-stream="$out/starnite-stream"
