#!/usr/bin/env bash
set -euo pipefail
base=$(realpath "$1")
shift
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cc=${CC:-gcc}
# Every C build takes the flags a release build takes (compiler/backend.ml): the same level of
# optimization, so that what is measured is what `starnite build --release` gives, and the same
# layout, so that a comparison measures the code and not where it happened to land. At -O3 GCC
# inlines differently, a recursive function into itself among other things, and results moved by
# up to 8% with changes elsewhere in the file.
release="-O2 -falign-functions=64 -falign-loops=64"
rustc=${RUSTC:-rustc}

compile_starnite() {
    local checkout=$1 compiler=$2 name=$3
    (cd "$checkout" && "$compiler" build --release --keep-c "$here/bench.stn" -o "$out/$name-generated")
    "$cc" $release -std=c11 -fno-strict-aliasing -I"$checkout/runtime" \
        "$out/$name-generated.c" "$checkout/runtime/stn_runtime.c" -lm -o "$out/$name"
}

compile_starnite "$base" "${BASE_STARNITE:-$base/_build/default/compiler/main.exe}" previous-starnite
compile_starnite "$repo" "${STARNITE:-$repo/_build/default/compiler/main.exe}" starnite
"$cc" $release -std=c11 -Wall -Wextra -Werror "$here/kernels.c" -o "$out/c-reference"
"$cc" $release -std=c11 -DSHARED -fno-strict-aliasing -I"$base/runtime" \
    "$here/kernels-c-tuned.c" "$base/runtime/stn_runtime.c" -lm -o "$out/c-tuned"
"$rustc" -C opt-level=3 -C overflow-checks=yes "$here/bench.rs" -o "$out/rust-reference"
"$here/measure.sh" "$out" "$@"
