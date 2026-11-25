#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Counting workloads (section 9): what moving at the last use, borrowing lets and appending in
# place are for. Builds counting.stn with this checkout and with a baseline one, and prints the
# best of nine runs of each kernel in milliseconds, with the checksum both must agree on.
# usage: run.sh BASE
set -euo pipefail
base=$(realpath "$1")
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
build() {
    local checkout=$1 name=$2
    (cd "$checkout" && "$checkout/_build/default/compiler/main.exe" build --release --keep-c "$here/counting.stn" -o "$out/$name-generated")
    "$cc" $release -std=c11 -fno-strict-aliasing -I"$checkout/runtime" "$out/$name-generated.c" "$checkout/runtime/stn_runtime.c" -lm -o "$out/$name"
}
build "$base" previous-starnite
build "$repo" starnite
printf '%-12s %14s %14s %7s\n' case previous-ms starnite-ms ratio
for case in accumulate alias push_last grow; do
    declare -A best sum
    for v in previous-starnite starnite; do
        best[$v]=
        for _ in 1 2 3 4 5 6 7 8 9; do
            read -r ns check < <(echo "$case" | "$out/$v")
            if [ -z "${best[$v]}" ] || [ "$ns" -lt "${best[$v]}" ]; then best[$v]=$ns; fi
            sum[$v]=$check
        done
    done
    if [ "${sum[previous-starnite]}" != "${sum[starnite]}" ]; then echo "$case: checksums differ" >&2; exit 1; fi
    awk -v c="$case" -v a="${best[previous-starnite]}" -v b="${best[starnite]}" 'BEGIN { printf "%-12s %14.3f %14.3f %7.3f\n", c, a / 1e6, b / 1e6, b / a }'
done
