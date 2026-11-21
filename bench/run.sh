#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
# Milestone 1 gate benchmarks (section 21.5): Starnite --release against C -O2.
set -e
here=$(cd "$(dirname "$0")" && pwd)
starnite=${STARNITE:-"$here/../_build/default/compiler/main.exe"}
# a private directory of our own, never a fixed shared path
out=$(mktemp -d "${TMPDIR:-/tmp}/starnite-bench.XXXXXXXX")
trap 'rm -rf "$out"' EXIT
best() { # best of 3 wall-clock runs, in seconds
    b=999
    for _ in 1 2 3; do
        s=$(date +%s.%N); "$1" > /dev/null; e=$(date +%s.%N)
        b=$(echo "$e - $s" | bc -l | awk -v b="$b" '{ print ($1 < b) ? $1 : b }')
    done
    echo "$b"
}
printf "%-12s %9s %9s %7s\n" benchmark starnite c ratio
for b in centroid nbody spectral mandelbrot; do
    "$starnite" build --release "$here/$b.stn" -o "$out/$b-stn"
    ${CC:-cc} -O2 -o "$out/$b-c" "$here/$b.c" -lm
    norm() { "$1" | awk '{ for (i = 1; i <= NF; i++) printf "%.12g ", $i; print "" }'; }
    if [ "$(norm "$out/$b-stn")" != "$(norm "$out/$b-c")" ]; then echo "$b: outputs differ"; exit 1; fi
    ts=$(best "$out/$b-stn"); tc=$(best "$out/$b-c")
    printf "%-12s %9.3f %9.3f %6.2fx\n" "$b" "$ts" "$tc" "$(echo "$ts / $tc" | bc -l)"
done
