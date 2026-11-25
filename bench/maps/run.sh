#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Measures the Map and Set workloads of maps.stn against the same work in Rust (maps.rs) and in C
# (maps.c, once with SipHash and once with a fast mixer), and against an earlier Starnite when one
# is given. For every run it records the time of the measured
# part, the CPU time of the whole process (user and system) and its peak resident memory.
# usage: run.sh [--base CHECKOUT] [--cpus 0,1,...] [--rounds N] [--cases a,b] [--output FILE]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
base= cpus=0 rounds=15 output= only=
while [ $# -gt 0 ]; do
    case $1 in
        --base) base=$(realpath "$2"); shift 2 ;;
        --cpus) cpus=$2; shift 2 ;;
        --rounds) rounds=$2; shift 2 ;;
        --cases) only=$2; shift 2 ;;
        --output) output=$2; shift 2 ;;
        *) echo "run.sh: unknown argument $1" >&2; exit 2 ;;
    esac
done
if [ -n "$output" ] && [ -d "$output" ]; then echo "run.sh: --output $output is a directory; give a file path" >&2; exit 2; fi
cc=${CC:-gcc}
# Every C build takes the flags a release build takes (compiler/backend.ml): the same level of
# optimization, so that what is measured is what `starnite build --release` gives, and the same
# layout, so that a comparison measures the code and not where it happened to land. At -O3 GCC
# inlines differently, a recursive function into itself among other things, and results moved by
# up to 8% with changes elsewhere in the file.
release="-O2 -falign-functions=64 -falign-loops=64"
rustc=${RUSTC:-rustc}
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

build_starnite() {
    local checkout=$1 name=$2
    (cd "$checkout" && "$checkout/_build/default/compiler/main.exe" build --release --keep-c "$here/maps.stn" -o "$out/$name-generated")
    "$cc" $release -std=c11 -fno-strict-aliasing -I"$checkout/runtime" "$out/$name-generated.c" "$checkout/runtime/stn_runtime.c" -lm -o "$out/$name"
}
variants="starnite rust c-siphash c-fast"
build_starnite "$repo" starnite
"$rustc" -C opt-level=3 -C overflow-checks=yes "$here/maps.rs" -o "$out/rust"
"$cc" $release -std=c11 -Wall -Wextra -Werror "$here/maps.c" -o "$out/c-siphash"
"$cc" $release -std=c11 -Wall -Wextra -Werror -DFAST_HASH "$here/maps.c" -o "$out/c-fast"
if [ -n "$base" ]; then build_starnite "$base" previous-starnite; variants="previous-starnite $variants"; fi
"$cc" -O2 -std=c11 "$here/rusage.c" -o "$out/rusage"

if [ -n "$only" ]; then cases=$(printf '%s' "$only" | tr ',' ' '); else cases=$(cat "$here/cases.txt"); fi
RANDOM=311
median() { sort -n | awk '{ a[NR] = $1 } END { if (NR % 2) print a[(NR + 1) / 2]; else print (a[NR / 2] + a[NR / 2 + 1]) / 2 }'; }
samples=$out/samples.json
printf '{\n' > "$samples"
printf '%-4s %-16s %-18s %10s %10s %10s\n' cpu case build "time ms" "cpu ms" "rss MiB"
first_cpu=1
for cpu in $(printf '%s' "$cpus" | tr ',' ' '); do
    [ $first_cpu = 1 ] || printf ',\n' >> "$samples"; first_cpu=0
    printf '  "%s": {\n' "$cpu" >> "$samples"
    first_case=1
    for case in $cases; do
        for v in $variants; do : > "$out/$v.t"; : > "$out/$v.c"; : > "$out/$v.m"; done
        for round in $(seq 1 $((rounds + 2))); do
            seed=$((RANDOM % 993 + 7))
            checksums=
            for v in $(printf '%s\n' $variants | shuf --random-source=<(yes "$RANDOM")); do
                if ! result=$(printf '%s\n%s\n' "$case" "$seed" | taskset -c "$cpu" "$out/rusage" "$out/$v"); then
                    echo "$v failed on $case (CPU $cpu)" >&2; exit 1
                fi
                if [[ ! $result =~ ^([1-9][0-9]*)\ (-?[0-9]+)\ ([0-9]+)\ ([0-9]+)$ ]]; then
                    echo "$v printed '$result' for $case; expected a time, a checksum, CPU time and memory" >&2; exit 1
                fi
                checksums="$checksums ${BASH_REMATCH[2]}"
                if [ "$round" -gt 2 ]; then
                    echo "${BASH_REMATCH[1]}" >> "$out/$v.t"; echo "${BASH_REMATCH[3]}" >> "$out/$v.c"; echo "${BASH_REMATCH[4]}" >> "$out/$v.m"
                fi
            done
            if [ "$(printf '%s\n' $checksums | sort -u | wc -l)" != 1 ]; then
                echo "Checksum mismatch for $case on CPU $cpu:$checksums" >&2; exit 1
            fi
        done
        [ $first_case = 1 ] || printf ',\n' >> "$samples"; first_case=0
        printf '    "%s": {' "$case" >> "$samples"
        first_v=1
        for v in $variants; do
            printf '%-4s %-16s %-18s %10s %10s %10s\n' "$cpu" "$case" "$v" \
                "$(median < "$out/$v.t" | awk '{ printf "%.3f", $1 / 1e6 }')" \
                "$(median < "$out/$v.c" | awk '{ printf "%.3f", $1 / 1e6 }')" \
                "$(median < "$out/$v.m" | awk '{ printf "%.1f", $1 / 1024 }')"
            [ $first_v = 1 ] || printf ', ' >> "$samples"; first_v=0
            printf '"%s": {"time_ns": [%s], "cpu_ns": [%s], "rss_kib": [%s]}' "$v" "$(paste -sd, "$out/$v.t")" "$(paste -sd, "$out/$v.c")" "$(paste -sd, "$out/$v.m")" >> "$samples"
        done
        printf '}' >> "$samples"
    done
    printf '\n  }' >> "$samples"
done
printf '\n}\n' >> "$samples"
if [ -n "$output" ]; then mv -T -- "$samples" "$output"; fi
