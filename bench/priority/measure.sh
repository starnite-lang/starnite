#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Measures the kernels of bench/priority. Every case runs 27 rounds on each CPU; a round runs the
# five variants in a random order, each on the same input, and their checksums must agree. The
# first two rounds warm up and are not counted. Prints the median of each variant in milliseconds
# and writes every sample, in nanoseconds, as JSON: {"CPU": {"case": {"variant": [ns, ...]}}}.
# usage: measure.sh BINARIES [--all] [--cpus 0,1,...] [--output FILE]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
binaries=$(cd "$1" && pwd); shift
output=priority-samples.json
cpus=$(taskset -cp $$ | sed 's/.*: //' | tr ',' '\n' | awk -F- '{ if (NF == 2) for (i = $1; i <= $2; i++) print i; else print $1 }' | head -4 | paste -sd, -)
all=0
while [ $# -gt 0 ]; do
    case $1 in
        --all) all=1; shift ;;
        --cpus) cpus=$2; shift 2 ;;
        --output) output=$2; shift 2 ;;
        *) echo "measure.sh: unknown argument $1" >&2; exit 2 ;;
    esac
done
# the output is a file: a directory there would take the samples as a file inside it
if [ -d "$output" ]; then echo "measure.sh: --output $output is a directory; give a file path" >&2; exit 2; fi
variants="previous-starnite starnite c-reference c-tuned rust-reference"
if [ $all = 1 ]; then cases=$(cat "$here/cases.txt"); else cases="str_prefix_suffix_eq array_contains array_clear_refill"; fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
RANDOM=310
median() { sort -n | awk '{ a[NR] = $1 } END { if (NR % 2) print a[(NR + 1) / 2]; else print (a[NR / 2] + a[NR / 2 + 1]) / 2 }'; }

# the samples are written to the output file only when every run has succeeded
final=$output; output=$tmp/samples.json
printf '{\n' > "$output"
first_cpu=1
for cpu in $(printf '%s' "$cpus" | tr ',' ' '); do
    [ $first_cpu = 1 ] || printf ',\n' >> "$output"; first_cpu=0
    printf '  "%s": {\n' "$cpu" >> "$output"
    first_case=1
    for case in $cases; do
        for v in $variants; do : > "$tmp/$v"; done
        for round in $(seq 1 27); do
            seed=$((RANDOM % 993 + 7))
            checksums=
            for v in $(printf '%s\n' $variants | shuf --random-source=<(yes "$RANDOM")); do
                # the run must succeed and print exactly a positive time and an integer checksum
                if ! result=$(printf '%s\n%s\n' "$case" "$seed" | taskset -c "$cpu" "$binaries/$v"); then
                    echo "$v failed on $case (CPU $cpu)" >&2; exit 1
                fi
                # the whole of what it printed is matched, so a second line is not a record to skip
                if [[ ! $result =~ ^([1-9][0-9]*)\ (-?[0-9]+)$ ]]; then
                    echo "$v printed '$result' for $case; expected a positive time and a checksum" >&2; exit 1
                fi
                elapsed=${BASH_REMATCH[1]} checksum=${BASH_REMATCH[2]}
                checksums="$checksums $checksum"
                if [ "$round" -gt 2 ]; then echo "$elapsed" >> "$tmp/$v"; fi
            done
            if [ "$(printf '%s\n' $checksums | sort -u | wc -l)" != 1 ]; then
                echo "Checksum mismatch for $case on CPU $cpu:$checksums" >&2; exit 1
            fi
        done
        line="$cpu $case"
        [ $first_case = 1 ] || printf ',\n' >> "$output"; first_case=0
        printf '    "%s": {' "$case" >> "$output"
        first_v=1
        for v in $variants; do
            line="$line $v=$(median < "$tmp/$v" | awk '{ printf "%.4f", $1 / 1e6 }')"
            [ $first_v = 1 ] || printf ', ' >> "$output"; first_v=0
            printf '"%s": [%s]' "$v" "$(paste -sd, "$tmp/$v")" >> "$output"
        done
        printf '}' >> "$output"
        echo "$line"
    done
    printf '\n  }' >> "$output"
done
printf '\n}\n' >> "$output"
mv -T -- "$output" "$final"
