#!/usr/bin/env python3
"""Measure paired kernel runtimes and verify checksums after each round."""
import argparse
import json
import os
import random
import statistics
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("binaries", type=Path)
parser.add_argument("--output", type=Path, default=Path("priority-samples.json"))
parser.add_argument("--cpus", default=",".join(map(str, sorted(os.sched_getaffinity(0))[:4])))
parser.add_argument("--all", action="store_true", help="Include all 31 collection and scalar workloads.")
args = parser.parse_args()
variants = [
    "previous-starnite", "starnite", "c-reference", "c-tuned", "rust-reference"
]
cases = (
    Path(__file__).with_name("cases.txt").read_text().splitlines()
    if args.all
    else ["str_prefix_suffix_eq", "array_contains", "array_clear_refill"]
)

rng = random.Random(310)
results = {}
for cpu in map(int, args.cpus.split(",")):
    os.sched_setaffinity(0, {cpu})
    results[cpu] = {}
    for case in cases:
        samples = {variant: [] for variant in variants}
        results[cpu][case] = samples
        for round_number in range(27):
            input_bytes = f"{case}\n{rng.randrange(7, 1000)}\n".encode()
            order = rng.sample(variants, k=len(variants))
            checksums = set()
            for variant in order:
                elapsed, checksum = map(int, subprocess.check_output(
                    [str((args.binaries / variant).resolve())], input=input_bytes
                ).split())
                if elapsed <= 0:
                    raise ValueError(f"{variant} recorded a nonpositive time for {case}")
                checksums.add(checksum)
                if round_number >= 2:
                    samples[variant].append(elapsed)
            if len(checksums) != 1:
                raise ValueError(f"Checksum mismatch for {case} on CPU {cpu}: {checksums}")
        print(cpu, case, *(
            f"{name}={statistics.median(values) / 1e6:.4f}"
            for name, values in samples.items()
        ), flush=True)

args.output.write_text(json.dumps(results, indent=2) + "\n")
