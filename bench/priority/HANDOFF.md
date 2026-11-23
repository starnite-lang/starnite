# Starnite collection performance handoff

These changes address the three largest gaps in the previous C and Rust matrix. They are based on the experimental parser and collection optimizations carried forward in the preceding commit. The common base for both commits is Starnite revision `310897b`.

## Results

Each range spans four logical CPUs (0, 1, 4, 5) on one Intel Xeon Platinum 8573C host. Each CPU used 25 recorded samples after two warm-ups, with randomized implementation order. Each C comparison uses the faster of the original independent and tuned C controls on the same CPU. Ratios below 1.00× favor Starnite.

| Workload | Previous Starnite, ms | New Starnite, ms | New ÷ previous | New ÷ C | New ÷ Rust |
|---|---:|---:|---:|---:|---:|
| String prefix, suffix, and equality | 1.549–1.599 | 0.796–0.868 | 0.514–0.544× | 0.988–1.036× | 0.521–0.548× |
| Integer array membership | 2.156–2.344 | 0.841–0.888 | 0.372–0.402× | 0.555–0.574× | 0.235–0.242× |
| Array clear and refill | 0.146–0.210 | 0.040–0.041 | 0.191–0.278× | 0.360–0.364× | 0.274–0.277× |

Membership and refill were faster than both controls on every CPU. String comparison was ahead of C on three CPUs and 3.6% behind on the fourth. Rust used rustc 1.85.1 at optimization level 3 with checked overflow. C and both Starnite builds used GCC 14.2 at `-O3` to match the original matrix. The C membership control links the preceding runtime, so the result measures the newly added algorithm against the previous tuned implementation. The timed membership fixture uses absent keys. The conformance tests also exercise present keys, including the end of the array.

## Implementation

- **String comparisons.** Lower short literal prefixes and suffixes to bounded, fixed-width loads. The length guard dominates every load and the overlapping chunks cover all bytes. The loads use `memcpy` for unaligned and alias-safe access. Dynamic or long patterns use the general comparison. Keeping small equality checks inline avoids an extra call in the combined comparison.
- **Integer membership.** Runtime dispatch selects an aligned AVX-512 scan when supported. A scalar prefix aligns the reads, the vector loop reads only complete blocks, and a scalar tail handles remaining elements. AVX2 and portable scans still handle other targets.
- **Array refill.** Recognize a counted loop whose only action appends an affine signed integer to a direct local array. Exclusive ownership and available capacity are checked before writing directly. Checking both endpoints proves that all additions fit. The ordinary push loop handles growth, copy-on-write, and overflow and preserves the source position of traps.

## Verification and remaining work

- The conformance run passed 184 cases. A separate overflow fixture then matched the same exit status and source location in the interpreter and debug and release builds. New cases cover copy-on-write, capacity growth, negative and empty ranges, overflow, membership hits and misses, and short UTF-8 literals.
- All 31 collection and scalar kernels matched checksums on the two-CPU regression run. Compared with the preceding build, the owned UTF-8 slice and four-byte substring search medians rose about 7–8% on both CPUs. Option and Result medians rose 8–12%. These deserve a rerun and investigation before landing the branch. The regression file records all medians, including changes that differed by CPU.
- Both 10 MB parser checks passed on CPUs 0 and 4, including the acceptance and rejection fixtures. The updated compiler changed the fast parser medians by −2.8% to +0.7% versus the preceding compiler across the two inputs.
- A spot check of the default Starnite release build at GCC `-O2` still beat both existing `-O3` controls on membership and refill on CPUs 0 and 4. String comparison remained 4–11% behind tuned C in that check.
- AVX-512 results describe this x86-64 host. Measure the CPU-specific paths on other targets before drawing conclusions about their speed.

## Reproduce

Pin both sides explicitly. `HEAD^` moves with every commit, so it is not a baseline once more commits land on the branch. The baseline is `a7475b6e4009031e6da538647ecf85c43f535bc0` (the Codex handoff parent), and the candidate is the commit under review. The baseline must compile the current `bench.stn` and `kernels-c-tuned.c`; it provides `byte_at_or_end` and `stn_array_contains_i64`, and the runner fails at build time if it does not.

```sh
git worktree add --detach ../starnite-benchmark-base a7475b6e4009031e6da538647ecf85c43f535bc0
(cd ../starnite-benchmark-base && dune build compiler/main.exe)
git rev-parse HEAD   # record the candidate commit next to the results
dune build compiler/main.exe
bench/priority/run.sh ../starnite-benchmark-base --output /tmp/priority-samples.json
bench/priority/run.sh ../starnite-benchmark-base --all --output /tmp/priority-regression.json
```

Use `--cpus` to select logical CPU IDs. The runner uses a private temporary build directory and compiles the tuned C control against the baseline runtime. `samples-ns.json` contains the recorded priority samples in nanoseconds. `regression-median-ns.json` contains the median for each workload and CPU in the regression run.
