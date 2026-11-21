# starnite

Starnite: a memory-safe language with Python-like syntax and no garbage collector. Value semantics, checked effects and typestate, aiming for C-level speed.

The language is defined by the *Starnite language specification, draft 0.1*. This repository holds the bootstrap compiler, written in OCaml as the specification decides (open issue 1), and is working through **milestone 1** of the specification's section 22.

```
fn centroid(points: Array[Vec3]) -> Vec3:
    var acc = Vec3(0.0, 0.0, 0.0)
    for p in points:
        acc += p
    acc / Float(len(points))
```

## Building

You need OCaml 4.14 or later, dune 3, and a C11 compiler (GCC or Clang).

```bash
dune build
```

The compiler is `_build/default/compiler/main.exe` (`dune install` puts it on your path as `starnite`).

## Using it

```bash
starnite run examples/hello.stn            # compile to C, build with the debug runtime, run
starnite run --release bench/nbody.stn     # -O2, no debug checks
starnite run --interp examples/hello.stn   # the reference interpreter (section 21.1)
starnite build examples/hello.stn -o hello # an executable
starnite check --json file.stn             # diagnostics only, as JSON
starnite test tests/unit/prelude_test.stn  # test blocks, including rejection tests
starnite emit-c file.stn                   # the generated C
```

Exit status follows section 11.5: 0 on success, 1 when an error reaches `main`, 2 on a trap. A debug build also exits with 3 when reference counts do not balance at exit.

## Layout

| Directory | Contents | Licence |
|---|---|---|
| `compiler/` | The bootstrap compiler: `lexer.ml`, `parser.ml` (pass 1), `typecheck.ml` and `exhaust.ml` (passes 2 to 6), `interp.ml` (the reference interpreter), `cgen.ml` (passes 10, 13 and 16), `main.ml` (the `starnite` command) | GPL-3.0-or-later |
| `runtime/` | The C runtime: object header, allocator, strings, arrays, closures, errors, traps | Apache-2.0 |
| `stdlib/` | `prelude.stn`, the core prelude loaded before every module | Apache-2.0 |
| `tests/` | The conformance corpus (`tests/run.sh`) | GPL-3.0-or-later |
| `bench/` | The milestone 1 gate benchmarks, each with a C baseline (`bench/run.sh`) | GPL-3.0-or-later |
| `examples/` | Small programs | GPL-3.0-or-later |

## Testing

CI (`.github/workflows/ci.yml`) runs on every push to `main` and every pull request:

- It builds with dune.
- It runs the conformance corpus with both GCC and Clang.
- It runs 500 fuzz cases from a fresh seed. The seed is printed first, so a failure can be replayed, and failing programs are kept as an artifact.


```bash
tests/run.sh
```

```bash
dune exec tests/fuzz/fuzz.exe -- --count 200
```

Each program in `tests/run` is run three ways (reference interpreter, debug C build, release C build), and all three must match each other and a reviewed golden output. That is oracle 3 of section 21.2, applied to a fixed corpus. The debug runtime also checks that counts balance at exit (oracle 2). `tests/errors` holds one golden test per implemented error code, with its location. `tests/unit` holds `test` blocks, and `rejects` tests that check the compiler refuses a misuse.

## Status against milestone 1

Milestone 1 (section 22.1) covers: the parser, type checker, structs, data types, generics, traits, trait values, projections, `mut` and `take`, errors as effects, naive counting, and C output, plus a reference interpreter, a fuzzer, a debug runtime, and a test runner.

Working now:

- **Pass 1, lexing and parsing (section 2).** Indentation, line continuation, every literal form (durations and sizes too), f-strings, and the full expression and statement grammar.
- **Passes 2 and 3, names and types (sections 3 and 5).** This covers structs with default fields, data types, aliases, generics with trait bounds, monomorphization, traits with type parameters, impls (generic ones too), method lookup, operators as trait methods, derived `Eq`, named arguments, and the `T -> T?` coercion. Matches are checked for exhaustiveness and reachability with Maranget's algorithm.
- **Pass 5, effects (sections 5.4, 7.1, 7.2).** Errors are a checked effect: `fail`, `try`, error unions, `Err(SomeType(...))` patterns, and `From` conversions. `io` is checked on exported functions. Private functions get their errors and `io` inferred by fixpoint. Function-typed parameters are effect-polymorphic, and `! pure` is checked.
- **Passes 4 and 6, the call-site rules (section 4).** `mut` must be marked at the call site (E0304) and must name a mutable place (E0303). A `mut` argument must not overlap another argument (E0301), and a closure argument must not capture one (E0305). A variable moved by an explicit `take` cannot be used again (E0302), across branches and loops.
- **Projections (section 4.6).** `lend` and `lend mut` functions hand out a place inside a parameter instead of a copy. The `Index` and `IndexMut` traits are lend methods, so a type that implements them gets `c[k]` and `c[k] = v`. A lent place lasts for one statement: it cannot be stored or returned (E0320), every path ends with exactly one `lend` (E0322), and a statement cannot take two `lend mut` places from one value (E0321) or touch the value they come from (E0323). In C a lend function returns a pointer into its argument.
- **Trait values (section 3.4).** `any Figure` holds a value of any type that implements the trait, chosen at run time. A value is boxed where `any Figure` is expected, and a method call on it runs the method of the hidden type. In C a trait value is two words, a counted box and a static method table for that type and trait, and the interpreter dispatches on the hidden type. Effects are the trait method's, and an impl may do less (a method that cannot fail can implement one that can). A trait can be used with `any` only if every method takes `Self` first, by borrow, has no type parameters, does not mention `Self` elsewhere, and does not lend a place (E0230). The compiler also refuses a type that does not implement the trait (E0204). Boxing needs an impl written in the program, except for `Show`, whose built-in formatting of primitives and tuples is used as it is; any other built-in implementation, such as `Hash` for `Int`, has no method table yet (E0204, or "not supported yet" when it is reached through a generic bound). Trait names are global until modules exist, so a second trait with the same name, a prelude trait's included, and a second impl of one trait for one type are E0101.
- **Closures and automatic sharing (section 13).** A captured `var` becomes a shared cell, and accesses keep their busy checks.
- **Arithmetic (section 17.1).** Overflow traps, wrapping operators, checked conversions, and division traps.
- **C output (section 11).** The object header, size-class allocator, inline and boxed data layouts with field-less variants encoded in the pointer (section 3.3), copy-on-write arrays, per-type release functions, and status-byte error returns. The debug build poisons freed memory and checks counts at exit.
- **The reference interpreter (section 21.1)**, the test runner with `assert`, `assert_fails` and `rejects` (section 20.2), and diagnostics in the format of section 19.1, plus JSON.
- **A first differential fuzzer (section 21.2)**, `tests/fuzz/fuzz.ml`. It builds well-typed programs by construction and requires the interpreter and the debug C build to agree, with balanced counts.

Not done yet:

- modules and `import` (3.5); one file is compiled at a time
- the rest of the fuzzer of section 21.2: shrinking failing programs, negative fuzzing, and comparing each optional pass on and off
- property, snapshot and doc tests, which belong to milestone 2

Strings are always heap buffers. The 15-byte inline form arrives with the layout work of milestone 2.

## Gate benchmarks

`bench/run.sh` compares `starnite build --release` with the same algorithm in C at `-O2`. Section 21.5 sets the milestone 1 target at 1.1 times C time or less.

| Benchmark | Starnite / C |
|---|---|
| centroid | 1.0x |
| n-body | 1.0x |
| Mandelbrot | 1.0x |
| spectral norm | 1.0x |

All four meet the gate and run at C speed, with every bounds check and overflow trap still in place. n-body, spectral norm and Mandelbrot land within about 3% of 1.0 from run to run. centroid runs for only about 35 ms, so its ratio moves by up to 10%.

What closed most of the gap:

- **Arrays hoisted out of loops.** A loop body may use an array only through element reads, element writes and `len`. The array is then made unshared once before the loop, and its data pointer and length are read into locals, so `-fno-strict-aliasing` no longer forces a reload after every store. Every bounds check stays.
- **Generated functions are `static inline`.** Bodies full of overflow checks look large to the C compiler, and small Starnite functions stayed calls in hot loops.
- **Large arrays grow with `realloc`**, which can move pages rather than copy them.
- **Array lengths carry their bound.** No array holds more than 2^40 elements, because every path that creates or grows one traps beyond that. `stn_len` tells the C compiler so. It can then bound loop counters and the index arithmetic built from them, and drop the overflow and sign checks it proves redundant. This took spectral norm from 1.17x to 1.0x.
- **`and`, `or` and comparisons stay C expressions** when their right side needs no statements of its own, so a loop condition reaches the C compiler as one test. Operands still evaluate left to right: the left one becomes a temporary unless it is a variable or a literal. This took Mandelbrot from 1.08x to 1.0x.

## Reading of the specification

Two choices here are interpretations where the draft is silent or in tension:

- Section 2.1 makes a line that starts with `-` continue the previous line, but section 5.5's patterns include negative literals. A line starting with `-` therefore starts a new line when it is a match arm, meaning it contains `->` outside brackets. Every other such line continues, as section 2.1 says.
- Section 13.3 gives the busy flag of a shared cell only for long accesses. This compiler also counts a `for ... in mut` over a cell as a long access, and clears the flag when the statement ends. A closure that reaches the array during the loop traps instead of reading freed memory. A direct use of the array in the loop body is rejected at compile time with E0323.
