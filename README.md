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
| `compiler/` | The bootstrap compiler: `lexer.ml`, `parser.ml` (pass 1), `loader.ml` (the imports of pass 2), `typecheck.ml` and `exhaust.ml` (passes 2 to 6), `interp.ml` (the reference interpreter), `cgen.ml` (passes 10, 13 and 16), `main.ml` (the `starnite` command) | GPL-3.0-or-later |
| `runtime/` | The C runtime: object header, allocator, strings, arrays, closures, errors, traps | Apache-2.0 |
| `stdlib/` | `prelude.stn`, the core prelude loaded before every module | Apache-2.0 |
| `tests/` | The conformance corpus (`tests/run.sh`) | GPL-3.0-or-later |
| `bench/` | The milestone 1 gate benchmarks, each with a C baseline (`bench/run.sh`) | GPL-3.0-or-later |
| `examples/` | Small programs | GPL-3.0-or-later |

## Testing

CI (`.github/workflows/ci.yml`) runs on every push to `main` and every pull request:

- It builds with dune.
- It runs the conformance corpus with both GCC and Clang.
- It runs 500 fuzz cases from a fresh seed: each program on the interpreter and the C build, and then one mutation of it that must be rejected. The seed is printed first, so a failure can be replayed, and failing programs are kept as an artifact, the first three shrunk.


```bash
tests/run.sh
```

```bash
dune exec tests/fuzz/fuzz.exe -- --count 200
```

`tests/deep.sh` runs `tests/run/destination_passing.stn` on a million elements with the C builds, where the corpus uses a few thousand, as deep as the reference interpreter can recurse.

`tests/portable.sh` runs the string tests on the byte-wise paths of the Str layout, which every target that is not little-endian takes: on this machine with the fast paths turned off, and, when a cross compiler and qemu are installed (as in CI), on big-endian s390x.

The fuzzer takes `--count N` and `--seed S` (programs of the seeds S to S+N-1; a failing case is replayed with `--seed CASE --count 1`), `--keep DIR` (failing programs are saved there, a mutated one as `caseN.neg.stn`), `--shrink` with `--shrink-budget N`, `--reduce FILE` for a program in a file, whose candidates are written next to it so that the modules it imports are found (with `--keeping TEXT`, which keeps what the compiler accepts and has TEXT in it, for a mutation that was accepted, or `--rejected CODE`, for one that was rejected with the wrong code), `--print` (with `--mutated`, the program of the seed after its mutation, and what it must be rejected with; with `--write DIR`, the files that the compiler is given, which for a split program are `main.stn` and `fuzzlib.stn`), `--no-negative`, `--negative-only`, and `--crash` with `--corruptions N`. The text of a program is the one file, and a split program has `# module` for its first line; a failing split program is kept as that text and as its two files in a directory `caseN.split`. `STARNITE` names the compiler to test. `tests/fuzz/selftest.sh` runs as part of `tests/run.sh`: it checks the fuzzer itself, against this compiler and against compilers with a fault put in on purpose (`tests/fuzz/buggy.sh`: a checker that accepts a use after `take`, one that says the wrong code, a C build that prints a line too many, and a compiler that does something else with a program in two files than with the same program in one).

Each program in `tests/run` is run three ways (reference interpreter, debug C build, release C build), and all three must match each other and a reviewed golden output. That is oracle 3 of section 21.2, applied to a fixed corpus. The debug runtime also checks that counts balance at exit (oracle 2). `tests/errors` holds one golden test per implemented error code, with its location. `tests/unit` holds `test` blocks, and `rejects` tests that check the compiler refuses a misuse.

## Status against milestone 1

Milestone 1 (section 22.1) covers: the parser, type checker, structs, data types, generics, traits, trait values, projections, `mut` and `take`, errors as effects, naive counting, and C output, plus a reference interpreter, a fuzzer, a debug runtime, and a test runner.

Working now:

- **Pass 1, lexing and parsing (section 2).** Indentation, line continuation, every literal form (durations and sizes too), f-strings, and the full expression and statement grammar.
- **Passes 2 and 3, names and types (sections 3 and 5).** This covers structs with default fields, data types, aliases, generics with trait bounds, monomorphization, traits with type parameters, impls (generic ones too), method lookup, operators as trait methods, derived `Eq`, named arguments, and the `T -> T?` coercion. Matches are checked for exhaustiveness and reachability with Maranget's algorithm. A name defined twice is E0101: a type, a trait, a variant, a method, a field of a struct or of a variant, and a generic parameter of a function, type, trait or impl. A parameter given twice in a call, by position and by name or by two names, is E0203. A trait method can have type parameters of its own, `fn map[U](x: Self, f: fn(Int) -> U) -> U`: a call settles them from its arguments, with their bounds as obligations, on a value of a type, through a bound, with the trait written out, and for an impl in another module. A type parameter that nothing settles, of a function or of a trait method, is E0210: the call needs an annotation on the value it returns, or for a function its type arguments written (section 5.1). The type arguments of a generic function or type can be written in brackets before the call, `first[Int](xs)`, `Box[Float](2.5)`, `Cons[Int](1, Nil)`, all of them or the first few, and are what the call then has; brackets after something that is not generic are E0102, more than it has E0203, and without a call E0102. An integer literal is an `Int`, or the integer type that is expected, and never a `Float` or an `F32` (section 5.2): `let x: Float = 1` is E0201, and `1.0` is the float.
- **Pass 5, effects (sections 5.4, 7.1, 7.2).** Errors are a checked effect: `fail`, `try`, error unions, `Err(SomeType(...))` patterns, and `From` conversions. `io` is checked on exported functions. Private functions get their errors and `io` inferred by fixpoint. Function-typed parameters are effect-polymorphic, and `! pure` is checked.
- **Passes 4 and 6, the call-site rules (section 4).** `mut` must be marked at the call site (E0304) and must name a mutable place (E0303). A `mut` argument must not overlap another argument (E0301), and a closure argument must not capture one (E0305). A variable moved by an explicit `take` cannot be used again (E0302), across branches and loops.
- **Projections (section 4.6).** `lend` and `lend mut` functions hand out a place inside a parameter instead of a copy. The `Index` and `IndexMut` traits are lend methods, so a type that implements them gets `c[k]` and `c[k] = v`. A lent place lasts for one statement: it cannot be stored or returned (E0320), every path ends with exactly one `lend` (E0322), and a statement cannot take two `lend mut` places from one value (E0321) or touch the value they come from (E0323). In C a lend function returns a pointer into its argument.
- **Trait values (section 3.4).** `any Figure` holds a value of any type that implements the trait, chosen at run time. A value is boxed where `any Figure` is expected, and a method call on it runs the method of the hidden type. In C a trait value is two words, a counted box and a static method table for that type and trait, and the interpreter dispatches on the hidden type. Effects are the trait method's, and an impl may do less (a method that cannot fail can implement one that can). A trait can be used with `any` only if every method takes `Self` first, by borrow, has no type parameters, does not mention `Self` elsewhere, and does not lend a place (E0230). The compiler also refuses a type that does not implement the trait (E0204). Boxing needs an impl written in the program, except for `Show`, whose built-in formatting of primitives and tuples is used as it is; any other built-in implementation, such as `Hash` for `Int`, has no method table yet (E0204, or "not supported yet" when it is reached through a generic bound). A second trait with the name of one in the same module or in the prelude, and a second impl of one trait for one type, are E0101. A trait cannot be implemented for a trait value itself (`impl Describe for any Figure`, E0230), since a call on a trait value uses only the methods of its own trait: add the method to that trait, or write a function that takes the trait value. An impl for a type that contains one, such as `Array[any Figure]`, is an ordinary impl.
- **Modules (section 3.5).** One file is one module. `import geometry.vec` loads `geometry/vec.stn`, looked up from the directory of the file given to the compiler, and `import geometry.vec as g` names it `g`. Each module is loaded once, after the modules it imports, and an import cycle is an error (E0101). An item is private unless its name is followed by `*`: functions, types, traits and constants. The program reaches an exported item through the module's name, `vec.add(a, b)`, `vec.Vec(1, 2)`, `vec.Circle(r)` as an expression and as a pattern, `vec.Shape.Dot`, `any vec.Area`, `T: vec.Area`, and an error type `! vec.Problem`. Every module has names of its own, so two modules, or a module and the program, can each have a type, a trait, a constant and a function of one name. A private item used from outside, a module that is not imported, and an exported name written without its module are E0101. The fields and variants of an exported type come with it, and a value of a private type that leaves its module has fields nobody outside can read. The default of a parameter or a field is checked where its parameter or field is declared: its names are that module's own, and neither the variables nor the type parameters of the call are in scope in it, while a type parameter of the function it belongs to means what the call made of it. An impl must be in the module that defines the trait or the module that defines the type (section 3.4), or it is E0101. In C a type of another module is named `Zq` and its path, with `Zd` for each dot.
- **The core library (section 20.1), as far as milestone 1 needs it.** `Array`: `len`, `push`, `pop`, `insert`, `remove`, `clear`, `extend`, `filled` and the repeat literal `[x; n]`, `contains`, `reverse`, a stable `sort`, `swap`, slicing and comprehensions. `Str`: `len`, `chars`, `split`, `words`, `join`, `trim`, `contains`, `starts_with`, `ends_with`, `repeat`, `parse_int` and `parse_float` (which fail with `ParseError`). `Option` and `Result` with `or`, `is_some`, `is_none`, `is_ok` and `unwrap`, the numeric functions, and the traits `Eq`, `Ord`, `Hash`, `Show`, `Add`, `Sub`, `Mul`, `Div`, `Index`, `IndexMut`, `From`, `Default` and `Copy`.
- **Closures and automatic sharing (section 13).** A captured `var` becomes a shared cell, and accesses keep their busy checks.
- **Arithmetic (section 17.1).** Overflow traps, wrapping operators, checked conversions, and division traps.
- **C output (section 11).** The object header, size-class allocator, inline and boxed data layouts with field-less variants encoded in the pointer (section 3.3), copy-on-write arrays, per-type release functions, and status-byte error returns. The debug build poisons freed memory and checks counts at exit. A program that recurses until its stack is gone is a trap, `stack overflow`, with the status of the others: in C a handler of the fault, which runs on a stack of its own, writes the output so far and the report, and on the interpreter the exception is turned into the same. A program nested deeper than the compiler's own recursion is E0100.
- **The reference interpreter (section 21.1)**, the test runner with `assert`, `assert_fails` and `rejects` (section 20.2), and diagnostics in the format of section 19.1, plus JSON.
- **The program fuzzer (section 21.2)**, `tests/fuzz/fuzz.ml`. It builds well-typed programs by construction and requires the interpreter and the debug C build to agree, with balanced counts. Its programs include trait values: boxing in arguments, arrays, fields and `Option`, calls through method tables, nested values, closures that capture them, `mut` parameters, failures that cross a trait method, and `any Show` of primitives, tuples and user types. Half of the programs are split across a module (section 3.5): the types, traits and functions that every program has are in `fuzzlib.stn`, all exported, and the main file imports it and writes each of their names with `fuzzlib.` before it, in expressions, patterns, types and bounds. Every program has a type of the main file, `Local`, that implements the trait `Fig` of the prelude, so a split program has an impl of a trait of one module for a type of another, boxed as `any fuzzlib.Fig`. A split program must also do what the same program in one file does, a third oracle that module resolution is checked by, since both backends share it. Its programs also use projections (section 4.6): writes and compound writes through `lend mut` calls on a field and on an element, a function that lends one of two places, and reads through `lend`. Those productions found that a lend in the body of an `if` or a loop was checked against the whole enclosing statement, which rejected valid programs.
- **Negative fuzzing (section 21.2).** A program that agrees gets one mutation with a known violation, and the checker must reject it with the code of the rule that was broken, or with a code of the E02 family for a type mismatch. There are twenty-two kinds: a use after `take`, a `take` in a loop, a `mut` marker left out, `mut` of an immutable, an assignment to an immutable, two overlapping `mut` arguments, a closure over a `mut` argument, an arm of a match left out, an unknown name, too few arguments, an argument given twice, an argument, an annotation or a result of another type, an error that an exported function does not list, a field named twice, a type parameter named twice, an element type that is never settled, type arguments after a function that is not generic, too many type arguments, an explicit type argument that breaks a bound, and an impl that adds a bound to a method. Each kind is as likely as any other. A mutation is made of the program's own lines and variables when it has some that fit (half of the time), and otherwise it is written with a variable of its own and put after one of the statements of the program, whatever its depth, so that the rules are tried inside loops and branches.
- **The compiler does not crash (section 21.2, the first oracle).** `--crash` changes the bytes of each program with no regard for what it says (a character taken out, the text cut short, a character replaced, a piece repeated or taken out, two characters swapped), most of them into programs that no rule of the language was written for, and whatever the compiler says of one it must say: an exception that nothing caught, a check or a run that does not end where it should, or C that the C compiler cannot build is a crash. A program that still checks is run by the interpreter, then built (a step of its own, with the C compiler) and the program it makes is run by the fuzzer, with what each prints on the standard output and on the standard error kept apart. A crash is an uncaught exception on the standard error, a status of 2 or more from the check, a build of a program that checked that fails (any nonzero status, the C compiler failing with or without a word, unless it is the compiler's own report that the program uses what it does not support yet: status 1 and a line `error: not supported yet: ...`, with no fatal exception and no failed C compiler), a process killed by a signal of any kind (the check, the interpreter, the build or the program built), or a build that does not end. The mode of a reduction is fixed by its input: a file that is not split is written as one file in every candidate, and what is next to it is never written over. A program that prints the words of a crash is not one, and a program that loops or traps is the program's. A crash is shrunk like the other failures. It found a binary operator with no rule, from a line that starts with `|` and so continues the one before it, and a built-in function used as a value, which made the C backend raise.
- **Shrinking (section 21.2).** A failing program (the interpreter and the C build disagree, a mutation was accepted, or one was rejected with the wrong code) is cut down while it still fails: statements and items are deleted, a loop, an `if` or a `match` is replaced by what is in its body, and declarations and numbers are made simple. A mutation that was accepted is kept by the lines that make the violation, so that the reduced program is still one. In the fuzzer's own tests, programs of 250 lines come down to between 2 and 45.

Not done yet:

- the last oracle of the fuzzer of section 21.2, comparing each optional pass on and off, which waits for the optional passes
- `split_at_mut`, `Slice[T]` and `StrView` of the `array` and `str` modules: they are views into a borrowed buffer, which the `local` mode of milestone 3 is for (section 10.5), and `swap` covers the common case of two parts of one array; and a search function over arrays, which the draft names without a signature
- property, snapshot and doc tests, which belong to milestone 2

## Milestone 2 so far

- **`Map` and `Set` (section 3.6).** Literals (`{"a": 1}`, `{1, 2}`, `{}` where the expected type says which, `Map()`, `Set()`), `m[k]` (which traps on a missing key), `m[k] = v`, `m[k] += v` from `Default.default()`, `get`, `contains`, `remove`, `clear`, `len`, `add`, `==` in any order, `Show`, the set operators `|`, `&` and `-`, `for (k, v) in m` and `for x in s` in insertion order, `{k: v for ...}` and `{x for ...}`, and an entry as a place: `m[k].x = v`, `m[k].push(x)`, `f(mut m[k])`, `for x in mut m[k]`. Keys are anything with `Hash` and `Eq`, derived for numbers, strings, tuples, structs, data types and arrays, or written by the program. The interpreter keeps a Map as an ordered array of pairs; the C runtime as a compact insertion-ordered table with an index of control bytes searched sixteen at a time, SipHash-1-3 under a key drawn per process, and no stored hash for 64-bit integer keys. Int and Str keys are looked up inline in the generated code.

- **Inline strings (section 3.6).** A `Str` is 16 bytes. A string of up to 15 bytes is stored in the value itself, with its length in the last byte, and needs no allocation; a longer one is a counted buffer and its length. Two inline strings are equal exactly when their two words are, and hash from those words. A slice is a new string: inline when short, the same buffer when it is the whole string, a copy otherwise. Runtime string functions read a string where it already is, by address, and short results are assembled in registers, because reading an inline string back right after its words were stored stalls the processor.

- **String views.** A slice of a string that cannot change while it is in scope (an immutable binding, a borrowed parameter, a literal, an element of an array that does not change) is a view of its bytes: nothing is copied. A view is a `Str` with a bit set. Dropping one does nothing and duplicating one copies it, so a view that is stored, returned or used as a key becomes a string of its own, and none of this can be seen from a program. A `let` or `var` of such a slice keeps the view. A variable whose only assignments are slices of itself (`rest = rest[k..]`) is kept as a view that each of them moves along, and one that owns its buffer is cut down in place when nothing else holds it. A cursor over a 300 KB string went from 30 ms to 0.15 ms.

- **Counting (section 9), first part.** The last use of an owned variable moves its reference: nothing is counted when a local is returned, stored or passed to a `take` parameter, and its buffer stays uniquely held, so what follows can change it in place. An occurrence moves when it is the last in the order of evaluation, the only one in its statement, and not in a loop or closure the variable was declared outside of; `x = f(take x)` moves anywhere, since the statement assigns `x` before anything reads it. A `let` that only names a binding that cannot change, or a field or element of one, borrows it. `a + b` appends in place when the expression owns `a` and nothing else holds its buffer. `bench/counting/run.sh BASE` measures these: an array handed to a function and assigned back 20,000 times went from 222 ms to 0.14 ms, lets of fields and elements from 18.8 ms to 4.1 ms, and a string grown by assignment from 2.35 ms to 0.86 ms. Still naive: a value that is only read is released at the end of its scope; `take` parameters are never demoted to borrows; and destination passing is not built.

- **Reuse (section 9.3).** A `match` holds a reference of its own to what it matches, so a variable at its last use moves into it. An arm that takes a boxed variant apart into variables consumes that reference: when nothing else holds the value, its fields move into the variables and its cell serves the first constructor of the same type that the arm runs, or is freed when the arm ends; otherwise the variables are duplicated and the value released. The variables are owned either way, so their last uses move too, and a function that takes a list or tree by `take`, takes it apart and rebuilds it does so in place: rebuilding a 1,000-element list 2,000 times went from 48.9 ms to 13.3 ms. Patterns that nest, and values reached through a read-only parameter, are not reused.

- **Destination passing (sections 9.5 and 9.7).** A function that returns a constructor holding a call of itself, such as `Cons(x + by, bump(take rest, by))`, runs as a loop: the constructor is stored with that field empty where the last turn left a destination, the destination becomes the empty field, and the parameters take the call's arguments. A plain call of itself in tail position is a turn of the same loop. Stack use is constant. A `take` parameter takes any argument; any other parameter that holds something counted must be passed on as it is; functions that can fail or have `mut` parameters are not converted. The release of a data type goes round a loop on the last field of its own type, so a long list is freed in constant stack too.
- **`noalloc fn` and `inplace fn` (section 9.6).** Both are checked on the C a function becomes, which is where this compiler decides counts, reuse and destination passing (`compiler/verify.ml`). Every name a body calls or mentions is another generated function, read the same way; or a function of the runtime from which no path reaches `malloc`, a list computed from the runtime's source; or else it is taken to allocate, as is any call through a closure or an `any` value. A `noalloc fn` must reach no allocation (E0601). An `inplace fn` must build every cell out of one that a match took apart (E0602), raise no count (E0603), call only inplace functions and functions that do not allocate (E0604), and call itself only in tail or constructor-tail position (E0605). The error names the expression and why it can allocate. Strict where `unique` (section 6.2) would be needed: a write to an array or map the function was handed counts as allocating, because it copies when the value is shared, and so does keeping a string that may be a view. Not built: callers of an inplace function do not yet have to pass a unique value, so the paths taken for a shared one, which copy, are exempt from the check rather than ruled out. The last use of a variable in each branch of an `if` or `match` now moves it, which the check on a filter found missing.
- **Reporting copies (section 9.8).** `--explain-copies` lists, with source positions, each write that copies its array, map or set first when something else holds it (section 4.5), and each count raised inside a loop of the program. `--profile-copies` builds the program so that it counts, per source line, the copies of shared arrays, maps and sets that actually happen, the views of strings copied to be kept, and the counts raised, and prints the totals to standard error when it ends. Generated C then carries `#line` directives, and the runtime is compiled with `STN_PROFILE_COPIES`; an ordinary build has neither. `tests/copies.sh` checks both on `tests/copies/copies.stn`. Not built: the earlier use that made a value shared is not named, and since `unique` parameters do not exist there are no implicit `copy()` calls to report.
- **Releasing large structures (section 9.7).** Releases nest at most `STN_RELEASE_DEPTH` (256) deep. Past that, an object whose count reached zero goes on a list and is released when the nesting has unwound, so a tree a million deep on its left, or a million values each held in the array of the next, is released without a stack as deep as it is (`tests/deep/release.stn`). `STN_FREE_BUDGET=n` releases at most `n` objects in one go and takes up the rest at the next allocation. Differs from the spec: the list is an array of the runtime's own that grows as needed, not a chain threaded through the objects being freed, whose headers have no room for a link; if it cannot grow, the object is released at once.

- **Release builds align functions and loops to 64 bytes.** Without it, the speed of a loop depended on where unrelated code before it happened to end: moving unchanged code by sixteen bytes changed single benchmarks by up to 80% with GCC and 66% with Clang, and two builds that ran the same instructions differed by up to 18%. Aligned, the same shifts move them by 8% or less (GCC) and 5% or less (Clang, one case at 16%). It costs about 5% of the size of the code. The benchmark scripts build every C program, the references included, with the flags of a release build: the same layout and the same `-O2`. Three of them, `bench/priority/run.sh`, `bench/maps/run.sh` and `bench/counting/run.sh`, used `-O3` until the counting work; at that level GCC's inlining of a recursive function into itself moved one result by 8% when unrelated functions changed. The results of those three suites recorded in this file before then were taken at `-O3`. The gate benchmarks below were not: `bench/run.sh` has always compared `starnite build --release` with C at `-O2`.

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

## Collection and string benchmarks

`bench/priority/run.sh` compares 31 collection, string and scalar workloads with the same work in plain C (`kernels.c`), in C tuned by hand against the runtime (`kernels-c-tuned.c`), and in Rust with overflow checks on (`bench.rs`). It also builds an earlier Starnite as a baseline, so a change is measured against what came before it.

To run it, check out the baseline next to the repository and build both compilers. The baseline must be able to compile the current `bench.stn` and the tuned C control; `3ae8247` is the first commit on `main` that can, and the runner fails at build time with an older one.

```sh
git worktree add --detach ../starnite-benchmark-base 3ae8247
(cd ../starnite-benchmark-base && dune build compiler/main.exe)
git rev-parse HEAD   # record the commit that is measured next to the results
dune build compiler/main.exe
bench/priority/run.sh ../starnite-benchmark-base --all --output /tmp/priority.json
```

- Without `--all` it runs three workloads (`str_prefix_suffix_eq`, `array_contains`, `array_clear_refill`); `cases.txt` lists all 31.
- `--cpus 0,1,2,3` picks the logical CPUs (the first four allowed ones by default). Every workload runs on each.
- It needs `gcc` (or `CC`), `rustc` (or `RUSTC`), `taskset` and `shuf`.
- Each workload runs 27 rounds per CPU. A round runs the five builds in a random order on the same input, and their checksums must agree; the first two rounds are not counted. A build that exits with an error or prints anything but a time and a checksum stops the run.
- It prints one line per CPU and workload with the median of each build in milliseconds, and writes every sample in nanoseconds to the `--output` file as JSON.
- `samples-ns.json` and `regression-median-ns.json` are an archive: the samples and medians recorded when the first of this work was measured. They were taken on logical CPUs 0, 1, 4 and 5 of one Intel Xeon Platinum 8573C host, with GCC 14.2 at `-O3` for C and for both Starnite builds, rustc 1.85.1 at optimization level 3 with checked overflow, and the baseline `a7475b6`, which is not on `main`. The [handoff written with them](https://github.com/starnite-lang/starnite/blob/3ae82471ebb67d59d713787e4c33f4a772d2f7fe/bench/priority/HANDOFF.md) has the method and the results in full. The `3ae8247` baseline above is for new runs.

Read a result as Starnite divided by the fastest of the three controls on the same CPU. On the 4-CPU x86-64 host it was last run on, 28 workloads were within 3% of that and the other three within 4.4%, with peak memory level. A few string workloads move by 10 to 25% with where the C compiler places code, and timings shift with what else the machine is doing, so compare builds within one run, never across runs. The AVX-512 results describe that host; other targets take the AVX2 or the portable paths.

Generated functions are marked hot in optimized builds, which makes GCC compile them 40 to 55% more slowly and keeps loops in rarely taken branches fast.

## Map and Set benchmarks

`bench/maps/run.sh` compares eleven Map and Set workloads with the same work in Rust (`HashMap` and `HashSet`, whose default hasher is SipHash-1-3 too) and in C (`maps.c`: an open-addressing table with linear probing, built once with SipHash and once with a fast multiply-and-shift mixer, `-DFAST_HASH`, which chosen keys can make collide). For every run it records the time of the measured part, the CPU time of the whole process and its peak resident memory, and the checksums of all four builds must agree.

```sh
bench/maps/run.sh --cpus 0,1,2,3 --rounds 15 --output /tmp/maps.json
```

`--cases a,b` runs some of the workloads and `--base CHECKOUT` adds an earlier Starnite. It needs `gcc` (or `CC`), `rustc` (or `RUSTC`), `taskset` and `shuf`.

On the 4-CPU x86-64 host it was last run on, Starnite was at or below Rust and the SipHash C table in time on every workload but one (string counting, level with C), and used less memory than both everywhere: about 30% less than Rust and 50 to 70% less than C. Against the C table with the fast mixer, lookups, updates and removals of integer keys take 1.2 to 2.4 times as long; that is the price of SipHash, which the specification keeps for every key so that chosen keys cannot force collisions.

## Reading of the specification

Seven choices here are interpretations where the draft is silent or in tension:

- When two impls of one trait both fit a type, the first one written whose bounds hold is used, by the checker and by both backends. The draft does not rank them, so a more specific impl does not win over an earlier generic one.

- Section 2.1 makes a line that starts with `-` continue the previous line, but section 5.5's patterns include negative literals. A line starting with `-` therefore starts a new line when it is a match arm, meaning it contains `->` outside brackets. Every other such line continues, as section 2.1 says.
- Section 13.3 gives the busy flag of a shared cell only for long accesses. This compiler also counts a `for ... in mut` over a cell as a long access, and clears the flag when the statement ends. A closure that reaches the array during the loop traps instead of reading freed memory. A direct use of the array in the loop body is rejected at compile time with E0323.
- Section 13.3 does not say when the busy flag of a long access starts, relative to the other arguments of the call, or when it ends. Arguments are evaluated left to right. A shared cell passed as `mut` to a function is busy from where that argument is written until the frame it was taken in ends: a statement, but also a condition, an operand of `and` or `or`, the value of a branch, an arm or a block, the body of a comprehension, a `try`, and a function body. An argument written before it can read the cell; one written after it traps. A built-in such as `push` cannot call a closure, so it lends nothing, and its arguments can read the receiver, or change it, first. The interpreter and the C backend agree on all of this.
- Section 3.5 shows an import only used through the module's name (`http.get`, `clock.now()`, `tcp.send`), so that is the only way in: `import net.http` gives the name `http`, and no item of the module is also a name of its own in the importing module. A module path is looked up from the directory of the file given to the compiler, whichever file the import is in, until package roots arrive (section 3.8).
- Section 4.7 finds a method among "functions named `f` in the module that defines `x`'s type", and then the methods of the traits in scope. Here the exported functions of the module that defines the type are found first, and only if none of them takes the receiver (a function of `Box[Int]` does not take a `Box[Str]`, nor does one, generic or not, whose bound the receiver breaks, nor a trait method whose impl's bounds do not hold) are the functions of the module that makes the call and of the prelude, and then the methods of the traits in scope before a type error, so a program can write a function over `Str` or `Array[Int]` and call it as a method, and a function of its own does not make the type's method ambiguous. `T.f(args)` takes the same order, and with several functions for `T` it takes the instantiation and bounds of its first argument into account as a receiver's would be. For an impl, a type that a module of the program declares is defined by that module alone, whatever it is applied to, and a type that the prelude's constructors make (`Array[Point]`, `Point?`, a tuple) is defined by the modules of the types it is made from. A trait is in scope in the module that defines it, in the prelude, and in a module that imports its module, if the trait is exported. Impls are not scoped: an impl applies wherever its trait and its type are known.
- Section 3.5 says the fields and variants of an exported type are visible with it. The other half is taken to hold as well: the fields of a type that is not exported cannot be read or assigned outside its module, though a function can return a value of that type.
