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

The fuzzer takes `--count N` and `--seed S` (programs of the seeds S to S+N-1; a failing case is replayed with `--seed CASE --count 1`), `--keep DIR` (failing programs are saved there, a mutated one as `caseN.neg.stn`), `--shrink` with `--shrink-budget N`, `--reduce FILE` for a program in a file, whose candidates are written next to it so that the modules it imports are found (with `--keeping TEXT`, which keeps what the compiler accepts and has TEXT in it, for a mutation that was accepted, or `--rejected CODE`, for one that was rejected with the wrong code), `--print` (with `--mutated`, the program of the seed after its mutation, and what it must be rejected with; with `--write DIR`, the files that the compiler is given, which for a split program are `main.stn` and `fuzzlib.stn`), `--no-negative`, `--negative-only`, and `--crash` with `--corruptions N`. The text of a program is the one file, and a split program has `# module` for its first line; a failing split program is kept as that text and as its two files in a directory `caseN.split`. `STARNITE` names the compiler to test. `tests/fuzz/selftest.sh` runs as part of `tests/run.sh`: it checks the fuzzer itself, against this compiler and against compilers with a fault put in on purpose (`tests/fuzz/buggy.sh`: a checker that accepts a use after `take`, one that says the wrong code, a C build that prints a line too many, and a compiler that does something else with a program in two files than with the same program in one).

Each program in `tests/run` is run three ways (reference interpreter, debug C build, release C build), and all three must match each other and a reviewed golden output. That is oracle 3 of section 21.2, applied to a fixed corpus. The debug runtime also checks that counts balance at exit (oracle 2). `tests/errors` holds one golden test per implemented error code, with its location. `tests/unit` holds `test` blocks, and `rejects` tests that check the compiler refuses a misuse.

## Status against milestone 1

Milestone 1 (section 22.1) covers: the parser, type checker, structs, data types, generics, traits, trait values, projections, `mut` and `take`, errors as effects, naive counting, and C output, plus a reference interpreter, a fuzzer, a debug runtime, and a test runner.

Working now:

- **Pass 1, lexing and parsing (section 2).** Indentation, line continuation, every literal form (durations and sizes too), f-strings, and the full expression and statement grammar.
- **Passes 2 and 3, names and types (sections 3 and 5).** This covers structs with default fields, data types, aliases, generics with trait bounds, monomorphization, traits with type parameters, impls (generic ones too), method lookup, operators as trait methods, derived `Eq`, named arguments, and the `T -> T?` coercion. Matches are checked for exhaustiveness and reachability with Maranget's algorithm. A name defined twice is E0101: a type, a trait, a variant, a method, a field of a struct or of a variant, and a generic parameter of a function, type, trait or impl. A parameter given twice in a call, by position and by name or by two names, is E0203.
- **Pass 5, effects (sections 5.4, 7.1, 7.2).** Errors are a checked effect: `fail`, `try`, error unions, `Err(SomeType(...))` patterns, and `From` conversions. `io` is checked on exported functions. Private functions get their errors and `io` inferred by fixpoint. Function-typed parameters are effect-polymorphic, and `! pure` is checked.
- **Passes 4 and 6, the call-site rules (section 4).** `mut` must be marked at the call site (E0304) and must name a mutable place (E0303). A `mut` argument must not overlap another argument (E0301), and a closure argument must not capture one (E0305). A variable moved by an explicit `take` cannot be used again (E0302), across branches and loops.
- **Projections (section 4.6).** `lend` and `lend mut` functions hand out a place inside a parameter instead of a copy. The `Index` and `IndexMut` traits are lend methods, so a type that implements them gets `c[k]` and `c[k] = v`. A lent place lasts for one statement: it cannot be stored or returned (E0320), every path ends with exactly one `lend` (E0322), and a statement cannot take two `lend mut` places from one value (E0321) or touch the value they come from (E0323). In C a lend function returns a pointer into its argument.
- **Trait values (section 3.4).** `any Figure` holds a value of any type that implements the trait, chosen at run time. A value is boxed where `any Figure` is expected, and a method call on it runs the method of the hidden type. In C a trait value is two words, a counted box and a static method table for that type and trait, and the interpreter dispatches on the hidden type. Effects are the trait method's, and an impl may do less (a method that cannot fail can implement one that can). A trait can be used with `any` only if every method takes `Self` first, by borrow, has no type parameters, does not mention `Self` elsewhere, and does not lend a place (E0230). The compiler also refuses a type that does not implement the trait (E0204). Boxing needs an impl written in the program, except for `Show`, whose built-in formatting of primitives and tuples is used as it is; any other built-in implementation, such as `Hash` for `Int`, has no method table yet (E0204, or "not supported yet" when it is reached through a generic bound). A second trait with the name of one in the same module or in the prelude, and a second impl of one trait for one type, are E0101. A trait cannot be implemented for a trait value itself (`impl Describe for any Figure`, E0230), since a call on a trait value uses only the methods of its own trait: add the method to that trait, or write a function that takes the trait value. An impl for a type that contains one, such as `Array[any Figure]`, is an ordinary impl.
- **Modules (section 3.5).** One file is one module. `import geometry.vec` loads `geometry/vec.stn`, looked up from the directory of the file given to the compiler, and `import geometry.vec as g` names it `g`. Each module is loaded once, after the modules it imports, and an import cycle is an error (E0101). An item is private unless its name is followed by `*`: functions, types, traits and constants. The program reaches an exported item through the module's name, `vec.add(a, b)`, `vec.Vec(1, 2)`, `vec.Circle(r)` as an expression and as a pattern, `vec.Shape.Dot`, `any vec.Area`, `T: vec.Area`, and an error type `! vec.Problem`. Every module has names of its own, so two modules, or a module and the program, can each have a type, a trait, a constant and a function of one name. A private item used from outside, a module that is not imported, and an exported name written without its module are E0101. The fields and variants of an exported type come with it, and a value of a private type that leaves its module has fields nobody outside can read. The default of a parameter or a field is checked where its parameter or field is declared: its names are that module's own, and neither the variables nor the type parameters of the call are in scope in it, while a type parameter of the function it belongs to means what the call made of it. An impl must be in the module that defines the trait or the module that defines the type (section 3.4), or it is E0101. In C a type of another module is named `Zq` and its path, with `Zd` for each dot.
- **Closures and automatic sharing (section 13).** A captured `var` becomes a shared cell, and accesses keep their busy checks.
- **Arithmetic (section 17.1).** Overflow traps, wrapping operators, checked conversions, and division traps.
- **C output (section 11).** The object header, size-class allocator, inline and boxed data layouts with field-less variants encoded in the pointer (section 3.3), copy-on-write arrays, per-type release functions, and status-byte error returns. The debug build poisons freed memory and checks counts at exit.
- **The reference interpreter (section 21.1)**, the test runner with `assert`, `assert_fails` and `rejects` (section 20.2), and diagnostics in the format of section 19.1, plus JSON.
- **The program fuzzer (section 21.2)**, `tests/fuzz/fuzz.ml`. It builds well-typed programs by construction and requires the interpreter and the debug C build to agree, with balanced counts. Its programs include trait values: boxing in arguments, arrays, fields and `Option`, calls through method tables, nested values, closures that capture them, `mut` parameters, failures that cross a trait method, and `any Show` of primitives, tuples and user types. Half of the programs are split across a module (section 3.5): the types, traits and functions that every program has are in `fuzzlib.stn`, all exported, and the main file imports it and writes each of their names with `fuzzlib.` before it, in expressions, patterns, types and bounds. Every program has a type of the main file, `Local`, that implements the trait `Fig` of the prelude, so a split program has an impl of a trait of one module for a type of another, boxed as `any fuzzlib.Fig`. A split program must also do what the same program in one file does, a third oracle that module resolution is checked by, since both backends share it.
- **Negative fuzzing (section 21.2).** A program that agrees gets one mutation with a known violation, and the checker must reject it with the code of the rule that was broken, or with a code of the E02 family for a type mismatch. There are seventeen kinds: a use after `take`, a `take` in a loop, a `mut` marker left out, `mut` of an immutable, an assignment to an immutable, two overlapping `mut` arguments, a closure over a `mut` argument, an arm of a match left out, an unknown name, too few arguments, an argument given twice, an argument, an annotation or a result of another type, an error that an exported function does not list, a field named twice, and a type parameter named twice. Each kind is as likely as any other. A mutation is made of the program's own lines and variables when it has some that fit (half of the time), and otherwise it is written with a variable of its own and put after one of the statements of the program, whatever its depth, so that the rules are tried inside loops and branches.
- **The compiler does not crash (section 21.2, the first oracle).** `--crash` changes the bytes of each program with no regard for what it says (a character taken out, the text cut short, a character replaced, a piece repeated or taken out, two characters swapped), most of them into programs that no rule of the language was written for, and whatever the compiler says of one it must say: an exception that nothing caught, a check or a run that does not end where it should, or C that the C compiler cannot build is a crash. A program that still checks is run by the interpreter, then built (a step of its own, with the C compiler) and the program it makes is run by the fuzzer, with what each prints on the standard output and on the standard error kept apart. A crash is an uncaught exception on the standard error, a status of 2 or more from the check, a build of a program that checked that fails (any nonzero status, the C compiler failing with or without a word, unless it is the compiler's own report that the program uses what it does not support yet: status 1 and a line `error: not supported yet: ...`, with no fatal exception and no failed C compiler), a process killed by a signal of any kind (the check, the interpreter, the build or the program built), or a build that does not end. The mode of a reduction is fixed by its input: a file that is not split is written as one file in every candidate, and what is next to it is never written over. A program that prints the words of a crash is not one, and a program that loops or traps is the program's. A crash is shrunk like the other failures. It found a binary operator with no rule, from a line that starts with `|` and so continues the one before it, and a built-in function used as a value, which made the C backend raise.
- **Shrinking (section 21.2).** A failing program (the interpreter and the C build disagree, a mutation was accepted, or one was rejected with the wrong code) is cut down while it still fails: statements and items are deleted, a loop, an `if` or a `match` is replaced by what is in its body, and declarations and numbers are made simple. A mutation that was accepted is kept by the lines that make the violation, so that the reduced program is still one. In the fuzzer's own tests, programs of 250 lines come down to between 2 and 45.

Not done yet:

- the last oracle of the fuzzer of section 21.2, comparing each optional pass on and off, which waits for the optional passes, and productions of the generator for projections (`lend`)
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

Seven choices here are interpretations where the draft is silent or in tension:

- When two impls of one trait both fit a type, the first one written whose bounds hold is used, by the checker and by both backends. The draft does not rank them, so a more specific impl does not win over an earlier generic one.

- Section 2.1 makes a line that starts with `-` continue the previous line, but section 5.5's patterns include negative literals. A line starting with `-` therefore starts a new line when it is a match arm, meaning it contains `->` outside brackets. Every other such line continues, as section 2.1 says.
- Section 13.3 gives the busy flag of a shared cell only for long accesses. This compiler also counts a `for ... in mut` over a cell as a long access, and clears the flag when the statement ends. A closure that reaches the array during the loop traps instead of reading freed memory. A direct use of the array in the loop body is rejected at compile time with E0323.
- Section 13.3 does not say when the busy flag of a long access starts, relative to the other arguments of the call, or when it ends. Arguments are evaluated left to right. A shared cell passed as `mut` to a function is busy from where that argument is written until the frame it was taken in ends: a statement, but also a condition, an operand of `and` or `or`, the value of a branch, an arm or a block, the body of a comprehension, a `try`, and a function body. An argument written before it can read the cell; one written after it traps. A built-in such as `push` cannot call a closure, so it lends nothing, and its arguments can read the receiver, or change it, first. The interpreter and the C backend agree on all of this.
- Section 3.5 shows an import only used through the module's name (`http.get`, `clock.now()`, `tcp.send`), so that is the only way in: `import net.http` gives the name `http`, and no item of the module is also a name of its own in the importing module. A module path is looked up from the directory of the file given to the compiler, whichever file the import is in, until package roots arrive (section 3.8).
- Section 4.7 finds a method among "functions named `f` in the module that defines `x`'s type", and then the methods of the traits in scope. Here the exported functions of the module that defines the type are found first, and only if none of them takes the receiver (a function of `Box[Int]` does not take a `Box[Str]`, nor does one, generic or not, whose bound the receiver breaks, nor a trait method whose impl's bounds do not hold) are the functions of the module that makes the call and of the prelude, and then the methods of the traits in scope before a type error, so a program can write a function over `Str` or `Array[Int]` and call it as a method, and a function of its own does not make the type's method ambiguous. `T.f(args)` takes the same order, and with several functions for `T` it takes the instantiation and bounds of its first argument into account as a receiver's would be. For an impl, a type that a module of the program declares is defined by that module alone, whatever it is applied to, and a type that the prelude's constructors make (`Array[Point]`, `Point?`, a tuple) is defined by the modules of the types it is made from. A trait is in scope in the module that defines it, in the prelude, and in a module that imports its module, if the trait is exported. Impls are not scoped: an impl applies wherever its trait and its type are known.
- Section 3.5 says the fields and variants of an exported type are visible with it. The other half is taken to hold as well: the fields of a type that is not exported cannot be read or assigned outside its module, though a function can return a value of that type.
