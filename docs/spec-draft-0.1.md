# Starnite language specification, draft 0.1

Nov 15, 2026 · @Shahab

Starnite is a value-semantics language compiled to C, with memory safety from layered static analysis and no tracing collector. This draft specifies every milestone of section 22; the two research-stage layers are given as implementation plans with safe fallbacks.

## 1. Scope and status

Every section carries one of three status levels, so an implementer knows how much to trust it.

| Status | Meaning | Sections |
| --- | --- | --- |
| Specified | Based on techniques with production implementations elsewhere. Build as written. | 2 to 8 (except 3.8.4, the models of 3.8.7, 7.3's suspending handlers, 7.5's evented backend and 20.2's schedule tests), 10 to 12, 18 to 21; policy rules in 17.7 |
| Specified, unproven in combination | Each rule is established alone; the interaction is new. Build as written, fuzz heavily. | 3.8.4, 7.3's suspending handlers, 7.5's evented backend, 9, 13, 14, 17 (law rules in 17.7); 20.2's schedule tests |
| Designed, unproven | A complete design with no production implementation of its kind to copy. Build after the parts it depends on, and measure before relying on it. | 3.8.7 |
| Research plan | No settled rules exist. The section gives an algorithm to try, a fallback that is always safe, and an exit test. | 15, 16 |

Nothing in this draft has been implemented or tested. Expect corrections once code exists.

Decisions already taken:

- The first compiler emits C11 and relies on a C compiler for optimization. A native backend for x86-64 and ARM64 follows and becomes the default there (section 11.7); C remains for other platforms and as a test oracle.
- A `var` captured by a closure becomes shared automatically (section 13).
- Integer overflow traps unless a refinement proves it cannot happen (section 17).
- Generics are monomorphized. There is no run-time type information in version 1.
- There is no `null`, no tracing collector, and no implicit numeric conversion.

Implementation and licences: the bootstrap compiler is written in OCaml. The compiler and tools are licensed GPLv3. The runtime (section 11) and the standard library (section 20) are licensed Apache 2.0, so programs compiled with Starnite, which link them, can use any licence. Each lives in its own directory with its own licence file, and every source file carries an SPDX identifier.

Conventions: "must" marks a rule the compiler enforces. "Trap" means the nearest supervised task, or else the program, stops with a message and source location (section 14.9); it is never undefined behaviour. Source files use the extension `.stn` and are UTF-8. In examples, `...` stands for code left out, and a function signature with no body is an excerpt; neither is valid source.

Syntax changes from the design sketch: `Ref[T]` is dereferenced through its pool (section 12); typestate transitions are written `Socket[Closed -> Connected]` (section 6); errors propagate implicitly as a checked effect, with no `?` operator (section 5.4); exported names carry a trailing `*` instead of a `pub` keyword (section 3.5); options are written `Some(x)` and `None`.

## 2. Lexical structure and grammar

Status: Specified. The grammar is indentation-based, LL(2), and written for a hand-coded recursive-descent parser.

### 2.1 Tokens

- **Indentation.** The lexer emits `INDENT` and `DEDENT` tokens as Python does. Indentation is spaces only; a tab in leading whitespace is an error. Inside `()`, `[]` or `{}` newlines and indentation are ignored. A line whose first token is a binary operator (`+ - * / % +% -% *% == != < <= > >= and or &`) or `|` continues the previous line: the lexer emits no `NEWLINE`, `INDENT` or `DEDENT` before it. This lets long expressions and data types with many variants span lines. So a statement cannot begin with unary `-`; write `(-x)` instead.
- **Comments.** `#` to end of line. ## starts a doc comment, read by documentation tools and doc tests (section 20.2).
- **Identifiers.** `[A-Za-z_][A-Za-z0-9_]*`. Types and variants start with an upper-case letter; everything else with lower-case or `_`. The parser relies on this.
- **Integers.** `42`, `1_000`, `0xFF`, `0b1010`. Type `Int` unless context demands another integer type.
- **Floats.** `1.0`, `2.5e-3`. Type `Float` unless context demands `F32`.
- **Durations and sizes.** `5ms`, `60s`, `2min`, `64mib`: an integer followed directly by a unit, of type `Duration` or `Bytes`. Duration units are `ns us ms s min h`; size units are `b kib mib gib`, powers of 1,024. A unit never follows a `0x` or `0b` literal, and `0b` alone is zero bytes.
- **Strings.** `"..."` with escapes `\n \t \\ \" \u{...}`. `f"...{expr}..."` interpolates. `'a'` is a `Char`.
- **Keywords.** `and as break check continue effect elif else ensures extern false fn for frozen handle if impl import in iso lend let level local match mut not or par resource resume return shared spawn struct take trait true try type unique var where while with`.
- **Contextual keywords.** These are keywords only in the position given and ordinary names elsewhere: `inplace`, `noalloc`, `strict`, `total` and `trusted` before `fn`; `any` at the start of a type; `repr` before `(` at the start of a type definition; `open` before `type` at the start of a type definition, after any `resource`; `assert`, `assert_fails`, `assert_snapshot`, `rejects`, `schedules`, `serial`, `threads`, `budget`, `measure`, `untimed` and `by` in test, fuzz and bench blocks (section 20.2), with `by` also after `handle expr`; `rule`, `reaches`, `imports`, `exported` and `trusted`, plus `no`, `errors` and `of`, in `rules.stn` (section 17.7). After `.`, any word is accepted as a field or method name, so `opt.or(0)` and `k.resume(())` are valid.

### 2.2 Grammar

```
file       = { import } { item } ;
import     = "import" path [ "as" IDENT ] NEWLINE ;
item       = fn_def | type_def | trait_def | impl_def | const_def | effect_def | level_def
           | extern_block | test_def | fuzz_def | bench_def ;   (* 7.3, 14.7, 18.1, 20.2 *)

fn_def     = { fn_mod } fn_sig ":" block ;
fn_sig     = "fn" IDENT [ "*" ] [ generics ] "(" [ params ] ")" [ "->" ret_type ]
             [ "!" effect { "," effect } ] [ "where" expr ] [ "ensures" expr ] ;
ret_type   = type | "lend" [ "mut" ] type ;                       (* 4.6 *)
fn_mod     = "inplace" | "total" | "noalloc" | "strict" | "trusted" [ "(" IDENT ")" ] ;
generics   = "[" gparam { "," gparam } "]" ;
gparam     = IDENT [ ":" path { "+" path } ] ;
params     = param { "," param } ;
param      = [ "mut" | "take" ] IDENT [ ":" [ "local" ] type ] [ "=" expr ] ;

type_def   = [ "repr" "(" IDENT ")" NEWLINE ] [ "resource" ] [ "open" ] "type" IDENT [ "*" ] [ generics ]
             [ "=" type_body ] [ "where" expr ] NEWLINE ;            (* open: 5.5 *)
type_body  = "struct" "(" fields ")"
           | "struct" ":" NEWLINE INDENT { IDENT ":" type [ "=" expr ] NEWLINE } DEDENT
           | variant { "|" variant } | type ;
variant    = IDENT [ "(" fields ")" ] | IDENT "(" "from" type ")" ;
fields     = field { "," field } ;
field      = [ IDENT ":" ] type [ "=" expr ] ;
trait_def  = "trait" IDENT [ "*" ] [ generics ] ":" NEWLINE INDENT { fn_sig NEWLINE } DEDENT ;
impl_def   = "impl" [ generics ] path [ targs ] "for" type
             ( ":" NEWLINE INDENT { fn_def } DEDENT | NEWLINE ) ;  (* no body: marker traits *)
const_def  = "let" IDENT [ "*" ] [ ":" type ] "=" expr NEWLINE ;

type       = [ "iso" | "frozen" | "unique" ] base [ "?" ] ;
base       = path [ targs ]
           | "any" path [ targs ]                                  (* 3.4 *)
           | "fn" "(" [ ptype { "," ptype } ] ")" [ "->" type ] [ "!" effect { "," effect } ]
           | "(" [ type { "," type } ] ")" ;
targs      = "[" targ { "," targ } "]" ;
targ       = type | IDENT "->" IDENT ;
ptype      = [ "mut" | "take" ] [ "local" ] type ;               (* fn(mut Stats) *)
path       = IDENT { "." IDENT } ;

block      = NEWLINE INDENT stmt { stmt } DEDENT | simple NEWLINE ;
stmt       = simple NEWLINE | if_stmt | if_let | let_else | try_stmt | match_stmt | for_stmt
           | while_stmt | par_stmt | with_stmt | handle ;         (* 6.5, 7.3 *)
simple     = "let" pattern [ ":" type ] "=" expr
           | [ "shared" ] "var" IDENT [ ":" type ] "=" expr
           | place assign_op expr
           | "return" [ expr ] | "break" | "continue" | "check" expr
           | "lend" [ "mut" ] place                                (* 4.6 *)
           | "resume" [ expr ]                                     (* 7.3 *)
           | assert_stmt                                           (* 20.2 *)
           | expr ;
assert_stmt = "assert" expr | "assert_fails" targs expr | "assert_snapshot" expr ;
assign_op  = "=" | "+=" | "-=" | "*=" | "/=" | "%=" ;
if_stmt    = "if" expr ":" block { "elif" expr ":" block } [ "else" ":" block ] ;
if_let     = "if" "let" pattern "=" expr ":" block [ "else" ":" block ] ;
let_else   = "let" pattern "=" expr "else" ( simple NEWLINE | ":" block ) ;
try_stmt   = "try" ":" block "catch" pattern ":" block { "catch" pattern ":" block } ;
match_stmt = "match" expr ":" NEWLINE INDENT { pattern [ "if" expr ] "->" block } DEDENT ;
for_stmt   = [ "par" ] "for" pattern "in" [ "mut" | "take" ] ( range | expr ) ":" block ;
while_stmt = "while" expr ":" block ;
par_stmt   = "par" ":" NEWLINE INDENT stmt stmt { stmt } DEDENT ;

pattern    = "_" | IDENT | literal | path [ "(" pattern { "," pattern } ")" ]
           | "(" pattern { "," pattern } ")"
           | "[" [ pattern { "," pattern } ] [ "," ".." | ".." ] "]" ;

expr       = lambda | or_expr [ "?:" expr ] ;
lambda     = "fn" "(" [ params ] ")" ":" ( expr | place assign_op expr ) ;
or_expr    = and_expr { "or" and_expr } ;
and_expr   = not_expr { "and" not_expr } ;
not_expr   = [ "not" ] cmp_expr ;
cmp_expr   = set_expr [ ( "==" | "!=" | "<" | "<=" | ">" | ">=" ) set_expr ] ;
set_expr   = add_expr { ( "|" | "&" ) add_expr } ;                (* Set union, intersection *)
add_expr   = mul_expr { ( "+" | "-" | "+%" | "-%" ) mul_expr } ;
mul_expr   = unary { ( "*" | "/" | "%" | "*%" ) unary } ;
unary      = [ "-" | "iso" | "spawn" | "try" | "untimed" ] postfix ;   (* untimed: only inside measure, 20.2 *)
postfix    = primary { "." IDENT | "(" [ args ] ")" | "[" barg { "," barg } "]" } ;
barg       = range | expr | type ;                                 (* see note on brackets *)
range      = add_expr ".." add_expr ;
args       = arg { "," arg } ;
arg        = [ IDENT "=" ] [ "mut" | "take" ] expr ;
primary    = literal | path | "(" [ expr { "," expr } ] ")" | "[" [ expr { "," expr } ] "]"
           | "if" expr ":" expr "else" ":" expr
           | "handle" expr "by" expr                            (* 20.2 *)
           | "[" expr comp "]"
           | "{" [ expr { "," expr } ] "}" | "{" expr comp "}"
           | "{" entry { "," entry } "}" | "{" entry comp "}" ;
entry      = expr ":" expr ;
comp       = "for" pattern "in" expr [ "if" expr ] { "for" pattern "in" expr [ "if" expr ] } ;
place      = postfix ;                                             (* see note on places *)
```

Notes:

- A `par` block has two or more statements; each runs as its own task.
- `+%`, `-%`, `*%` are the wrapping arithmetic operators. Plain `+`, `-`, `*` trap on overflow.
- Comparison does not chain: `a < b < c` is a syntax error.
- Postfix `?` is not an operator; failures propagate implicitly (section 5.4). Postfix `?` on a type means option.
- Parameters and fields may have default values; arguments may be passed by name, as in Python: Request(Get, u, body = data). Named arguments follow positional ones. A multi-statement lambda is written as a local `fn` definition; lambdas hold one expression.
- **Brackets.** After an expression, `[...]` is parsed as a bracket node holding expressions, ranges or types. Name resolution (pass 2) decides what it is: type arguments if the expression before it names a generic function or type (`parse[Int](text)`, `channel[iso Batch](4)`, `Ptr[U8].null()`), indexing otherwise. A bracket that contains a type but follows a non-generic name is E0102.
- **Places.** A place is a variable, or a postfix expression rooted in one that ends in a field, an index, or a call to a `lend mut` function (section 4.6), rooted in a variable. Anything else on the left of an assignment is E0103.
- **Parameter types.** A parameter's type may be omitted only in a lambda or a handler arm, where it is inferred from the expected function type (`fn(a, b): max(a, b)`, `yield(v, k) ->`). Everywhere else it is required (E0104).
- **Bodies.** A function without a body appears only inside `trait_def` and `extern_block`. Every foreign function is declared in an `extern_block` (section 18.1).
- **Tail statements.** A block's value is its last statement. An `if`, `match`, `with` or `handle` statement in last position is an expression whose value is that of the branch taken, so `match try f(): ...` can end a function.
- **Shorter forms.** Five forms are other ways to write a `match`, and mean exactly what the match does.
  - `if let PATTERN = e: A else: B` is `match e:` with the arms `PATTERN -> A` and `_ -> B`.
  - `let PATTERN = e else S`, followed by the rest of its block R, is `match e:` with the arms `PATTERN -> R` and `_ -> S`. S must leave: it ends in `return`, `break`, `continue` or a call that never returns, such as `fail` (E0207), since R needs what the pattern binds.
  - In those two forms a pattern that is a plain name or a tuple would match anything, so it stands for `Some` of itself: `if let v = m.get(k):` is `if let Some(v) = m.get(k):`, and `let (a, b) = split_once(s, sep) else return` takes the pair out of the option.
  - `a ?: b` is `match a:` with the arms `Some(v) -> v` and `None -> b`. `a` is an option, `b` runs only when it is `None`, and `b` may be a call of `fail`. It binds more loosely than `or`, and to the right.
  - `try: B`, then `catch P1: C1`, and so on, is `match try B:` with the arms `Ok(v) -> v`, then `Err(P1) -> C1` and so on. When no catch is a name or `_` and the catches do not name every error, a last arm `Err(e) -> fail(e)` passes on what was not caught, so the function still lists those errors; when they name every error, nothing is passed on. The value of B is the value of the statement where one is wanted.
  - A variant written `V(from T)` holds one value of type T, and stands also for `impl From[T]` for its type, with `from(x)` giving `V(x)`. An error of type T raised inside a function that lists the variant's type then becomes `V(...)` on the way out (section 5.4). It is not available in a type with type parameters.
- **Array patterns.** `[p1, p2]` matches an array of exactly two elements, and `[p1, p2, ..]` one of two or more; `[]` matches the empty array and `[..]` any. Elements are read where they are. An array has no end of lengths, so a match on one needs a `_` or `[..]` arm, as a match on an integer does, and a `let` with an array pattern needs an `else` (E0202). The check does not yet see that `[]`, `[x]` and `[x, y, ..]` together cover every array.
- **Struct blocks.** `struct:` followed by an indented line for each field is the same type as `struct(...)` with the fields in one line.
- **Contextual words.** The full list of contextual keywords, which are keywords only in certain positions, is in section 2.1.
- **`any`.** `any` is a keyword only at the start of a type (`Array[any Figure]`, `x: any Figure`). Everywhere else it is an ordinary name, so the iterator function `any(xs, pred)` in section 20.1 keeps its name.

## 3. Types and data layout

Status: Specified. Every type has a size and alignment known at compile time after monomorphization, and values are stored inline unless the table below says boxed.

### 3.1 Built-in types

| Type | Representation in C | Notes |
| --- | --- | --- |
| `Int` | `int64_t` | Default integer |
| `I8 I16 I32 I64 U8 U16 U32 U64` | Matching `stdint.h` type | No implicit conversion between them |
| `Float`, `F32` | `double`, `float` | IEEE 754 |
| `Bool` | `uint8_t`, 0 or 1 |  |
| `Char` | `uint32_t` | A Unicode scalar value |
| `Unit` | No storage | The type of `()` |
| `(A, B)` | Anonymous struct | Inline |
| `T?` | Null pointer when `T` is boxed; else a tag byte plus `T` | `Some(x) / N``one` |
| `Array[T]` | One pointer to a boxed buffer: header, `len`, `cap`, elements inline | Copy-on-write (section 4) |
| `Str` | 16 bytes: up to 15 bytes inline, otherwise a pointer to a counted UTF-8 buffer and a length (section 3.6); always valid UTF-8 |  |
| `Map[K, V]`, `Set[K]` | One pointer to a boxed compact, insertion-ordered hash table (section 3.6) | `K` needs `Hash + Eq` |
| `fn(A) -> B` | One pointer to a closure object (section 13) |  |
| `Pool[T]`, `Ref[T]` | Section 12 |  |

Integer `/` truncates toward zero and `%` takes the sign of the dividend, as in C. Both trap on a zero divisor, and `/` traps on the minimum value divided by -1.

### 3.2 Structs

```
type Vec3 = struct(x: Float, y: Float, z: Float)
```

A struct is laid out as the equivalent C struct, with fields in declaration order and no header. A struct is never boxed by itself. A field of boxed type is stored as a pointer inside it.

### 3.3 Data types

```
type Shape = Circle(r: Float) | Rect(w: Float, h: Float) | Empty
type List[T] = Nil | Cons(head: T, tail: List[T])
```

The compiler picks one of three layouts:

1. **Enumeration.** No variant has fields: an integer of the smallest sufficient width.
2. **Inline union.** Not recursive and at most 16 bytes of payload: a tag byte followed by a C union. `Shape` uses this.
3. **Boxed.** Recursive, or larger than 16 bytes: one pointer to a heap object with a header. `List` uses this. A variant without fields is encoded in the pointer itself as `(tag << 1) | 1` and never allocates.

### 3.4 Generics and traits

```
trait Show:
    fn show(self: Self) -> Str

impl Show for Vec3:
    fn show(self: Vec3) -> Str:
        f"({self.x}, {self.y}, {self.z})"

fn largest[T: Ord](xs: Array[T]) -> T? : ...
```

- Each use of a generic function or type with distinct type arguments produces a separate copy. Dynamic dispatch is explicit, through trait values (below).
- Operators are trait methods: `+` is `Add.add`, `==` is `Eq.eq`, indexing is `Index.at`.
- The compiler derives these traits automatically when all fields allow it: `Copy` (section 6), `Eq`, `Hash`, `Send` (section 14).
- An impl must be in the module that defines the trait or the module that defines the type.

**Trait values.** `any Figure` is a value of some type that implements the trait `Figure`, chosen at run time. This resolves open issue 4.

```
trait Figure:
    fn area(f: Self) -> Float
    fn name(f: Self) -> Str

let figures: Array[any Figure] = [Square(2.0), Tri(4.0, 4.0)]   # two types that implement Figure
let total = sum([f.area() for f in figures])
```

- Grammar: `type ::= ... | "any" path`.
- Representation: two words, a pointer to a counted box holding the value and a pointer to a static method table for that type and trait. A value is boxed implicitly where `any T` is expected.
- A trait can be used with `any` only if every method takes `Self` as its first parameter, has no type parameters of its own, and does not return `Self` (E0230 otherwise).
- A method's declared effects are part of the trait, so a call through `any` has the trait method's effects. An impl may perform fewer, never more.
- `any T` has Shared kind (section 6.1); uniqueness, reuse and `frozen` apply to the box as to any value. `any` of a resource type is not allowed in version 1.
- There is no downcasting and no `match` on the hidden type: use a data type for a closed set of cases, `any` for an open one.
- When the concrete type is known at a call, the compiler calls the method directly.

### 3.5 Modules

One file is one module. `import geometry.vec` loads `geometry/vec.stn`. An item is private unless its name is followed by `*` where it is defined: `fn get*(url: Str)`, `type Response* = ...`. Fields and variants of an exported type are visible with it. Import cycles are an error.

### 3.6 Collections and comprehensions

Lists, dictionaries and sets are variable-length built-ins with value semantics and literal syntax.

| Collection | Type | Literal | Empty |
| --- | --- | --- | --- |
| List | `Array[T]` | `[1, 2, 3]` | `[]` |
| Dictionary | `Map[K, V]` | `{"a": 1, "b": 2}` | `Map()` |
| Set | `Set[K]` | `{1, 2, 3}` | `Set()` |

`{}` alone is accepted only where the expected type says which of the two it is.

`[x; n]` is an array of `n` copies of `x`, built in one allocation: `[0; 500]`, `[false; len(xs)]`. Evaluation is left to right, as everywhere (section 4.4): `x` once, then the count, which is any `Int` expression; a negative count traps. The result is an ordinary `Array[T]`, which can grow like any other. `filled(n, x)` builds the same array as a function, taking the count first.

A fixed-size array type, `Array[T, N]`, is planned for milestone 5. `N` is an `Int` known at compile time and part of the type. Such an array cannot grow: `push`, `pop`, `insert` and `remove` do not exist for it. It is stored inline, in the frame or in the struct that holds it, with no box of its own; an index that is a constant in range needs no check; and `[x; N]` builds one where the expected type is `Array[T, N]`. Until then `[x; n]` always builds a growable array.

Growth and core operations:

- `Array`: `push`, `pop`, `insert`, `remove`, `len`, indexing, slicing `xs[a..b]`. Capacity doubles when full, so `push` is constant time on average.
- `Map`: `m[k]` traps on a missing key; `m.get(k)` returns `V?`; `m[k] = v` inserts or replaces; `m[k] += 1` starts from `Default.default()` if the key is missing.
- `Set`: `add`, `remove`, `contains`, and the operators `|`, `&`, `-`.
- `Map` and `Set` iterate in insertion order, so program output is deterministic.
- Indexing an `Array` out of range traps, unless a refinement proves the index valid (section 17).

Layouts (this resolves open issue 9; each layout sits behind its type's API and may change if the benchmark gates of section 21.5 show a better one):

- `Str` is 16 bytes. A string of up to 15 bytes is stored inline, with no allocation. A longer one is a pointer to a counted UTF-8 buffer plus its length; the form follows from the length alone. A slice `s[a..b]` is a new string, and behaves as one in every way. One of up to 15 bytes is inline. A longer one is a view of the bytes it was cut from, with nothing copied, when what it was cut from cannot change while the slice is in scope (an immutable binding, a borrowed parameter, a literal); it gets a buffer of its own when it is stored or returned. A variable assigned only slices of itself, `rest = rest[k..]`, moves along its bytes in constant time. Any other slice copies its bytes. Strings are immutable; `+` and f-strings build new ones, reusing a uniquely owned buffer in place when possible (section 9).
- `Map` and `Set` are compact insertion-ordered hash tables: a dense array of entries in insertion order, and an index of one control byte per slot plus the place of each slot's entry in the dense array, in 1, 2, 4 or 8 bytes as the capacity needs. A control byte is free, removed, or seven bits of the hash of its entry; a lookup compares a group of sixteen control bytes at a time and reads an entry only where one matches, so a missing key is usually settled within the control bytes. The index holds up to seven eighths of its slots. An entry is its hash word, its key and its value; with a 64-bit integer key it is only its key and value, and the hash is worked out again when the index is rebuilt. Removal leaves a tombstone. Tombstones are closed up when the table next needs room, or at once when they are three quarters of the entries, so that a table that shrinks gives its memory back. Keeping order costs one extra read per lookup that finds its key, and uses less memory than a plain open-addressing table at the same load factor.
- An entry of a `Map` is a place inside a longer place: `m[k].x = v`, `m[k][i] = v`, `m[k].push(x)`, `f(mut m[k])` and `for x in mut m[k]` change the entry where it is, and trap if the key is missing, as `m[k]` does. The entry is lent out of the Map for the statement, as an `IndexMut` place is (section 4.6), so the statement cannot also read the Map (E0323). `m[k] = v` alone puts the entry, and `m[k] += v` starts from `Default.default()`.
- `{k: v for ...}` and `{x for ...}` put each element as it is made, in order: a later pair with an equal key replaces the value and keeps the place.
- Hashing is SipHash-1-3 with a per-process random key, so chosen keys cannot force collisions. Iteration order does not depend on the key, so output stays deterministic. A key made of several parts (a tuple, a struct, a data type, an array) is one SipHash over the words of its parts in order, a data type's tag first and an array's length first; a part that is a string or has a `Hash` of its own adds its hash as one word.
- `SortedMap` and `SortedSet` (B-trees) are in the standard library for order by key.

Comprehensions:

```
let squares = [x * x for x in xs]
let evens   = [x for x in xs if x % 2 == 0]
let lengths = {word: len(word) for word in words}
let initials = {word[0] for word in words}
let pairs   = [(a, b) for a in xs for b in ys if a < b]
```

A comprehension is rewritten to a loop that pushes into a fresh collection. Three guarantees follow from that:

1. The result is `unique`, since it is freshly built.
2. With a single `for` over a source of known length and no `if`, the result is allocated once at its final size.
3. If the source is consumed by the comprehension, is unique, and elements keep their size, the source's buffer is reused and nothing is allocated. `xs = [f(x) for x in xs]` therefore updates in place.

A comprehension body may fail (section 5.4) and perform effects; these behave as in the equivalent loop.

### 3.7 Platform ports

Status: Specified. Platform-specific code lives in port directories chosen by the package manifest. There is no conditional compilation inside files, and the compiler checks that every port implements everything any port provides.

The manifest is `starnite.toml` at the package root.

```
[package]
name = "audio"

[features]
wayland = false

[port.win32]
when = { os = "windows" }
dirs = ["ports/win32"]

[port.x11]
when = { os = "linux", feature = "!wayland" }
dirs = ["ports/x11", "ports/posix"]

[port.wayland]
when = { os = "linux", feature = "wayland" }
dirs = ["ports/wayland", "ports/posix"]
```

Portable code imports a module without naming any platform:

```
import platform.clock          # resolves to ports/win32/platform/clock.stn on Windows
let t = clock.now()
```

Resolution: `import a.b` loads `a/b.stn` if that portable file exists. Otherwise it loads `a/b.stn` from the directories of the active port.

Rules:

1. Exactly one port is active for a target. If no port's `when` matches, or more than one does, the build fails and names the ports involved.
2. `when` may test `os`, `arch` and features; `"!name"` means the feature is off.
3. A module path provided both by a portable file and by the active port is an error.
4. A module path provided by two directories of the active port is an error.
5. **Seams must be complete.** Every module path that any port provides must be provided by every port, with the same exported names and signatures, effects and error types included.
6. Every build parses and type-checks all ports, not only the active one. A Windows type error is reported on a Linux machine, because no port file needs its target to exist in order to be checked.
7. Names exported from port modules are visible inside the package but never to packages that depend on it. Dependents see only portable modules.
8. Features are additive. A dependent can turn a feature on but never off.

`starnite ports` prints a table of every seam against every port, with a mark for each one implemented.

This pairs naturally with a program rule (section 17.7) that keeps foreign code inside the ports, for example `trusted in ports.*`.

### 3.8 Packages and the registry

Status: Specified. Capability checks on upgrade (section 3.8.4) are Specified, unproven in combination. The `starnite` command is also the package manager, and the default registry is starnite.dev. Packages cannot run code when fetched or built: there are no build scripts and no install hooks. Foreign libraries are found only through the named `extern` blocks of section 18.1.

#### 3.8.1 Manifest

```
[package]
name = "http"
version = "0.4.2"
license = "MIT OR Apache-2.0"
description = "HTTP/1.1 client"
repository = "https://github.com/starnite-lang/http"

[dependencies]
json = "2.1"
net = { version = "1.3", effects = ["io.net"] }
image = { version = "0.8", trusted = "deny" }
util = { path = "../util" }
fork = { git = "https://github.com/someone/fork", rev = "a1b2c3d" }

[dev-dependencies]
testdata = "0.2"
```

- A package name is lowercase letters, digits and `_`, and is also its top-level module name: `import json.value`.
- Versions follow semantic versioning. Dev-dependencies are visible only to tests and benchmarks.
- `effects` is an allow-list: the build fails (E1111) if any function of that dependency the package calls can perform an effect outside it. Leaving it out allows all effects.
- `trusted = "deny"` is described in section 18.5. Registry packages may depend only on registry packages, never on `path` or `git` sources.
- `[grants]` sets the most I/O authority an application may use: the paths, hosts, environment variables and programs it may reach. It is allowed in application manifests only (E1120), and section 7.5 defines its keys.

A `[policy]` table sets the bar a package's dependencies must meet, using the test metadata the registry records (section 3.8.5):

```
[policy]
dependencies.min-coverage = 70          # line coverage, percent
dependencies.min-mutation = 50          # mutation score, percent
dependencies.effect-coverage = true
```

`starnite add` and `starnite update` refuse a package below the bar (E1113), naming the metric and its value. `path` and `git` dependencies are measured locally. A single dependency can be exempted with `policy = "exempt"` in its entry, which `starnite.lock` records like an accepted widening.

#### 3.8.2 Version resolution

| Constraint | Means |
| --- | --- |
| `"2.1"` | at least 2.1.0, below 3.0.0 |
| `"0.4"` | at least 0.4.0, below 0.5.0 (before 1.0 the minor number is breaking) |
| `"=2.1.4"` | exactly 2.1.4 |
| `">=2.1, <2.5"` | the stated range |

1. Resolution is minimal version selection, as in Go: each package gets the lowest version that meets every constraint on it. The result is the same on every machine without a lock file, needs no SAT solver, and changes only when a manifest changes or `starnite update` runs.
2. One version per major version. Two major versions of a package may coexist; they are separate modules and their types are distinct. Passing a value of one to the other is error E1101, which names both dependency paths.
3. No version meeting every constraint is error E1102, which shows the conflicting constraints and who imposed each.
4. Features are additive: a feature enabled by any dependent is enabled for all.

#### 3.8.3 Lock file

`starnite.lock` records, for every package in the build, its exact version, its source, the SHA-256 of its archive, and its capability summary (section 3.8.4). It is written by `starnite add`, `remove` and `update`, and is meant to be committed. It is separate from `rules.lock` (section 17.7), which records approved rules.

- `--locked` fails the build if the lock would change, for packages as well as rules.
- `--offline` uses only the local cache. `starnite vendor` copies every dependency's source into `vendor/`, and a build then reads only that.
- An archive whose checksum does not match the lock is a hard error, never a warning.

#### 3.8.4 Capability checks on upgrade

Every published version carries a capability summary, computed by the compiler from its interface files (section 8.3): the effect set of each exported function, the names of its trusted functions, and the foreign libraries it links. The compiler knows every function's effects: exported functions list them and private ones have them inferred. The finer io tags (io.net, io.fs, io.env, io.proc, io.clock, io.rand, io.console) are inferred for private functions, may be declared by exported ones (section 7.5), and are always stored in the interface file. So the summary is exact, not a guess from scanning source.

`starnite update` compares the old and new summaries of each package it would move, and refuses the move (E1110) when a function the build reaches gains an effect, or the package gains trusted functions or a linked library:

```
$ starnite update json
error[E1110]: json 2.3.0 can do more than json 2.2.1
  json.parse gains effect io.net
    used by: config.load -> json.parse
  json gains trusted function json.fast.scan (links libsimdjson)
help: if this is intended, run `starnite update json --accept` and commit starnite.lock
```

- `--accept` records the approval and the approver in `starnite.lock`, so the widening shows in review, as `rules.lock` does for rules.
- A package losing effects or trusted code is reported as a note and never blocks.
- The same check runs when `starnite add` pulls in a new indirect dependency, and on every `--locked` build.
- Program rules (section 17.7) still apply after an accepted widening: a rule that forbids `io.net` under `config` fails the build either way.

The capability summary also holds a flow summary: for each exported function, which sources reach which sinks. Sources are effect inputs such as `io.env`, file reads (with their path when it is a constant or a known prefix such as `~/.ssh`) and incoming network data. Sinks are effect outputs such as `io.net` sends, file writes and process starts. It is computed by an information-flow pass over Core after effect inference, and is exact up to the usual over-approximation at trusted code and dynamic dispatch, which are marked as such. A new flow (for example `io.env` reaching `io.net`) is treated like a new effect: `starnite update` refuses it (E1110) until accepted.

The registry also runs a behaviour diff. It runs the package's own tests in a sandbox with recording handlers for `io` (section 20.2), which log every host contacted, file path touched and process started, and compares the log with the previous version's. A new destination is reported even when the effect was already allowed. A package with no tests gets no behaviour diff, and that is shown on its registry page.

#### 3.8.5 Registry

- `starnite publish` builds the package, runs `starnite test`, checks that it still builds with the lowest versions its manifest allows, and uploads source only, never binaries. The registry rebuilds the capability summary itself and rejects an upload whose summary does not match.
- The registry checks semantic versioning: an upload that removes an exported item, changes a signature, adds an effect to an exported function, adds a typestate requirement or adds a variant to an exported data type not marked open (section 5.5), without a major version bump, is refused (E1112). Because effects and states are in signatures, this check is exact.
- A published version can never be changed or deleted. `starnite yank` hides it from new resolutions; existing lock files still build.
- Uploads are signed with the publisher's identity (Sigstore-style, no long-lived keys) and logged in a public transparency log. `starnite verify` checks every locked package against it.
- Names are first come, first served, owned by an account or an organization. A new name within one edit of a popular package's name needs manual review.
- The registry publishes security advisories. `starnite audit` lists locked versions with advisories, and builds warn (W1120). Other registries can be added under `[registries]` in the manifest or the user configuration.

Publishing runs the package's tests on the registry's own builders, not the publisher's, and records line, branch and effect coverage and mutation score in the version's metadata. Requirements scale with what the package can do; failing one refuses the upload (E1114):

| Package has | Required to publish |
| --- | --- |
| No effects | Nothing; coverage is shown |
| Any effect | Tests, and effect coverage: every effect sink is reached by at least one test |
| Trusted functions or linked libraries | Also 100% line coverage of trusted functions and a mutation score of at least 60% on them |
| A release that widens capabilities | Also a test reaching each new effect or flow |

Effect coverage is what makes the behaviour diff (section 3.8.4) complete: an untested network call is one the sandbox never sees. There is deliberately no registry-wide line-coverage minimum, since it rewards padding tests and penalises small packages; consumers set their own bar with `[policy]`.

#### 3.8.6 Commands

| Command | Effect |
| --- | --- |
| `starnite new <name>` | Creates a package directory with `starnite.toml`, `main.stn` and a test |
| `starnite init` | Does the same in the current directory |
| `starnite add json[@2.1]` | Adds a dependency to the manifest and the lock |
| `starnite remove json` | Removes it from both |
| `starnite update [<pkg>]` | Moves to the newest allowed versions, with the checks of section 3.8.4 |
| `starnite tree [--why <pkg>]` | Prints the dependency graph, or why a package is present |
| `starnite vendor` | Copies dependency sources into `vendor/` |
| `starnite publish`, `starnite yank <version>` | Publishes or yanks a version |
| `starnite audit`, `starnite verify` | Checks advisories, and signatures and checksums |

| Code | Meaning |
| --- | --- |
| E1101 | Values of two major versions of one package mixed |
| E1102 | No version meets every constraint |
| E1110 | An upgrade widens a package's capabilities |
| E1111 | A dependency performs an effect outside its `effects` allow-list |
| E1112 | Breaking change published without a major version bump |
| W1120 | A locked version has a security advisory |
| E1113 | A dependency is below the package's \[policy\] bar |
| E1114 | An upload does not meet the registry's test requirements |

#### 3.8.7 Automated review

Status: the deterministic layer is Specified and required; the models are Designed, unproven, and optional. Review does not depend on one person and does not need a language model at launch. A model can only make a package's status stricter: it can queue or quarantine an upload, never clear one that a deterministic check flagged.

Pipeline, in order:

1. Deterministic checks, on every upload: capability and flow diff (section 3.8.4), behaviour diff, archive against tagged commit, semver, file-type and obfuscation rules, and a fixed policy table. Plain anomaly scores against the package's own history (diff size, new dependencies, string entropy, account age, owner changes) feed the same table. This layer ships first and stands alone.
2. Tree model, added once labelled quarantines exist: gradient-boosted trees over the summary's features, returning a score and the features that drove it. It is not a language model.
3. Behaviour-sequence model, added after that: a transformer of 2 to 6 layers and about 1 to 10 million parameters, trained from scratch. Its input is not source code but sequences the compiler emits from the flow summary and call paths, such as `read io.env -> concat -> send io.net`, over a vocabulary of a few hundred tokens. Comments and string contents never reach it, only their entropy and where they flow, so text written to persuade it has nothing to act on. It runs on a CPU in milliseconds.
4. A pretrained code encoder (CodeT5-small's encoder or similar) is added only if steps 1 to 3 measurably miss cases on the red-team set.

| Deterministic checks | Classifiers | Result |
| --- | --- | --- |
| Clean | Low | Published |
| Clean | High | Published, queued for review |
| Capabilities widened | Low | Published, flagged in `starnite update` |
| Capabilities widened | High | Quarantined until two reviewers clear it |
| Any | Very high | Quarantined, owners notified |

Training data. No Starnite malware exists at launch, which is why the deterministic layer comes first. Public npm and PyPI malware sets (Datadog's dataset, MalwareBench) are mapped into Starnite's behaviour vocabulary: reading credential files and the environment, then sending over the network, becomes `io.fs` plus `io.env` reaching `io.net`. That mapped set trains the tree model and the behaviour-sequence model alike. Every confirmed quarantine becomes a labelled Starnite example, and red-team packages are written each release to measure recall.

Operations:

- Precision and recall on a held-out set are published with each model version.
- Every quarantine has an appeal and a response deadline. Reviewers are a vetted group; clearing a quarantine takes two of them.
- Verdict reasons for borderline scores are shown to reviewers only, so publishers cannot tune uploads against them.
- Every publish is in the transparency log, so outside scanners can score it too and report through the registry API.

## 4. Values, bindings and parameter conventions

Status: Specified. Every variable holds an independent value; no assignment or call can make a change in one variable visible through another.

The only exceptions are explicit and covered elsewhere: shared cells (section 13) and pools (section 12).

### 4.1 Bindings

- `let x = e` binds an immutable value. `var x = e` binds a mutable one.
- A variable must be initialized where it is declared.
- Shadowing is allowed in an inner block, not in the same block.
- `b = a` gives `b` its own value. Physically the two may share storage until one is written (section 4.5).

### 4.2 Parameter conventions

| Declared as | Callee may | Caller afterwards | Call site | In generated C |
| --- | --- | --- | --- | --- |
| `x: T` | Read | Still owns the value, unchanged | `f(a)` | By value if `T` is at most 16 bytes and has no boxed fields; else `const T*` or the box pointer, with no count update |
| `mut x: T` | Read and write | Sees the changes | `f(mut a)` | `T*` to the caller's storage |
| `take x: T` | Read, write, store, return, destroy | Has lost the value | `f(a)` or `f(take a)` | By value; the callee owns one reference |

Rules:

- `mut` must be written at the call site. The argument must be a mutable place: a `var`, a mut parameter, a lend mut place (section 4.6), or a field or element of one of these.
- The receiver of a method call is the one exception: `v.push(x)` passes `v` as `mut` with no marker, because the method's first parameter says so (section 4.7). The receiver must still be a mutable place.
- For a `take` parameter, a variable argument is moved if this is its last use. If it is used later, the compiler passes a copy and reports it under `--explain-copies`. For a resource type that is an error.
- Writing `take a` at the call site asserts the move: any later use of `a` is an error.
- A function cannot return a reference; a lend function returns a place that lasts only for the caller's statement (section 4.6). Results are values.

### 4.3 Exclusivity

While a `mut` argument is live, nothing else may read or write the same storage. The compiler enforces this at each call:

1. Arguments are evaluated left to right before the call begins. An argument that is a finished value at that point takes no part in the check: a literal, an arithmetic result, the result of a call to a function that is not `lend` and returns no borrow (`len(v)`, `m.get(k).or(0)`), or a place passed to a `take` parameter. A `take` argument that overlaps a `mut` argument of the same call is always copied, never moved, and the copy is reported under `--explain-copies`.
2. Reduce each remaining argument, one passed by borrow or by `mut`, or the result of a `lend` call, to a place path, such as `scene.meshes[i].verts`.
3. Two paths overlap if one is a prefix of the other. Two index expressions on the same array always count as overlapping.
4. A `mut` argument must not overlap any other remaining argument of the same call (E0301).
5. A closure argument must not capture a variable that overlaps a `mut` argument (E0305).
6. A `lend mut` place counts as a use of its root for the whole statement (section 4.6). No other part of that statement may read or write a place overlapping the root, except through the lent place itself: `at_mut(mut g, 0, 0).x = g.width` is E0323; write `let w = g.width` first.

`f(mut a, a)` is rejected with the hint to write `let tmp = a` first. Disjoint parts of one array are obtained through library functions such as `split_at_mut` and `swap`.

### 4.4 Moves and lifetime

- The last use of a variable moves its value. There is no use after move, because there is no later use.
- A value is released immediately after its last use, not at the end of the block.
- Assigning to a `var` releases the old value first, unless the right-hand side reads it.
- Evaluation order is left to right. Arguments are evaluated before the call.

### 4.5 Writes to boxed values

A write to an element of a boxed value (`a[i] = x`, `m[k] += 1`, any `mut` use) needs the box to be unshared:

1. If the checker knows the value is unique (section 6), write directly.
2. Otherwise test the reference count at run time. If it is 1, write directly.
3. Otherwise allocate a copy of the box, release one reference to the old box, and write to the copy.

The copy in step 3 is shallow: elements that are themselves boxed are shared with the old box, each gaining one reference. Step 3 is the event that `--explain-copies` reports.

### 4.6 Projections

Status: Specified. A function can lend out a place inside one of its parameters instead of returning a copy. This lets user-defined collections offer element access and in-place update without trusted code, and resolves open issue 3.

```
type Grid* = struct(width: Int, cells: Array[Cell])

fn at*(g: Grid, x: Int, y: Int) -> lend Cell:
    lend g.cells[y * g.width + x]

fn at_mut*(mut g: Grid, x: Int, y: Int) -> lend mut Cell:
    lend mut g.cells[y * g.width + x]

at_mut(mut grid, 2, 3).alive = true
let n = at(grid, 2, 3).neighbours
```

Grammar: `ret_type ::= type | "lend" [ "mut" ] type` and the statement `"lend" [ "mut" ] place`.

Rules:

1. Every path of a `lend` function ends with exactly one `lend` statement, whose place is rooted in a parameter: a borrowed parameter for `lend`, a `mut` parameter for `lend mut`. Nothing runs after it. Work that must happen after the caller is done (rebalancing, updating a count) needs a function that takes a closure instead.
2. The result is a place, not a value. It can be read, assigned to (`lend mut`), passed as a borrowed or `mut` argument, or copied by `let`. It cannot be stored, returned or captured, except that another `lend` function may lend it on (`lend at(g, x, y)`). Doing otherwise is E0320.
3. The lent place counts as a use of its parameter for the whole statement that uses it, under the exclusivity rules of section 4.3. Two `lend mut` places from one value in one statement are rejected (E0321); `split_at_mut` and `swap` cover the common cases.
4. The traits `Index` and `IndexMut` have `lend` methods, so implementing them gives a type the `c[k]` syntax.
5. A `lend` function compiles to a function returning a pointer to the place, usually inlined. The place lives inside a parameter that outlives the caller's statement, so no counting is needed. For `lend mut`, any copy required by section 4.5 happens before the pointer is taken.

### 4.7 Method calls

Status: Specified. `x.f(args)` is a call of a function `f` whose first parameter accepts `x`; after lookup it means exactly `f(x, args)`.

1. Lookup, in order: functions named `f` in the module that defines `x`'s type whose first parameter has that type; then methods of traits implemented for that type and in scope (defined in, or imported into, the current module). Two candidates at the same step is E0105; write `Trait.f(x, args)` to choose.
2. The receiver is passed the way the first parameter says: borrowed, `mut` or `take`. The call site writes no marker for it. For `mut` the receiver must be a mutable place; for `take` the last-use rule of section 4.2 applies, and a resource receiver must be at its last use.
3. Exclusivity (section 4.3) treats the receiver as the first argument. `v.push(v[0])` and `v.push(len(v))` are accepted: `push` takes its element by `take`, so the element is a finished value before `v` is changed. `v.extend(v)` is rejected, because `extend` borrows its argument and would read `v` while growing it; write `v.extend(v.copy())`.
4. A field holding a function is not a method: call it as `(x.f)(args)`.
5. Module-qualified calls such as `tcp.send(mut c.sock, data)` are ordinary calls, not method calls, and mark `mut` as usual.

Calls through a type or trait name: `T.f(args)` calls the function `f` defined in the module of type `T` (`Url.parse(url)`, `Ptr[U8].null()`, `Response.status(500)`). `Trait.f(args)` calls the trait's method, with `Self` inferred from the arguments or the expected type (`Default.default()`). On an `any T` receiver, only the methods of trait `T` are found, and the call goes through the method table (section 3.4).

## 5. Type checking and inference

Status: Specified. Function signatures are written out; everything inside a function body is inferred by bidirectional checking.

### 5.1 What is written and what is inferred

| Item | Rule |
| --- | --- |
| `fn` item | Parameter types required. Return type required unless it is `Unit`. |
| Effects and error types on an exported function | Required. On a private function they are inferred (section 7). |
| `let` and `var` | Type inferred from the initializer; an annotation is optional. |
| Lambda | Parameter and return types taken from the expected function type. With no expected type, parameter types are required. |
| Generic arguments | Inferred by unification at each call. Explicit form: `parse[Int](text)`. |

Local variables are never generalized: a local lambda has one type.

### 5.2 Algorithm

Two mutually recursive functions over the syntax tree:

- `check(expr, expected_type)` pushes a known type inward. Used for function arguments, annotated bindings, return expressions and lambda bodies.
- `infer(expr) -> type` synthesizes a type. Used for variables, calls, field access and literals.

Unification variables exist only for generic arguments of a single call and are resolved before the call's checking finishes. If any remain unresolved, that is an error asking for an explicit argument.

Literals: an integer literal takes the expected integer type, else `Int`. A float literal takes the expected float type, else `Float`. A literal that does not fit its type is an error.

Empty literals: `[]`, `{}` and an empty set get a fresh unification variable for their element type, which may be solved anywhere in the same function body (`var out = []` followed by `out.push(v)`). This is the one case where a variable outlives a single call. If it is still unsolved at the end of the body, the literal needs an annotation (E0210).

### 5.3 Subtyping

There is no subtyping between data types and no numeric conversion. Four narrow coercions exist:

- A unique value may be used where a shared one is expected (section 6).
- A function with fewer effects may be used where one with more is expected (section 7).
- `T` converts to `T?` by wrapping in `Some`.
- `iso T` converts to `T` when taken, which ends its isolation (section 14).

### 5.4 Errors

Failure is a checked effect. A function lists the error types it can fail with after `!`, returns its plain result type, and failures propagate to the caller with no marker at the call site.

```
fn parse_port(text: Str) -> Int ! ParseError:
    let n = parse_int(text)              # may fail; propagates
    if n < 0 or n > 65535:
        fail(ParseError.range(n))
    n

fn load(path: Str) -> Config ! io, ConfigError:
    let text = read_file(path)           # IoError converts to ConfigError
    Config(port = parse_port(text))      # so does ParseError
```

Rules:

1. `fail(e)` ends the current function with error `e`.
2. A call to a function that can fail with `E` is allowed if the caller's signature lists `E`, or lists an `E2` with an `impl From[E] for E2`. The conversion is applied automatically.
3. Otherwise the failure must be captured: `try e` evaluates `e` and yields `Result[T, E]`, which is ordinary data.
4. An exported function must list its error types. For private functions they are inferred.
5. `main` may list error types. An error reaching it prints the error and exits with status 1.

Error sets and `try`:

- The errors a function lists form a set. `try e` yields `Result[T, E]`, where `E` is the single error type if the set has one member, and otherwise an anonymous union of the set's types.
- A pattern `Err(p)` matches when the error is of the type `p` is a pattern for: `Err(Trapped(t))` matches only a `Trapped`. `Err(e)` matches the rest, and `e` has the union of the types not matched by earlier arms.
- A union value can be passed on with `fail(e)` from a function that lists every type in it.
- Conversion: a call that fails with `E` needs no conversion if the caller lists `E`, even when a `From` impl also fits. Otherwise exactly one listed type `E2` must have `impl From[E] for E2`. If several do, the call is E0520: capture it with `try` and convert explicitly.

```
match try load("app.conf"):
    Ok(cfg) -> start(cfg)
    Err(e)  -> print(f"bad config: {e}")

let port = (try parse_port(text)).or(8080)
```

Compilation: a function that can fail returns a one-byte status and writes its result or its error through a hidden pointer. Each call is followed by one test of the status. There is no stack unwinding and no cost beyond that branch.

Because every failing call is a possible exit, pass 4 treats it as one when checking resources (section 6.3). A trap is different: it is a program bug, cannot be captured, and is not listed in signatures.

Options are plain data and do not propagate. Use `match`, or `opt.or(default)`.

Failing calls carry no marker in source, by design; this resolves open issue 5. Tools show the exits instead:

- The language server draws an inlay `!` after every call that can fail, with the error type on hover (section 19.5).
- `starnite check --explain-exits <fn>` lists every exit point of a function and the error each carries.
- The lint `marked-failures`, off by default, warns on any failing call made inside a `with` block, where an early exit runs abandon. Outside with, a failing call while a resource is live is already an error (section 6.4).

A resource left live on an exit is already an error (E0412), so no unmarked exit can leak one.

### 5.5 Pattern matching

- A `match` must be exhaustive, and an unreachable arm is an error. Both are checked with Maranget's usefulness algorithm.
- A data type declared `open type` may gain variants in later releases; it is meant for error types. Outside the package that declares it, a `match` over an open type must have a `_` arm even when it names every current variant (E0205). Inside that package the usual rule applies. Adding a variant to an exported open type is a minor-version change (section 3.8.2); adding one to any other exported data type is a major change. `open` is a contextual keyword before `type` (sections 2.1 and 2.2), so names such as `fn open` stay valid. The standard error types `IoError` and `HttpError` are open.
- Matches compile to decision trees: each scrutinee tag is tested at most once.
- Matching on a value borrows it. Fields bound by a pattern are borrowed unless the scrutinee is consumed, in which case they are moved out (section 9.3).

## 6. Usage kinds: copy, shared, unique, resource

Status: Specified. Every type has one of three kinds, which decides whether its values can be duplicated and whether they can be dropped silently.

### 6.1 Kinds

| Kind | Which types | Duplicating | Dropping without use |
| --- | --- | --- | --- |
| Copy | Primitives; structs, tuples and inline unions whose fields are all Copy | Bitwise copy | Allowed |
| Shared | Boxed types, and structs containing them. The default for heap data. | Allowed; costs one count increment | Allowed; the compiler inserts the release |
| Resource | Types declared `resource type`, and any type containing one | Never | Never: the value must be consumed |

### 6.2 Uniqueness

`unique T` is a Shared-kind value that the checker knows has no other reference, at any depth through owned fields. It is a compile-time attribute with no run-time representation.

How a value becomes unique:

- It is built by a constructor, literal or collection literal from unique or Copy parts.
- It is returned by a function whose return type is `unique T`.
- It is produced by `copy(x)`, a deep copy.

How uniqueness is kept or lost:

| Use of unique `x` | Afterwards |
| --- | --- |
| Passed to a read-only parameter | Still unique |
| Passed to `mut p: unique T` | Still unique |
| Passed to `mut p: T` | Still unique, unless the callee's interface records that it duplicates `p`; then shared. Library mutators such as `push` never duplicate their receiver. |
| Moved (last use, or `take`) | Gone; the receiver has a unique value |
| Used again after a use that needed ownership | Shared: this is the point where a duplicate is made |

What uniqueness buys: writes skip the run-time count test, cell reuse is guaranteed (section 9), and the value can become `iso` or `frozen` (section 14).

A parameter declared `take p: unique T` demands a unique argument. If the argument is shared, the compiler inserts `copy()` and reports it under `--explain-copies`; with `--no-implicit-copies` it is an error.

### 6.3 Resource types

```
resource type File[S]

fn open(path: Str) -> File[Open] ! io, IoError
fn close(take f: File[Open]) ! io
```

Rules, checked per function on the control-flow graph:

1. On every path from its creation to a function exit, a resource value is consumed exactly once.
2. Consuming means: passing it to a `take` parameter, returning it, storing it in a field of another value (which is then a resource too), or destructuring it with a pattern (`let Conn(sock, _) = c`), which consumes it and binds its fields.
3. Reading it or passing it as `mut` does not consume it.
4. A resource cannot be captured by a closure that escapes. A `local` closure may use it through a `mut` capture.
5. Each resource type has, written or derived (below), `fn abandon(take self)`. It is called when a with block exits with the resource unconsumed (section 6.5), and by the runtime when a task traps or is cancelled (section 14.6).

Writing `abandon` by hand is not required; this resolves open issue 6.

- If a resource type defines no `abandon`, the compiler derives one: it abandons each field that is a resource, in reverse declaration order, and drops the rest.
- A typestate resource may define `abandon` for one state (`impl Abandon for Conn[Sent]`), which overrides the derived one in that state.
- A state with no safe cleanup is marked with the marker trait `NoAbandon`:

```
resource type Txn[S] = struct(db: Db, id: Int)
impl NoAbandon for Txn[Committing]
```

A resource in a `NoAbandon` state may not be live at any exit the compiler can see, including a failing call (E0413, which names the call). If a trap happens anyway, there is no cleanup to run, so `supervise` cannot confine it: the whole program stops, and the trap message names the resource (section 14.9).

This overrides every run-time path that abandons resources: a trap (section 11.5), cancellation (14.6), supervision (14.9), `k.abandon()` (7.3) and `par` cancellation (14.4) all stop the program instead when they reach a resource in a `NoAbandon` state. A suspension point counts as a visible exit for E0413, since cancellation can happen there.

### 6.4 Typestate

A resource type may take state parameters. A state is any type name used only as a marker; it has no run-time representation.

```
resource type Socket[S]

fn socket() -> Socket[Closed] ! io
fn connect(mut s: Socket[Closed -> Connected], addr: Addr) ! io, IoError
fn send(mut s: Socket[Connected], data: Array[U8]) ! io, IoError
fn close(take s: Socket[Connected]) ! io
fn discard(take s: Socket[Closed])
```

The checker keeps, for each resource variable, its current state or `moved`. Rules:

- A call requires the argument's current state to equal the parameter's.
- `Socket[A -> B]` on a `mut` parameter changes the variable's state from `A` to `B` after the call.
- If the function can fail, the change applies only on success. Inside a `with` block nothing more is needed (section 6.5). Elsewhere, capture the outcome with `try` and match on it:

```
var s = socket()
match try connect(mut s, addr):
    Ok(_)  -> ...          # here s: Socket[Connected]
    Err(e) -> discard(s)   # here s: Socket[Closed]
```

- Where control flow joins, every incoming path must leave the variable in the same state. A loop body must end in the state it started in.
- Values in different states cannot share a collection. Wrap them: `type AnySocket = Idle(Socket[Closed]) | Live(Socket[Connected])`.

Outside a `with` block, a call that can fail while an owned resource is live (a local variable holding one, not a `mut` parameter) is an error (E0414) unless it is wrapped in `try`. The implicit exit would otherwise skip the resource's consumption. A resource behind a `mut` parameter belongs to the caller, which is checked at its own call.

### 6.5 Scoped resources: `with`

`with` binds a resource for a block and guarantees its cleanup on every exit, so calls that can fail need no handling while the resource is live.

```
with_stmt = "with" IDENT "=" expr ":" block ;
```

```
fn get*(url: Str) -> Response ! io, HttpError:
    let u = Url.parse(url)
    with c = connect(u.host, u.port):
        send(mut c, Request(Get, u))
        receive(mut c)
```

Rules:

1. The bound variable is a mutable resource, in the state the initializer returns.
2. On any exit from the block (falling off the end, a propagating failure, `return`, `break`), if the resource has not been consumed, the compiler calls its `abandon` function. `abandon` accepts any state except a NoAbandon one (section 6.3).
3. The block may consume the resource itself, for example with a graceful `close(c)`. Nothing further happens on that path.
4. A call with a fallible state transition needs no special form. The code after it sees the success state; the failure path leaves the block.
5. The value of the block is the value of its last expression.

`with` is the one place where a resource is released implicitly. Everywhere else, consumption stays explicit.

## 7. Effects

Status: Specified. Each function has a set of effects; a function may only call functions whose effects are within its own set.

### 7.1 Built-in effects

| Effect | Meaning | How it is declared or checked |
| --- | --- | --- |
| `io` | Files, network, clock, randomness, console; sub-effects io.fs, io.net, io.env, io.proc, io.clock, io.rand and io.console (section 7.5) | Listed by exported functions (`! io`), inferred for private ones (section 7.2) |
| `async` | May suspend (section 14.5) | Listed by exported functions (`! async`), inferred for private ones (section 7.2) |
| `alloc` | May allocate on the heap. Stack and region allocation do not count. | Inferred for every function. `noalloc fn` is an error if it is present. |
| `div` | May fail to terminate | Inferred for every function. `total fn` is an error if it is present (section 17.4). |
| `lock[L]` | May hold mutexes up to level L (section 14.7) | Listed by exported functions, inferred for private ones |
| `pure` | Not an effect: a marker for the empty effect set | Written only in a function type, as in `fn(T) -> Int ! pure`; checked where the function is passed (section 7.2) |

`alloc` and `div` are never written in signatures. This is a change from the design sketch, made to keep signatures short. Their inferred values are stored in the compiled module interface.

Error types appear in the same list (section 5.4). `-> Config ! io, ConfigError` reads: returns a `Config`, may perform I/O, may fail with `ConfigError`.

### 7.2 Effect rules

- An exported function lists its `io`, `async`, `lock` and user effects. A private function's set is inferred as the union over its body.
- A function-typed parameter with no effect list is effect-polymorphic: whatever the argument does is added to the caller's effects at that call.

```
fn map*[T, U](xs: Array[T], f: fn(T) -> U) -> Array[U]     # effects of f pass through
fn sort_by*[T](mut xs: Array[T], key: fn(T) -> Int ! pure)  # key must have no effects
```

- `! pure` on a function type demands the empty set (`alloc` and `div` are still permitted unless the enclosing function is `noalloc` or `total`).
- Recursive private functions are solved by fixpoint iteration over each strongly connected group, starting from the empty set.

* An exported function that lists an effect or an error type its body can never produce gets warning W0502, naming the unused entry. Signatures then say what a function really does. A library that reserves an effect or error for a future version can allow the warning for a module in the manifest's `[lints]` table.

### 7.3 User-defined effects and handlers

This extends the grammar of section 2:

```
effect_def = "effect" IDENT [ "*" ] [ generics ] ":" NEWLINE INDENT { fn_sig NEWLINE } DEDENT ;
handle     = "handle" expr ( "by" expr | ":" NEWLINE INDENT arm { arm } DEDENT ) ;
arm        = IDENT "(" [ params ] ")" "->" block ;
effect     = path [ targs ] ;     (* in a "!" list: an effect if declared with effect or built in, else an error type *)
```

```
effect Log:
    fn log(msg: Str)

fn work() ! Log:
    log("starting")

fn main() ! io:
    handle work():
        log(msg) ->
            print(msg)
            resume
```

Three handler shapes are supported. Together they cover exceptions, dependency injection, generators and async; they stop short of full algebraic effects by excluding multi-shot resumption.

| Shape | Rule | Compiled as | Status |
| --- | --- | --- | --- |
| Resuming | `resume` is the last statement of the arm, exactly once | An ordinary call through a hidden handler parameter | Specified |
| Aborting | The arm never resumes | An early return propagated like `Err` up to the `handle` | Specified |
| Suspending | The arm binds the continuation, `op(args, k) -> ...`, and may store it or resume it later, once | The state-machine transform of section 14.5 | Specified, unproven in combination |

Rules for a suspending handler:

- The continuation `k` has a resource type, `Cont[A, R]`. It must be consumed exactly once: by `k.resume(value)` or by `k.abandon()`.
- `abandon` runs the suspended computation's cleanup: it calls `abandon` on every resource live at the suspension point.
- A function that performs a suspending effect is compiled twice: once as a plain function for callers under resuming handlers, once as a state machine.

```
effect Yield[T]:
    fn yield(value: T)

fn numbers() ! Yield[Int]:
    var i = 0
    while true:
        yield(i)
        i += 1

fn first(n: Int) -> Array[Int]:
    var out = []
    handle numbers():
        yield(v, k) ->
            out.push(v)
            if len(out) < n: k.resume(())
            else: k.abandon()
    out
```

Multi-shot resumption, where one continuation is resumed more than once, is excluded by design. It would duplicate the suspended frame and any resource in it, which contradicts section 6.3. Backtracking search is written with explicit data structures instead.

### 7.4 Compilation

- Built-in effects have no run-time representation.
- For each user effect `E` in its set, a function receives one extra hidden parameter: a pointer to a struct of function pointers plus the handler's environment.
- `handle` builds that struct on the stack and passes it down.
- An aborting operation makes each function between it and the `handle` return through its error path, which runs the same releases as an ordinary early return.

### 7.5 I/O capabilities

Status: Specified, except the evented backend of rule 5, which is Specified, unproven in combination, like the suspending handlers it relies on. `io` is split into seven sub-effects that a function can declare, a test can fake, and a handler can narrow for one call. Effects say what kind of I/O a function does; the handlers below also limit where it may go.

| Sub-effect | Covers | Narrowing handler |
| --- | --- | --- |
| `io.fs` | Files, directories, paths | `fs.under(dir, access)` |
| `io.net` | Sockets, DNS | `net.only(hosts)` |
| `io.env` | Environment variables, arguments | `env.only(names)` |
| `io.proc` | Starting processes | `proc.only(programs)` |
| `io.clock` | Wall and monotonic clocks, sleep | None; replaced in tests |
| `io.rand` | OS randomness | None; seeded in tests |
| `io.console` | Standard input, output and error | None; captured in tests |

Rules:

1. `io` is the union of the seven sub-effects. Writing `! io` keeps its current meaning.
2. An exported function may list sub-effects in place of `io`, as in `! io.net, HttpError`. The checker rejects a body whose inferred tags exceed the list (E0503); an unknown tag, such as io.disk, is E0504. Private functions infer their tags, as in section 7.2. Listing `io` allows every sub-effect.
3. All `io.*` tags share one hidden handler parameter, the `io` struct of section 7.4. The tags exist only in types and interface files, so declaring them adds no run-time cost.
4. `fs.under`, `net.only`, `env.only` and `proc.only` in module `io` are resuming handlers (section 7.3). Each forwards an operation to the enclosing `io` handler when it is within its limit, and fails with `IoError.Denied` otherwise. Denied(op: Str, target: Str) is a variant of IoError, the error type of module io. It names the refused operation and its target, as in Denied("open", "/etc/passwd"). Because it is an IoError, no signature that already lists IoError changes. Each wraps the whole `io` struct, so other sub-effects pass through unchanged. Nested handlers can only narrow: the limit in force is the intersection. `fs.under` takes an `Access`, defined in module `io` as `type Access* = Read | Write | ReadWrite`.
5. The active port (section 3.7) supplies the root `io` handler for `main`. Each port names a default backend, threaded or evented, and `--io=threaded` or `--io=evented` overrides it at build time. Library code does not change with the backend. The evented backend relies on suspending handlers and carries their status.
6. An application manifest may hold a `[grants]` table. With no table, the root handler allows every operation. With one, the root handler fails any operation outside it with `IoError.Denied`, before any narrowing handler sees it. A `[grants]` table in a library manifest is an error (E1120), and so is an unknown key or malformed entry (E1121). Standard streams are granted unless the table sets console = false. When the program's inferred tags include a sub-effect that the table grants nothing for, the build warns (W1122).
7. Foreign functions declare their tags under section 18.1. They can bypass handlers at run time, so narrowing handlers and grants limit Starnite code only. Their declared tags appear in the capability summary (section 3.8.4).
8. `alloc`, `div` and `lock[L]` stay inferred only (section 7.1). Regions (section 10.3) cover allocator choice.
9. In tests, `handle e by h` (section 20.2) may replace one sub-effect, such as a fixed clock or seeded randomness, and forward the rest to the real handler.

```
[grants]
fs   = { read = ["./config"], write = ["./data"] }
net  = { connect = ["api.example.com:443"], listen = [":8080"] }
env  = ["PORT", "API_KEY"]
proc = []
```

```
fn fetch_user*(id: Int) -> User ! io.net, HttpError:
    ...

fn main() ! io:
    handle run_plugin() by fs.under("./plugins", Read)
```

## 8. Compiler pipeline

Status: Specified. The compiler is a sequence of 22 passes (16 numbered, 6 lettered) over three intermediate forms, and every pass after type checking can be validated by re-checking its output.

### 8.1 Intermediate forms

| Form | Shape | Used for |
| --- | --- | --- |
| Typed tree | The syntax tree with every expression's type, kind, effect set and resolved names | Checking passes |
| Core | Monomorphic, in A-normal form: every intermediate value has a name; control flow is `let`, `match`, `call`, `loop`, `jump` | Analyses and optimization |
| Counted Core | Core plus explicit `dup`, `drop`, `reuse`, `region_enter`, `region_exit` instructions | Memory passes and C generation |

### 8.2 Passes

| # | Pass | Input to output | Section |
| --- | --- | --- | --- |
| 1 | Lex and parse | Text to syntax tree | 2 |
| 2 | Resolve names and imports | Syntax tree | 3.5 |
| 2a | Port resolution and seam completeness | Syntax tree | 3.7 |
| 3 | Type check, method lookup, trait-value check | Syntax tree to typed tree | 5 |
| 4 | Kind, move and resource check | Typed tree | 4, 6 |
| 5 | Effect check | Typed tree | 7 |
| 5a | Lock-level check | Typed tree | 14.7 |
| 6 | Exclusivity check | Typed tree | 4.3 |
| 7 | Capture inference; reachability inference (optional, research) | Typed tree | 13, 15 |
| 8 | Isolation and separation check | Typed tree | 14 |
| 9 | Refinement check | Typed tree | 17 |
| 10 | Monomorphize and lower: method calls, trait-value tables, comprehensions, with blocks | Typed tree to Core | 3.4, 3.6, 4.7, 6.5 |
| 10a | Range analysis; refinement obligations pass 9 could not discharge; strict-mode checks | Core | 17.2, 17.6 |
| 11 | Simplify: inline, fold constants, remove dead code, compile matches | Core | 5.5 |
| 11a | Flow summary: which effect sources reach which sinks, per exported function | Core to capability and flow summary, written to the interface file | 3.8.4 |
| 11b | Program rules check | Core and flow summaries | 17.7 |
| 11c | Handler and async lowering: handlers to direct calls or unwinding, suspending functions to state machines | Core | 7.4, 14.5 |
| 12 | Escape analysis, stack and region placement | Core | 10 |
| 13 | Insert counts; reuse; destination passing | Core to Counted Core | 9 |
| 14 | `inplace` and `noalloc` verification | Counted Core | 9.6 |
| 15 | Optional whole-program count removal | Counted Core | 16 |
| 16 | Emit C | Counted Core to C11, or to SSA and machine code (section 11.7) | 11 |

Passes 2a to 9 report errors and, apart from building the typed tree (pass 3) and choosing which variables become shared cells (pass 7), change nothing; pass 9 hands any refinement obligation it cannot discharge to pass 10a. From pass 10 on, only passes 10a, 11b and 14 report user errors.

### 8.3 Separate compilation

Each module compiles to an object file and an interface file. The interface holds, per exported function:

- its signature, including effects;
- inferred facts: `alloc`, `div`, which parameters escape, and its capture summary;
- its capability and flow summary (section 3.8.4), which package tools read without the source;
- the Core body of generic and small functions, for monomorphization and inlining.

The compiler is organised as queries, each a pure function of its inputs with its result cached by input hash: parse a file, resolve a module, type-check a function, infer a function's effects, build its Core, emit its object code. A query reruns only when an input's hash changes. The build, `starnite check` and the language server (section 19.5) all use the same queries, so an editor sees exactly the errors a build would report.

A change to a function body that leaves its interface entry unchanged does not force dependents to recompile.

### 8.4 Internal validation

A debug build of the compiler runs a checker after passes 10 to 15:

- Core is well typed.
- In Counted Core, every owned value is consumed exactly once on every path.
- No value is used after its last `drop`.

These checks turn most compiler bugs into compiler crashes instead of memory errors in user programs.

## 9. Counting and reuse

Status: Specified, unproven in combination. Pass 13 inserts the minimum count updates that ownership requires, then turns releases followed by allocations into in-place reuse. The method follows Koka's Perceus and Lean 4's borrow inference.

### 9.1 Owned and borrowed variables

In Core, every variable of Shared kind is one or the other:

| Variable | Status |
| --- | --- |
| Read-only parameter, `mut` parameter | Borrowed |
| `take` parameter | Owned |
| Result of a call or constructor | Owned |
| Pattern binding from a borrowed scrutinee | Borrowed |
| Pattern binding from a consumed scrutinee | Owned (moved out) |

An owned variable carries exactly one reference that this function must hand on or release. A borrowed variable carries none.

A use is *consuming* if it passes the value to a `take` parameter, stores it in a constructor or collection, captures it in a closure, or returns it. Every other use is a read.

### 9.2 Insertion algorithm

Walk each function body backwards, keeping the set of variables that are live after the current point.

| Situation | Instruction inserted |
| --- | --- |
| Consuming use of owned `x`, and `x` is not live afterwards | None: the reference moves |
| Consuming use of owned `x`, and `x` is live afterwards | `dup x` before the use |
| Consuming use of borrowed `x` | `dup x` before the use |
| Read of owned `x`, and `x` is not live afterwards | `drop x` after the reading expression completes |
| Owned `x` is never used | `drop x` immediately after its binding |
| Owned `x` is consumed on one branch and not on another | `drop x` at the start of each branch that does not consume it |
| Any use of a Copy-kind value | None |

`dup` and `drop` of a struct expand to one instruction per boxed field. Resource-kind values never receive `dup` or `drop`; pass 4 has already proven they are consumed exactly once.

### 9.3 Reuse

When an owned boxed value is matched and not used afterwards, its memory can serve the next allocation of the same size.

```
# source
match xs:
    Cons(x, rest) -> Cons(f(x), map(rest, f))

# Counted Core, general case
match xs:
    Cons(x, rest) ->
        if is_unique(xs):
            r = token(xs)            # keep the cell; x and rest are moved out
        else:
            dup x; dup rest
            decref xs
            r = null
        y  = f(x)
        ys = map(rest, f)
        Cons@r(y, ys)                # writes into r if non-null, else allocates
```

Rules:

1. A token is created at a `match` on an owned variable whose last use is that match.
2. The token is offered to the first constructor on each path whose allocation size class equals the matched cell's.
3. If a path has no such constructor, the token is freed at the earliest point on that path.
4. If the value is statically `unique` (section 6.2), the `is_unique` test and the `else` branch are omitted.
5. When a reused cell receives a field value identical to what it already holds, the write is omitted.

### 9.4 Demoting `take` to borrow

For private functions only: if a `take` parameter is never consumed and never used for reuse in the body, the compiler rewrites it as a read-only parameter. Callers then pass it with no count update. The analysis iterates to a fixpoint over each group of mutually recursive functions.

### 9.5 Destination passing

A call in *constructor-tail position* is one whose result is stored directly into a field of a constructor that is then returned. A self-recursive call in that position is rewritten to a loop:

```
fn map(xs, f, dst):                  # dst: pointer to the field to fill
    loop:
        match xs:
            Nil -> *dst = Nil; return
            Cons(x, rest) ->
                cell = Cons@r(f(x), <hole>)
                *dst = cell
                dst  = &cell.tail
                xs   = rest
```

Conditions: the constructor has exactly one field receiving the recursive result, and no code runs between the call and the constructor. The entry wrapper allocates a one-word destination on the stack. Stack use is then constant.

### 9.6 `inplace` and `noalloc` verification

Pass 14 checks an `inplace fn` on its Counted Core:

1. Each `take` parameter of boxed type is treated as `unique`. Callers supply that under the rule in section 6.2.
2. No `dup` of a boxed value appears on any path.
3. Every constructor that would allocate is paired with a token on every path.
4. Every call is to an `inplace` function or to one whose interface records no `alloc`.
5. Recursion appears only in tail position or constructor-tail position.

A `noalloc fn` is checked for one thing: no allocating instruction and no call to a function with `alloc` on any path. A failure of either check is a compile error naming the instruction and the source line.

### 9.7 Releasing large structures

`drop` decrements the count; at zero it calls the type's generated release function. That function does not recurse. It pushes child pointers onto a worklist threaded through the memory of the objects being freed, and loops. Deep structures therefore cannot overflow the stack.

The runtime option `STN_FREE_BUDGET=n` stops after `n` objects and resumes at the next allocation, which bounds the pause from releasing a very large structure.

### 9.8 Reporting copies

`--explain-copies` lists, with source lines:

- each write that may take the slow path of section 4.5, with the earlier use that made the value shared;
- each implicit `copy()` inserted for a `unique` parameter;
- each `dup` inside a loop.

`--profile-copies` adds run-time counters to the same sites and prints totals at exit.

## 10. Stack, modes and regions

Status: Specified. Pass 12 places each boxed value on the stack, in a per-call region, or on the heap, using one escape analysis; the `local` mode lets a signature promise non-escape so callers can rely on it.

### 10.1 Escape analysis

Each boxed value in a function gets one of two marks: *stays* or *escapes*. A value escapes if any of these holds:

- it is returned;
- it is stored into a value that escapes, or through a `mut` parameter;
- it is captured by a closure that escapes;
- it is sent on a channel or passed to `spawn`;
- it is passed to a parameter whose interface summary says that parameter escapes;
- it is passed to a function-typed value whose parameter is not `local`.

The analysis runs to a fixpoint within a function. Parameter summaries are computed bottom-up over the call graph, one group of mutually recursive functions at a time, and stored in module interfaces.

### 10.2 Placement

| Value | Placement | Release |
| --- | --- | --- |
| Copy-kind values and structs | Registers or stack, always | None |
| Boxed, stays, size fixed at compile time and at most 4 KiB, not allocated in a loop | A slot in the stack frame | None |
| Boxed, stays, otherwise | The current call's region | Bulk, at function exit |
| Boxed, escapes | Heap | Counting |

Stack and region objects have the `STN_NOCOUNT` flag set in their header. `dup` and `drop` test that flag and do nothing, so callees that borrow such a value need no special code.

### 10.3 Region rules

1. A function has at most one region per invocation, created on the first region allocation and released on every exit path, including error returns and traps.
2. A value qualifies for the region only if every value stored into it is Copy, borrowed from a value that outlives the call, or itself placed in the same region.
3. Resource-kind values are never placed in a region.
4. If rule 2 fails, the value goes to the heap. Region placement never changes program behaviour.

The runtime region is a linked list of 64 KiB blocks with a bump pointer. Release returns the blocks to a per-thread cache.

### 10.4 Allocator passing

Rule 2 would exclude every value built by a callee. To avoid that, a function gets a second entry point when its summary says its result is freshly allocated and its allocations flow only into that result:

```
StnArray* tokenize(StnStr* text);                        /* allocates on the heap */
StnArray* tokenize__in(StnStr* text, stn_region* where);  /* allocates in the caller's region */
```

A caller whose use of the result *stays* calls the `__in` entry with its own region. `load_config`, a function that reads and parses a configuration file, relies on this: `tokenize` and `parse` both allocate in `load_config`'s region.

### 10.5 The `local` mode

`local` on a parameter or a function-typed parameter's argument is a checked promise:

- A `local` value must not be returned, stored in a non-local value, captured by a non-local closure, or passed to a non-local parameter.
- Arguments passed to a `local` parameter are marked *stays* in the caller without consulting the callee's body.
- A closure literal passed to a `local` parameter is itself local. It lives on the stack and may capture `mut` borrows and resources.

Some library types exist only in local mode, so they never need counts: `StrView` and `Slice[T]` (a pointer and a length into a borrowed buffer), and every iterator. `for x in xs` builds its iterator on the stack.

## 11. Runtime and C output

Status: Specified. The compiler emits one C11 file per module and links a runtime of roughly 3,000 lines of C; that size is a target, not a measurement.

### 11.1 Object header

Every boxed object starts with 8 bytes:

```c
typedef struct stn_header {
    uint32_t rc;          /* reference count */
    uint16_t tag;         /* variant index; 0 for other objects */
    uint8_t  flags;       /* STN_NOCOUNT | STN_ATOMIC */
    uint8_t  size_class;  /* allocator class, for reuse and free */
} stn_header;
```

| Flag | Set on | Effect on `dup` and `drop` |
| --- | --- | --- |
| none | Ordinary heap objects | Plain increment or decrement |
| `STN_NOCOUNT` | Stack objects, region objects, constants | Nothing |
| `STN_ATOMIC` | Objects visible to more than one thread (section 14.3) | Atomic increment or decrement |

```c
static inline void stn_dup(void* p) {
    if ((uintptr_t)p & 1) return;                 /* field-less variant */
    stn_header* h = p;
    if (h->flags == 0) { h->rc++; return; }       /* fast path */
    if (h->flags & STN_NOCOUNT) return;
    atomic_fetch_add_explicit((_Atomic uint32_t*)&h->rc, 1, memory_order_relaxed);
}

static inline void stn_drop(void* p, void (*release)(stn_header*)) {
    if ((uintptr_t)p & 1) return;
    stn_header* h = p;
    if (h->flags == 0) { if (--h->rc == 0) release(h); return; }
    if (h->flags & STN_NOCOUNT) return;
    if (atomic_fetch_sub_explicit((_Atomic uint32_t*)&h->rc, 1, memory_order_acq_rel) == 1)
        release(h);
}
```

A count that reaches `UINT32_MAX` sets `STN_NOCOUNT`: the object becomes permanent instead of overflowing.

### 11.2 Allocation

- Size classes step by 16 bytes up to 1 KiB. Each thread keeps a free list per class; larger requests go to the system allocator.
- `stn_alloc(class)` pops the thread's list or refills it. `stn_free(h)` pushes onto the list of the freeing thread.
- The underlying allocator is replaceable at link time. The default is the platform `malloc`.
- Each object type has one generated `release` function, used by `drop` and by the worklist of section 9.7.

### 11.3 Calling convention

- Parameters follow the table in section 4.2.
- A result of at most 16 bytes is returned by value. A larger one is written through a hidden first parameter. A function that can fail returns a status byte and always uses the hidden pointer (section 5.4).
- Hidden parameters come first, in this order: result pointer, effect handlers (section 7.4), region (section 10.4).
- Names are mangled as `module__name`, with `__Type` appended per generic argument: `list__map__Int`.

### 11.4 Generated code

Source and output for the two gate examples.

```
fn centroid(points: Array[Vec3]) -> Vec3:
    var acc = Vec3(0.0, 0.0, 0.0)
    for p in points:
        acc += p
    acc / Float(len(points))
```

```c
typedef struct { double x, y, z; } geo__Vec3;

geo__Vec3 geo__centroid(const StnArray* points) {
    geo__Vec3 acc = {0.0, 0.0, 0.0};
    const geo__Vec3* p = (const geo__Vec3*)points->data;
    int64_t n = points->len;
    for (int64_t i = 0; i < n; i++) {
        acc.x += p[i].x; acc.y += p[i].y; acc.z += p[i].z;
    }
    double d = (double)n;
    return (geo__Vec3){acc.x / d, acc.y / d, acc.z / d};
}
```

The `inplace` list `map` from section 9, after reuse and destination passing:

```c
typedef struct list__Cons__Int {
    stn_header h; int64_t head; struct list__Cons__Int* tail;
} list__Cons__Int;
#define LIST_NIL ((list__Cons__Int*)(uintptr_t)1)

list__Cons__Int* list__map__Int(list__Cons__Int* xs, StnClosure* f) {
    list__Cons__Int*  result;
    list__Cons__Int** dst = &result;
    while (xs != LIST_NIL) {
        xs->head = ((int64_t (*)(StnClosure*, int64_t))f->code)(f, xs->head);
        *dst = xs;                 /* the cell is reused: no allocation */
        dst  = &xs->tail;
        xs   = xs->tail;
    }
    *dst = LIST_NIL;
    return result;
}
```

### 11.5 Checks and traps

| Check | Emitted as |
| --- | --- |
| Integer overflow | `__builtin_add_overflow` and relatives, then `stn_trap` |
| Array bounds | One unsigned comparison of index against length |
| Division by zero (integers) | A test before the division |
| Missing map key, failed `ref` access with `pool[r]` | A test in the library function |
| Exclusivity of shared cells | Section 13.3 |

`stn_trap(code, file, line)` prints the message, calls `abandon` on every live resource, and ends the nearest supervised task, or the process with a non-zero exit status if there is none (section 14.9). Live resources are found through a per-task intrusive list, which a resource joins when created and leaves when consumed.

A trap writes `trap: <kind> at <file>:<line>:<col>` to standard error, then the message and a backtrace in debug builds. Kinds include `integer overflow`, `index out of range`, `division by zero` and `missing key`. Exit status is 0 on success, 1 when an error reaches `main` (section 5.4) and 2 on a trap.

A trap ends the nearest enclosing supervised task (section 14.9), or the whole program if there is none.

### 11.6 Build modes

| Mode | C flags | Runtime additions |
| --- | --- | --- |
| Debug | `-O0 -g` | Freed memory is poisoned; every `drop` validates the header; counts must balance at exit; line information for traps |
| Release | `-O2 -fno-strict-aliasing` | None |
| Whole | Release, with pass 15 run over the whole program (section 16); selected by --release=whole | None |
| Hardened | Release plus address sanitizer or memory tagging where available | Section 18.4 |

### 11.7 Native backend

Status: Specified. This is a large engineering project, not a research one. On x86-64 and ARM64 the compiler generates machine code and links executables itself, with no C compiler; the C backend stays for other platforms and as a test oracle.

#### Why it can match C

Optimizing C compilers spend much of their effort trying to prove facts that this language guarantees by construction:

| Fact the optimizer needs | In C | Here |
| --- | --- | --- |
| Two pointers do not overlap | Only with `restrict`, which is rarely written | Always true for distinct `mut` arguments and for unique values (section 4.3) |
| A call has no side effects | Inferred where possible; often fails across files | Recorded in each function's effect set (section 7) |
| A call cannot unwind | Not an issue in C, but a cost in C++ | Failure is a status test, never unwinding (section 5.4) |
| A value does not change | `const` is not a guarantee | `let` and `frozen` are |
| An index is in bounds | Never checked | Proven by ranges or refinements, or checked (section 17) |

#### Pipeline

1. Counted Core is converted to an SSA intermediate form: typed, with an explicit control-flow graph and an alias class on every memory operation.
2. Machine-independent optimization, using the passes below.
3. Instruction selection per target, using addressing modes and fused multiply-add.
4. Register allocation: linear scan for debug builds, graph colouring with coalescing for release builds.
5. Object files in ELF, Mach-O or PE/COFF.
6. A built-in linker for programs made only of this language's code. The system linker is used only when foreign libraries are linked (section 18).

Passes needed for parity with C compiled at `-O2`:

| Pass | What it buys |
| --- | --- |
| Inlining, by size and call frequency | Removes call overhead and exposes everything below |
| Sparse conditional constant propagation | Folds constants through branches |
| Global value numbering | Removes repeated computations, including repeated loads where alias classes allow |
| Dead code and dead store elimination | Removes unused work |
| Loop-invariant code motion | Hoists loads, bounds checks and count tests out of loops |
| Scalar replacement of aggregates | Keeps struct fields in registers |
| Induction variables and strength reduction | Turns index arithmetic into pointer increments |
| Loop unrolling | Speeds up small counted loops |
| Check elimination | Applies section 17.2's range facts again after inlining |
| Tail calls | Guaranteed for self-calls in tail position |
| Loop vectorization | See below |

#### Vectorization

- A counted loop over arrays is vectorized when iterations depend on each other only through a reduction. The no-overlap guarantee makes this test simpler than in C, where compilers often give up or add run-time overlap checks.
- Floating-point operations are never reassociated, because that changes results. A plain sequential float sum is therefore not vectorized. `xs.sum_fast()` declares the order free; its result is then fixed for a given target and build.
- The library type `Simd[T, N]` supports hand-written kernels and is lowered to SSE, AVX2, AVX-512 or NEON.
- `--cpu=baseline` (the default, for portable binaries), `--cpu=native`, or a named CPU selects instruction sets. `--cpu-dispatch` builds hot functions for several instruction sets and picks one at start-up.

#### Runtime without C

- The runtime (allocator, counting, scheduler, traps, formatting) is rewritten in the language itself as trusted functions (section 18.3) and compiled by the same backend.
- On Linux the runtime makes system calls directly, with no C library. On macOS it calls `libSystem`, because Apple does not keep the system-call interface stable. On Windows it calls `kernel32` and `ntdll`.
- Math functions such as `sin`, `exp`, `log` and `pow` are implemented in the language with an error of at most 1 ulp, and tested against the system math libraries.
- Foreign C code still works. Linking it brings in the system linker and C library, for that program only.

#### Debugging and tools

- The backend writes DWARF on Linux and macOS and CodeView on Windows, so gdb, lldb and Visual Studio show source lines and variables. On native targets this replaces the `#line` directives of section 20.3.
- It inserts its own edge counters for coverage (section 20.2) and coverage-guided fuzzing. Until it does, those modes build with the C backend.

#### Validation

- A verifier checks the SSA form after every pass in debug builds of the compiler.
- The fuzzer of section 21.2 compiles every program with both backends and runs the reference interpreter, and requires identical output, floating-point bits included.

#### Expected speed

The aim is to beat typical C on allocation-heavy, generic and string-heavy code, and to match tuned C elsewhere. Every figure below is a projection, not a measurement. Section 21.5 defines the two C baselines and the gates.

| Workload | Against typical C | Against tuned C | Why | Confidence |
| --- | --- | --- | --- | --- |
| Allocation-heavy: trees, lists, syntax trees | 1.2 to 2 times faster | About equal | Reuse analysis turns many allocations into in-place updates; the rest use size-class lists instead of `malloc` | Medium |
| Generic code: sorting and maps with comparison functions | 1.1 to 1.5 times faster | About equal | Each instantiation is compiled separately, so comparisons are inlined instead of called through function pointers as in `qsort` | Medium |
| Formatting and parsing numbers and text | 1.1 to 2 times faster | About equal | The runtime library is written for speed, not for C library compatibility | Medium |
| Scalar loops and branchy code | About equal | Up to 1.2 times slower | Remaining bounds and overflow checks | Medium |
| Number-crunching loops C compilers vectorize | 1.5 to 3 times slower before the vectorizer; about equal after | Up to 1.1 times slower after | The no-overlap guarantee helps; tuned C may use hand-written intrinsics | Low |
| Code with checks that cannot be removed | Slower by the cost of the checks | Slower | Visible with `--explain-checks`; removable with `where` clauses, strict mode and budgets | High |

Compiling should also be several times faster than going through a C compiler, because no C text is generated and parsed again.

LLVM could later be added as an optional third backend for maximum optimization. This plan does not need it, and it is a large C++ dependency.

#### Order of work

1. SSA form and verifier, x86-64 instruction selection, linear-scan allocation, ELF output and static linking on Linux. Gate: every test passes on both backends.
2. The optimization passes above, except vectorization. Gate: within 1.3 times tuned C on the benchmark suite of section 21.5.
3. ARM64, Mach-O and PE/COFF output; the runtime rewritten in the language; DWARF and CodeView.
4. The loop vectorizer and `Simd[T, N]`. Gate: every row of the native-backend table in section 21.5.

### 11.8 Freestanding targets

Status: Specified; planned after the native backend. A freestanding target has no operating system and no C library, for microcontrollers and boot code.

```
[port.board]
when = { os = "none", arch = "thumbv7em" }
dirs = ["ports/board"]

[target.thumbv7em-none]
heap = "48 KiB"
stack = "8 KiB"
entry = "board.reset"
```

- **Selecting it:** `--target <arch>-none`, matched by ports with `os = "none"` (section 3.7).
- **Code generation:** microcontroller architectures (ARM Thumb, RISC-V, Xtensa) use the C backend with the vendor's C compiler at first. Native Thumb and RISC-V support can follow the x86-64 and ARM64 work of section 11.7.
- **Memory:** the heap is a fixed static region of the size the manifest gives. The allocator, counting and reuse work as on other targets. Running out of heap traps.
- **Tasks:** there are no threads. Tasks, channels and `par` run on one core with a cooperative scheduler, so `par` is still deterministic. `supervise` works, giving each supervised task a slice of the static heap.
- **Library:** `core`, `array`, `str`, `map`, `iter`, `mem` and cooperative `task` are available. `io`, `net` and threads are not, unless the board's port provides them.
- **Traps:** the port supplies `on_trap`, for example to log over a serial line and reset the board.
- **Testing:** tests and benchmarks run on the host by default. `starnite test --target <arch>-none --runner <command>` runs them on a board or an emulator, comparing output as the host runner does.

## 12. Pools and generational references

Status: Specified. A `Pool[T]` owns its elements; a `Ref[T]` is an 8-byte slot number and generation that is validated against the pool on each access.

This replaces the design sketch's pointer-based `ref` and its `r.get()`. Going through the pool makes the reference half the size, ties each access to an owner the checker can see, and removes the need for `get_unchecked`.

### 12.1 Layout

```c
typedef struct { uint32_t slot; uint32_t gen; } stn_ref;        /* 8 bytes, Copy kind */

typedef struct StnPool {
    stn_header h;
    uint32_t  len, cap, free_head;
    uint32_t* gens;      /* one generation per slot; odd = occupied */
    T*        items;     /* elements stored inline */
} StnPool;
```

- `Ref[T]?` uses slot `0xFFFFFFFF` for `None`, so it is also 8 bytes.
- A slot's generation is incremented when it is filled and again when it is emptied. A slot whose generation would overflow is retired and never reused.
- A pool is a Shared-kind value with copy-on-write, like `Array`. Refs remain valid in a copy, so a copied pool is a consistent snapshot.

### 12.2 Operations

| Operation | Result | Behaviour |
| --- | --- | --- |
| `pool.add(take v)` | `Ref[T]` | Fills a free slot or grows |
| `pool.get(r)` | Borrowed `T?` | `None` if `r` is stale |
| `pool[r]` | Place of type `T` | Traps if `r` is stale. Usable on the left: `pool[r].hull -= 10` |
| `pool.remove(r)` | `T?` | Moves the element out and bumps the generation |
| `pool.contains(r)` | `Bool` |  |
| `for (r, x) in pool` |  | Visits occupied slots in slot order |

`get` and `[]` are built-in projections, like array indexing: the borrowed element is usable only while the pool is not modified.

A validity check is: slot below `cap`, then `gens[slot] == r.gen`. That is two comparisons and one load.

### 12.3 Removing checks

The compiler tracks, per function, a set of (pool, ref) pairs known valid.

1. A successful `get`, `contains` or `[]` adds the pair.
2. Refs produced by iterating a pool are valid for that pool.
3. `pool.add` leaves the set unchanged. `pool.remove`, passing the pool as `mut`, or reassigning the pool or the ref variable removes the affected pairs.
4. While a pool is only borrowed read-only, nothing can be removed, so pairs stay valid for the whole scope and checks are hoisted out of loops.

```
fn total_threat(fleet: Pool[Ship]) -> Int:     # read-only: no removals possible
    var sum = 0
    for (r, s) in fleet:
        match fleet.get(s.target):             # one check per distinct target
            Some(t) -> sum += t.hull
            None    -> ()
    sum
```

### 12.4 Limits

- A ref used with a different pool of the same element type is memory-safe but may name an unrelated element. Debug builds widen refs to 16 bytes with a pool identifier and trap on mismatch.
- Tying a ref to its pool in the type is deferred to section 15, where the pool becomes part of the ref's reachability set.
- Elements never own each other through refs, so ownership stays acyclic and counting cannot leak.

## 13. Closures and automatic sharing

Status: Specified, unproven in combination. A closure copies what it only reads; a `var` that a closure writes, or that changes while a closure can still see it, is moved into a shared cell automatically.

### 13.1 Closure objects

```c
typedef struct StnClosure {
    stn_header h;
    void*     code;                      /* first parameter is the closure itself */
    void    (*release)(stn_header*);      /* releases the captures */
    /* captured values follow */
} StnClosure;
```

A function with no captures is a constant closure object with `STN_NOCOUNT`. A closure passed to a `local` parameter is built in the caller's stack frame.

### 13.2 Capture rules

| Captured variable | How it is captured |
| --- | --- |
| `let`, or a parameter | By value: a bitwise copy for Copy kind, one `dup` for Shared kind |
| `var` that is not assigned after the closure is created, and that the closure does not assign | By value, as above |
| `var` assigned by the closure, or assigned elsewhere while the closure is live | Shared cell (section 13.3) |
| Any variable, when the closure is `local` | By address of the stack slot; no cell, no allocation |
| Resource | Only by a `local` closure |

"While the closure is live" is decided conservatively: from the closure's creation to the end of the variable's scope, unless the closure is `local`.

### 13.3 Shared cells

A shared cell is a heap box holding one variable. The declaring function and every capturing closure access the variable through it.

```c
typedef struct { stn_header h; uint8_t busy; T value; } StnCell;
```

This is the one deliberate exception to section 4: two closures really do see each other's writes. It is limited by scope, since only code that can name the variable can reach the cell.

Exclusivity for cells is enforced at run time, then optimized away where possible:

| Access | Example | Emitted code |
| --- | --- | --- |
| Short: read or replace the whole value, or update a Copy value | `c`, `c = 5`, `c += 1` | Trap if `busy` is set |
| Long: the contents are passed as `mut`, or a method mutates them in place | `sort(mut items)`, `items.push(x)` | Trap if `busy` is set; set `busy`; run; clear `busy` |

Removal rule: if no long access to a cell contains a call that can reach that cell, the `busy` field and every check on it are deleted. "Can reach" is answered by section 15; until that pass exists, the answer is "yes" for any call to a function value and "no" for calls to named functions that do not receive a closure capturing the cell.

Shared cells and closures that capture them are not `Send` (section 14.1).

### 13.4 Example

```
fn counter() -> (fn() -> Unit, fn() -> Int):
    var c = 0
    (fn(): c += 1, fn(): c)
```

`c` is assigned by the first closure, so it becomes a cell. Both closures hold one reference to it. Every access is short and there is no long access, so `busy` is deleted: each call is one load or one add through a pointer.

### 13.5 The `shared` keyword

`shared var c = 0` requests a cell explicitly and behaves identically. The lint `--require-shared` reports every automatic promotion, for teams that prefer the explicit form.

## 14. Concurrency

Status: Specified, unproven in combination. Tasks are structured, data crosses threads only by move or as immutable data, and counts stay non-atomic for everything a single thread owns.

### 14.1 Sendable types

`Send` is derived automatically. A value may cross to another task only if its type is `Send`.

| Type | `Send` | Why |
| --- | --- | --- |
| Copy-kind types, `Ref[T]` | Yes | No shared heap state |
| `iso T` | Yes | Unique, so no other thread can see it |
| `frozen T` | Yes | Immutable, counts are atomic |
| `Sender[T]`, `Receiver[T]`, `Mutex[T, L]` (L is its lock level, section 14.7), `Atomic[T]` | Yes | Internally synchronized |
| Plain boxed values (`Array[T]`, `Str`, closures) | No | Non-atomic counts |
| Shared cells and closures that capture them | No | Unsynchronized mutable state |
| `local` values | No | Tied to a stack frame |

### 14.2 `iso`

`iso T` is a storable form of `unique T` (section 6.2). Uniqueness is a fact about a variable; `iso` is a type, so it can be an element, a field or a channel payload.

- `iso e` requires `e` to be unique. It costs nothing at run time.
- An `iso` value can be moved, not duplicated. It may be dropped.
- Taking it (`take x: iso T` passed where `T` is expected) yields a `unique T`.
- Borrowing it read-only or as `mut p: unique T` is allowed and keeps it isolated.

### 14.3 `frozen` and thread-shared marking

- `freeze(take x: unique T) -> frozen T` makes a value deeply immutable. It walks the value once and sets `STN_ATOMIC` on every box.
- A `frozen` value is duplicated freely across tasks. To change it, `copy()` it, which yields a new unique value.
- Constants and string literals are `frozen` with `STN_NOCOUNT`: sharing them costs nothing.

The same marking walk is applied implicitly in one case: a non-unique boxed value read by more than one branch of a `par` (section 14.4). Its type does not change; its counts become atomic from then on. `--explain-copies` reports each implicit marking.

### 14.4 `par`

`par:` runs each statement of its block as a task and waits for all of them. `par for` does the same per iteration, splitting the range recursively. Each branch is checked as a closure:

| Use of an outer variable | Rule | Run-time cost |
| --- | --- | --- |
| Used by exactly one branch, any way | Allowed; it is an exclusive borrow | None |
| Read by several branches; Copy or `frozen` | Allowed | None |
| Read by several branches; other boxed value | Allowed; the value is marked thread-shared first | One marking walk, then atomic counts |
| Written by one branch and used by another | Error |  |
| `par for x in mut xs`, `xs` unique | Each iteration owns its element | None |
| `par for x in mut xs`, `xs` not unique | Elements are marked thread-shared; writes copy on demand | Marking walk, atomic counts |
| Shared cell or resource | At most one branch | None |

A branch may call a closure only if the closure is `Send` or no other branch uses it. Section 15 relaxes this by proving two closures separate.

A `par` with no `io` and no channels is deterministic: its result does not depend on scheduling.

#### Reductions

Parallel reductions give bit-identical results on any number of threads, including floating-point sums.

```
let total = par_sum(xs)                                   # Float
let best  = par_reduce(scores, 0, fn(a, b): max(a, b))
```

1. The input is split into chunks whose size depends only on the input length (4,096 elements), never on thread count or timing.
2. Chunk results are combined in a balanced binary tree in index order. The tree's shape depends only on the number of chunks.
3. So a reduction returns the same bits on 1 or 64 threads, on every run, for a given target. Single-threaded targets such as WebAssembly get the same result too.
4. A tree-ordered sum can differ in its last bits from a sequential left-to-right `sum(xs)`. Both are deterministic.
5. The combining function should be associative. The compiler cannot check that in general; the result is still deterministic if it is not, but may differ from the sequential result.
6. Work that needs no combining, such as `par_map` or a `par for` writing one element per iteration, keeps the adaptive chunking of section 14.8.

Failure in parallel code: if a `par` branch, a `par for` iteration or a `par_map` closure fails with an error, the others are cancelled at their next suspension point and their resources abandoned. Once all have stopped, the construct fails with the error from the lowest-numbered branch or iteration that failed, so the result does not depend on timing. A trap is handled the same way, then continues as a trap (section 14.9).

### 14.5 Tasks, channels and async

```
let (tx, rx) = channel[iso Batch](capacity = 16)
let worker = spawn consume(rx)          # Task[Unit], a resource
tx.send(iso load("data.bin"))
tx.close()
worker.join()
```

- `spawn f(args)` requires `Send` arguments and returns `Task[T]`. `Task` is a resource type: it must be consumed by `join()` or `cancel()`. This is how structured concurrency is enforced; a task cannot be forgotten.
- `channel[T: Send]` is bounded. `send` suspends when full; `recv()` returns `T?`, with `None` after close.
- `async` is a suspending effect (section 7.3). A function with `! async` is compiled to a state machine: a frame struct holding the variables live across suspension points, and a resume function with a `switch` on the saved state.
- A frame is embedded in its caller's frame when its size is known, otherwise heap-allocated.
- A task may move between worker threads only if its frame type is `Send`. Otherwise it stays on the thread that started it.
- Borrowing across a suspension is sound because the caller's frame outlives the callee's.

### 14.6 Cancellation and traps

`cancel()` sets a flag that the task observes at its next suspension point. The task's continuation is then abandoned: every live resource in its frames gets `abandon`, and owned values are dropped. `join()` on a cancelled task fails with the error `Cancelled`.

### 14.7 Mutexes and lock levels

```
level Cache < Db                        # declares an order

let stats = Mutex[Stats, Cache](Stats())

stats.lock(fn(mut s): s.hits += 1)      # the closure parameter is local
```

- The protected value is reachable only inside the `lock` callback, through a `local mut` parameter, so it cannot leak.
- Each mutex type names a level. The checker tracks the highest level a function may hold, as part of its effect set: inferred for private functions, written `! lock[Db]` on exported ones.
- Acquiring level `M` while holding level `L` requires `L < M`. Two mutexes of the same level cannot be held together. This rules out lock-order deadlocks.
- `Atomic[T]` offers `load`, `store`, `swap`, `compare_exchange` and `fetch_add` for Copy types up to 8 bytes.

Grammar addition: `level_def = "level" IDENT { "<" IDENT } NEWLINE ;`

### 14.8 Scheduler

- One worker thread per core by default (`STN_THREADS` overrides), each with a work-stealing deque.
- `par` pushes all branches but the first and runs the first inline. An idle worker steals the oldest entry.
- `par for` splits its range in half until a chunk is below a grain size, initially 1,024 iterations and adjusted from measured iteration time. Reductions use the fixed split of section 14.4 instead.
- `io` runs on an event-driven reactor in each worker: epoll on Linux, kqueue on macOS and the BSDs, IOCP on Windows. A task waiting on a socket, timer or pipe is parked at a suspension point and its worker runs other tasks; no thread blocks. File I/O and other calls with no readiness interface run on a small blocking pool. Programs do not change: `io` stays one effect, there is no separate async API, and `async` follows the rules of section 7.1. io\_uring may later replace epoll on Linux behind the same interface. This resolves open issue 8.

### 14.9 Supervision

Status: Specified, unproven in combination. `supervise` runs a function as a task with its own heap, so a trap inside it ends only that task: its memory is discarded, its resources are abandoned, and the caller gets a `Trapped` error instead of the program ending. This resolves open issue 2.

#### Example: one bad request instead of a dead server

```
fn route(req: Request) -> Response ! io, DbError:
    let items = db.recent_items()
    let page = items[req.page * 20 .. req.page * 20 + 20]    # traps if the page is past the end
    render(page)

fn serve(req: Request) -> Response ! io:
    match try supervise(fn(): route(req), memory = 64mib):
        Ok(resp) -> resp
        Err(Trapped(t)) ->
            log.error(f"{req.path} crashed: {t.message} at {t.location}")
            Response.status(500)
        Err(e) -> Response.status(503)                       # a DbError, failed normally
```

Without `supervise`, a request for page 9,999 makes the slice trap, and the trap ends the whole server: every other request in flight is lost and the process must be restarted. With it, that one request gets a 500, the log names the line, and the other requests carry on. A request that tries to allocate more than 64 MB is stopped the same way.

#### Example: workers that restart themselves

```
let sup = Supervisor(strategy = OneForOne, max_restarts = 5, within = 60s)
sup.start("indexer", fn(): index_forever(jobs))
sup.start("mailer", fn(): send_forever(outbox))
sup.run()
```

If the indexer traps on a malformed document, the supervisor logs it and starts the indexer again from scratch, after a short backoff, while the mailer keeps running. If the indexer traps 5 times within 60 seconds, `run` fails with `TooManyRestarts`, because a crash that repeats that fast is a bug, not bad luck.

#### Rules

1. `supervise(f)` runs `f` as a new task and waits for it, like a `par` branch. Its captures follow the rules of section 14.4, and in addition it may not capture anything as `mut` or capture a shared cell. So a trap can never leave the caller's data half-updated.
2. The task gets its own heap. On success, that heap is merged into the caller's: its 64 KiB blocks are re-parented, at a cost proportional to the number of blocks, not objects. The result is then returned.
3. On a trap, in this order: every resource live in the task is abandoned (section 6.3), newest first; tasks it started are cancelled; mutexes it held are marked poisoned; its channel ends are closed; count changes it made to objects outside its heap are undone; its heap is released wholesale, without visiting objects. Then `supervise` fails with `Trapped`, which carries the message, location and a backtrace.
4. Inside a supervised task, `dup` and `drop` first check whether the object belongs to the task's own heap: one load from the header of the object's 64 KiB block. An operation on an outside object is also recorded in an undo log. Read-only borrows make no count operations at all (section 9.1), so ordinary inputs cost nothing.
5. `memory = n` caps the task's heap; exceeding it traps the task, not the program. Each supervised task has its own stack with a guard page, so stack overflow traps the task too.
6. A poisoned mutex makes its next `lock` fail with `Poisoned`, which gives access to the value for inspection. `lock_ignoring_poison` is available for state known to be safe.
7. Supervised tasks nest, and a trap goes to the nearest enclosing `supervise`. A trap outside any supervised task still ends the program (section 11.5).
8. Not contained: a crash inside foreign code, which can corrupt memory anywhere, and a trap inside a callback from C (section 18.1). Both end the process. Traps in trusted Starnite code are contained, because they are ordinary checks.
9. `Supervisor` is a library type in `task`. Strategies are `OneForOne` (restart only the child that trapped) and `OneForAll` (restart every child). Restarts back off exponentially from 100 ms to 10 s. Each restart calls the child's function again from scratch.
10. Code that never calls `supervise` pays nothing for it.

`supervise` fails with `Trapped` and passes through the effects and errors of `f`. Its signature in `task` is `fn supervise*[T: Send](f: local fn() -> T, memory: Bytes = Bytes.unlimited) -> T ! Trapped`.

## 15. Reachability inference

Status: Research plan. The pass computes, for every closure, which shared cells, resources and pools it can reach; when it cannot, it answers "everything", which keeps run-time checks and rejects more programs but is never unsafe.

### 15.1 Why this is tractable here

The published reachability calculi track every reference in the program. Starnite does not need that: ordinary values cannot alias (section 4). Only four kinds of *tracked entity* can be shared, and only closures can carry them invisibly:

- shared cells (section 13.3);
- resources captured by `local` closures;
- pools, for tying refs to them (section 12.4);
- `mut` borrows held by `local` closures.

So reachability reduces to capture sets of closures over these entities. That is a much smaller problem than the general one, and it is the main bet of this section.

### 15.2 Consumers

| Consumer | Question asked | Without this pass |
| --- | --- | --- |
| Cell exclusivity (13.3) | Can any call inside this long access reach this cell? | `busy` checks stay |
| `par` separation (14.4) | Do two branches reach a common entity that one of them writes? | Non-`Send` closures are limited to one branch |
| Resource consumption (6.3) | Does a live closure still reach the resource being consumed? | Resources are capturable by `local` closures only |
| Pool-tied refs (12.4) | Is this ref known to belong to this pool? | Wrong-pool use is caught in debug builds only |

### 15.3 Qualifiers

Each expression whose type contains a function type gets a qualifier: a set of entries `x:r` or `x:w`, where `x` names a tracked entity through a variable in scope, plus two special elements.

| Element | Meaning |
| --- | --- |
| `x:r`, `x:w` | May read / may write the entity held in `x` |
| `fresh` | Reaches an entity created inside the expression and not otherwise visible |
| `top` | Unknown: may reach any non-`Send` entity |

### 15.4 Algorithm

A forward pass over the typed tree, in the bidirectional style of the PLDI 2026 paper listed in section 23.

1. **Closure literal.** Union over its free variables: a tracked entity contributes itself with the access the body performs; a closure variable contributes its own qualifier.
2. **Binding and assignment.** `let g = f` gives `g` the qualifier of `f`. Assigning into a `var` or a field joins the qualifiers.
3. **Containers.** A struct, array or cell holding closures has the join of everything stored in it. Reading back yields that join. There is no per-element precision.
4. **Call.** `f(args)` reaches the qualifier of `f` joined with those of every closure argument the callee's summary says it may call or store.
5. **Leaving scope.** When a variable named in a qualifier goes out of scope, it is replaced by `fresh` if the entity was created in that scope, or by the qualifier it was derived from.
6. **Function results.** Two components of a result that reach the same `fresh` entity are recorded as overlapping. `counter()` yields a pair whose summary says: components 0 and 1 overlap, component 0 writes.
7. **Summaries.** Each function's interface entry records, per function-typed parameter, whether it is called and whether it is stored in the result; and per result component, its qualifier in terms of parameters and `fresh`.
8. **Recursion.** Fixpoint iteration per group of mutually recursive functions, starting from empty qualifiers. Qualifiers only grow and are bounded by the variables in scope, so it terminates.

Any construct outside these rules yields `top`: a closure stored in a cell that the closure itself reaches, a closure crossing a `trusted` boundary, or a qualifier exceeding a size limit of 64 entries.

### 15.5 Decisions made from qualifiers

- **Separate.** Two closures are separate if their qualifiers contain no `top`, and every entity they share is accessed `r` by both and holds Copy or `frozen` contents.
- **Cannot reach `c`.** A call cannot reach cell `c` if the joined qualifier of its callee and closure arguments has no `top` and no entry for `c`.
- **Consumable.** A resource `f` may be consumed if no live closure's qualifier names `f` or contains `top`.

### 15.6 Build stages

| Stage | Scope | Unlocks |
| --- | --- | --- |
| R1 | Rule 1 only: literals used where they are written | `busy` removal for direct cases; the `counter` example |
| R2 | Rules 2 to 6 within one function | `par` over locally built closures |
| R3 | Rules 7 and 8: summaries across functions and modules | Higher-order library code |
| R4 | Pools as tracked entities; `ref` values carry their pool | Compile-time wrong-pool errors |

### 15.7 Validation and exit test

- **Differential fuzzing.** Compile each generated program twice: with the pass, and with every qualifier forced to `top`. Run both with all checks kept and logged. A check that fires at a site the pass would have removed is a soundness bug.
- **Reference cases.** Translate the case studies from the papers in section 23, and the test programs of the group's Diamond prototype, into Starnite where they can be expressed.
- **Proposed exit test.** Keep each stage only if it shows zero soundness discrepancies over ten million fuzzed programs and removes at least 90% of the `busy` checks in the standard library and example corpus. These thresholds are proposals to be agreed, not derived values.

### 15.8 Known gaps against the literature

- The published systems are not yet unified: the work on cyclic references and the work on deallocation each leave the other out. This plan sidesteps both by falling back to `top` for cyclic captures and by leaving deallocation to sections 6 and 9.
- No soundness proof exists for this reduced variant. A mechanized proof of rules 1 to 6 over a small core calculus is the natural first proof target (section 21.4).

## 16. ASAP pass

Status: Research plan. Pass 15 is an optional whole-program optimization in three stages of rising ambition; it only ever removes count operations that section 9 inserted, so disabling it changes speed and nothing else.

### 16.1 Stages

| Stage | What it removes | Analysis needed | Risk |
| --- | --- | --- | --- |
| A | A `dup` and its matching `drop`, when another owner provably keeps the object alive in between | Interprocedural aliasing and liveness | Low |
| B | All counting on objects from an allocation site whose last use is at a statically known point; a direct free is inserted there | Points-to analysis plus liveness | Medium |
| C | Counting on objects whose release point depends on the path taken; a small generated scan decides at run time | The full analysis of Proust's thesis | High; outside version 1 |

### 16.2 Stage A as Datalog

Facts are exported from Counted Core for the whole program. The rules below are schematic, in Soufflé syntax.

```
.decl Dup(p: Point, v: Var)            // dup v at p
.decl Drop(p: Point, v: Var)           // drop v at p
.decl Next(p: Point, q: Point)         // control-flow edge, across calls and returns
.decl SameObj(v: Var, w: Var)          // v and w always denote the same object
.decl Owner(p: Point, w: Var)          // w holds an owned reference at p
.decl Consumes(p: Point, v: Var)       // v's reference is moved away at p
.decl TestsUnique(p: Point, v: Var)    // is_unique or a reuse token on v's object at p

// the extra reference taken at d is still held by v at p
Held(d, v, d) :- Dup(d, v).
Held(d, v, q) :- Held(d, v, p), Next(p, q), !Drop(q, v).

// something on the way makes the pair unsafe to remove
Bad(d, v) :- Held(d, v, p), Consumes(p, v).
Bad(d, v) :- Held(d, v, p), SameObj(v, u), TestsUnique(p, u).
Bad(d, v) :- Held(d, v, p), !HasGuard(p, v).

HasGuard(p, v) :- SameObj(v, w), v != w, Owner(p, w).

Removable(d, v) :- Dup(d, v), !Bad(d, v).
```

For each `Removable(d, v)`, delete the `dup` at `d` and every `drop` of `v` that `Held` reaches.

The three `Bad` rules are the safety conditions:

1. The extra reference must only be read, never handed to a new owner.
2. No uniqueness test may run on the object in between. Removing the `dup` would make a shared object look unique, and an in-place write would then be visible through the other owner.
3. Another owned reference must exist at every point in between.

### 16.3 Stage B outline

1. Compute a points-to relation from allocation sites to variables and fields (inclusion-based, context-insensitive to start).
2. An allocation site qualifies if every reference to its objects stays within analysed code and none is stored in a `frozen` value, a channel or a `trusted` call.
3. Find a program point that is reached after every last use of the site's objects on every path.
4. Allocate such objects with `STN_NOCOUNT`, insert a direct release at that point, and delete their count operations.

Sites that fail any step keep counting. Stage B overlaps with regions (section 10); its gain is for objects that outlive the function that created them.

### 16.4 Stage C outline

Proust's design generates, at each point where liveness is path-dependent, a scan over a bounded part of the heap that finds objects no longer reachable from live variables. It needs three analyses: which heap paths a function may access, which objects may be shared, and what remains reachable. No production compiler implements it. Stage C is listed so the design leaves room; no work is scheduled.

### 16.5 Safety net

`--asap-verify` keeps a shadow count for every object. Removed operations still update the shadow count. The debug runtime traps if a direct release from stage B runs while the shadow count is non-zero, or if any object is accessed after its shadow count reached zero. The fuzzer of section 21 runs with this flag.

### 16.6 Implementation notes and exit test

- Use an existing Datalog engine at first; Soufflé compiles rules to C++. A built-in evaluator can follow if the stage is kept.
- Rust's Polonius project is prior art for expressing ownership analysis as Datalog.
- The pass runs only with `--release=whole`.
- Proposed exit test for stage A: keep it if it removes at least 20% of executed count operations on the benchmark suite and adds no more than 100% to compile time. Otherwise delete it. Stage B is attempted only if A is kept.

## 17. Refinements, check removal and termination

Status: Specified, unproven in combination. Run-time checks are the default; a range analysis removes most of them silently, and `where` clauses let a function demand a proof instead of performing a check.

### 17.1 Arithmetic

| Operation | Behaviour |
| --- | --- |
| `+`, `-`, `*` on integers | Trap on overflow |
| `+%`, `-%`, `*%` | Wrap |
| `a.saturating_add(b)` and relatives | Clamp |
| `/`, `%` on integers | Trap on a zero divisor, and on `MIN / -1` |
| Float arithmetic | Never traps; follows IEEE 754 |
| `I32(x)`, `U8(x)` and other conversions | Trap if the value does not fit; `I32.wrapping(x)` truncates |

### 17.2 Check removal

Pass 10a runs an interval analysis on Core. Each integer variable gets a range whose bounds are constants or `len(v) + constant` for an array `v` in scope.

- Sources of facts: literals, `range(n)`, `for i in range(len(xs))`, conditions of enclosing `if` and `while`, `where` clauses of the current function, and earlier checks that passed.
- A bounds, overflow or zero-divisor check whose condition follows from the ranges is deleted.
- Loops are analysed to a fixpoint, widening a bound to infinity after three changes.

### 17.3 `where` clauses

```
fn get[T](xs: Array[T], i: Int) -> T where 0 <= i and i < len(xs)
fn mean(xs: Array[Float]) -> Float where len(xs) > 0
```

- A `where` clause is a precondition. Inside the function it is assumed; `get` above compiles to an unchecked load.
- At each call site the compiler must prove it, first with the ranges of 17.2, then with an SMT solver.
- If neither succeeds, the call is a compile error. The programmer adds an `if`, or writes `check i < len(xs)`, a run-time test that traps on failure and adds the fact.
- Allowed in a clause: integer comparison and linear arithmetic, `and`, `or`, `not`, `len`, parameters and their fields, and calls to `total` functions, which the solver treats as opaque.
- Postconditions and type invariants are in section 17.5.

Solver interface: obligations are emitted as SMT-LIB text to Z3 with a fixed random seed and a resource limit instead of a time limit, so results are the same on every machine. An obligation that exhausts the limit counts as unproven.

### 17.4 `total fn`

A `total fn` must not have the `div` effect. The checker accepts a function body only if:

- it contains no `while`;
- every `for` iterates a collection or a `range`;
- every recursive call passes, in one fixed argument position, a value bound by a pattern from that same parameter (structural recursion);
- every function it calls is itself free of `div`;
- it performs no suspending effect.

Anything else gets `div`. This is deliberately simple: it proves the easy cases and makes no attempt at the hard ones.

### 17.5 Postconditions and type invariants

Status: Specified, unproven in combination. A function can promise a property of its result with `ensures`, and a type can declare a property every visible value has with `where`.

```
fn clamp*(x: Int, lo: Int, hi: Int) -> Int where lo <= hi ensures lo <= result and result <= hi:
    if x < lo:
        return lo
    if x > hi:
        return hi
    x

fn push_one*(mut v: Array[Int], x: Int) ensures len(v) == old(len(v)) + 1:
    v.push(x)

type Span* = struct(lo: Int, hi: Int) where lo <= hi
```

Postconditions:

1. `result` names the return value. `old(e)` is `e` evaluated on entry, and may mention only parameters.
2. The postcondition must hold at every successful return. A path that fails with an error (section 5.4) is exempt.
3. The compiler tries to prove it with the ranges of section 17.2, then the solver of section 17.3. Callers then assume it, which removes checks in their code.
4. If it cannot be proven, the compiler warns (W0801) and inserts a check at each return. In strict code (section 17.6) it is an error.

Type invariants:

1. The invariant holds whenever a value can be seen outside its module. It is checked after each construction, and at the end of each exported function of the module that returns the type or takes it as `mut`.
2. Outside the defining module, fields of a type with an invariant are read-only; changes go through the module's functions.
3. Inside the module, the invariant may be broken temporarily between those points.
4. These check points are enough because of value semantics: no other code holds a reference through which it could change the value in between.
5. Proof and fallback follow postcondition rules 3 and 4.

The expressions allowed are those of `where` clauses (section 17.3).

### 17.6 Strict mode

`strict fn`, or `--strict` for a whole package (not its dependencies), makes every run-time check the compiler cannot remove a compile error.

| Becomes an error when not removed | Still allowed |
| --- | --- |
| Array bounds | Explicit `check e` |
| Integer overflow and division by zero | `pool.get(r)`, which returns an option |
| `pool[r]` validity | Failures listed in the signature |
| Shared-cell `busy` checks | Wrapping operators `+%`, `-%`, `*%` |
| Unproven `ensures` and type invariants | Copies; control those with `inplace` and budgets |

- Each error names the check and offers fixes: add a `where` clause, add a `check`, or use a wrapping operator.
- The list is the same one `--explain-checks` prints. Strict mode turns it into errors.
- Guarantee: a strict function traps only through an explicit `check`, running out of memory, or overflowing the stack.

Grammar changes: `fn_sig` takes `[ "ensures" expr ]` after its `where` clause; `type_def` takes `[ "where" expr ]` before its newline; `strict` joins `fn_mod`; `ensures` is a keyword, and `strict` is a contextual keyword before `fn` (section 2.1).

### 17.7 Program rules

Status: policy rules are Specified; law rules are Specified, unproven in combination. A package can state rules about the whole program in one file, `rules.stn` at its root. The compiler checks them on every build, and a lock file makes any change to them visible in review.

There are two kinds:

- **Policy rules** constrain facts the compiler already computes: imports, effects, allocation, errors, trusted code. Checking them is exact and fast.
- **Law rules** state how functions relate. The compiler tries to prove each one and, when it cannot, tests it with generated inputs and says so.

Rules are for properties that span functions or modules. A property of one type is a type invariant (section 17.5); a property of one function is a postcondition or a property test (section 20.2).

#### Grammar

```
rule_def = "rule" STRING ( ":" policy | "for" params [ "where" expr ] ":" block ) ;
policy   = clause | NEWLINE INDENT clause { NEWLINE clause } DEDENT ;
clause   = scope "reaches" "no" fact { "," "no" fact }
         | fact "in" scope { "," scope }
         | scope "not" "imports" scope
         | "errors" "of" scope "in" type { "," type } ;
scope    = path [ ".*" ] [ "exported" ] ;
fact     = IDENT [ "." IDENT ] ;
```

`rule_def` is allowed only in `rules.stn`. `rule`, `reaches`, `imports` and `exported` are keywords only there.

#### Scopes

- `api.*` means module `api` and every module under it. `audio.render` names one function or one module.
- `exported` restricts a scope to exported names (section 3.5).
- A scope may name modules of dependencies. Their facts come from their interface files (section 8.3).

#### Facts

| Fact | Holds for a function that | Computed by |
| --- | --- | --- |
| `alloc` | May allocate on the heap | Effect inference (section 7.1) |
| `div` | May not terminate | Effect inference (section 7.1) |
| `async` | May suspend | Effect inference (section 7.1) |
| `io` | Performs any I/O | Effect inference (section 7.1) |
| `io.fs`, `io.net`, `io.proc`, `io.env`, `io.clock`, `io.console` | Performs that kind of I/O | Each library function that performs I/O carries one of these tags, and the tags propagate like effects |
| `lock` | May acquire a mutex or wait on a channel | The lock analysis of section 14.7 |
| `trusted` | Is or calls trusted code | Section 18.3 |
| `traps` | Contains a check that was not removed | The list of section 17.6 |
| `copies` | May copy a shared value on write | Section 9.8 |
| A user effect's name | Performs that effect | Section 7.3 |

The I/O tags exist only as facts. Signatures still write `! io`.

#### Clauses

| Clause | Holds when |
| --- | --- |
| `S reaches no F` | No function in `S`, nor anything it can call, has fact `F`. A call through a function value counts the facts of every function that can be passed there (section 7.2) |
| `F in S1, S2` | Fact `F` originates only inside those scopes: every direct call to a library function tagged `F`, and every trusted body with `F`, is in one of them. Calling into those scopes from outside is allowed |
| `S not imports T` | No module in `S` imports a module in `T` |
| `errors of S in E1, E2` | Every function in `S` can fail only with the listed error types |

Facts of foreign functions are what their declarations say (section 18.2). A rule about them is only as reliable as those declarations.

#### Policy rules: example

```
rule "the audio callback is real-time safe":
    audio.render reaches no alloc, no lock, no io

rule "the API layer goes through services":
    api.* not imports db.*

rule "payments only use the network through the gateway":
    io.net in payments.gateway

rule "public API errors are typed":
    errors of api.* exported in ApiError

rule "unsafe code stays in two modules":
    trusted in mem.*, ffi.*
```

A broken rule is an error in family E10xx, and shows the call path that introduced the fact:

```
error[E1001]: rule "the audio callback is real-time safe" is broken
  --> audio/render.stn:42:9
   |
42 |     log(f"underrun at {t}")
   |     ^^^ log performs io.console
   = path: audio.render -> mix -> report_underrun -> log
help: send the message on a channel and log it from another task
```

Checking every policy rule takes time proportional to the size of the call graph, so it runs on every build.

#### Law rules

```
rule "transfers keep the total" for a: Account, b: Account, amt: Money where 0 <= amt and amt <= a.balance:
    let (a2, b2) = transfer(a, b, amt)
    a2.balance + b2.balance == a.balance + b.balance

rule "orders only move forward" for o: Order, e: Event:
    rank(apply(o, e).status) >= rank(o.status)

rule "playlists survive saving and loading" for p: Playlist:
    decode(encode(p)) == p
```

1. The body's last expression is a `Bool`. The body may call any function but may not perform `io` or user effects. A failure inside the body breaks the rule.
2. On every build, the compiler inlines the functions involved to a bounded depth and gives the result to the solver of section 17.3. Linear integer arithmetic, booleans, data-type constructors and `match` are within reach; loops, recursion and floating point usually are not.
3. A proven law is reported as proven, and callers may assume it.
4. An unproven law is run as a property test (section 20.2) by `starnite test`: 1,000 cases by default, with shrinking and saved regressions. The build reports it as "tested, not proven".
5. Under strict mode (section 17.6), an unproven law is an error.
6. Results are cached by a hash of the rule and of every function body it depends on, so unchanged rules cost nothing on later builds.

Build summary:

```
rules: 5 policy rules hold
       transfers keep the total ............ proven
       orders only move forward ............ proven
       playlists survive saving and loading  tested (1,000 cases), not proven
```

#### The lock file

`rules.lock` records the approved rules: a format version, a hash per rule, a hash of the whole file, the approver's name and the date. Hashes ignore comments and formatting, so reformatting needs no new approval.

- `starnite rules approve` writes the lock. The approver's name comes from the version-control identity, or from `--as`.
- `--locked` makes the build fail if `rules.stn` no longer matches the lock. The error lists each rule added, removed or changed, by name. Without `--locked` this is a warning.
- CI should build with `--locked`, so a change that weakens a rule must carry a new approval, which shows up in review.

```
$ starnite build --locked
error[E1010]: rules.stn changed since it was approved
  removed: rule "the audio callback is real-time safe"
  last approved by alice on 2 Nov 2026
help: if this change is intended, run `starnite rules approve` and commit rules.lock
```

The lock is not a security mechanism: anyone who can edit the repository can edit both files. It turns a quiet weakening into a visible, reviewable change. Pair it with code-review permissions that restrict who may change `rules.stn` and `rules.lock`.

A dependency's rules do not apply to packages that use it.

## 18. Foreign code and trusted blocks

Status: Specified. C functions are declared with a Starnite signature that the compiler believes without checking; every guarantee in this document holds only if those declarations are true.

### 18.1 Declaring C functions

Foreign functions are declared in blocks that name the library they come from:

```
extern "C" from "c":
    fn read(fd: I32, mut buf: Slice[U8]) -> I64 ! io      # passed as pointer and length
    fn write(fd: I32, buf: Slice[U8]) -> I64 ! io

extern "C" from "sqlite3":
    fn sqlite3_open(path: CStr, out: Ptr[Ptr[U8]]) -> I32 ! io
    fn sqlite3_close(db: Ptr[U8]) -> I32 ! io
    fn open_raw(path: CStr, out: Ptr[Ptr[U8]]) -> I32 ! io = extern "sqlite3_open"

trusted fn open_db*(path: Str) -> Db ! io, DbError:
    var raw = Ptr[U8].null()
    let rc = sqlite3_open(path.to_cstr(), Ptr.to(mut raw))
    if rc != 0:
        fail(DbError.code(rc))
    Db(raw)
```

Grammar: `extern_block = "extern" STRING "from" STRING ":" NEWLINE INDENT { fn_sig [ "=" "extern" STRING ] NEWLINE } DEDENT ;`. The optional `= extern "name"` gives the C symbol when it differs from the Starnite name. `from` is a keyword only here.

Rules for foreign libraries:

1. Every foreign function is declared in an `extern "C" from "<library>"` block. Declarations in the block are trusted and carry the promises of section 18.2.
2. The library name is logical. `"sqlite3"` resolves per target to `libsqlite3.so`, `libsqlite3.dylib` or `sqlite3.dll`. `"c"` names the platform C library; on Windows, names such as `"kernel32"` name system libraries.
3. The manifest may map a name to a file instead: `[libraries]` then `sqlite3 = { static = "vendor/libsqlite3.a" }`.
4. A program links only the libraries it actually calls, after dead-code removal. There are no linker flags and no link section.
5. A foreign function cannot list error types or suspending effects. C reports failure through a return value, which a trusted wrapper turns into `fail(...)`, as `open_db` does.
6. A Starnite function passed to C as a callback must also have no error types and no suspending effects. A trap inside a callback ends the program; it cannot be contained by supervise (section 14.9).
7. A foreign function lists the I/O sub-effects it may use (section 7.5) after its signature, as in `! io.fs`. One that lists none counts as performing all of `io` in the capability summary (section 3.8.4). The list is trusted, not verified.
8. Violations of rules 5 and 6 are errors in family E09xx.

| Starnite type at the boundary | C type |
| --- | --- |
| Integers, floats, `Bool` | The matching C type |
| Struct of the above, marked `repr(c)` | The same struct |
| `Slice[T]`, `mut Slice[T]` | Pointer and length, as two arguments |
| `CStr` | `const char*`, NUL-terminated; created by `text.to_cstr()` |
| A resource type wrapping `Ptr` | `void*` |
| `Ptr[T]` | `T*`; usable only in `trusted` code |

Boxed Starnite values (`Array`, `Str`, `Map`, closures) cannot be passed directly. Their contents are lent as a `Slice` for the duration of the call, or copied.

### 18.2 What a declaration promises

The author of an `extern` block (section 18.1) asserts that each C function it declares:

- keeps no pointer to a borrowed argument after it returns;
- writes only within the bounds of `mut` slices;
- performs only the listed effects, and fails only with the listed errors;
- does not call back into Starnite except through declared callback parameters;
- is safe to call from any thread, unless marked `trusted(main_thread)`.

### 18.3 `trusted` functions written in Starnite

A `trusted fn` with a Starnite body may use `Ptr[T]`, pointer arithmetic, unchecked indexing and unchecked casts. Passes 4, 6 and 9 do not run on its body. Its signature is still enforced on callers. The standard library's `Array`, `Map`, `Pool` and `Mutex` are written this way.

The compiler flag `--list-trusted` prints every trusted function linked into a program, so the audit surface is known.

### 18.4 Containment

| Measure | Protects against | Cost |
| --- | --- | --- |
| Hardened build with address sanitizer | Out-of-bounds and use-after-free in C code, in testing | About 2x time; a typical figure, not measured here |
| Memory tagging on ARM hardware that has it | The same, probabilistically, in production | Low |
| Compiling the C library to WebAssembly and running it sandboxed | Any memory corruption reaching the Starnite heap | A call-boundary cost and a copy of the data |

None of these is required. They are options for libraries that are not trusted.

### 18.5 Visible trusted code

Status: Specified. Whether a dependency contains trusted code or links foreign libraries is shown, and can be refused, without reading its source.

```
$ starnite deps
json 2.1     pure
image 0.8    trusted (3 functions in image.mem), links libpng
sqlite 1.4   trusted (41 functions), links sqlite3
  via orm 0.6
```

- A package is marked `trusted` if it, or anything it depends on, contains a trusted function or an `extern` block. The mark shows which package the trusted code is really in, through `via`.
- A dependency can be refused trusted code in the manifest: `image = { version = "0.8", trusted = "deny" }`. The build then fails if `image` or anything under it contains trusted code, naming where.
- `--list-trusted` (section 18.3) still lists every trusted function in the program.
- Inside a package, program rules (section 17.7) such as `trusted in mem.*` keep trusted code in agreed modules.

## 19. Diagnostics and build flags

Status: Specified. Every error about an inferred property must point at the source line that caused the inference, because the programmer never wrote that property down.

### 19.1 Error format

```
error[E0412]: `s` is not consumed on this path
  --> net/client.stn:18:9
   |
14 |     var s = socket()
   |         - resource created here, in state Closed
18 |         return Timeout
   |         ^^^^^^^^^^^^^^ function exits here while `s` is still live
   |
help: call `discard(s)` before returning, or bind it with `with s = socket():`
```

Each error has a stable code, a primary location, zero or more secondary locations that explain inferred facts, and where possible a `help` line with a concrete edit.

### 19.2 Error families

| Codes | Family | Example message |
| --- | --- | --- |
| E01xx | Syntax and names | `unknown name 'cofnig'; did you mean 'config'?` |
| E02xx | Types | `expected Int, found Str` |
| E03xx | Moves and exclusivity | `'a' is passed as mut and also read in the same call` |
| E04xx | Resources and typestate | `'c' is in state Sent here; receive it or abandon it before close` |
| E05xx | Effects and errors | `load can fail with IoError, which this function does not list` |
| E06xx | Uniqueness, inplace, noalloc | `inplace fn allocates: no reusable cell reaches this Cons` |
| E07xx | Concurrency | `both par branches reach 'c', and the first writes it` |
| E08xx | Refinements | `cannot prove i < len(xs) at this call` |
| E09xx | Trusted and foreign code | `Ptr[T] used outside a trusted fn` |
| E10xx | Program rules | `rule "the audio callback is real-time safe" is broken` |
| E11xx | Packages and registry | `json 2.3.0 can do more than json 2.2.1` |

Warnings use the same families with `W` in place of `E`: W0502, the unused-effect warning, is in the effects family. W1122, a sub-effect the program can perform but its \[grants\] table does not grant (section 7.5), is in the packages family. Port and seam errors (section 3.7) are E0110 to E0119. A typestate that differs between branches that join, such as a resource `Sent` on one path and `Idle` on the other, is E0420.

Codes fixed for milestone 1 and its conformance corpus, plus the I/O capability codes of section 7.5 (E0504, E1120 and E1121). Codes in sections 2 to 6 not listed here keep the meaning their section gives.

| Code | Meaning | Section |
| --- | --- | --- |
| E0100 | Syntax error | 2.2 |
| E0101 | Unknown name | 3.5 |
| E0102 | Type in brackets after a name that is not generic | 2.2 |
| E0103 | Assignment to something that is not a place | 2.2 |
| E0104 | Parameter type omitted outside a lambda or handler arm | 2.2 |
| E0105 | Method call matches more than one trait | 4.7 |
| E0106 | Tab in indentation | 2.1 |
| E0201 | Type mismatch | 5.1 |
| E0202 | `match` does not cover every case | 5.5 |
| E0203 | Wrong number of arguments | 5.1 |
| E0204 | Type does not implement a required trait | 3.4 |
| E0205 | `match` over an open type has no `_` arm | 5.5 |
| E0210 | Empty literal whose element type is never settled | 5.2 |
| E0230 | Trait cannot be used with `any` | 3.4 |
| E0301 | `mut` argument overlaps another argument | 4.3 |
| E0302 | Use after move | 4.2 |
| E0303 | `mut` argument is not a mutable place | 4.2 |
| E0304 | `mut` parameter passed without the `mut` marker | 4.2 |
| E0305 | Closure argument captures a place overlapping a `mut` argument | 4.3 |
| E0320 | Lent place stored, returned or captured | 4.6 |
| E0321 | Two `lend mut` places from one value in one statement | 4.6 |
| E0322 | A path of a `lend` function does not end with `lend` | 4.6 |
| E0323 | Statement reads or writes the root of a `lend mut` place | 4.3 |
| E0414 | Failing call while an owned resource is live, outside `with` | 6.4 |
| E0501 | Exported function fails with an error it does not list | 5.4 |
| E0503 | Exported function performs an effect or I/O sub-effect it does not list | 7.2, 7.5 |
| E0504 | Unknown I/O sub-effect in an effect list | 7.5 |
| E0520 | More than one `From` conversion fits | 5.4 |
| E1120 | `[grants]` table in a library manifest | 7.5 |
| E1121 | Unknown key or malformed entry in `[grants]` | 7.5 |

Family E10xx covers program rules (section 17.7).

### 19.3 Flags

| Flag | Effect |
| --- | --- |
| `--debug`, `--release`, `--release=whole`, `--hardened` | Build mode (section 11.6); `whole` enables pass 15 |
| `--explain-copies` | Report possible copies, implicit `copy()` and implicit thread-shared marking |
| `--profile-copies` | Count them at run time |
| `--no-implicit-copies` | Make an implicit `copy()` an error |
| `--require-shared` | Report automatic promotion of a `var` to a shared cell |
| `--explain-checks` | List bounds, overflow, `ref` and `busy` checks that were not removed, with the reason |
| `--list-trusted` | Print all trusted functions in the program |
| `--asap-verify` | Shadow counts for pass 15 (section 16.5) |
| `--emit=core`, `--emit=counted`, `--emit=c` | Print an intermediate form and stop |

Output flags: `--format=text` (the default) or `--format=json` (section 19.4), `--apply-fixes`, `--quiet`. Run-time environment variables: `STN_THREADS`, `STN_FREE_BUDGET`.

Rule flags: `--locked` and the `starnite rules approve` command (section 17.7).

### 19.4 Machine-readable output

`--format=json` makes the compiler write every diagnostic and report as JSON, one object per line, so editors, CI systems and coding agents can act on them without parsing text.

Rules:

1. Output is JSON Lines on standard output: one object per line, each with a `kind` field. Nothing else is written to standard output in this mode.
2. The text format of section 19.1 still goes to standard error unless `--quiet` is given.
3. Every object carries `"version": 1`. Within a version, fields are only ever added, never removed or renamed. Consumers must ignore fields they do not know.
4. Positions give a 1-based `line`, a 1-based `col` counted in Unicode scalar values, and a 0-based `byte` offset into the UTF-8 file. Ranges are half-open: `end` is the first position after the range.
5. The last line is always one `summary` object.

| `kind` | Written for | Main fields |
| --- | --- | --- |
| `diagnostic` | Each error, warning or note | `severity`, `code`, `message`, `primary`, `related`, `facts`, `fixes` |
| `report` | Each entry from an `--explain-*` or `--list-*` flag | `report` (`copies`, `checks`, `exits`, `trusted`), `location`, `detail` |
| `summary` | The end of the run | `errors`, `warnings`, `status` (`ok`, `failed`, `crashed`) |

Test and benchmark runs add objects of kind `test` and `bench` (sections 20.2 and 20.3).

Program rules add objects of kind `rule`, each with its name, result (`holds`, `broken`, `proven`, `tested` or `unproven`) and, when broken, the call path (section 17.7).

Fields of a `diagnostic`:

| Field | Contents |
| --- | --- |
| `severity` | `error`, `warning` or `note` |
| `code` | The stable code from section 19.2, such as `E0412` |
| `message` | The one-line message, identical to the text form |
| `primary` | `{file, start, end, label}`: where the problem is reported |
| `related` | A list of `{file, start, end, label, role}`. `role` is `cause` for the source of an inferred fact, `previous` for an earlier conflicting use, or `context` |
| `facts` | Inferred facts the error depends on, each `{fact, subject, value}`, for example a resource's state or a value's uniqueness |
| `fixes` | A list of `{title, applicability, edits}`. Each edit is `{file, start, end, text}`. `applicability` is `safe` (meaning-preserving) or `maybe` (needs review) |

The error from section 19.1, in this format:

```json
{"version":1,"kind":"diagnostic","severity":"error","code":"E0412",
 "message":"`s` is not consumed on this path",
 "primary":{"file":"net/client.stn","start":{"line":18,"col":9,"byte":412},"end":{"line":18,"col":23,"byte":426},
            "label":"function exits here while `s` is still live"},
 "related":[{"file":"net/client.stn","start":{"line":14,"col":9,"byte":318},"end":{"line":14,"col":10,"byte":319},
             "label":"resource created here, in state Closed","role":"cause"}],
 "facts":[{"fact":"state","subject":"s","value":"Closed"}],
 "fixes":[{"title":"call `discard(s)` before returning","applicability":"safe",
            "edits":[{"file":"net/client.stn","start":{"line":18,"col":9,"byte":412},"end":{"line":18,"col":9,"byte":412},
                       "text":"discard(s)\n        "}]}]}
{"version":1,"kind":"summary","errors":1,"warnings":0,"status":"failed"}
```

Applying fixes: `--apply-fixes` applies every `safe` fix, re-checks the program, and repeats until no `safe` fix remains or ten rounds have run. `maybe` fixes are never applied automatically.

The schema is published as a JSON Schema file with each compiler release. A test in section 21.3 checks that every error code produces valid output with at least one primary location.

Compilation is the same in both formats: `--format=json` changes only how results are reported, never which programs are accepted.

### 19.5 Tooling

Status: Specified. One command, `starnite`, provides every tool. This resolves open issue 10.

| Command | Purpose | Section |
| --- | --- | --- |
| `starnite build`, `run`, `check` | Compile, compile and run, or check without generating code. `run file.stn` works without a manifest | 8 |
| `starnite test`, `bench`, `fuzz` | Tests, benchmarks, fuzzing | 20.2, 20.3 |
| `starnite fmt` | Formats source | below |
| `starnite lsp` | Language server | below |
| `starnite doc` | Documentation and doc tests | below |
| `starnite add`, `update`, `publish`, ... | Packages | 3.8 |
| `starnite rules approve`, `ports`, `deps` | Rules, ports, trusted code | 17.7, 3.7, 18.5 |

- `starnite fmt` has one style and no options. It works on the syntax tree, keeps comments, and with `--check` fails CI on unformatted files.
- `starnite lsp` is built on the compiler's incremental queries (section 8.3) and the JSON diagnostics (section 19.4). It reports errors as you type, shows inlay hints for failing calls, inferred effects and implicit copies (section 4.5), and offers go to definition, rename and the fixes diagnostics carry.
- `starnite doc` builds HTML documentation from `##` comments. Each function's page shows its effects, errors and typestate transitions, and its examples run as doc tests.

## 20. Standard library, testing and benchmarking

Status: Specified. Version 1 ships 13 modules; anything not listed is out of scope until the compiler passes its gates.

`print(x)` takes any `Show` value, writes it followed by a newline, and has the `io` effect. `Show` for `Int` and the other integer types writes decimal digits with a leading `-` when negative; for `Bool`, `true` or `false`; for `Str`, its contents without quotes; for `Float`, the shortest text that reads back as the same value.

### 20.1 Modules

| Module | Contents | Needed by milestone |
| --- | --- | --- |
| `core` | Integer and float types, `Bool`, `Char`, `Unit`, option, `Duration`, `Bytes`, `Result`, `fail`, `copy`, `check`, traits `Eq Ord Hash Show Add Sub Mul Div Index IndexMut Iter From Default Send Copy Abandon NoAbandon`, and `Cont` (section 7.3) | 1 |
| `array` | `Array[T]`, `Slice[T]`, `range`, sort, search, `split_at_mut`, `swap` | 1 |
| `str` | `Str`, `StrView`, `CStr`, formatting, UTF-8 iteration, `split`, `words`, `parse_int`, `parse_float` | 1 |
| `map` | `Map[K, V]`, `Set[K]`, `SortedMap[K, V]`, `SortedSet[K]` | 2 |
| `iter` | `map`, `filter`, `zip`, `enumerate`, `fold`, `sum`, `any`, `all`; all on local iterators | 2 |
| `mem` | `Ptr[T]`, raw allocation; trusted code only | 2 |
| `io` | `print`, standard streams, `File[S]`, `read_file`, `write_file`, paths, clock, random; IoError, including its Denied variant; `Access`; narrowing handlers fs.under, net.only, env.only and proc.only; the root handler and \[grants\] checks (section 7.5) | 4 |
| `log` | Leveled logging (log.info, log.error) to a replaceable sink, with the io effect | 4 |
| `pool` | `Pool[T]`, `Ref[T]` | 5 |
| `task` | `spawn`, `Task[T]`, `channel`, `par_map`, `Mutex`, `Atomic`, `freeze` | 6 |
| `net` | `Socket[S]`, TCP, DNS lookup | 6 |
| `test` | Test and benchmark runner, assertions, `Arbitrary` generators, snapshots, I/O fakes (sections 20.2 and 20.3) | 1 |
| `ffi` | `extern` support types | 4 |

Module `io` defines `IoError`, the error of every I/O operation. It is open (section 5.5), so a `match` on it outside the standard library needs a `_` arm. Errors the operating system reports with no matching variant arrive as `Os`.

```
open type IoError* =
    NotFound(path: Str)
  | AlreadyExists(path: Str)
  | NotADirectory(path: Str)
  | IsADirectory(path: Str)
  | PermissionDenied(path: Str)      # the operating system refused
  | Denied(op: Str, target: Str)     # a handler or [grants] refused (section 7.5)
  | HostNotFound(host: Str)
  | ConnectionRefused(addr: Addr)
  | ConnectionReset
  | AddrInUse(addr: Addr)
  | TimedOut
  | UnexpectedEof
  | InvalidData(reason: Str)         # for example, bad UTF-8 from read_file
  | StorageFull
  | Unsupported(op: Str)             # not available on the active port
  | Os(code: Int, message: Str)      # errno or Windows error code
```

Library rules:

- Everything the library does with raw memory is in `trusted fn`s inside `array`, `map`, `pool`, `task` and `mem`. The rest is ordinary checked Starnite.
- Collection methods that build a new collection return `unique` values.
- Every resource type in the library provides `abandon`.
- The library is the first large body of Starnite code, so it doubles as the compiler's main test corpus.

### 20.2 Built-in testing

Status: Specified, except schedule tests, which are specified but unproven in combination. Tests are part of the language: `test`, `fuzz` and `bench` blocks sit next to the code they check, and one runner handles eight kinds of test.

| Kind | Written as | What it checks | When it runs |
| --- | --- | --- | --- |
| Example | `test "name":` | Specific inputs give specific results | Every `starnite test` |
| Property | `test "name" for x: T:` | A statement holds for generated inputs; failures are shrunk to a minimal case | Every `starnite test`, 100 cases by default |
| Snapshot | `assert_snapshot value` | Output matches a stored, reviewed copy | Every `starnite test` |
| Rejection | `test rejects E0412 "name":` | The compiler refuses a misuse of an API | Every `starnite test`, at compile time |
| Schedule | `test "name" schedules 200:` | Concurrent code is correct under many interleavings | Every `starnite test` |
| Fuzz | `fuzz "name" for input: T:` | No input makes the code trap, leak or fail an assertion | `starnite fuzz`, for a set time |
| Integration | Files in `tests/` | The exported interface works as a whole program | Every `starnite test` |
| Doc | `>>>` examples in doc comments | Documented examples stay correct | Every `starnite test` |

The command is `starnite`.

Grammar additions:

```
test_def  = "test" [ "rejects" CODE ] STRING [ "for" params [ "where" expr ] ]
            [ "schedules" INT ] [ "serial" ] ":" block ;
fuzz_def  = "fuzz" STRING "for" params ":" block ;
bench_def = "bench" STRING [ "for" IDENT "in" expr ] [ "threads" expr ] { budget } ":" block ;
budget    = "budget" IDENT ( "==" | "<=" | "<" ) ( DURATION | expr ) ;
measure   = "measure" ":" block ;          (* a statement, only inside bench_def *)
untimed   = "untimed" ( ":" block | expr ) ;          (* a statement inside measure, or a prefix expression (section 2.2); its time is not counted *)
(* handle, in both its forms, is defined in section 7.3 *)
CODE      = ( "E" | "W" ) DIGIT DIGIT DIGIT DIGIT ;   (* a diagnostic code, such as E0412 *)
DURATION  = INT ( "ns" | "us" | "ms" | "s" | "min" | "h" ) ;   (* such as 5ms; section 2.1 *)
SIZE      = INT ( "b" | "kib" | "mib" | "gib" ) ;              (* such as 64mib; section 2.1 *)
```

`handle` chooses between its two forms by the token after its expression, `by` or `:`. This is the one place the grammar needs more than two tokens of lookahead; the parser handles it by parsing the expression first.

`test`, `fuzz`, `bench`, `budget`, `measure`, `untimed`, `rejects`, `schedules`, `serial` and `threads` are keywords only in these positions, so they stay usable as names elsewhere.

#### Example tests and assertions

```
fn parse_port*(text: Str) -> Int ! ParseError: ...

test "accepts a valid port":
    assert parse_port("8080") == 8080

test "rejects an out-of-range port":
    assert_fails[ParseError] parse_port("70000")
```

- Test blocks are compiled only by `starnite test`; ordinary builds drop them. A test inside a source file can use that module's private items.
- A test body may perform `io` and fail with any error. A failure that reaches the end of the body fails the test, with the error and its location.
- When `assert e` fails, it prints the value of every subexpression of `e`, so most failures need no extra logging.
- `assert_fails[E] e` passes only if `e` fails with an error of type `E`.
- Every test runs on the debug runtime. When it ends, every object it allocated must have been released and every resource consumed; otherwise it fails with a leak report naming the allocation site.

#### Property tests

```
test "sorting keeps every element" for xs: Array[Int]:
    let ys = sorted(xs)
    assert len(ys) == len(xs)
    assert is_sorted(ys)

test "get returns the element" for xs: Array[Int], i: Int where 0 <= i and i < len(xs):
    assert get(xs, i) == xs[i]
```

1. Inputs come from the `Arbitrary` trait. It is derived automatically for primitives, collections, structs and data types, as `Eq` is (section 3.4). Resource types never derive it; a type can implement it by hand.
2. Inputs start small and grow across cases. The default is 100 cases; `--cases n` changes it.
3. A `where` clause constrains inputs. Linear clauses of the kind section 17.3 allows become direct generators, so no cases are wasted. Other clauses filter, and the test fails with "too few valid inputs" if fewer than 10% of generated inputs pass.
4. A failing case is shrunk automatically: numbers toward 0, collections shorter, data types toward simpler variants. The minimal case and the seed are printed, and `--seed` replays it.
5. Each failing case is saved in `.stn/regressions/` and run first on every later `starnite test` until it passes.

#### Snapshot tests

`assert_snapshot e` formats `e` with `Show` and compares it with `snapshots/<module>/<test>.snap`. The first run writes the file and fails, asking for review. `starnite test --update-snapshots` accepts changes. Snapshot files are meant to be committed.

#### Rejection tests

```
test rejects E0412 "a connection must be closed or abandoned":
    var c = http.connect("example.com")
```

The body must fail to compile with exactly that error code. The test fails if the body compiles or fails with a different code. This is how a library proves that its typestate and resource rules reject misuse. Each body is compiled on its own, so an expected error does not stop the rest of the build.

#### Replacing I/O in tests

Under `starnite test`, the built-in `io` effect is compiled like a user effect (section 7.3) whose default handler performs real I/O. A test can swap in a fake with `handle e by h`:

```
test "get reads the status line":
    let net = test.fake_net({"example.com:80": "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi"})
    let resp = handle http.get("http://example.com/") by net
    assert resp.status == 200
    assert resp.text() == "hi"
```

- The `test` module provides `fake_fs`, `fake_net` (scripted responses), `fake_clock` (time moves only when the test advances it), `fake_env`, and captured standard input and output.
- Randomness is seeded per test. The seed is printed on failure.
- Release and debug builds are unchanged: outside `starnite test`, `io` keeps no run-time representation.
- `handle e by h` also works outside tests, for user effects, where `h` is a value implementing the effect's operations.

#### Schedule tests

```
test "workers drain the queue" schedules 200:
    let (tx, rx) = channel[Int](capacity = 4)
    let a = spawn worker(rx)
    let b = spawn worker(rx)
    for i in range(100): tx.send(i)
    tx.close()
    assert a.join() + b.join() == 100
```

- The body runs 200 times on a deterministic scheduler. Each run chooses a different interleaving at the points where tasks can affect each other: channel operations, lock acquisition, suspension, and task start and join.
- Choices are random from a seed, with a small number of forced task switches per run (3 by default). This follows the probabilistic concurrency testing method, which finds most ordering bugs in few runs (Burckhardt et al., ASPLOS 2010).
- A failing run prints its seed, and `--seed` replays exactly that interleaving.
- If every task is blocked, the test fails as a deadlock and prints where each task is waiting.
- A `par` block without channels or `io` is already deterministic (section 14.4) and needs no schedules.

#### Fuzz tests

```
fuzz "the request parser never traps" for input: Array[U8]:
    let _ = try parse_request(input)
```

- Fuzz targets run only under `starnite fuzz <name> --time 10m`.
- A trap, a leak or a failed assertion is a finding. Errors captured with `try` are expected behaviour.
- Fuzzing is coverage-guided: the generated C is compiled with Clang's fuzzing instrumentation, and inputs are mutated toward new branches.
- Inputs may be of any `Arbitrary` type, not only bytes; the fuzzer mutates a byte stream that the type's generator decodes.
- The corpus lives in `fuzz/<name>/`. Findings are shrunk and copied into `.stn/regressions/`, so `starnite test` reruns them.

#### Integration and doc tests

- Each file in `tests/` is compiled as a separate program that sees only the package's exported names (section 3.5).
- `##` starts a doc comment. An indented `>>>` line in a doc comment is run, and the lines after it are compared with the result formatted by `Show`:

```
## Parses a port number.
##
##     >>> parse_port("443")
##     443
fn parse_port*(text: Str) -> Int ! ParseError: ...
```

#### Running tests

| Command | Does |
| --- | --- |
| `starnite test` | Builds in debug mode and runs every test except fuzz targets |
| `starnite test port` | Runs tests whose name or module contains `port` |
| `starnite test --kind property` | Runs one kind only |
| `starnite test --coverage` | Reports line and branch coverage, using Clang's coverage instrumentation mapped back to `.stn` lines |
| `starnite test --mutate` | Changes operators and constants one at a time and reports each change that no test caught |
| `starnite fuzz <name> --time 10m` | Fuzzes one target |

Thresholds make `starnite test` fail below a bar, locally and in CI:

```
[test]
min-coverage = 80          # lines and branches, percent
min-mutation = 60          # with --mutate
effect-coverage = true     # every effect sink reached by a test
```

The same limits can be given as flags (`--min-coverage 80`). Effect coverage maps each `io` sink in the flow summary (section 3.8.4) to the tests that reach it, and `starnite test --coverage` lists any sink no test reaches. A test that asserts nothing still counts toward line coverage, which is why mutation score is the stronger check: such a test kills no mutants.

- Tests run in parallel across worker processes. Each test runs under supervise (section 14.9), so a trap fails only that test. Tests that call foreign code run in separate worker processes instead, because a crash in C cannot be contained; the runner restarts a worker that dies and reports the crash as that test's failure.
- Tests that use real `io` run alongside others unless marked `serial`.
- Results stream as text, or as objects of kind `test` under `--format=json` (section 19.4).
- The exit status is 0 only if every test passes.

### 20.3 Built-in benchmarking

Status: Specified. Benchmarks are `bench` blocks run by `starnite bench`. They measure time, and also counters that are the same on every machine, so performance can be enforced in CI without flaky timing.

```
bench "parse a 10 MB log" budget allocs <= 1_000:
    let text = read_file("bench/data/access.log")    # setup: not measured
    measure:
        parse_log(text)

bench "sort" for n in [1_000, 100_000, 1_000_000] budget copies == 0:
    let xs = random_ints(n, seed = 1)
    measure:
        var ys = untimed copy(xs)
        sort(mut ys)

bench "word count" threads [1, 2, 4, 8]:
    let chunks = load_chunks("bench/data/access.log")
    measure:
        count_words_parallel(chunks)
```

Rules:

1. Code before `measure` runs once per benchmark and is not measured.
2. The `measure` block is one iteration. The runner warms up for 0.5 s, then runs batches until 3 s have passed or the 95% confidence interval of the median is within 1%. These defaults are configurable.
3. `untimed e` evaluates `e` with the timer and counters paused. Pausing costs a few clock reads, so it suits setup that is large compared with that.
4. The value of the `measure` block, and every variable it reads, passes through an opaque sink, so the C compiler cannot delete or hoist the measured work.
5. `for n in list` runs and reports each value separately, and the runner fits a growth exponent across them, so an accidental quadratic shows up as `n^2`.
6. `threads list` runs once per thread count and reports the speedup relative to one thread.
7. Benchmarks always build in release mode, and their order is shuffled on each run.

#### What is measured

| Measurement | Source | Same on every machine | Best used for |
| --- | --- | --- | --- |
| `time` | Monotonic clock: median and 95% confidence interval per iteration | No | Comparisons on one machine |
| `allocs`, `alloc_bytes` | Allocator counters in the runtime | Yes, for the same compiler version and flags | Hard budgets |
| `copies` | The copy events of section 9.8 | Yes | Hard budgets |
| `count_ops` | `dup` and `drop` operations executed | Yes | Hard budgets; shows how much reuse analysis removed |
| `checks` | Bounds, `ref` and `busy` checks executed | Yes | Hard budgets |
| `peak_heap` | Highest live heap during `measure` | Yes | Hard budgets |
| `instructions`, `cache_misses`, `branch_misses` | Hardware counters, on Linux | Close, but varies by CPU model | Diagnosis |

Counters are compiled in only under `starnite bench` and `starnite test`. Time and counters come from separate runs, so counting never inflates timings.

#### Budgets

- `budget <counter> <op> <value>` applies per iteration. It is checked on every `starnite bench`, and also on every `starnite test`, which runs each `measure` block once with counters on and no timing. So `budget allocs == 0` fails CI as deterministically as an ordinary test.
- A time budget such as `budget time < 5ms` is only a warning unless `--strict-time` is given, because wall-clock time varies between machines.
- Budgets complement `noalloc` and `inplace` (section 9.6). Those prove a single function never allocates; budgets cover whole workloads where a proof is impractical.

#### Tracking regressions

- `starnite bench --save base` writes results, with a machine description (CPU model, core count, OS, compiler version and flags), to `.stn/bench/base.json`.
- `starnite bench --compare base` reruns and compares. A time change counts as a regression only if it exceeds the threshold (3% by default) and a Mann-Whitney U test on the samples gives p < 0.01. Counter changes are exact.
- The exit status is non-zero on any regression, so CI can block a merge. Comparing results from different machines is refused unless `--any-machine` is given.
- The runner pins itself to one core where the OS allows, raises its priority, and warns when CPU frequency scaling is active or the machine is busy.

Example output; the numbers are illustrative, not measured:

```
bench sort  n=1,000       12.4 us ± 0.3%   allocs 0   copies 0   count_ops 0
bench sort  n=100,000     1.92 ms ± 0.5%   allocs 0   copies 0   count_ops 0
bench sort  n=1,000,000   23.8 ms ± 0.4%   allocs 0   copies 0   count_ops 0
            growth ≈ n^1.07
```

#### Profiling

- `starnite bench <name> --profile` runs the benchmark under the system's sampling profiler (`perf` on Linux) and writes folded stacks that flame-graph tools read.
- `--profile=alloc` lists allocation sites by count and bytes; `--profile=copies` lists copy sites by total cost.
- The C emitter writes `#line` directives, so profiles, debuggers and coverage reports point at `.stn` source lines, not generated C.
- Results are also available as objects of kind `bench` under `--format=json`.

## 21. Testing and verification plan

Status: Specified. Soundness of the combined design rests on three things built alongside the compiler: a reference interpreter, a program fuzzer that compares the two, and a formal model of the core.

### 21.1 Reference interpreter

A direct implementation of section 4, in about 2,000 lines: every assignment and argument is a deep copy, nothing is shared, nothing is reused, nothing is freed. It is slow and obviously correct, and it is the executable definition of what a program means.

### 21.2 Program fuzzer

The generator builds well-typed programs by construction: it picks a type, then a production that yields that type, recursively, tracking which variables are live, moved, unique or in which state. It gains productions as each milestone adds features.

| Oracle | A failure means |
| --- | --- |
| The compiler does not crash and the validators of section 8.4 pass | Compiler bug |
| Debug runtime: no access to poisoned memory, counts balance, nothing leaks at exit | Counting or reuse bug |
| Output equals the reference interpreter's | Miscompilation |
| Output is equal with each optional pass on and off (reuse, regions, pass 7, pass 15) | Bug in that pass |
| Parallel programs without `io`: same output single-threaded and under two schedules; thread sanitizer reports nothing | Separation or marking bug |

Once the native backend exists (section 11.7), every generated program is also built with both backends, and their outputs must match bit for bit.

Negative fuzzing: take a well-typed program, apply one mutation with a known violation (use a value after `take`, delete a `close`, add a second writer to a `par`), and require the compiler to reject it with the expected error family.

Failing programs are shrunk automatically by deleting statements and simplifying expressions while the failure persists.

### 21.3 Test corpus

- One golden test per error code: source, expected code and location, in both text and JSON form. The JSON form is validated against the published schema.
- One golden test per row of each rule table in sections 4, 6, 9 and 14.
- The standard library's own tests.
- The spec's own examples, including Appendix A, as end-to-end programs.

### 21.4 Formal model

A core calculus with values, `mut` and `take`, data types, `match`, and the `dup`/`drop`/reuse instructions, written in a proof assistant. Targets, in order:

| # | Property | Prior result to build on |
| --- | --- | --- |
| P1 | Counted programs never release a reachable object, and release everything by exit | Proven for the Perceus core calculus |
| P2 | Reuse and destination passing preserve the meaning given by the reference semantics | Stated informally in prior work; new here |
| P3 | Resource values are consumed exactly once, including under `with` and failure | Standard for linear type systems |
| P4 | Rules 1 to 6 of section 15.4 over-approximate what a closure can reach | Mechanized proofs exist for the fuller published calculi |

Before any proof is attempted, each property is first tested by random generation inside the model. That finds most specification errors at a small fraction of the cost.

### 21.5 Benchmarks and gates

Targets are proposals, relative to the same algorithm in C compiled with `-O2`.

| Milestone | Benchmark | Target |
| --- | --- | --- |
| 1 | `centroid`, n-body, spectral norm, Mandelbrot | At most 1.1x C time |
| 2 | List `map`; red-black tree insertion; binary trees | Zero allocations for `map`; at most 1.5x C time for the others |
| 3 | Tokenizer and parser over a 10 MB input | One bulk release per call; at most 1.3x C time |
| 4 | Line-by-line file copy with `with` | No leaked handles under fault injection |
| 5 | Breadth-first search over a `Pool` graph | At most 1.5x C time; zero `ref` checks left in the read-only loop |
| 6 | Parallel word count, 8 cores | At least 5x the single-thread speed |
| 7 | Closure-heavy event loop | At least 90% of `busy` checks removed |
| 8 | Whole suite | Section 16.6 exit test |

For the native backend (section 11.7), each benchmark is compared with two C baselines:

| Baseline | What it is | Built with |
| --- | --- | --- |
| Typical C | The straightforward version a competent C programmer writes: `malloc` and `free`, `qsort`, `printf` and `strtod`, no `restrict`, no intrinsics | `-O2`, baseline CPU |
| Tuned C | The fastest known C for the same algorithm: custom allocators, `restrict`, inlined comparisons, intrinsics allowed | `-O3` with the same CPU target as the build it is compared against |

Fairness rules: both sides use the same algorithm, machine and CPU target. Each C version is built with both GCC and Clang, and the faster result counts. Every published result includes the C sources, compiler versions and flags.

Native-backend gates, proposed and applying from step 4 of section 11.7:

| Benchmark | Against typical C | Against tuned C |
| --- | --- | --- |
| Binary trees | At least 1.2 times faster | At most 1.1 times slower |
| Sorting structs with a comparison function | At least 1.2 times faster | At most 1.1 times slower |
| Formatting and parsing 1 million floats | At least 1.2 times faster | At most 1.1 times slower |
| N-body, spectral norm | At most 1.05 times slower | At most 1.2 times slower |
| Mandelbrot, matrix multiply | At least equal | At most 1.1 times slower |

A speed claim in release notes or documentation is made only for benchmarks that pass these gates, and names the baseline it is against.

### 21.6 Continuous checks

Every commit: all tests, plus ten minutes of fuzzing. Nightly: eight hours of fuzzing across all build modes, the benchmark suite, and a comparison against the previous night's numbers.

## 22. Milestones and open issues

Eleven milestones, plus the native backend as milestone 12. Milestones 1 to 8 each end in a gate from section 21.5, 9 to 11 in the checks listed in their rows (for milestone 9: the solver discharges every where clause in the spec's examples), and 12 in the native-backend gates of section 21.5; milestones 1 and 2 alone are enough to test the central claim of C-like speed with Python-like code.

### 22.1 Milestones

| # | Deliverable | Spec sections | Also built |
| --- | --- | --- | --- |
| 1 | Parser, type checker, structs, data types, generics, traits, trait values, projections, `mut` and `take`, errors as effects, naive counting, C output | 2, 3.1 to 3.5, 3.6 (Array and Str only), 4, 5, 6.1, 7.1, 7.2, 8 (passes 1 to 6, 10, 11, 13 naive, 16), 11.1 to 11.6, 13, 17.1 | Reference interpreter, fuzzer, debug runtime; example tests, assert and the test runner |
| 2 | Counting insertion, reuse, destination passing, uniqueness, `inplace`, `noalloc`, copy reporting, collections and comprehensions | 3.6, 6.2, 9 | Formal model with P1 and P2 tested; property, snapshot and doc tests; benchmarks with counters and budgets |
| 3 | Escape analysis, stack and region placement, allocator passing, `local` | 10 |  |
| 4 | Resource types, typestate, `with`, built-in and user effects, resuming and aborting handlers, foreign functions | 6.3 to 6.5, 7 (except 7.5's evented backend), 18 | P3 tested; I/O fakes, rejection tests, fuzz targets |
| 5 | `Pool`, `Ref`, check removal, interval analysis, fixed-size arrays `Array[T, N]` | 3.6, 12, 17.1, 17.2 |  |
| 6 | `iso`, `frozen`, marking, `par`, tasks, channels, mutexes with levels, suspending handlers and async, the I/O reactor | 7.3, 7.5's evented backend, 14 | Thread-sanitizer runs; schedule tests, thread-scaling benchmarks |
| 7 | Reachability inference, stages R1 to R4 | 13.3, 15 | P4 tested |
| 8 | ASAP stage A, then B if A passes its exit test | 16 | Shadow-count verifier |
| 9 | `where` clauses with the solver, `total fn` | 17.3, 17.4 |  |
| 10 | Package manager and registry: manifest, resolution, lock file, capability and flow summaries, upgrade checks (including that a new variant in an exported type not marked open is a major change), publishing, registry test requirements, automated review stage 1 | 3.8, 5.5 | Behaviour-diff sandbox, red-team package set |
| 11 | Formatter, language server, documentation tool; automated review stages 2 and 3 once labelled quarantines exist | 3.8.7, 19.5 | Published precision and recall for each model version |
| 12 | Native backend, in the four steps of section 11.7; then freestanding targets | 11.7, 11.8 | Native-backend gates of section 21.5 |

Milestone 1 builds a correct, slow compiler before the optimizing passes exist:

- **Naive counting:** every copy of a counted value becomes a `dup` and every last use a `drop`, with no borrowing inference, reuse, elision or destination passing (section 9 with none of its optimizations). Milestone 2 replaces it.
- **Passes:** milestone 1 runs passes 1, 2, 3, 4, 5, 6, 10, 11, 13 (naive) and 16. Passes 2a, 5a, 7 to 9, 10a, 11a to 11c, 12, 14 and 15 arrive with the milestones of the sections they implement; until then their checks are skipped and nothing else changes.
- **Library:** `array` and `str` are runtime built-ins written in C until milestone 4 brings `trusted fn` and `extern`. `for x in xs` over an array or a range is built-in iteration until local iterators (section 10.5) arrive in milestone 3.
- **Overflow:** the overflow traps and the wrapping operators of section 17.1 are in milestone 1; the rest of section 17 is not.
- **Before effects (milestone 4):** `print` and `read_line` are built-in functions with the `io` effect recorded in signatures but no handlers. Error effects, `fail` and `try` are in milestone 1, so 7.1 and 7.2's inference and effect polymorphism are too.
- **Before `supervise` (milestone 6):** each test runs in its own process, so a trap fails only that test.

Automatic sharing (section 13) arrives with closures in milestone 1, with all `busy` checks kept until milestone 7 removes them.

Fixed-order reductions (section 14.4) join milestone 6. Postconditions, type invariants and strict mode (sections 17.5 and 17.6) join milestone 9. Milestone 12, after self-hosting, is the native backend (section 11.7), built in the four steps listed there.

Policy rules and the lock file (section 17.7) join milestone 4, once effects and allocation facts exist. Law rules join milestone 9, with the solver.

Platform ports, the package manifest and named foreign libraries (sections 3.7 and 18.1) join milestone 4, with foreign functions.

Supervision (section 14.9) joins milestone 6. The unused-effect warning (section 7.2) and visible trusted code (section 18.5) join milestone 4. Freestanding targets (section 11.8) follow milestone 12.

### 22.2 Open issues

| # | Issue | Why it is open |
| --- | --- | --- |
| 1 | Language the compiler is written in | Resolved: OCaml for the bootstrap compiler. Self-hosting in Starnite can follow milestone 4. |
| 2 | Confining a trap to one task | Resolved by supervise, section 14.9. |
| 3 | User-defined projections | Resolved by `lend` functions, section 4.6. |
| 4 | Dynamic dispatch | Resolved by trait values (`any T`), section 3.4. |
| 5 | Invisible exits | Resolved: no marker; editor hints, `--explain-exits` and an optional lint, section 5.4. |
| 6 | `abandon` in every state | Resolved by derived `abandon` and `NoAbandon` states, section 6.3. |
| 7 | Postconditions and invariants | Resolved by section 17.5. |
| 8 | Event-driven I/O | Resolved: a reactor per worker, section 14.8. |
| 9 | Small-string optimization; cost of ordered maps | Resolved: inline strings up to 15 bytes, compact insertion-ordered maps, section 3.6. |
| 10 | Tooling: build tool, formatter, editor support, package manager | Resolved: one `starnite` command (section 19.5), packages in section 3.8. |
| 11 | Name | Resolved: Starnite (starnite.dev), command starnite, file extension .stn. |

### 22.3 Interactions to fuzz first

These pairs have no precedent in a shipped language and are the likeliest sources of soundness bugs:

- reuse with thread-shared marking: the uniqueness test must be an atomic read once `STN_ATOMIC` is set;
- regions with suspending functions: a region must not be released while a suspended frame still points into it;
- uniqueness with shared cells: a value read out of a cell is never unique;
- `with` and typestate with failure inside `par` branches;
- allocator passing with reuse tokens from a different allocator.

## 23. References

Reachability types, found by search for this project (abstracts and summaries read, not the full papers):

- [Polymorphic Reachability Types (POPL 2024)](https://arxiv.org/pdf/2307.13844)
- [Complete the Cycle: Reachability Types with Expressive Cyclic References (OOPSLA 2025)](https://dl.acm.org/doi/10.1145/3763172)
- [Escape with Your Self: Bidirectional Typing with Avoidance for Reachability Types (PLDI 2026)](https://arxiv.org/pdf/2404.08217)
- [Reachability Types with Flow-Sensitive Effects for Deallocation and Ownership Transfer](https://arxiv.org/html/2510.08939)
- [When Lifetimes Liberate: A Type System for Arenas with Higher-Order Reachability Tracking (OOPSLA 2026)](https://arxiv.org/pdf/2509.04253)
- [Mechanized proofs and the Diamond prototype](https://github.com/TiarkRompf/reachability)

Cited from memory, not re-checked for this draft; verify before relying on details:

- Reinking, Xie, de Moura, Leijen: Perceus, reference counting with reuse (PLDI 2021).
- Ullrich and de Moura: Counting Immutable Beans, Lean 4's borrow inference (IFL 2019).
- Lorenzen, Leijen and others: fully in-place functional programming, Koka's `fip` (ICFP 2023).
- Leijen and Lorenzen: tail recursion modulo context (POPL 2023).
- Racordon and others: mutable value semantics, the Hylo language (2022).
- Proust: As Static As Possible memory management (PhD thesis, Cambridge, 2017).
- Tofte and Talpin: region-based memory management (1997).
- Clebsch and others: reference capabilities in Pony (2015); Microsoft Research's Project Verona.
- Ovadia: generational references, the Vale language.
- Maranget: warnings for pattern matching (2007).
- Jane Street: modes for locality and uniqueness in OxCaml.

## Appendix A. Worked example: an HTTP client

A complete small library using data types, defaults, comprehensions, resources, typestate, `with`, and errors as effects.

```
# net/http.stn
import net.tcp

type Method* = Get | Post | Put | Delete

type Request* = struct(
    method: Method,
    url: Url,
    headers: Map[Str, Str] = {},
    body: Array[U8] = [])

type Response* = struct(status: Int, headers: Map[Str, Str], body: Array[U8])

open type HttpError* = BadUrl(Str) | Net(IoError) | Protocol(Str)

impl From[IoError] for HttpError:
    fn from(e: IoError) -> HttpError: Net(e)

impl From[ParseError] for HttpError:
    fn from(e: ParseError) -> HttpError: Protocol(e.message)

# A connection is Idle, or has Sent a request and awaits the response.
resource type Conn*[S] = struct(sock: Socket[Connected], buf: Array[U8])

fn connect*(host: Str, port: Int = 80) -> Conn[Idle] ! io.net, HttpError:
    with s = socket():
        tcp.connect(mut s, Addr(host, port))
        Conn(s, [])                          # s moves into the connection

fn send*(mut c: Conn[Idle -> Sent], req: Request) ! io.net, HttpError:
    let lines = [f"{name}: {value}" for (name, value) in req.headers]
    let head = f"{req.method} {req.url.path} HTTP/1.1\r\nHost: {req.url.host}\r\n"
             + "\r\n".join(lines)
             + f"\r\nContent-Length: {len(req.body)}\r\n\r\n"
    tcp.send(mut c.sock, head.bytes())
    tcp.send(mut c.sock, req.body)

fn receive*(mut c: Conn[Sent -> Idle]) -> Response ! io.net, HttpError:
    let (status, headers) = parse_head(read_until(mut c, "\r\n\r\n"))
    let n = parse_int(headers.get("content-length").or("0"))
    Response(status, headers, read_exact(mut c, n))

fn close*(take c: Conn[Idle]) ! io.net:
    let Conn(sock, _) = c
    tcp.close(sock)

impl[S] Abandon for Conn[S]:
    fn abandon(take self: Conn[S]):
        let Conn(sock, _) = self
        tcp.abandon(sock)

fn request*(req: Request) -> Response ! io.net, HttpError:
    with c = connect(req.url.host, req.url.port):
        send(mut c, req)
        receive(mut c)

fn get*(url: Str) -> Response ! io.net, HttpError:
    request(Request(Get, Url.parse(url)))
```

Three private helpers are omitted for length: `read_until(mut c, delim)` reads into `c.buf` until `delim` and returns the bytes before it; `read_exact(mut c, n)` returns exactly `n` bytes; `parse_head(bytes)` parses the status line and headers, lower-casing header names, and fails with `ParseError`.

Using it:

```
import net.http

fn main() ! io, HttpError:
    let resp = http.get("http://example.com/users.json")
    print(resp.text())

    let urls = [f"http://example.com/page/{i}" for i in range(1, 9)]
    let sizes = par_map(urls, fn(u): len(http.get(u).body))
    print(f"total bytes: {sum(sizes)}")
```

What the compiler checks here, with no extra code from the author:

- `receive` before `send`, or two `send`s in a row, is a type error.
- Every connection is closed or abandoned on every path, including each failing call inside `request`.
- `get` cannot be called from a function that does not allow `io` and `HttpError`.
- The eight downloads run in parallel with no shared mutable state; `urls` is marked thread-shared once.

A state change such as `Idle -> Sent` is declared by the function's author and trusted by callers; the compiler does not derive it from the body.
