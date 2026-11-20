#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Differential program fuzzer (section 21.2), first cut.

Builds well-typed programs by construction: it picks a type, then a production that
yields that type, tracking which variables are live and mutable. Each program runs on
the reference interpreter and on the debug C build; the outputs and exit statuses must
match, and the debug runtime must report balanced counts.

    tests/fuzz.py [--count N] [--seed S] [--keep DIR]
"""
import argparse, os, random, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STARNITE = os.environ.get("STARNITE", os.path.join(ROOT, "_build", "default", "compiler", "main.exe"))

TYPES = ["Int", "Bool", "Str", "Array[Int]", "Pair", "Shape", "Int?"]

PRELUDE = """fn no_int() -> Int?:
    None

fn no_ints() -> Array[Int]:
    []

type Pair = struct(a: Int, b: Str)
type Shape = Dot | Box(w: Int, h: Int) | Named(name: Str, inner: Array[Int])

impl Show for Pair:
    fn show(p: Pair) -> Str:
        f"Pair({p.a}, {p.b})"

impl Show for Shape:
    fn show(s: Shape) -> Str:
        match s:
            Dot -> "Dot"
            Box(w, h) -> f"Box({w}, {h})"
            Named(n, xs) -> f"Named({n}, {xs})"
"""


class Gen:
    def __init__(self, rng):
        self.r = rng
        self.scopes = [[]]          # (name, type, mutable)
        self.n = 0
        self.fns = []               # (name, param types, return type)

    def fresh(self, p="v"):
        self.n += 1
        return f"{p}{self.n}"

    def vars_of(self, t, mutable=None):
        out = []
        for sc in self.scopes:
            for (n, ty, m) in sc:
                if ty == t and (mutable is None or m == mutable):
                    out.append(n)
        return out

    # ---- expressions ----
    def expr(self, t, d):
        r = self.r
        vs = self.vars_of(t)
        if vs and r.random() < 0.45:
            return r.choice(vs)
        if d <= 0:
            return self.leaf(t)
        if t == "Int":
            k = r.randrange(9)
            if k == 0: return f"({self.expr('Int', d-1)} +% {self.expr('Int', d-1)})"
            if k == 1: return f"({self.expr('Int', d-1)} -% {self.expr('Int', d-1)})"
            if k == 2: return f"({self.expr('Int', d-1)} *% {self.small()})"
            if k == 3: return f"len({self.expr('Array[Int]', d-1)})"
            if k == 4: return f"len({self.expr('Str', d-1)})"
            if k == 5: return f"(if {self.expr('Bool', d-1)}: {self.expr('Int', d-1)} else: {self.expr('Int', d-1)})"
            if k == 6: return f"{self.expr('Pair', d-1)}.a"
            if k == 7: return f"({self.expr('Int?', d-1)}).or({self.small()})"
            fn = [f for f in self.fns if f[2] == "Int"]
            if fn:
                name, ps, _ = r.choice(fn)
                return f"{name}({', '.join(self.expr(p, d-1) for p in ps)})"
            return self.leaf(t)
        if t == "Bool":
            k = r.randrange(5)
            if k == 0: return f"({self.expr('Int', d-1)} < {self.expr('Int', d-1)})"
            if k == 1: return f"({self.expr('Str', d-1)} == {self.expr('Str', d-1)})"
            if k == 2: return f"({self.expr('Bool', d-1)} and {self.expr('Bool', d-1)})"
            if k == 3: return f"(not {self.expr('Bool', d-1)})"
            return f"({self.expr('Array[Int]', d-1)} == {self.expr('Array[Int]', d-1)})"
        if t == "Str":
            k = r.randrange(4)
            if k == 0: return f"({self.expr('Str', d-1)} + {self.expr('Str', d-1)})"
            if k == 1: return f'f"<{{{self.expr("Int", d-1)}}}|{{{self.expr(r.choice(TYPES), d-1)}}}>"'
            if k == 2: return f"{self.expr('Pair', d-1)}.b"
            return f'join(["x", {self.expr("Str", d-1)}], "-")'
        if t == "Array[Int]":
            k = r.randrange(4)
            if k == 0: return "[" + ", ".join(self.expr("Int", d-1) for _ in range(r.randrange(1, 4))) + "]"
            if k == 1: return f"[x +% {self.small()} for x in {self.expr('Array[Int]', d-1)}]"
            if k == 2: return f"[i *% i for i in 0..{r.randrange(6)}]"
            return f"filled({r.randrange(4)}, {self.expr('Int', d-1)})"
        if t == "Pair":
            return f"Pair({self.expr('Int', d-1)}, {self.expr('Str', d-1)})"
        if t == "Shape":
            k = r.randrange(3)
            if k == 0: return "Dot"
            if k == 1: return f"Box({self.expr('Int', d-1)}, {self.expr('Int', d-1)})"
            return f"Named({self.expr('Str', d-1)}, {self.expr('Array[Int]', d-1)})"
        if t == "Int?":
            return f"Some({self.expr('Int', d-1)})" if r.random() < 0.6 else "no_int()"
        raise ValueError(t)

    def small(self):
        return str(self.r.randrange(-5, 6)) if self.r.random() < 0.8 else str(self.r.choice([2**31, 2**62, -2**40]))

    def leaf(self, t):
        r = self.r
        return {
            "Int": self.small(),
            "Bool": r.choice(["true", "false"]),
            "Str": r.choice(['"a"', '"bc"', '""', '"héllo"', '"0123456789abcdef"']),
            "Array[Int]": r.choice(["no_ints()", "[1]", "[3, 1, 2]"]),
            "Pair": 'Pair(0, "p")',
            "Shape": "Dot",
            "Int?": "no_int()",
        }[t]

    # ---- statements ----
    def stmts(self, ind, k, d):
        out = []
        for _ in range(k):
            out += self.stmt(ind, d)
        return out

    def stmt(self, ind, d):
        r = self.r
        p = "    " * ind
        k = r.randrange(10)
        if k <= 1 or d <= 0:
            t = r.choice(TYPES)
            n = self.fresh()
            mut = r.random() < 0.5
            line = f"{p}{'var' if mut else 'let'} {n}: {t} = {self.expr(t, 3)}"
            self.scopes[-1].append((n, t, mut))
            return [line]
        if k == 2:
            t = r.choice(TYPES)
            vs = self.vars_of(t, True)
            if vs:
                return [f"{p}{r.choice(vs)} = {self.expr(t, 3)}"]
        if k == 3:
            vs = self.vars_of("Array[Int]", True)
            if vs:
                v = r.choice(vs)
                c = r.randrange(4)
                if c == 0: return [f"{p}{v}.push({self.expr('Int', 2)})"]
                if c == 1: return [f"{p}if len({v}) > 0:", f"{p}    {v}[0] = {self.expr('Int', 2)}"]
                if c == 2: return [f"{p}sort(mut {v})"]
                return [f"{p}let {self.fresh()} = {v}.pop()"]
        if k == 4:
            return [f"{p}print({self.expr('Str', 3)})"]
        if k == 5:
            t = r.choice(TYPES)
            return [f'{p}print(f"{{{self.expr(t, 3)}}}")']
        if k == 6:
            out = [f"{p}if {self.expr('Bool', 2)}:"]
            self.scopes.append([])
            out += self.stmts(ind + 1, r.randrange(1, 3), d - 1)
            self.scopes.pop()
            out.append(f"{p}else:")
            self.scopes.append([])
            out += self.stmts(ind + 1, r.randrange(1, 3), d - 1)
            self.scopes.pop()
            return out
        if k == 7:
            n = self.fresh("i")
            out = [f"{p}for {n} in {self.expr('Array[Int]', 2)}:"]
            self.scopes.append([(n, "Int", False)])
            out += self.stmts(ind + 1, r.randrange(1, 3), d - 1)
            self.scopes.pop()
            return out
        if k == 8:
            out = [f"{p}match {self.expr('Shape', 2)}:"]
            for pat, binds in [("Dot", []), ("Box(w, h)", [("w", "Int"), ("h", "Int")]),
                               ("Named(nm, xs)", [("nm", "Str"), ("xs", "Array[Int]")])]:
                out.append(f"{p}    {pat} ->")
                self.scopes.append([(b, t, False) for b, t in binds])
                out += self.stmts(ind + 2, 1, d - 1)
                self.scopes.pop()
            return out
        if k == 9:
            vs = self.vars_of("Int", True)
            if vs:
                v = r.choice(vs)
                return [f"{p}var {self.fresh('c')} = 0", f"{p}while {v} > 0 and {v} < 50:", f"{p}    {v} = {v} +% 7"]
        return [f"{p}print({self.leaf('Str')})"]

    def program(self):
        out = [PRELUDE]
        for _ in range(self.r.randrange(0, 3)):
            name = self.fresh("f")
            ps = [self.r.choice(["Int", "Str", "Array[Int]"]) for _ in range(self.r.randrange(0, 3))]
            saved = self.scopes
            self.scopes = [[(f"p{i}", t, False) for i, t in enumerate(ps)]]
            body = self.stmts(1, self.r.randrange(0, 3), 1)
            ret = self.expr("Int", 3)
            self.scopes = saved
            out.append(f"fn {name}({', '.join(f'p{i}: {t}' for i, t in enumerate(ps))}) -> Int:")
            out += body
            out.append(f"    ({ret})")
            out.append("")
            self.fns.append((name, ps, "Int"))
        out.append("fn main():")
        out += self.stmts(1, self.r.randrange(3, 12), 3)
        out.append('    print("end")')
        return "\n".join(out) + "\n"


def run(args, path):
    p = subprocess.run([STARNITE] + args + [path], capture_output=True, text=True, timeout=120)
    return p.returncode, p.stdout + p.stderr


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=50)
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--keep", default=None, help="directory to save failing programs in")
    a = ap.parse_args()
    seed = a.seed if a.seed is not None else random.randrange(1 << 30)
    print(f"seed {seed}")
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        for i in range(a.count):
            prog = Gen(random.Random(seed + i)).program()
            path = os.path.join(tmp, f"fuzz{i}.stn")
            with open(path, "w") as f:
                f.write(prog)
            ci, oi = run(["check"], path)
            if ci != 0:
                failures += 1
                print(f"case {seed + i}: the generator produced a program the checker rejects:\n{oi}")
            else:
                ri, out_i = run(["run", "--interp"], path)
                rc, out_c = run(["run"], path)
                if ri != rc or out_i != out_c:
                    failures += 1
                    print(f"case {seed + i}: interpreter (exit {ri}) and C (exit {rc}) differ")
                    for l1, l2 in zip(out_i.splitlines(), out_c.splitlines()):
                        if l1 != l2:
                            print(f"  interp: {l1}\n  c:      {l2}")
                            break
                    else:
                        print(f"  interp tail: {out_i[-200:]!r}\n  c tail:      {out_c[-200:]!r}")
                else:
                    continue
            if a.keep:
                os.makedirs(a.keep, exist_ok=True)
                with open(os.path.join(a.keep, f"case{seed + i}.stn"), "w") as f:
                    f.write(prog)
    print(f"{a.count - failures} of {a.count} agreed")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
