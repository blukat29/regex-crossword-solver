# regex-crossword-solver

[Regex Crossword](https://regexcrossword.com/) solver written in Python.

It solves a puzzle by converting the puzzle into equivalent SMT problem. Detailed method is described [here](http://blukat29.github.io/2016/01/regex-crossword-solver/).

### Requirements

- [PLY (Python Lex-Yacc)](https://github.com/dabeaz/ply)
- [Z3](https://github.com/Z3Prover/z3) with Python bindings

### Usage

Solve Regex Crossword puzzle directly.

```
>>> from crossword import solve_crossword
Generating LALR tables
>>> solve_crossword(["HE|LL|O+","[PLEASE]+"], ["[^SPEAK]+","EP|IP|EF"])
[['H', 'E'], ['L', 'P']]
>>> solve_crossword(["[A-GN-Z]+"], ["[D-HJ-M]","[^A-RU-Z]"], ["[^A-DI-S]+"], ["[^F-KM-Z]","[A-KS-V]"])
[['E', 'T']]
```

You can also manually find a solution to each regex.

```py
import z3
from crossword import RegexSolver

L = 7
unknowns = []
for i in range(L):
    unknowns.append(z3.Int("x_%02d" % i))

expr = RegexSolver(L, "[SALT]+O(\sB|S,|E,)+[F\s]", unknowns).sat_expr()
solver = z3.Solver()
solver.add(expr)
print solver.check()
answer = solver.model()
for i in range(L):
    print chr(answer[unknowns[i]].as_long()),
```

```
sat
T L T O E , F
```

### Run tests

```
nosetests
```

