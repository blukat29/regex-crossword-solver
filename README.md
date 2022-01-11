# regex-crossword-solver

[Regex Crossword](https://regexcrossword.com/) solver written in Python. Runs in both Python 2 and 3.

It solves a puzzle by converting the puzzle into equivalent SMT problem. Detailed method is described [here](http://blukat29.github.io/2016/01/regex-crossword-solver/).

### Demo

5 x 14 regex crossword posted in [BBC Radio 4 Puzzle for Today](http://www.bbc.co.uk/programmes/articles/5LCB3rN2dWLqsmGMy5KYtBf/puzzle-for-today).

```
$ python bbc.py
```

### Requirements

- [PLY (Python Lex-Yacc)](https://github.com/dabeaz/ply)
- [Z3](https://github.com/Z3Prover/z3) with Python bindings OR [angr-z3](https://github.com/angr/angr-z3)

You can install them by

```
pip install ply z3-solver
```

Make sure you have `/usr/local/lib/` and `$HOME/.local/lib` in `LD_LIBRARY_PATH` environment variable.

### Usage

Solve Regex Crossword puzzle directly.

```py
>>> from crossword import solve_crossword
>>> solve_crossword(["HE|LL|O+","[PLEASE]+"], ["[^SPEAK]+","EP|IP|EF"])
[['H', 'E'], ['L', 'P']]
>>> solve_crossword(["[A-GN-Z]+"], ["[D-HJ-M]","[^A-RU-Z]"], ["[^A-DI-S]+"], ["[^F-KM-Z]","[A-KS-V]"])
[['E', 'T']]
```

You can also manually find a solution to each regex.

```py
>>> from crossword import solve_regex
>>> solve_regex("(U|O|I)*T[FRO]+", 5)
'IIITF'
```

### Run tests

```
pip install nose
nosetests
```

