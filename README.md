# regex-crossword-solver

[Regex Crossword](https://regexcrossword.com/) solver written in Python.

It solves a puzzle by converting the puzzle into equivalent SMT problem.

### Requirements

- [PLY](https://github.com/dabeaz/ply)
- [Z3](https://github.com/Z3Prover/z3)

### Usage

```
>>> import crossword
>>> crossword.solve_crossword(["HE|LL|O+","[PLEASE]+"], ["[^SPEAK]+","EP|IP|EF"])
[['H', 'E'], ['L', 'P']]
```

Works well with syntaxes like `[A-Z]`, `[^ABC]`, `{m,n}`, `+`, `?`, `|`, `\1`. Can solve puzzles with backreferences.

Cannot handle special characters (`,`,`-`,`^`,`'`) when they are not part of bracket syntax (`[^A-F]`) nor brace syntax (`{2,3}`).

### Run tests

```
nosetests
```

### How it works

Please refer to [this post](http://blukat29.github.io/2016/01/regex-crossword-solver/).

