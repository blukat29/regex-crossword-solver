
Regular expression grammar

Lexer design:

```
CHAR : [A-Za-z\s:/']
DIGIT : [0-9]
```

Grammar

```
regex : expr

expr : expr expr
     | "(" expr ")"
     | expr "*"
     | expr "+"
     | expr "?"
     | expr "{" inbrace "}"
     | "[" inbracket "]"
     | "."
     | "\" DIGIT
     | "\." | "\*" | "\(" | "\)" | "\+" | "\?" | "\{" | "\}"
     | "\[" | "\]" | "\\" | "\^" | "-" | ","
     | expr "|" expr
     | CHAR
     | DIGIT
     | (empty)

inbrace : number
        | number COMMA
        | number COMMA number

number : DIGIT number
       | (empty)

inbracket : CARET inbracket_nocaret
          | inbracket_nocaret

inbracket_nocaret : CHAR inbracket_nocaret
                  | DIGIT inbracket_nocaret
                  | "\-" inbracket_nocaret
                  | "\^" inbracket_nocaret
                  | CHAR "-" CHAR inbracket_nocaret
                  | DIGIT "-" DIGIT inbracket_nocaret
```

Precedence

```
(high to low)
escape: \
group and character set: [], ()
quantifiers: *, +, ?, {}
concat
characters and dot: DIGIT, ., CHAR
cases: |
```

