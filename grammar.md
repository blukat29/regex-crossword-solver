
Regular expression grammar

Lexer design:

```
NON_META_CHAR : [A-Za-z :/']
DIGIT : [0-9]
```

Grammar

```
regex : term
      | term "|" regex

term : factor
     | factor term

factor : NON_META_CHAR
       | DIGIT
       | "(" regex ")"
       | factor "*"
       | factor "+"
       | factor "?"
       | "."
       | "\" DIGIT
       | set
       | "-" | ","
       | "\." | "\*" | "\+" | "\?"
       | "\|" | "\(" | "\)" | "\[" | "\]"
       | "\^" | "\{" | "\}" | "\\"
       | factor "{" number "}"
       | factor "{" number "," "}"
       | factor "{" number "," number "}"

set : "[" set_items "]"
    | "[" "^" set_items "]"

set_items : set_item
          | set_item set_items

set_item : set_non_meta_char
         | set_non_meta_char "-" set_non_meta_char
         | "\[" | "\]" | "\^" | "\-" | "\\"

set_non_meta_char : NON_META_CHAR
                  | DIGIT
                  | "|" | "*" | "+" | "?"
                  | "." | "(" | ")" | ","
                  | "{" | "}"

number : DIGIT
       | DIGIT number
```

