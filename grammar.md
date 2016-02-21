
Regular expression grammar

```
NON_META_CHAR : [A-Za-z :/']
SPECIAL_CHAR : .*+|()[]{},-^\:'!
DIGIT : [0-9]
CHARACTER_CLASS : [sd]

regex : outer_term
      | outer_term "|" regex

outer_term : term
           | "^" term
           | term "$"
           | "^" term "$"

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
       | factor "{" number "}"
       | factor "{" number "," "}"
       | factor "{" number "," number "}"
       | "\" SPECIAL_CHAR
       | "\" CHARACTER_CLASS

set : "[" set_items "]"
    | "[" "^" set_items "]"

set_items : set_item
          | set_item set_items

set_item : set_non_meta_char
         | set_non_meta_char "-" set_non_meta_char
         | "\" SPECIAL_CHAR
         | "\" CHARACTER_CLASS

set_non_meta_char : NON_META_CHAR
                  | DIGIT
                  | "." | "*" | "+" | "?"
                  | "|" | "(" | ")" | ","
                  | "{" | "}"

number : DIGIT
       | DIGIT number
```

