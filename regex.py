import ply.lex as lex
import ply.yacc as yacc
import string

[CHAR, DOT, STAR, BAR, CONCAT] = range(5)
CHARSET = string.lowercase + string.uppercase + string.digits + ' '

class RegexLexer:
    tokens = (
        "CHAR", "DOT",
        "STAR", "BAR",
        "LPAREN", "RPAREN",
        "LBRACKET", "RBRACKET", "DASH", "CARET",
    )
    def t_CHAR(self, t):
        r"[0-9a-zA-Z\s]"
        return t;
    t_DOT = r"\."
    t_STAR = r"\*"
    t_BAR = r"\|"
    t_LPAREN = r"\("
    t_RPAREN = r"\)"
    t_LBRACKET = r"\["
    t_RBRACKET = r"\]"
    t_DASH = r"\-"
    t_CARET = r"\^"
    def t_error(self, t):
        print "Error parsing '%s'" % t.value[0]
    def __init__(self):
        self.lexer = lex.lex(module=self)

class RegexParser:
    precedence = (
        ('left', 'BAR'),
        ('left', 'DOT', 'CHAR'),
        ('left', 'CONCAT'),
        ('right', 'STAR'),
    )
    def p_regex_expr(self, p):
        """regex : expr"""
        p[0] = p[1]
    def p_expr_group(self, p):
        """expr : LPAREN expr RPAREN"""
        p[0] = p[2]
    def p_expr_star(self, p):
        """expr : expr STAR"""
        p[0] = (STAR, p[1])
    def p_expr_concat(self, p):
        """expr : expr expr %prec CONCAT"""
        p[0] = (CONCAT, p[1], p[2])
    def p_expr_dot(self, p):
        """expr : DOT"""
        p[0] = (DOT,)
    def p_expr_char(self, p):
        """expr : CHAR"""
        p[0] = (CHAR, p[1])
    def p_expr_or(self, p):
        """expr : expr BAR expr"""
        p[0] = (BAR, p[1], p[3])

    def p_expr_bracket(self, p):
        """expr : LBRACKET inbracket RBRACKET"""
        expr = p[2]

        if expr[0] == '^':
            negate = True
            expr = expr[1:]
        else:
            negate = False

        s = set()
        pos = 0
        while pos < len(expr):
            if expr[pos] == '-':
                for ch in range(ord(expr[pos-1]), ord(expr[pos+1])+1):
                    s.add(chr(ch))
            else:
                s.add(expr[pos])
            pos += 1
        if negate:
            s = set(set(CHARSET) - s)

        s = map(lambda x: (CHAR, x), list(s))
        p[0] = reduce(lambda x, y: (BAR, x, y), s)

    def p_inbracket_single(self, p):
        """
        inbracket : CHAR inbracket
                  | DASH inbracket
                  | CARET inbracket
        """
        p[0] = p[1] + p[2]
    def p_inbracket_empty(self, p):
        """inbracket : """
        p[0] = ""

    def p_error(self, p):
        print "Parse error at '%s'" % p.value
    def __init__(self):
        self.lexer = RegexLexer()
        self.tokens = self.lexer.tokens
        self.parser = yacc.yacc(module=self)
    def parse(self, data):
        return self.parser.parse(data, self.lexer.lexer)

