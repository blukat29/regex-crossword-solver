import ply.lex as lex
import ply.yacc as yacc
import string

[EMPTY, CHAR, DOT, STAR, BAR, CONCAT, GROUP, BACKREF] = range(8)
CHARSET = string.lowercase + string.uppercase + string.digits + ' '

class RegexLexer:
    tokens = (
        "CHAR", "DOT",
        "STAR", "BAR",
        "LPAREN", "RPAREN",
        "LBRACKET", "RBRACKET", "DASH", "CARET",
        "PLUS", "QUESTION", "BACKSLASH", "DIGIT",
        "LBRACE", "RBRACE", "COMMA",
    )
    def t_CHAR(self, t):
        r"[a-zA-Z\s]"
        return t;
    def t_DIGIT(self, t):
        r"[0-9]"
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
    t_PLUS = r"\+"
    t_QUESTION = r"\?"
    t_BACKSLASH = r"\\"
    t_LBRACE = r"\{"
    t_RBRACE = r"\}"
    t_COMMA = ","
    def t_error(self, t):
        print "Error parsing '%s'" % t.value[0]
    def __init__(self):
        self.lexer = lex.lex(module=self)

class RegexParser:
    precedence = (
        ('left', 'BAR'),
        ('left', 'DIGIT', 'DOT', 'CHAR'),
        ('left', 'CONCAT'),
        ('right', 'STAR', 'PLUS', 'QUESTION', 'LBRACE'),
        ('left', 'LBRACKET', 'LPAREN'),
        ('left', 'BACKSLASH'),
    )
    def p_regex_expr(self, p):
        """regex : expr"""
        p[0] = p[1]
    def p_expr_backslash(self, p):
        """
        expr : BACKSLASH DIGIT
        """
        p[0] = (BACKREF, int(p[2]))
        self.backrefs.add(int(p[2]))
    def p_expr_group(self, p):
        """expr : LPAREN expr RPAREN"""
        self.groups.append(p[2])
        p[0] = (GROUP, len(self.groups), p[2])
    def p_expr_star(self, p):
        """expr : expr STAR"""
        p[0] = (STAR, p[1])
    def p_expr_plus(self, p):
        """expr : expr PLUS"""
        p[0] = (CONCAT, p[1], (STAR, p[1]))
    def p_expr_question(self, p):
        """expr : expr QUESTION"""
        p[0] = (BAR, p[1], (EMPTY,))
    def p_expr_concat(self, p):
        """expr : expr expr %prec CONCAT"""
        p[0] = (CONCAT, p[1], p[2])
    def p_expr_dot(self, p):
        """expr : DOT"""
        p[0] = (DOT,)
    def p_expr_char(self, p):
        """
        expr : CHAR
             | DIGIT
        """
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

    def p_expr_braces(self, p):
        """
        expr : expr LBRACE inbrace RBRACE
        """
        inner = p[1]
        inbrace = p[3]
        if ',' not in inbrace:
            times = int(inbrace)
            p[0] = reduce(lambda x, y: (CONCAT, x, y), [inner for _ in range(times)])
        else:
            if ',' == inbrace[-1]:
                times = int(inbrace[:-1])
                before = reduce(lambda x, y: (CONCAT, x, y), [inner for _ in range(times)])
                p[0] = (CONCAT, before, (STAR, inner))
            else:
                times1, times2 = map(int, inbrace.split(','))
                cases = []
                for l in range(times1, times2+1):
                    case = reduce(lambda x, y: (CONCAT, x, y), [inner for _ in range(l)])
                    cases.append(case)
                p[0] = reduce(lambda x, y: (BAR, x, y), cases)

    def p_inbrace_empty(self, p):
        """inbrace : """
        p[0] = ""
    def p_inbrace_single(self, p):
        """
        inbrace : DIGIT inbrace
                | COMMA inbrace
        """
        p[0] = p[1] + p[2]

    def p_error(self, p):
        print "Parse error at '%s'" % p.value
    def __init__(self):
        self.lexer = RegexLexer()
        self.tokens = self.lexer.tokens
        self.parser = yacc.yacc(module=self)
    def parse(self, data):
        self.groups = []
        self.backrefs = set()
        root = self.parser.parse(data, self.lexer.lexer)
        return {'groups': self.groups, 'root': root, 'backrefs': self.backrefs}

