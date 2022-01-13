import unittest
from nose.tools import nottest
from ..regex_parser import *

parser = RegexParser()

class ParserTestCase(unittest.TestCase):
    @nottest
    def do_test(self, regex, root, groups=[], backrefs=set()):
        first = parser.parse(regex)
        second = {'groups': groups, 'root': root, 'backrefs': backrefs}
        self.assertEquals(first, second)
    @staticmethod
    @nottest
    def extract_chars(root):
        if root[0] == BAR:
            l = BracketTest.extract_chars(root[1])
            r = BracketTest.extract_chars(root[2])
            return l.union(r)
        elif root[0] == CHAR:
            return set([root[1]])
        else:
            raise ValueError
    @nottest
    def do_bracket_test(self, regex, chars):
        first = parser.parse(regex)
        try:
            first_chars = BracketTest.extract_chars(first['root'])
            self.assertEqual(first_chars, chars)
        except ValueError:
            self.assertTrue(False)

class SimpleTest(ParserTestCase):
    def test_char(self):
        self.do_test("A", (CHAR, 'A'))
        self.do_test("1", (CHAR, '1'))
    def test_special_char(self):
        self.do_test("\s", (CHAR, ' '))
        self.do_test(":", (CHAR, ':'))
        self.do_test("/", (CHAR, '/'))
        self.do_test("'", (CHAR, '\''))
        self.do_test(",", (CHAR, ','))
        self.do_test("-", (CHAR, '-'))
        self.do_test("!", (CHAR, '!'))
    def test_concat(self):
        self.do_test("AB", (CONCAT, (CHAR, 'A'), (CHAR, 'B')))
    def test_escape(self):
        self.do_test("\.", (CHAR, '.'))
        self.do_test("\*", (CHAR, '*'))
        self.do_test("\|", (CHAR, '|'))
        self.do_test("\(", (CHAR, '('))
        self.do_test("\)", (CHAR, ')'))
        self.do_test("\[", (CHAR, '['))
        self.do_test("\]", (CHAR, ']'))
        self.do_test("\^", (CHAR, '^'))
        self.do_test("\+", (CHAR, '+'))
        self.do_test("\?", (CHAR, '?'))
        self.do_test("\\\\", (CHAR, '\\'))
        self.do_test("\{", (CHAR, '{'))
        self.do_test("\}", (CHAR, '}'))
        self.do_test("\!", (CHAR, '!'))
        self.do_test("\-", (CHAR, '-'))
        self.do_test("\,", (CHAR, ','))
    def test_dot(self):
        self.do_test(".", (DOT,))
    def test_bar(self):
        self.do_test("A|B", (BAR, (CHAR, 'A'), (CHAR, 'B')))
    def test_star(self):
        self.do_test("A*", (STAR, (CHAR, 'A')))
    def test_plus(self):
        self.do_test("A+", (CONCAT, (CHAR, 'A'),
                                    (STAR, (CHAR, 'A'))))
    def test_question(self):
        self.do_test("A?", (BAR, (CHAR, 'A'), (EMPTY,)))
    def test_char_class(self):
        self.do_test("\s", (CHAR, ' '))
        self.do_bracket_test("\d", set("0123456789"))

class BracketTest(ParserTestCase):
    def test_simple(self):
        self.do_bracket_test("[ABC]", set("ABC"))
        self.do_bracket_test("[D1]", set("D1"))
    def test_series(self):
        self.do_bracket_test("[M-O]", set("MNO"))
        self.do_test("[A-A]", (CHAR, 'A'))
        self.do_bracket_test("[X-Y3K-L]", set("XY3KL"))
    def test_negate(self):
        self.do_bracket_test("[^A-Za-z0-9 :/'!]", set("])(+*-,.?|[{})\\^"))
    def test_special(self):
        self.do_bracket_test("[a\-\^b\]]", set("ab-^]"))
        self.do_bracket_test("[I,T]", set("I,T"))
        self.do_bracket_test("[.*+?{}()[\]\\\\]", set(".*+?{}()[]\\"))
    def test_char_class(self):
        self.do_bracket_test("[\s]", set(" "))
        self.do_bracket_test("[\d]", set("0123456789"))

class BraceTest(ParserTestCase):
    def test_one(self):
        self.do_test("A{1}", (CHAR, 'A'))
        self.do_test("A{2}", (CONCAT, (CHAR, 'A'), (CHAR, 'A')))
    def test_two(self):
        self.do_test("A{2,}", (CONCAT, (CONCAT, (CHAR, 'A'), (CHAR, 'A')),
                                       (STAR, (CHAR, 'A'))))
    def test_three(self):
        self.do_test("A{1,3}", (BAR, (BAR, (CHAR, 'A'),
                                           (CONCAT, (CHAR, 'A'), (CHAR, 'A'))),
                                     (CONCAT, (CONCAT, (CHAR, 'A'), (CHAR, 'A')),
                                              (CHAR, 'A'))))
    def test_four(self):
        self.do_test("A{0,1}", (CHAR, 'A'))

class GroupTest(ParserTestCase):
    def test_simple(self):
        self.do_test("(A)", (GROUP, 1, (CHAR, 'A')),
                            [(CHAR, 'A')],
                            set())
        self.do_test("(A)(.)", (CONCAT, (GROUP, 1, (CHAR, 'A')),
                                        (GROUP, 2, (DOT,))),
                               [(CHAR, 'A'), (DOT,)],
                               set())
        self.do_test("([B])", (GROUP, 1, (CHAR, 'B')),
                              [(CHAR, 'B')],
                              set())
    def test_backref(self):
        self.do_test("(A)\\1", (CONCAT, (GROUP, 1, (CHAR, 'A')),
                                        (BACKREF, 1)),
                               [(CHAR, 'A')],
                               set([1]))
        self.do_test("(A)(B)\\2\\1", (CONCAT,
                                        (GROUP, 1, (CHAR, 'A')),
                                        (CONCAT, (GROUP, 2, (CHAR, 'B')),
                                            (CONCAT, (BACKREF, 2),
                                                     (BACKREF, 1)))),
                                      [(CHAR, 'A'), (CHAR, 'B')],
                                      set([1,2]))

class StartEndTest(ParserTestCase):
    def test_caret(self):
        self.do_test("^A", (CARET, (CHAR, 'A')))
    def test_dollar(self):
        self.do_test("B$", (DOLLAR, (CHAR, 'B')))
        self.do_test("(K|B$)2",
                (CONCAT, (GROUP, 1, (BAR, (CHAR, 'K'), (DOLLAR, (CHAR, 'B')))), (CHAR, '2')),
                [(BAR, (CHAR, 'K'), (DOLLAR, (CHAR, 'B')))],
                set())
        self.do_test("(Y$|YH)*",
                (STAR, (GROUP, 1, (BAR, (DOLLAR, (CHAR, 'Y')), (CONCAT, (CHAR, 'Y'), (CHAR, 'H'))))),
                [(BAR, (DOLLAR, (CHAR, 'Y')), (CONCAT, (CHAR, 'Y'), (CHAR, 'H')))],
                set())
    def test_caret_dollar(self):
        self.do_test("^A$", (DOLLAR, (CARET, (CHAR, 'A'))))

class ComplexTest(ParserTestCase):
    def test_special_char(self):
        self.do_test("A,", (CONCAT, (CHAR, 'A'), (CHAR, ',')))
        self.do_test("\s9", (CONCAT, (CHAR, ' '), (CHAR, '9')))
        self.do_test("(L|,|O)", (GROUP, 1, (BAR, (CHAR, 'L'), (BAR, (CHAR, ','), (CHAR, 'O')))),
                                [(BAR, (CHAR, 'L'), (BAR, (CHAR, ','), (CHAR, 'O')))],
                                set())
    def test_quantifier_precedence(self):
        self.do_test("AB*", (CONCAT, (CHAR, 'A'),
                                     (STAR, (CHAR, 'B'))))
        self.do_test("AB+", (CONCAT, (CHAR, 'A'),
                                     (CONCAT, (CHAR, 'B'), (STAR, (CHAR, 'B')))))
        self.do_test("AB?", (CONCAT, (CHAR, 'A'),
                                     (BAR, (CHAR, 'B'), (EMPTY,))))
        self.do_test("AB{2}", (CONCAT, (CHAR, 'A'),
                                       (CONCAT, (CHAR, 'B'), (CHAR, 'B'))))
    def test_paren_precedence(self):
        root = (CONCAT, (CHAR, 'A'),
                        (CONCAT, (GROUP, 1, (CONCAT, (CHAR, 'B'), (CHAR, 'C'))),
                                 (CHAR, 'D')))
        self.do_test("A(BC)D", root, [(CONCAT, (CHAR, 'B'), (CHAR, 'C'))], set())
        root = (CONCAT, (CHAR, 'A'),
                        (CONCAT, (BAR, (CHAR, 'C'), (CHAR, 'B')),
                                 (CHAR, 'D')))
        self.do_test("A[BC]D", root)
        self.do_test("(AB)*", (STAR, (GROUP, 1, (CONCAT, (CHAR, 'A'), (CHAR, 'B')))),
                              [(CONCAT, (CHAR, 'A'), (CHAR, 'B'))],
                              set())

