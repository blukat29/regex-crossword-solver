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

class SimpleTest(ParserTestCase):
    def test_char(self):
        self.do_test("A", (CHAR, 'A'))
        self.do_test("1", (CHAR, '1'))
        self.do_test("\s", (CHAR, ' '))
        self.do_test(":", (CHAR, ':'))
        self.do_test("/", (CHAR, '/'))
        self.do_test("'", (CHAR, '\''))
        self.do_test(",", (CHAR, ','))
        self.do_test("-", (CHAR, '-'))
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
    def test_dot(self):
        self.do_test(".", (DOT,))
    def test_bar(self):
        self.do_test("A|B", (BAR, (CHAR, 'A'), (CHAR, 'B')))
    def test_star(self):
        self.do_test("A*", (STAR, (CHAR, 'A')))
    def test_quantifiers(self):
        self.do_test("A+", (CONCAT, (CHAR, 'A'),
                                    (STAR, (CHAR, 'A'))))
        self.do_test("A?", (BAR, (CHAR, 'A'), (EMPTY,)))

class BracketTest(ParserTestCase):
    def test_simple(self):
        self.do_test("[ABC]", (BAR, (BAR, (CHAR, 'A'), (CHAR, 'C')),
                                    (CHAR, 'B')))
        self.do_test("[D1]", (BAR, (CHAR, '1'), (CHAR, 'D')))
    def test_series(self):
        self.do_test("[M-O]", (BAR, (BAR, (CHAR, 'M'), (CHAR, 'O')),
                                    (CHAR, 'N')))
        self.do_test("[A-A]", (CHAR, 'A'))
        self.do_test("[X-Y3K-L]", (BAR, (BAR, (BAR, (BAR, (CHAR, 'Y'), (CHAR, 'X')),
                                                    (CHAR, 'K')),
                                              (CHAR, 'L')),
                                        (CHAR, '3')))
    def test_negate(self):
        self.do_test("[^a-z0-9A-X\s:/']", (BAR, (CHAR, 'Y'), (CHAR, 'Z')))
    def test_special(self):
        self.do_test("[\-\^]", (BAR, (CHAR, '-'), (CHAR, '^')))
        self.do_test("[I,T]", (BAR, (BAR, (CHAR, 'I'), (CHAR, 'T')), (CHAR, ',')))

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

class ComplexTest(ParserTestCase):
    def test_special_char(self):
        self.do_test("A,", (CONCAT, (CHAR, 'A'), (CHAR, ',')))
        self.do_test("\s9", (CONCAT, (CHAR, ' '), (CHAR, '9')))
        self.do_test("(L|,|O)", (GROUP, 1, (BAR, (BAR, (CHAR, 'L'), (CHAR, ',')),
                                                 (CHAR, 'O'))),
                                [(BAR, (BAR, (CHAR, 'L'), (CHAR, ',')), (CHAR, 'O'))],
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
        self.do_test("A(BC)D", (CONCAT,
                                   (CONCAT, (CHAR, 'A'),
                                            (GROUP, 1,
                                                (CONCAT, (CHAR, 'B'), (CHAR, 'C')))),
                                   (CHAR, 'D')),
                               [(CONCAT, (CHAR, 'B'), (CHAR, 'C'))],
                               set())
        self.do_test("A[BC]D", (CONCAT,
                                   (CONCAT, (CHAR, 'A'),
                                            (BAR, (CHAR, 'C'), (CHAR, 'B'))),
                                   (CHAR, 'D')))
        self.do_test("(AB)*", (STAR, (GROUP, 1, (CONCAT, (CHAR, 'A'), (CHAR, 'B')))),
                              [(CONCAT, (CHAR, 'A'), (CHAR, 'B'))],
                              set())


