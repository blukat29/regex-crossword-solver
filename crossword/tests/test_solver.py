import unittest
import re
import z3
from nose.tools import nottest
from ..regex_solver import RegexSolver

class SolverTestCase(unittest.TestCase):
    @nottest
    def do_test(self, regex, length, has_solution=True):
        print (regex, length, has_solution)
        v = []
        for i in range(length):
            v.append(z3.Int("x_%d" % i))
        e = RegexSolver(length, regex, v).sat_expr()
        print (e)
        solver = z3.Solver()
        solver.add(e)
        check = solver.check()
        if has_solution:
            self.assertTrue(check == z3.sat)
            if check == z3.sat:
                model = solver.model()
                s = ""
                for i in range(length):
                    x = model[v[i]].as_long()
                    s += chr(int(x))
                self.assertTrue(re.match(regex, s))
        else:
            self.assertFalse(check == z3.sat)

class SimpleTest(SolverTestCase):
    def test_char(self):
        self.do_test("a", 1)
        self.do_test("4", 1)
        self.do_test("a", 0, False)
    def test_concat(self):
        self.do_test("abc", 3)
        self.do_test("a.c", 3)
    def test_special_char(self):
        self.do_test("-", 1)
        self.do_test(",", 1)
        self.do_test("\\\\", 1)
        self.do_test("\*", 1)
        self.do_test("\+", 1)
        self.do_test("\?", 1)
        self.do_test("\)", 1)
        self.do_test("\]", 1)
        self.do_test("\}", 1)

class QuantifierTest(SolverTestCase):
    def test_star(self):
        self.do_test("a*", 0)
        self.do_test("a*", 1)
        self.do_test("a*", 3)
        self.do_test("ab*c", 2)
        self.do_test("ab*c", 3)
        self.do_test("ab*c", 4)
    def test_plus(self):
        self.do_test("a+", 0, False)
        self.do_test("a+", 1)
        self.do_test("a+", 2)
        self.do_test("ab+c", 2, False)
        self.do_test("ab+c", 3)
        self.do_test("ab+c", 4)
    def test_question(self):
        self.do_test("a?", 0)
        self.do_test("a?", 1)
        self.do_test("a?", 2, False)
    def test_brace_one(self):
        self.do_test("a{2}", 1, False)
        self.do_test("a{2}", 2)
        self.do_test("a{2}", 3, False)
    def test_brace_two(self):
        self.do_test("a{2,}", 1, False)
        self.do_test("a{2,}", 2)
        self.do_test("a{2,}", 3)
    def test_brace_three(self):
        self.do_test("a{2,4}", 1, False)
        self.do_test("a{2,4}", 2)
        self.do_test("a{2,4}", 3)
        self.do_test("a{2,4}", 4)
        self.do_test("a{2,4}", 5, False)

class BracketTest(SolverTestCase):
    def test_simple(self):
        self.do_test("[a]", 1)
        self.do_test("[a][b]", 2)
        self.do_test("[abCDeF9I]", 1)
    def test_range(self):
        self.do_test("[a-cA-X]", 1)
        self.do_test("[K-K]", 1)
        self.do_test("[^1-9a-zA-Z]", 1)
    def test_quantifier(self):
        self.do_test("[ab]*", 2)
        self.do_test("[ab]+", 2)
        self.do_test("[ab]?", 1)
        self.do_test("[ab]{2}", 2)
    def test_special_char(self):
        self.do_test("[\s]", 1)
        self.do_test("[\^]", 1)
        self.do_test("[,]", 1)
        self.do_test("[:]", 1)
        self.do_test("[']", 1)
        self.do_test("[/]", 1)

class GroupTest(SolverTestCase):
    def test_backref(self):
        self.do_test("(.)\\1", 2)
        self.do_test("(a)(b)c\\2\\1", 5)
        self.do_test("(.)\\1\\1", 3)
        self.do_test("(..)\\1", 4)
    def test_bar(self):
        self.do_test("(LR|EO|\sN)+", 2)
        self.do_test("(ab|defgh)+", 2)
        self.do_test("(ab|defgh)+", 3, False)
        self.do_test("(ab|defgh)+", 4)
        self.do_test("(ab|defgh)+", 5)
        self.do_test("(ab|defgh)+", 6)
        self.do_test("(ab|defgh)+", 7)
    def test_nested(self):
        self.do_test("((a)b)+", 2)
        self.do_test("((a)b)+", 3, False)
        self.do_test("((a)b)+", 4)

class StartEndTest(SolverTestCase):
    def test_caret(self):
        self.do_test("^A", 1)
        self.do_test("^A", 2, False)
        self.do_test("AB|^A", 1)
        self.do_test("AB|^A", 2)
    def test_dollar(self):
        self.do_test("B$", 1)
        self.do_test("B$", 2, False)
        self.do_test("AB|C$", 1)
        self.do_test("AB|C$", 2)
    def test_caret_dollar(self):
        self.do_test("^A$", 1)
        self.do_test("^A$", 2, False)
        self.do_test("^(P|Y)*(PA|\.H$)", 3)
        self.do_test("(Y$|YH|\d$)+", 3)
        self.do_test("(Y$)+", 3, False)

class ComplexTest(SolverTestCase):
    def test_complex(self):
        self.do_test("(CAT|A-T)+", 3)
        self.do_test("(.)(.)\\2\\1[WE]", 5)
        self.do_test("(WE|GA|AL)T*O+", 5)
        self.do_test("(.).*\\1N\\1", 5)
        self.do_test("[SALT]+O(\sB|S,|E,)+[F\s]", 7)
        self.do_test("(T|K)[POE]\\1\\1(B|E|\s)*", 6)
        self.do_test("[I,T]{4}(QN|BA)*", 6)
        self.do_test(".(L|,|O)[,E\sB]+", 7)
        self.do_test("[MI/SON]+[^OLDE]{4}", 7)
        self.do_test("[HITE'\s]+", 4)
        self.do_test("[IN'THE.\s]+", 7)
        self.do_test("[IT'\s]{4}[H.TE]+", 7)
        self.do_test("[MA\-\sE]+", 3)
        self.do_test("(\!|\\'|\.|\?)?P[YO!]+", 4)
        self.do_test("(A|\?|\?P|NP)+", 4)

