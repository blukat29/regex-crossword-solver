import unittest
import re
from nose.tools import nottest
from ..crossword import solve_crossword
import sys
import inspect

class CrosswordTestCase(unittest.TestCase):
    @nottest
    def record_answer(self, answer):
        name = str(sys._getframe(2).f_code.co_name)
        sys.stderr.write('\n' + name + '\n')
        val = ""
        for row in answer:
            val += ' '.join(row) + '\n'
        sys.stderr.write(val)

    @nottest
    def do_test(self, rows, cols, rows2=None, cols2=None):
        answer = solve_crossword(rows, cols, rows2, cols2)
        #self.record_answer(answer)
        for row in answer:
            print (' '.join(row))
        self.assertNotEqual(answer, None)

        for i in range(len(rows)):
            answer_row = ''.join(answer[i])
            print (answer_row, rows[i])
            self.assertTrue(re.match(rows[i], answer_row))
            if rows2:
                print (answer_row, rows2[i])
                self.assertTrue(re.match(rows2[i], answer_row))

        for j in range(len(cols)):
            answer_col = ''.join(map(lambda row: row[j], answer))
            print (answer_col, cols[j])
            self.assertTrue(re.match(cols[j], answer_col))
            if cols2:
                print (answer_col, cols2[j])
                self.assertTrue(re.match(cols2[j], answer_col))

class CrosswordTest(CrosswordTestCase):
    def test_basic(self):
        self.do_test(["HE|LL|O+", "[PLEASE]+"], ["[^SPEAK]+", "EP|IP|EF"])
    def test_backref_1(self):
        self.do_test([".*M?O.*", "(AN|FE|BE)"], ["(A|B|C)\\1", "(AB|OE|SK)"])
    def test_backref_2(self):
        self.do_test(["[UGLER]*","[CAST]*REX[PEA]*","[SIRES]*","(L|OFT|ON)*","H*(AY|ED)*"],
                     ["[ARK]*O.*","(.).*\\1N\\1","(SOD|DO|GE)*","[FAXUS]*","[LOPITY]*"])
    def test_special_1(self):
        self.do_test(["[*]+", "/+"], [".?.+", ".+"])
    def test_special_2(self):
        self.do_test(["CAT|FOR|FAT", "RY|TY\\-", "[TOWEL]*"],
                     [".(.)\\1", ".*[WAY]+", "[RAM].[OH]"])
    def test_char_class(self):
        self.do_test(["18|19|20", "[6789]\\d"], ["\\d[2480]", "56|94|73"])
    def test_large(self):
        self.do_test(
                ["[RA](A|E)[V\s]\\1[NG]+\\1","[SHI\s]+.{2}","(FO|UL|ED)*[DAN\s]+",
                 "[TORM]+ST(U|\s|N|K)*","(F|N)(.)[RUNT]+\\2[CL]*","\s[URM]*[ERD]{3,}"],
                ["[RQ\s]*(N|U|M|\s){3,}","(N|I|E)[HOLE]{2,}A(M|N)","[VIT]{2}[T\s]?(STU|PLO)+",
                 "(E|\s)(A|S|K)*.U?[FR]","(F|A|N)(\s)\\1\\2[RIF](K|D)+","(G|A|\s)(DU|F|SET)+[WAE]+",
                 "[ASK]?(LR|EO|\sN)+"])
    def test_two_sided_1(self):
        self.do_test(["[A-GN-Z]+"],
                     ["[D-HJ-M]","[^A-RU-Z]"],
                     ["[^A-DI-S]+"],
                     ["[^F-KM-Z]","[A-KS-V]"])
    def test_two_sided_2(self):
        self.do_test(["(W\s|NE|PS)*", "[YOU]{2}[ARK]+"],
                     ["[NAYE]*", "(EO|N\s)", "[WRONG]*", "(K|R|I|M|\s)+"],
                     ["[END\sWITH]+", ".+R.*"],
                     ["[YEN]+", "[ETPHONE\s]+", "[^GONE\s]+", "[\sANKT]+"])
    def test_special_3(self):
        self.do_test(["[^APE]+.?", "[SNAKE]+..", "(\!|\\'|\.|\?)?P[YO!]+"],
                     ["[MENSA?]+", "(A|\?|\?P|NP)+", "[YOU?BE]+", "(O|P)\\1\\1"],
                     ["[M-Q].[A-E][M-Q]", "[^NAKED].?(UO|DUO)", ".+[M-W]+"],
                     ["[^NAP\s]+.", "[PEN\sA?]+", ".+(Y|BE)", "[^BAT'S?]+"])
    def test_special_4(self):
        self.do_test(
                ["(\d+)[MEW]+", "[\/BEDS]+", "(\d|/d|P|\sS|S)+", "[^ZO\s\/\d]+"],
                ["[A5-9\/]+\d(\s|:|\.)", "[T0X\sD]+", "[BMX'S]+N?", "[PA/\sWE]+"],
                ["[W407OM]+", ".+(D|B)+.?", "[SP1NE\s]+", "[NA:X,S]+"],
                ["[0-9:A-Z\/\s]+", "(0D|E\s|\sX)+", ".+B(SN|XN|:P)+", "[^\sIN\/5]+"])
    def test_caret_dollar(self):
        self.do_test(
                ["(Y|\d|M)+", "(.H|P|.P)+", "[\dIP\s].+"],
                ["M[\DIP]*", "(\\\\d|\d.)[\\\\\/B]", "(Y$|YH|\d$)+"],
                ["[^IB][0-3]Y", "^(P|Y)*(PA|\.H$)", "[PA\\\\d\d]+"],
                ["(M|A|P)+", "[^2O13]\.\\\\*(A|P)?", "[HOW2Y]+"])

