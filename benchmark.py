from crossword import solve_crossword, RegexParser
import time

# Compile parser before start testing
RegexParser()

messages = []
times = []
quiet = False

def test_case(rows, cols, title="", rows2=None, cols2=None):
    message = "%s (%d x %d)" % (title, len(rows), len(cols))
    messages.append(message)
    print message
    if not quiet:
        print "== rows:"
        print "\n".join(rows)
        print "== cols:"
        print "\n".join(cols)
    t0 = time.time()
    result = solve_crossword(rows, cols, rows2, cols2)
    t1 = time.time()
    times.append(t1 - t0)
    if not quiet:
        print "== ans:"
        print '\n'.join(map(lambda x: ' '.join(x), result))
    print "solved in %.2f seconds" % (t1 - t0)
    print

if __name__ == '__main__':
    test_case(["HE|LL|O+","[PLEASE]+"], ["[^SPEAK]+","EP|IP|EF"], "Simple test 1")
    test_case(["18|19|20","(6|7|8|9)."], [".(2|4|8|0)","56|94|73"], "Simple test 2")
    test_case(["[a]+","b+"], [".?.+",".+"], "Quantifier test")
    test_case(["[AWE]+","[ALP]+K","(PR|ER|EP)"],
              ["[BQW](PR|LE)","[RANK]+"],
              "Bracket test")
    test_case(["(EP|ST)*","T[A-Z]*",".M.T",".*P.[S-X]+"],
              [".*E.*","[^P]I(IT|ME)","(EM|FE)(IT|IP)","(TS|PE|KE)*"],
              "Bracket and star test")
    test_case(["(..)\\1"], ["A|B","B|C","A|S","B|D"], "Backref test 2")
    test_case(["(Y|F)(.)\\2[DAF]\\1","(U|O|I)*T[FRO]+","[KANE]*[GIN]*"],
              ["(FI|A)+","(YE|OT)K","(.)[IF]+","[NODE]+","(FY|F|RG)+"],
              "Backref test 2")
    test_case(["[UGLER]*","[CAST]*REX[PEA]*","[SIRES]*","(L|OFT|ON)*","H*(AY|ED)*"],
              ["[ARK]*O.*","(.).*\\1N\\1","(SOD|DO|GE)*","[FAXUS]*","[LOPITY]*"],
              "Large test 1")
    test_case(
            ["[QA].[WEST]*","(HE|RT|TK)*.","(RE|QR)[QUART]*",
             "[EUW]*S[RITE]*","(.)(.)\\2\\1[WE]"],
            ["[ABC]*(.)\\1(ME|UO)","(.)T*E*\\1","[HAS]*(SN|PA)",
             "(WE|GA|AL)T*O+","(EG|BEEE)[WIQ]*"],
            "Large test 2")
    test_case(
            ["[IT](O)*(BE|AD)*\\1","[NORMAL]+T{2}",".*(XA|BE).*",
             "(EG|UL){2}[ALF]*","[REQ]*(G|P)(.)+"],
            ["[RUTH]*(OE|EO)[RB]*","(BG|ON|KK)+[RIF]+","(MN|BO|FI)[EU]{2,}",
             "(KT|AL|ET)+G","[OH](PR|AX|TR)+"],
            "Large test 3")

    test_case(
            ["[RA](A|E)[V\s]\\1[NG]+\\1","[SHI\s]+.{2}","(FO|UL|ED)*[DAN\s]+",
             "[TORM]+ST(U|\s|N|K)*","(F|N)(.)[RUNT]+\\2[CL]*","\s[URM]*[ERD]{3,}"],
            ["[RQ\s]*(N|U|M|\s){3,}","(N|I|E)[HOLE]{2,}A(M|N)","[VIT]{2}[T\s]?(STU|PLO)+",
             "(E|\s)(A|S|K)*.U?[FR]","(F|A|N)(\s)\\1\\2[RIF](K|D)+","(G|A|\s)(DU|F|SET)+[WAE]+",
             "[ASK]?(LR|EO|\sN)+"],
            "Large + \s test")

    test_case(
            ["[A-GN-Z]+"],
            ["[D-HJ-M]","[^A-RU-Z]"],
            "double cross test",
            ["[^A-DI-S]+"],
            ["[^F-KM-Z]","[A-KS-V]"])

    print "== Summary =="
    for idx, message in enumerate(messages):
        print "%2d. %30s  %.2fs" % (idx+1, message, times[idx])
