import z3
from regex_parser import RegexParser
from regex_solver import RegexSolver

def solve_crossword(rows, cols):
    row_cnt = len(rows)
    col_cnt = len(cols)

    x = [[None]*col_cnt for _ in range(row_cnt)]
    for i in range(row_cnt):
        for j in range(col_cnt):
            x[i][j] = z3.Int("x_%d_%d" % (i,j))

    solver = z3.Solver()
    for i in range(row_cnt):
        v = x[i]
        e = RegexSolver(col_cnt, rows[i], v).sat_expr()
        solver.add(e)
    for j in range(col_cnt):
        v = map(lambda x: x[j], x)
        e = RegexSolver(row_cnt, cols[j], v).sat_expr()
        solver.add(e)
    check = solver.check()
    if check == z3.sat:
        model = solver.model()
        answer = [[0]*col_cnt for _ in range(row_cnt)]
        for i in range(row_cnt):
            for j in range(col_cnt):
                v = model[x[i][j]]
                answer[i][j] = chr(int(v.as_long()))
        return answer
    else:
        return None

print solve_crossword(["18|19|20","(6|7|8|9)."], [".(2|4|8|0)","56|94|73"])

print solve_crossword(["HE|LL|O+","[PLEASE]+"], ["[^SPEAK]+","EP|IP|EF"])

print solve_crossword(["[a]+","b+"], [".?.+",".+"])

print solve_crossword(
        ["[AWE]+","[ALP]+K","(PR|ER|EP)"],
        ["[BQW](PR|LE)","[RANK]+"])

print solve_crossword(["(..)\\1"], ["A|B","B|C","A|S","B|D"])

print solve_crossword(
        ["(Y|F)(.)\\2[DAF]\\1","(U|O|I)*T[FRO]+","[KANE]*[GIN]*"],
        ["(FI|A)+","(YE|OT)K","(.)[IF]+","[NODE]+","(FY|F|RG)+"])

print solve_crossword(
        ["[UGLER]*","[CAST]*REX[PEA]*","[SIRES]*","(L|OFT|ON)*","H*(AY|ED)*"],
        ["[ARK]*O.*","(.).*\\1N\\1","(SOD|DO|GE)*","[FAXUS]*","[LOPITY]*"])

print solve_crossword(
        ["[QA].[WEST]*","(HE|RT|TK)*.","(RE|QR)[QUART]*","[EUW]*S[RITE]*","(.)(.)\\2\\1[WE]"],
        ["[ABC]*(.)\\1(ME|UO)","(.)T*E*\\1","[HAS]*(SN|PA)","(WE|GA|AL)T*O+","(EG|BEEE)[WIQ]*"])

print solve_crossword(
        ["[IT](O)*(BE|AD)*\\1","[NORMAL]+T{2}",".*(XA|BE).*","(EG|UL){2}[ALF]*","[REQ]*(G|P)(.)+"],
        ["[RUTH]*(OE|EO)[RB]*","(BG|ON|KK)+[RIF]+","(MN|BO|FI)[EU]{2,}","(KT|AL|ET)+G","[OH](PR|AX|TR)+"])

print solve_crossword(
        ["[RA](A|E)[V\s]\\1[NG]+\\1","[SHI\s]+.{2}","(FO|UL|ED)*[DAN\s]+",
         "[TORM]+ST(U|\s|N|K)*","(F|N)(.)[RUNT]+\\2[CL]*","\s[URM]*[ERD]{3,}"],
        ["[RQ\s]*(N|U|M|\s){3,}","(N|I|E)[HOLE]{2,}A(M|N)","[VIT]{2}[T\s]?(STU|PLO)+",
         "(E|\s)(A|S|K)*.U?[FR]","(F|A|N)(\s)\\1\\2[RIF](K|D)+","(G|A|\s)(DU|F|SET)+[WAE]+",
         "[ASK]?(LR|EO|\sN)+"])
