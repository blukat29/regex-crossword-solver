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
