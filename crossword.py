import z3
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

