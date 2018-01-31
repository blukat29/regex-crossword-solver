import z3

from .regex_solver import RegexSolver

def solve_crossword(rows, cols, rows2=None, cols2=None):
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
        if rows2:
            e = RegexSolver(col_cnt, rows2[i], v).sat_expr()
            solver.add(e)
    for j in range(col_cnt):
        v = list(map(lambda x: x[j], x))
        e = RegexSolver(row_cnt, cols[j], v).sat_expr()
        solver.add(e)
        if cols2:
            e = RegexSolver(row_cnt, cols2[j], v).sat_expr()
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

def solve_regex(regex, length):
    unknowns = [z3.Int("x_%02d" % i) for i in range(length)]
    expr = RegexSolver(length, regex, unknowns).sat_expr()
    solver = z3.Solver()
    solver.add(expr)
    if solver.check() == z3.sat:
        model = solver.model()
        answer = [model[unknowns[i]].as_long() for i in range(length)]
        return ''.join(map(chr, answer))
    else:
        return None
