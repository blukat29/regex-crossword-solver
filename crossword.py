import z3
import regex
import gen

def solve_crossword(rows, cols, charset):
    row_cnt = len(rows)
    col_cnt = len(cols)

    parser = regex.RegexParser()
    row_r = [None]*row_cnt
    for i in range(row_cnt):
        row_r[i] = parser.parse(rows[i])
    col_r = [None]*col_cnt
    for j in range(col_cnt):
        col_r[j] = parser.parse(cols[j])

    cvt_row = gen.Converter(col_cnt, charset)
    cvt_col = gen.Converter(row_cnt, charset)

    x = [[None]*col_cnt for _ in range(row_cnt)]
    for i in range(row_cnt):
        for j in range(col_cnt):
            x[i][j] = z3.Int("x_%d_%d" % (i,j))

    solver = z3.Solver()
    for i in range(row_cnt):
        v = x[i]
        e = cvt_row.sat_expr(v, row_r[i])
        solver.add(e)
    for j in range(col_cnt):
        v = map(lambda x: x[j], x)
        e = cvt_col.sat_expr(v, col_r[j])
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

charset = "0123456789"
rows = [
    "18|19|20",
    "(6|7|8|9)."
]
cols = [
    ".(2|4|8|0)",
    "56|94|73"
]
print solve_crossword(rows, cols, charset)

