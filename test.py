
import z3

CONCAT = 1
CHAR = 2
DOT = 3
STAR = 4
OR = 5

MAXLEN = 4
CHARSET = 'abcdefghijklmnopqrstuvwxyz'

x = []
for i in range(MAXLEN):
    x.append(z3.Int("x_%d" % i))

def eq_expr(x, i, ch):
    return (x[i] == ord(ch))

def len_set(r):
    ty = r[0]
    if ty == DOT:
        return set([1])
    if ty == CHAR:
        return set([1])
    if ty == CONCAT:
        res = set()
        l1 = len_set(r[1])
        l2 = len_set(r[2])
        for i1 in l1:
            for i2 in l2:
                res.add(i1 + i2)
        return res
    if ty == STAR:
        res = set()
        l1 = len_set(r[1])
        for i1 in l1:
            k = 0
            while k * i1 <= MAXLEN:
                res.add(k * i1)
                k += 1
        return res
    if ty == OR:
        return len_set(r[1]) | len_set(r[2])

def sat_expr(x, r, i, l):
    """
    SAT expression over variables x[i], ..., x[i+l]
    that satisfies the regular expression r.
    """
    if l not in len_set(r):
        return False
    if i + l > MAXLEN:
        return False
    ty = r[0]
    if ty == DOT:
        expr = False
        for ch in CHARSET:
            expr = z3.Or(expr, eq_expr(x, i, ch))
    elif ty == CHAR:
        ch = r[1]
        expr = eq_expr(x, i, ch)
    elif ty == CONCAT:
        expr = False
        r1 = r[1]
        r2 = r[2]
        for l1 in len_set(r1):
            expr = z3.Or(expr, z3.And(
                sat_expr(x, r1, i, l1),
                sat_expr(x, r2, i+l1, l-l1)
            ))
    elif ty == STAR:
        if l == 0:
            expr = True
        else:
            expr = False
            r1 = r[1]
            for l1 in len_set(r1):
                expr = z3.Or(expr, z3.And(
                    sat_expr(x, r1, i, l1),
                    sat_expr(x, r, i+l1, l-l1)
                ))
    elif ty == OR:
        expr = z3.Or(
                sat_expr(x, r[1], i, l),
                sat_expr(x, r[2], i, l)
        )
    else:
        raise ValueError("Unknown type '%d'" % ty)
    return expr

def sat_expr_all(x, r):
    expr = False
    for l in len_set(r):
        expr = z3.Or(expr, sat_expr(x, r, 0, l))
    return expr

r = (DOT,)
r = (CHAR, 'b')
r = (CONCAT, (CHAR, 'h'), (CHAR, 'i'))
r = (CONCAT, (CHAR, 'h'),
        (CONCAT, (CHAR, 'e'),
            (CONCAT, (DOT,),
                (CONCAT, (DOT,), (CHAR, 'o')))))
r = (STAR, (CHAR, 'c'))
r = (CONCAT, (CHAR, 'a'),
        (STAR, (CHAR, 'c')))
r = (OR, (CHAR, 'a'), (CHAR, 'b'))
e = sat_expr_all(x, r)
e = z3.simplify(e)
print e

solver = z3.Solver()
solver.add(e)
print solver.check()
m = solver.model()
print m
for i in range(MAXLEN):
    if m[x[i]]:
        print chr(int(m[x[i]].as_long()))

