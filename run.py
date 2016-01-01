import z3
import regex
import gen
import string

charset = "heoab"
r = regex.RegexParser().parse("he.*o")
cvt = gen.Converter(6, charset)

x = []
for i in range(6):
    x.append(z3.Int("x_%d" % i))

e = cvt.sat_expr(x, r)
e = z3.simplify(e)

print e
solver = z3.Solver()
solver.add(e)
print solver.check()
print solver.model()

