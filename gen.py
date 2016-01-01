import z3
import regex

class Converter:
    def __init__(self, length, charset):
        self.length = length
        self.charset = charset

    def _len_set(self, r):
        ty = r[0]

        if ty == regex.CHAR:
            return set([1])

        elif ty == regex.DOT:
            return set([1])

        elif ty == regex.STAR:
            # LEN(r) = { k * l <= MAX : k = 0,1,2,... && l in len_set(r) }
            s = set()
            for l in self._len_set(r[1]):
                k = 0
                while k * l <= self.length:
                    s.add(k * l)
                    k += 1
            return s

        elif ty == regex.BAR:
            # LEN(r1 | r2) = LEN(r1) union LEN(r2)
            l1 = self._len_set(r[1])
            l2 = self._len_set(r[2])
            return l1 | l2

        elif ty == regex.CONCAT:
            # LEN(r1 r2) = { l1 + l2 <= MAX : l1 in LEN(r1) and l2 in LEN(r2) }
            s = set()
            l1 = self._len_set(r[1])
            l2 = self._len_set(r[2])
            for i in l1:
                for j in l2:
                    if i + j <= self.length:
                        s.add(i + j)
            return s

        else:
            raise ValueError("Unknown regex type '%s'" % repr(ty))

    def _sat_expr(self, x, r, i, l):
        if l not in self._len_set(r):
            return False
        if i + l > self.length:
            return False

        ty = r[0]

        if ty == regex.CHAR:
            return (x[i] == ord(r[1]))

        elif ty == regex.DOT:
            expr = False
            for ch in self.charset:
                expr = z3.Or(expr, x[i] == ord(ch))
            return expr

        elif ty == regex.STAR:
            # SAT(r*, i, l) = Union for l' in LEN(r):
            #                   [ SAT(r, i, l') && SAT(r*, i+l', l-l') ]
            if l == 0:
                return True
            else:
                expr = False
                for l1 in self._len_set(r[1]):
                    expr = z3.Or(expr, z3.And(
                        self._sat_expr(x, r[1], i, l1),
                        self._sat_expr(x, r, i + l1, l - l1)
                    ))
                return expr

        elif ty == regex.BAR:
            # SAT(r1 | r2, i, l) = SAT(r1, i, l) || SAT(r2, i, l)
            expr = z3.Or(
                    self._sat_expr(x, r[1], i, l),
                    self._sat_expr(x, r[2], i, l)
            )
            return expr

        elif ty == regex.CONCAT:
            # SAT(r1 r2, i, l) = Union for l1 in LEN(r1):
            #                      [ SAT(r1, i, l1) && SAT(r2, i+l1, l-l1) ]
            expr = False
            for l1 in self._len_set(r[1]):
                expr = z3.Or(expr, z3.And(
                    self._sat_expr(x, r[1], i, l1),
                    self._sat_expr(x, r[2], i + l1, l - l1)
                ))
            return expr

        else:
            raise ValueError("Unknown regex type '%s'" % repr(ty))

    def sat_expr(self, x, r):
        expr = self._sat_expr(x, r, 0, self.length)
        return z3.simplify(expr)

