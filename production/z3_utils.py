import z3


from terms import *


zero56 = z3.BitVecVal(0, 56)

def term_to_z3(t, vars={}):
    if isinstance(t, tuple):
        op = t[0]
        if op == PLUS:
            assert len(t) == 3
            return term_to_z3(t[1], vars) + term_to_z3(t[2], vars)
        if op == AND:
            assert len(t) == 3
            return term_to_z3(t[1], vars) & term_to_z3(t[2], vars)
        if op == OR:
            assert len(t) == 3
            return term_to_z3(t[1], vars) | term_to_z3(t[2], vars)
        if op == XOR:
            assert len(t) == 3
            return term_to_z3(t[1], vars) ^ term_to_z3(t[2], vars)
        elif op == SHL1:
            assert len(t) == 2
            return term_to_z3(t[1], vars) << 1
        elif op == SHR1:
            assert len(t) == 2
            return z3.LShR(term_to_z3(t[1], vars), 1)
        elif op == SHR4:
            assert len(t) == 2
            return z3.LShR(term_to_z3(t[1], vars), 4)
        elif op == SHR16:
            assert len(t) == 2
            return z3.LShR(term_to_z3(t[1], vars), 16)
        elif op == NOT:
            assert len(t) == 2
            return ~term_to_z3(t[1], vars)
        elif op == IF0:
            assert len(t) == 4
            return z3.If(
                term_to_z3(t[1], vars) == 0,
                term_to_z3(t[2], vars),
                term_to_z3(t[3], vars))
            pass
        elif op == FOLD:
            _, bytes, start, fn = t
            _, (formal_y, formal_z), body = fn

            bytes = term_to_z3(bytes, vars)
            accum = term_to_z3(start, vars)
            assert formal_y not in vars
            assert formal_z not in vars
            new_vars = dict(vars)
            for i in range(8):
                new_vars[formal_y] = \
                    z3.Concat(zero56, z3.z3.Extract(8*i+7, 8*i, bytes))
                new_vars[formal_z] = accum
                accum = term_to_z3(body, new_vars)
            return accum
        assert False

    if isinstance(t, (int, long)):
        return z3.BitVecVal(t, 64)

    return vars[t]


def z3_eval_term(t, context={}):
    context = {k:z3.BitVecVal(v, 64) for k, v in context.items()}
    t = term_to_z3(t, context)
    result = z3.BitVec('result', 64)

    z3_solver.push()
    z3_solver.add(result == t)
    assert z3_solver.check() == z3.sat
    result = z3_solver.model()[result]
    assert result is not None
    result = int(result.as_string())
    z3_solver.pop()

    return result


z3_solver = z3.Solver()


if __name__ == '__main__':
    t = (FOLD, 'x', 0, (LAMBDA, ('y', 'z'), (OR, 'y', 'z')))
    r = z3_eval_term(t, dict(x=2**64-1))
    print r
