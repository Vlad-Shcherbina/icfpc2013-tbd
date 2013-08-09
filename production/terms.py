
LAMBDA = 'lambda'
IF0 = 'if0'
FOLD = 'fold'
NOT = 'not'
SHL1 = 'shl1'
SHR1 = 'shr1'
SHR4 = 'shr4'
SHR16 = 'shr16'
AND = 'and'
OR = 'or'
XOR = 'xor'
PLUS = 'plus'

CONSTANTS = [0, 1]
UNARY_OPS = [NOT, SHL1, SHR1, SHR4, SHR16]
BINARY_OPS = [AND, OR, XOR, PLUS]


MASK = 2**64-1

def term_to_str(t):
    if isinstance(t, tuple):
        return '({})'.format(' '.join(map(term_to_str, (elem for elem in t))))
    return str(t)


def apply(lambda_expr, context, *args):
    lam, formal_args, body = lambda_expr
    assert lam == LAMBDA, lambda_expr
    assert len(formal_args) == len(args), (formal_args, args)
    context = dict(context)
    for fa, a in zip(formal_args, args):
        assert fa not in context
        context[fa] = a
    return evaluate(body, context)


def evaluate(t, context={}):
    if isinstance(t, tuple):
        op = t[0]
        if op == NOT:
            assert len(t) == 2, t
            return MASK ^ evaluate(t[1], context)
        elif op == SHL1:
            assert len(t) == 2, t
            return MASK & (evaluate(t[1], context) << 1)
        elif op == SHR1:
            assert len(t) == 2, t
            return evaluate(t[1], context) >> 1
        elif op == SHR4:
            assert len(t) == 2, t
            return evaluate(t[1], context) >> 4
        elif op == SHR16:
            assert len(t) == 2, t
            return evaluate(t[1], context) >> 16
        elif op == AND:
            assert len(t) == 3
            return evaluate(t[1], context) & evaluate(t[2], context)
        elif op == OR:
            assert len(t) == 3
            return evaluate(t[1], context) | evaluate(t[2], context)
        elif op == XOR:
            assert len(t) == 3
            return evaluate(t[1], context) ^ evaluate(t[2], context)
        elif op == PLUS:
            assert len(t) == 3
            return (evaluate(t[1], context) + evaluate(t[2], context)) & MASK
        if op == IF0:
            _, cond, then, else_ = t
            if evaluate(cond, context) == 0:
                return evaluate(then, context)
            else:
                return evaluate(else_, context)
        elif op == FOLD:
            _, bytes, start, fn = t
            bytes = evaluate(bytes, context)
            accum = evaluate(start, context)
            for i in range(8):
                byte = (bytes >> i*8) & 255
                accum = apply(fn, context, byte, accum)
            return accum
        else:
            assert False, t
    else:
        if t in CONSTANTS:
            return t
        elif t in context:
            return context[t]
        else:
            assert False, t


def subst(t, replacements={}):
    if t in replacements:
        return replacements[t]
    if isinstance(t, tuple):
        return tuple(subst(tt, replacements) for tt in t)
    return t


def term_size(t):
    if isinstance(t, tuple):
        if t[0] == LAMBDA:
            assert len(t) == 3
            return 1 + term_size(t[2])
        else:
            # fold is covered by this case
            return sum(map(term_size, t))
    return 1


def term_op(t):
    '''
    Implementation of function Op from problem statement.
    '''
    if isinstance(t, tuple):
        if t[0] == LAMBDA:
            assert len(t) == 3
            return term_op(t[2])
        else:
            result = set([t[0]])
            for tt in t[1:]:
                result |= term_op(tt)
            return result
    return set()


def term_operators(t):
    '''
    Implementation of Operators relation from problem statement as function.
    '''
    if isinstance(t, tuple) and t[0] == FOLD:
        return term_op(t) | set(['tfold'])
    return term_op(t)
