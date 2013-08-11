

from terms import *
from z3_utils import Control


POINTS = [0x1234, 0x84392467, 0x48848585^MASK]


def get_attached_values(t):
    if isinstance(t, TupleWithValues):

        # check with evaluate (slooow)
        if False:
            for pt in POINTS:
                if 'fold' in repr(t):
                    ctx = dict(x=pt)
                else:
                    ctx = dict(x=pt, y=pt, z=pt)
                v = evaluate(t, ctx)
                assert v == t.values[pt], (v, t.values[pt])

        return t.values
    if isinstance(t, tuple):
        return None
    if t in [0, 1]:
        return dict.fromkeys(POINTS, t)
    if t in 'xyz':
        return {x:x for x in POINTS}


class TupleWithValues(tuple):
    def __repr__(self):
        return tuple.__repr__(self) + '@' + repr(self.values)

    @staticmethod
    def create(t, values):
        assert isinstance(t, tuple)
        result = TupleWithValues(t)


        result.values = values
        return result


def propagate_attached(t):
    assert type(t) is tuple, (type(t), t)

    op = t[0]

    arg_values = map(get_attached_values, t[1:])

    if op == NOT:
        values = {k: MASK^v for k, v in arg_values[0].items()}
    elif op == SHL1:
        values = {k: MASK&(v<<1) for k, v in arg_values[0].items()}
    elif op == SHR1:
        values = {k: v>>1 for k, v in arg_values[0].items()}
    elif op == SHR4:
        values = {k: v>>4 for k, v in arg_values[0].items()}
    elif op == SHR16:
        values = {k: v>>16 for k, v in arg_values[0].items()}
    elif op == PLUS:
        arg2 = arg_values[1]
        values = {k: MASK &(v + arg2[k]) for k, v in arg_values[0].items()}
    elif op == AND:
        arg2 = arg_values[1]
        values = {k: v & arg2[k] for k, v in arg_values[0].items()}
    elif op == OR:
        arg2 = arg_values[1]
        values = {k: v | arg2[k] for k, v in arg_values[0].items()}
    elif op == XOR:
        arg2 = arg_values[1]
        values = {k: v ^ arg2[k] for k, v in arg_values[0].items()}
    elif op == IF0:
        arg2 = arg_values[1]
        arg3 = arg_values[2]
        values = {k: arg3[k] if v else arg2[k] for k, v in arg_values[0].items()}
    else:
        assert False, t

    return TupleWithValues.create(t, values)

def eval_and_attach(t):
    if t in [0, 1, 'x', 'y', 'z']:
        return t

    has_fold = 'fold' in repr(t)
    values = {}
    for pt in POINTS:
        if has_fold:
            ctx = dict(x=pt)
        else:
            ctx = dict(x=pt, y=pt, z=pt)
        values[pt] = evaluate(t, ctx)

    return TupleWithValues.create(t, values)


if __name__ == '__main__':
    t = (FOLD, 'x', 0, (LAMBDA, ('y', 'z'), propagate_attached((OR, 'y', 'z'))))
    t = eval_and_attach(t)
    print t
    print get_attached_values(t)