from collections import defaultdict

from terms import *

from z3_utils import *
import stats


POINTS = [1 << i for i in range(64)]
QQ = [0, 1, 4, 16, 63]
POINTS += [(1 << i) | (1 << j) for i in QQ for j in QQ if i < j]
POINTS += [MASK^x for x in POINTS]


def predicate_signature(t):
    result = 0
    for pt in POINTS:
        vars = dict(x=pt)
        if FOLD not in repr(t):
            vars['y'] = 0
            vars['z'] = 0
        result *= 2
        result += int(evaluate(t, vars)==0)
    return '{:034x}'.format(result)


X = z3.BitVec('x', 64)
Y = z3.BitVec('y', 64)
Z = z3.BitVec('z', 64)


def filter_distinct(terms):
    predicates = []

    buckets = defaultdict(list)

    for t in terms:
        with stats.TimeIt('predicate_signature'):
            signature = predicate_signature(t)

        if FOLD in repr(t):
            zt = term_to_z3(t, dict(x=X))
        else:
            zt = term_to_z3(t, dict(x=X, y=Y, z=Z))

        zt = z3.simplify(zt)

        for zz in buckets[signature]:
            if predicates_equivalent(zz, zt):
                break
        else:
            predicates.append(t)
            buckets[signature].append(zt)

    return predicates


def predicates_equivalent(t1, t2):
    with PushPop():
        z3_solver.add((t1==0) != (t2==0))

        with stats.TimeIt('z3.check'):
            result = z3_solver.check()

        if result == z3.unsat:
            return True
        elif result == z3.sat:
            return False
        else:
            assert False, result


if __name__ == '__main__':
    import logging
    logging.basicConfig(level=logging.INFO)

    from enum_terms import base_enum

    size = 5
    required_ops = frozenset(['fold'])
    allowed_ops = frozenset([0, 1, 'if0', 'fold', 'x'])

    #size = 8
    #required_ops = frozenset(['not', 'plus', 'shr16', 'shr1', 'or'])
    #allowed_ops = frozenset([0, 1, 'if0', 'shr16', 'plus', 'shr1', 'not', 'x', 'or'])

    with stats.TimeIt('enum terms'):
        terms = list(base_enum(size, required_ops, allowed_ops))
    print len(terms), 'terms'

    preds = filter_distinct(terms)
    print len(preds), 'distinct predicates'

    stats.log_stats()
