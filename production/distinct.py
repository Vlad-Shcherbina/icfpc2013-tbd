from collections import defaultdict
import logging

from terms import *

from z3_utils import *
import stats


POINTS = [1 << i for i in range(64)]
QQ = [0, 1, 4, 16, 63]
POINTS += [(1 << i) | (1 << j) for i in QQ for j in QQ if i < j]
POINTS += [MASK^x for x in POINTS]


def term_signature(t):
    pts = [0x345034994, 0x4759607901000000, 0x0123400000^MASK]
    result = 0
    for pt in pts:
        vars = dict(x=pt)
        if FOLD not in repr(t):
            vars['y'] = pt ^ 2345
            vars['z'] = pt >> 5
        result *= 7
        result += evaluate(t, vars)
    return result

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


def nice_term_to_z3(t):
    if FOLD in repr(t):
        return term_to_z3(t, dict(x=X))
    else:
        return term_to_z3(t, dict(x=X, y=Y, z=Z))
    pass

def filter_distinct(terms, as_predicates=False):
    buckets = defaultdict(list)

    if as_predicates:
        signature_fn = predicate_signature
    else:
        signature_fn = term_signature

    for t in terms:
        signature = predicate_signature(t)


        zt = nice_term_to_z3(t)
        zt = z3.simplify(zt)

        for zz in buckets[signature]:
            if terms_equivalent(zz, zt, as_predicates=as_predicates):
                break
        else:
            buckets[signature].append(zt)
            yield t


def terms_equivalent(t1, t2, as_predicates=False):
    with PushPop():
        if as_predicates:
            z3_solver.add((t1==0) != (t2==0))
        else:
            z3_solver.add(t1 != t2)

        with stats.TimeIt('z3.check'):
            result = z3_solver.check()

        if result == z3.unsat:
            return True
        elif result == z3.sat:
            return False
        else:
            logging.warning('z3 timeout on ({}, {})'.format(t1, t2))
            return False
            #assert False, result


if __name__ == '__main__':
    import logging
    logging.basicConfig(level=logging.INFO)

    from enum_terms import base_enum

    size = 3
    required_ops = frozenset()
    allowed_ops = frozenset([0, 1, 'if0', 'plus', 'shl1', 'x'])

    #size = 8
    #required_ops = frozenset(['not', 'plus', 'shr16', 'shr1', 'or'])
    #allowed_ops = frozenset([0, 1, 'if0', 'shr16', 'plus', 'shr1', 'not', 'x', 'or'])

    with stats.TimeIt('enum terms'):
        terms = list(base_enum(size, required_ops, allowed_ops))
    print len(terms), 'terms'

    preds = list(filter_distinct(terms, as_predicates=True))
    print len(preds), 'distinct predicates'
    for pred in preds:
        print pred

    terms = list(filter_distinct(terms))
    print len(terms), 'distinct terms'
    for term in terms:
        print term

    stats.log_stats()
