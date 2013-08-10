from terms import *
from utils import cached, frozen_powerset

from z3_utils import *

import logging
logger = logging.getLogger('enum')



MIN_SIZE = {
    0: 1,
    1: 1,
    'x': 1,
    NOT: 2,
    SHL1: 2,
    SHR1: 2,
    SHR4: 2,
    SHR16: 2,
    PLUS: 3,
    AND: 3,
    OR: 3,
    XOR: 3,
    FOLD: 5,
    IF0: 4,
}


def size_lower_bound(required_ops):
    return sum(MIN_SIZE[op] for op in required_ops) - len(required_ops) + 1


def base_enum(size, required_ops, allowed_ops):
    if size_lower_bound(required_ops) > size:
        return
    for op in allowed_ops:
        req = required_ops - set([op])
        if op in [0, 1, 'x', 'y', 'z']:
            if len(req) == 0 and size == 1:
                yield op
        elif op in UNARY_OPS:
            for t in base_enum(size-1, req, allowed_ops):
                yield (op, t)
        elif op in BINARY_OPS:
            for size1 in range(1, size):
                size2 = size - 1 - size1
                if size2 < 1:
                    continue
                for req1 in frozen_powerset(req):
                    req2 = req - req1
                    if size_lower_bound(req2) > size2:
                        continue
                    for t1 in base_enum(size1, req1, allowed_ops-req2):
                        for t2 in base_enum(size2, req2, allowed_ops):
                            if t2 > t1:
                                continue
                            yield (op, t1, t2)
        elif op == IF0:
            for t in enum_if0(size, req, allowed_ops):
                yield t
        elif op == FOLD:
            for t in enum_fold(size, req, allowed_ops - set([FOLD]), top_level=False):
                yield t
        else:
            assert False


def enum_fold(size, required_ops, allowed_ops, top_level):
    # If top_level is true, first term is only allowed to be 'x'.
    assert FOLD not in required_ops
    assert FOLD not in allowed_ops
    for size1 in range(1, size):
        if top_level and size1 != 1:
            continue
        size23 = size - 2 - size1
        if size23 < 2:
            continue
        for req1 in frozen_powerset(required_ops):
            req23 = required_ops - req1
            if size_lower_bound(req23)+1 > size23:
                # plus 1 because there are two terms
                continue
            for t1 in base_enum(size1, req1, allowed_ops-req23):
                if top_level and t1 != 'x':
                    continue
                for size2 in range(1, size23):
                    size3 = size23 - size2
                    if size3 < 1:
                        continue
                    for req2 in frozen_powerset(req23):
                        req3 = req23 - req2
                        if size_lower_bound(req3) > size3:
                            continue
                        for t2 in base_enum(size2, req2, allowed_ops-req3):
                            for t3 in base_enum(
                                    size3, req3, allowed_ops | set('yz')):
                                yield (FOLD, t1, t2, (LAMBDA, ('y', 'z'), t3))


def enum_if0(size, required_ops, allowed_ops):
    for size1 in range(1, size):
        size23 = size - 1 - size1
        if size23 < 2:
            continue
        for req1 in frozen_powerset(required_ops):
            req23 = required_ops - req1
            if size_lower_bound(req23)+1 > size23:
                # plus 1 because there are two terms
                continue
            for pred in generate_distinct_predicates(
                size1, frozenset(req1), frozenset(allowed_ops-req23)):
                for size2 in range(1, size23):
                    size3 = size23 - size2
                    if size3 < 1:
                        continue
                    for req2 in frozen_powerset(req23):
                        req3 = req23 - req2
                        if size_lower_bound(req3) > size3:
                            continue
                        for then in base_enum(size2, req2, allowed_ops-req3):
                            for else_ in base_enum(size3, req3, allowed_ops):
                                yield (IF0, pred, then, else_)


@cached
def generate_distinct_predicates(size, required_ops, allowed_ops):
    logger.debug('generate distinct predicates {} {} {}'.format(size, required_ops, allowed_ops))
    predicates = []
    for t in base_enum(size, required_ops, allowed_ops):
        for p in predicates:
            if predicates_equivalent(p, t, in_fold_lambda='y' in allowed_ops):
                break
        else:
            predicates.append(t)
    logger.debug('{} predicates'.format(len(predicates)))
    return predicates


X = z3.BitVec('x', 64)
Y = z3.BitVec('y', 64)
Z = z3.BitVec('z', 64)
def predicates_equivalent(t1, t2, in_fold_lambda=False):
    if in_fold_lambda:
        vars=dict(x=X, y=Y, z=Z)
    else:
        vars=dict(x=X)
    t1 = term_to_z3(t1, vars)
    t2 = term_to_z3(t2, vars)

    with PushPop():
        z3_solver.add((t1==0) != (t2==0))

        result = z3_solver.check()
        if result == z3.unsat:
            return True
        elif result == z3.sat:
            return False
        else:
            assert False, result


def enumerate_terms(size, operators):
    unaries = [op for op in UNARY_OPS if op in operators]
    binaries = [op for op in BINARY_OPS if op in operators]

    ops = set(UNARY_OPS+BINARY_OPS+[IF0]) & set(operators)

    if 'tfold' in operators:
        return enum_fold(size, ops, set([0, 1, 'x']) | ops, top_level=True)

    if 'fold' in operators:
        ops.add('fold')

    return base_enum(size, ops, set([0, 1, 'x']) | ops)


if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)

    size = 5
    cnt = 0
    operators = set([IF0, NOT])

    for t in enumerate_terms(size, operators):
        print term_to_str(t)
        assert term_size(t) == size
        #assert term_op(t) == operators
        cnt += 1
    print cnt
