from terms import *
from utils import cached

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


def base_enum(size, required_ops, allowed_ops):
    if sum(MIN_SIZE[op] for op in required_ops) - len(required_ops) + 1 > size:
        return
    for op in allowed_ops:
        new_req = required_ops - set([op])
        if op in [0, 1, 'x', 'y', 'z']:
            if len(new_req) == 0 and size == 1:
                yield op
        elif op in UNARY_OPS:
            for t in base_enum(size-1, new_req, allowed_ops):
                yield (op, t)
        elif op in BINARY_OPS:
            for s in range(1, size-1):
                for t1 in base_enum(s, set(), allowed_ops):
                    new_new_req = new_req - term_op(t1)
                    for t2 in base_enum(size-1-s, new_new_req, allowed_ops):
                        if t2 > t1:
                            continue
                        yield (op, t1, t2)
                pass
        elif op == IF0:
            for t in enum_if0(size, allowed_ops):
                yield t
        elif op == FOLD:
            for t in enum_fold(size, new_req, allowed_ops - set([FOLD]), top_level=False):
                yield t
        else:
            assert False


def enum_fold(size, required_ops, allowed_ops, top_level):
    assert 'fold' not in required_ops
    assert 'fold' not in allowed_ops
    for s1 in range(1, size-3):
        if top_level:
            t1_candidates = ['x']
        else:
            t1_candidates = base_enum(s1, set(), allowed_ops)
        for t1 in t1_candidates:
            new_req = required_ops - term_op(t1)
            for s2 in range(1, size-2-s1):
                for t2 in base_enum(s2, set(), allowed_ops):
                    new_new_req = new_req - term_op(t2)
                    for t3 in base_enum(size-2-s1-s2, new_new_req, allowed_ops | set('yz')):
                        yield (FOLD, t1, t2, (LAMBDA, ('y', 'z'), t3))


def enum_if0(size, allowed_ops):
    for s1 in range(1, size-2):
        for pred in generate_distinct_predicates(s1, frozenset(allowed_ops)):
            for s2 in range(1, size-1-s1):
                for then in base_enum(s2, set(), allowed_ops):
                    for else_ in base_enum(size-1-s1-s2, set(), allowed_ops):
                        yield (IF0, pred, then, else_)


@cached
def generate_distinct_predicates(size, allowed_ops):
    logger.debug('generate distinct predicates {} {}'.format(size, allowed_ops))
    predicates = []
    for t in base_enum(size, set(), allowed_ops):
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
        #z3_solver.add(t1 != t2)

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

    size = 6
    cnt = 0
    operators = set([IF0, NOT, SHL1])

    for t in enumerate_terms(size, operators):
        print term_to_str(t)
        assert term_size(t) == size
        #assert term_op(t) == operators
        cnt += 1
    print cnt
