from terms import *
from utils import cached, frozen_powerset
from z3_utils import fresh_control, Control
from distinct import filter_distinct
import attach

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


def base_enum(size, required_ops, allowed_ops, shapes=False):
    if size_lower_bound(required_ops) > size:
        return []

    if not shapes and size < 6:
        return generate_distinct_terms(
            size, frozenset(required_ops), frozenset(allowed_ops))

    return base_enum_impl(size, required_ops, allowed_ops, shapes=shapes)


def base_enum_impl(size, required_ops, allowed_ops, shapes=False):
    if shapes:
        assert len(required_ops) == 0
        leafs = [op for op in [0, 1, 'x', 'y', 'z'] if op in allowed_ops]
        unaries = [op for op in UNARY_OPS if op in allowed_ops]
        binaries = [op for op in BINARY_OPS if op in allowed_ops]
        if leafs and size == 1:
            yield fresh_control(leafs)
        if unaries:
            for t in enum_unary(
                fresh_control(unaries), size, set(), allowed_ops, shapes=shapes):
                yield t
        if binaries:
            for t in enum_binary(
                fresh_control(binaries), size, set(), allowed_ops, shapes=shapes):
                yield t

    for op in allowed_ops:
        req = required_ops - set([op])
        if op in [0, 1, 'x', 'y', 'z']:
            if not shapes:
                if len(req) == 0 and size == 1:
                    yield op
        elif op in UNARY_OPS:
            if not shapes:
                for t in enum_unary(op, size, req, allowed_ops, shapes=shapes):
                    yield t
        elif op in BINARY_OPS:
            if not shapes:
                for t in enum_binary(op, size, req, allowed_ops, shapes=shapes):
                    yield t
        elif op == IF0:
            for t in enum_if0(size, req, allowed_ops, shapes=shapes):
                yield t
        elif op == FOLD:
            for t in enum_fold(
                size, req, allowed_ops - set([FOLD]), top_level=False, shapes=shapes):
                yield t
        else:
            assert False, op


att = attach.TupleWithValues.create

def enum_unary(op, size, required_ops, allowed_ops, shapes=False):
    for t in base_enum(size-1, required_ops, allowed_ops, shapes=shapes):
       yield att((op, t))


def enum_binary(op, size, required_ops, allowed_ops, shapes=False):
    for size1 in range(1, size):
        size2 = size - 1 - size1
        if size2 < 1:
            continue
        for req1 in frozen_powerset(required_ops):
            req2 = required_ops - req1
            if size_lower_bound(req2) > size2:
                continue
            for t1 in base_enum(size1, req1, allowed_ops-req2, shapes=shapes):
                for t2 in base_enum(size2, req2, allowed_ops, shapes=shapes):
                    # TODO: commutativity cutoff for shapes
                    if not shapes and t2 > t1:
                        continue
                    yield att((op, t1, t2))


def enum_fold(size, required_ops, allowed_ops, top_level, shapes=False):
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
            for t1 in base_enum(size1, req1, allowed_ops-req23, shapes=shapes):
                if top_level:
                    if isinstance(t1, Control):
                        if 'x' not in t1.operations:
                            continue
                        t1 = 'x'
                    if t1 != 'x':
                        continue
                for size2 in reversed(range(1, size23)):  # favor smaller size3
                    size3 = size23 - size2
                    if size3 < 1:
                        continue
                    for req2 in frozen_powerset(req23):
                        req3 = req23 - req2
                        if size_lower_bound(req3) > size3:
                            continue
                        for t2 in base_enum(size2, req2, allowed_ops-req3, shapes=shapes):
                            for t3 in base_enum(
                                    size3, req3, allowed_ops | set('yz'), shapes=shapes):
                                yield att((FOLD, t1, t2, (LAMBDA, ('y', 'z'), t3)))


def enum_if0(size, required_ops, allowed_ops, shapes=False):
    for size1 in range(1, size):
        size23 = size - 1 - size1
        if size23 < 2:
            continue
        for req1 in frozen_powerset(required_ops):
            if size_lower_bound(req1) > size1:
                # to avoid caching empty lists in generate_distinct_predicates
                continue
            req23 = required_ops - req1
            if size_lower_bound(req23)+1 > size23:
                # plus 1 because there are two terms
                continue
            for pred in enum_predicates(
                size1, req1, allowed_ops-req23, shapes=shapes):
                for size2 in range(1, size23):
                    size3 = size23 - size2
                    if size3 < 1:
                        continue
                    for req2 in frozen_powerset(req23):
                        req3 = req23 - req2
                        if size_lower_bound(req3) > size3:
                            continue
                        for then in base_enum(size2, req2, allowed_ops-req3, shapes=shapes):
                            for else_ in base_enum(size3, req3, allowed_ops, shapes=shapes):
                                yield att((IF0, pred, then, else_))


def enum_predicates(size, required_ops, allowed_ops, shapes=False):
    # TODO: fix code duplicatoin
    if shapes:
        assert len(required_ops) == 0
    if shapes and size > 4 or size > 6:
        return base_enum(size, required_ops, allowed_ops, shapes=shapes)
    distinct = generate_distinct_predicates(
        size, frozenset(required_ops), frozenset(allowed_ops))
    if shapes:
        return [fresh_control(distinct)]
    else:
        return distinct



@cached
def generate_distinct_terms(size, required_ops, allowed_ops):
    logger.debug('generate distinct terms {} {} {}'.format(size, required_ops, allowed_ops))
    predicates = filter_distinct(base_enum_impl(size, required_ops, allowed_ops), as_predicates=False)
    logger.debug('{} terms'.format(len(predicates)))
    return predicates


@cached
def generate_distinct_predicates(size, required_ops, allowed_ops):
    logger.debug('generate distinct predicates {} {} {}'.format(size, required_ops, allowed_ops))
    predicates = filter_distinct(base_enum(size, required_ops, allowed_ops), as_predicates=True)
    logger.debug('{} predicates'.format(len(predicates)))
    return predicates


def enumerate_terms(size, operators, shapes=False):
    ops = set(UNARY_OPS+BINARY_OPS+[IF0]) & set(operators)

    if 'tfold' in operators:
        if shapes:
            required_ops = set()
        else:
            required_ops = ops
        required_ops = set()
        return enum_fold(size, required_ops, set([0, 1, 'x']) | ops, top_level=True, shapes=shapes)

    if 'fold' in operators:
        ops.add('fold')

    if shapes:
        required_ops = set()
    else:
        required_ops = ops
    required_ops = set()
    return base_enum(size, required_ops, set([0, 1, 'x']) | ops, shapes=shapes)


if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)

    #size = 10
    #operators = set([IF0, NOT, SHL1, AND, OR, FOLD])
    size = 5
    operators=frozenset(['or'])

    cnt = 0
    for t in enumerate_terms(size, operators):
        print term_to_str(t)
        assert term_size(t) == size
        #assert term_op(t) == operators
        cnt += 1
    print cnt
