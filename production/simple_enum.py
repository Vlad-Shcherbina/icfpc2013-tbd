from terms import *
from utils import cached
#from z3_utils import fresh_control, Control
from distinct import filter_distinct
import attach
import unique

import logging
logger = logging.getLogger('enum')


def base_enum(size, allowed_ops, fold=False):
    if size < 1:
        return

    # res = unique.get_unique(
    #     size, 'terms', allowed_ops | (frozenset(['fold']) if fold else frozenset()))
    # if res is not None:
    #     for t in res:
    #         yield t
    #     return

    if fold and size < 5:
        return
    if size == 1 and not fold:
        yield 0
        yield 1
        yield 'x'
    for op in allowed_ops:
        if op in ['y', 'z']:
            if size == 1 and not fold:
                yield op
        elif op in UNARY_OPS:
            for t in base_enum(size-1, allowed_ops, fold=fold):
               yield attach.propagate_attached((op, t))
        elif op in BINARY_OPS:
            for size1 in range(1, size):
                size2 = size - 1 - size1
                if size2 < 1:
                    continue
                for fold1 in False, True:
                    if fold1 and not fold:
                        continue
                    for t1 in base_enum(size1, allowed_ops, fold=fold1):
                        for t2 in base_enum(size2, allowed_ops, fold=fold and not fold1):
                            if t2 > t1:
                                continue
                            yield attach.propagate_attached((op, t1, t2))
        elif op == IF0:
            for t in enum_if0(size, allowed_ops, fold=fold):
                yield t
        else:
            assert False, op
    if fold:
        for t in enum_fold(size, allowed_ops, top_level=False):
            yield t


def enum_fold(size, allowed_ops, top_level):
    # If top_level is true, first term is only allowed to be 'x'.
    for size1 in range(1, size):
        if top_level and size1 != 1:
            continue
        size23 = size - 2 - size1
        if size23 < 2:
            continue
        for t1 in base_enum(size1, allowed_ops):
            if top_level:
                if t1 != 'x':
                    continue
            for size2 in reversed(range(1, size23)):  # favor smaller size3
                size3 = size23 - size2
                if size3 < 1:
                    continue
                for t2 in base_enum(size2, allowed_ops):
                    for t3 in base_enum(
                            size3, allowed_ops | set('yz')):
                        yield attach.eval_and_attach((FOLD, t1, t2, (LAMBDA, ('y', 'z'), t3)))


def enum_if0(size, allowed_ops, fold=False):
    for size1 in range(1, size):
        size23 = size - 1 - size1
        if size23 < 2:
            continue
        for fold1 in False, True:
            if fold1 and not fold:
                continue
            for pred in enum_preds(size1, allowed_ops, fold=fold1):
                for size2 in range(1, size23):
                    size3 = size23 - size2
                    if size3 < 1:
                        continue
                    if fold and not fold1:
                        fold23s = [(True, False), (False, True)]
                    else:
                        fold23s = [(False, False)]
                    for fold2, fold3 in fold23s:
                        for then in base_enum(size2, allowed_ops, fold=fold2):
                            for else_ in base_enum(size3, allowed_ops, fold=fold3):
                                yield attach.propagate_attached((IF0, pred, then, else_))


def enum_preds(size, allowed_ops, fold=False):
    if size < 1:
        return

    # res = unique.get_unique(
    #     size, 'preds', allowed_ops | (frozenset(['fold']) if fold else frozenset()))
    # if res is not None:
    #     for t in res:
    #         yield t
    #     return

    for t in base_enum(size, allowed_ops, fold=fold):
        yield t


def top_level_enum(size, operators):
    ops = frozenset(UNARY_OPS+BINARY_OPS+[IF0]) & frozenset(operators)

    if 'tfold' in operators:
        return enum_fold(size, ops, top_level=True)

    if 'fold' in operators:
        ops.add('fold')

    return base_enum(size, ops)


if __name__ == '__main__':
    ops = frozenset([IF0, 'tfold'])

    for t in top_level_enum(8, ops):
        print term_to_str(t)

