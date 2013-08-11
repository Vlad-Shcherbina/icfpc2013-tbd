import time
import gc

from terms import *
from utils import cached
#from z3_utils import fresh_control, Control
from distinct import filter_distinct
import attach
import unique_db
import stats
import z3_utils

import logging
logger = logging.getLogger('enum')


@cached
def list_unique(type, size, allowed_ops):
    db = unique_db.get_unique_db(type)
    if db.is_complete_for(unique_db.Constraint(size, allowed_ops)):
        return map(attach.eval_and_attach, db.get_unique_terms(size, allowed_ops))
    else:
        return None


def base_enum(size, allowed_ops, fold=False):
    if size < 1:
        return

    if not fold:
        u = list_unique('terms', size, allowed_ops)
        if u is not None:
            for t in u:
                yield t
            return

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

    if not fold:
        u = list_unique('preds', size, allowed_ops)
        if u is not None:
            for t in u:
                yield t
            return

    for t in base_enum(size, allowed_ops, fold=fold):
        yield t


def top_level_enum(size, operators):
    ops = frozenset(UNARY_OPS+BINARY_OPS+[IF0]) & frozenset(operators)

    if 'bonus' in operators:
        return enum_if0(size, ops, fold=('fold' in operators))
    if 'tfold' in operators:
        return enum_fold(size, ops, top_level=True)

    return base_enum(size, ops, fold=('fold' in operators))


def populate_unique_db(size, ops):
    for type in 'terms', 'preds':
        db = unique_db.get_unique_db(type)
        c = unique_db.Constraint(size, ops)
        if db.is_complete_for(c):
            continue

        terms = base_enum(size, ops)

        def progress_generator(xs):
            xs = list(xs)
            #print 'list created'
            start = time.clock()
            time_to_report = start + 5
            for i, x in enumerate(xs):
                if (i+1) % 5 == 0 and time.clock() > time_to_report:
                    remaining = (time.clock() - start) * (len(xs)-i) / i
                    logger.info(
                        'progress {}% ({}/{}) (approx {:.1f}s remaining)'
                        .format(100*i/len(xs), i, len(xs), remaining))
                    time_to_report = time.clock() + 5
                    gc.collect()
                    z3_utils.z3_solver.reset()
                yield x

        db.complete(c, progress_generator(terms))
        list_unique.clear_cache()
        db.save_and_destroy()


def warmup_unique_db(size, ops):
    with stats.TimeIt('warming up unique db'):
        populate_unique_db(1, frozenset())
        for i in range(1, size+1):
            populate_unique_db(i, ops)


if __name__ == '__main__':
    import logging
    logging.basicConfig(level=logging.INFO)

    warmup_unique_db(7, unique_db.DB_OPS - frozenset([XOR, PLUS, 'y', 'z']))
    #warmup_unique_db(5, unique_db.DB_OPS)
