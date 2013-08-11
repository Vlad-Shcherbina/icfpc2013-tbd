import sys
sys.path.append('../production')  # to run outside of eclipse

import os
import itertools
import time

from terms import *
import unique
from simple_enum import base_enum, enum_preds
from distinct import filter_distinct

import logging
logger = logging.getLogger('gen_unique')


def generate_unique(size, category, ops):

    #smaller_uniques = set()
    #for s in range(1, size):
    #    smaller_uniques |= set(unique.get_unique(s, category, ops))

    logging.info('generating {}'.format((size, category, ops)))
    filename = unique.ops_file(size, category, ops)
    if os.path.exists(filename):
        logging.info('already generated')
        return

    def progress_generator(xs):
        xs = list(xs)
        start = time.clock()
        time_to_report = start + 5
        for i, x in enumerate(xs):
            if (i+1) % 10 == 0 and time.clock() > time_to_report:
                remaining = (time.clock() - start) * (len(xs)-i) / i
                logger.info(
                    'progress {}% ({}/{}) (approx {:.1f}s remaining)'
                    .format(100*i/len(xs), i, len(xs), remaining))
                time_to_report = time.clock() + 5
            yield x

    fold = FOLD in ops
    ops -= frozenset([FOLD])
    terms = progress_generator(
        itertools.chain(
            *(base_enum(sz, ops, fold=fold)
            for sz in range(1, size+1))))
    ds = filter_distinct(terms, as_predicates=(category == 'preds'))

    ds = itertools.dropwhile(lambda t: term_size(t) < size, ds)
    ds = sorted(map(term_to_str, ds))

    with open(filename, 'w') as fout:
        for d in ds:
            print>>fout, d
    logger.info('done ({} terms were saved)'.format(len(ds)))

    unique.get_unique.clear_cache()  # because now new file was created



if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)

    ops = frozenset(['if0', 'not', 'or', 'plus', 'shl1', 'shr1', 'shr16', 'shr4', 'xor'])
    print unique.ops_dir(ops)

    for size in range(1, 5+1):
        generate_unique(size, 'terms', ops)
        generate_unique(size, 'preds', ops)
        #filename = ops_file(1, 'terms', ops)
        #if os.path.exists(filename):
        #    continue
        #logging.info('generating')


    pass