
import os

from utils import cached
from terms import *
import attach

import logging
logger = logging.getLogger('unique')



def ops_dir(ops):
    assert 'fold' not in ops
    assert 'tfold' not in ops
    assert 'bonus' not in ops
    return '../data/unique/' + '_'.join(sorted(ops))


def ops_file(size, category, ops):
    assert 'tfold' not in ops
    assert category in ['terms', 'preds']
    dir = ops_dir(set(ops) - set([0, 1, 'x', 'tfold', 'fold', 'bonus']))
    if not os.path.exists(dir):
        os.mkdir(dir)
    filename = '{}_{}'.format(size, category)

    if 'fold' in ops:
        filename += '_fold'
    if 'y' in ops:
        filename += '_yz'
    assert filename.count('_') <= 2, filename

    return '{}/{}.txt'.format(dir, filename)


@cached
def get_unique(size, category, ops):
    filename = ops_file(size, category, ops)
    if os.path.exists(filename):
        result = []
        with open(filename) as fin:
            for line in fin:
                line = line.strip()
                t = parse_any_term(line)
                assert term_to_str(t) == line, (t, line)
                t = attach.eval_and_attach(t)
                result.append(t)
        return result

    return None
