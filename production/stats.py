import logging
logger = logging.getLogger('stats')

from math import sqrt

from collections import defaultdict


stats = defaultdict(list)


def add_value(name, value):
    logger.debug('{} {}'.format(name, value))
    stats[name].append(value)


def list_stats_to_str(xs):
    assert xs != []

    result = []
    result.append('n={}'.format(len(xs)))
    if len(xs) == 1:
        result.append(str(xs[0]))
    else:
        mean = 1.0*sum(xs)/len(xs)
        sigma2 = sum((x-mean)**2 for x in xs) / (len(xs)-1.0)
        sigma = sqrt(sigma2)
        result.append('mean={:.1f}+-{:.1f}'.format(mean, sigma/sqrt(len(xs))))
        result.append('sigma={:.1f}'.format(sigma))
        result.append('min={}'.format(min(xs)))
        result.append('max={}'.format(max(xs)))

    return ', '.join(result)


def log_stats():
    logger.info('-'*20)
    for k, v in sorted(stats.items()):
        logger.info('{}: {}'.format(k, list_stats_to_str(v)))
    logger.info('-'*20)


if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)
    add_value('zzz', 1)
    add_value('x', 2.4)
    add_value('x', 1.5)

    for _ in range(1):
        for i in range(10):
            add_value('i', i)

    log_stats()
