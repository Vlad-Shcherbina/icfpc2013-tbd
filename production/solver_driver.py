import logging
logger = logging.getLogger('driver')

import sys
import time
import random
from collections import Counter

from terms import *
from communicate import get_status, Problem, get_training_problem
from enum_terms import simple_terms

import brute_force_solver


def train(solver):
    logger.info('================= training  ==================')
    solved = Counter()
    while True:
        logger.info('----------- trying another problem ------------')
        size = random.choice(solver.supported_sizes())
        p = get_training_problem(size=size)

        logger.info(str(p))

        if solver.is_applicable(p):
            solver.solve(p)
            solved[size] += 1
            logger.info(
                'Successfully solved problems of various sizes: {}'
                .format(solved))
        else:
            logger.info('dunno how to solve')

        time.sleep(10)


def setup_dual_logging():
    logging.getLogger().setLevel(logging.DEBUG)

    handler = logging.FileHandler('log.txt')
    formatter = logging.Formatter('%(asctime)s %(levelname)s:%(name)s: %(message)s')
    handler.setFormatter(formatter)
    handler.setLevel(logging.DEBUG)
    logging.getLogger().addHandler(handler)

    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter("%(levelname)s:%(name)s: %(message)s")
    handler.setFormatter(formatter)
    handler.setLevel(logging.INFO)
    logging.getLogger().addHandler(handler)


if __name__ == '__main__':
    setup_dual_logging()

    solver = brute_force_solver.Solver()

    print get_status()
    time.sleep(5)

    train(solver)

