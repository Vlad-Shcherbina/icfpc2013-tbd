import logging
logger = logging.getLogger('brute')

import sys
import time
from random import randrange
import itertools

from terms import *
from communicate import Problem, get_training_problem
from enum_terms import enumerate_terms
import stats


NUMBERS_TO_TEST = [0] + [1 << i for i in [1, 2, 3, 4, 5, 15, 16, 31, 32, 63]]
NUMBERS_TO_TEST.extend([MASK ^ i for i in NUMBERS_TO_TEST])


def random_interesting_number():
    if randrange(2) == 0:
        return randrange(2**64)
    size = randrange(1, 64)
    x = randrange(1 << size)
    if randrange(2) == 0:
        x <<= 64-size
    if randrange(2) == 0:
        x ^= MASK
    return x


class Solver(object):
    @classmethod
    def supported_sizes(cls):
        return range(3, 12+1)

    @classmethod
    def is_applicable(cls, problem):
        if problem.size not in cls.supported_sizes():
            return False
        return True

    @classmethod
    def solve(cls, problem):
        assert cls.is_applicable(problem)

        def filter_candidates(candidates):
            num_tries = 0
            for candidate in candidates:
                num_tries += 1
                if all(
                    evaluate(candidate, dict(x=x)) == y
                    for x, y in problem.values.items()):

                    stats.add_value(
                        problem.kind()+'_tries_to_find_candidate', num_tries)
                    yield candidate

        candidates = enumerate_terms(problem.size-1, problem.operators)
        candidates = filter_candidates(candidates)

        basic_solver_loop(problem, candidates, logger)


def basic_solver_loop(problem, candidates, logger):
    attempts = 0
    start = time.time()
    while True:
        time.sleep(5)
        xs = []
        for i in NUMBERS_TO_TEST:
            if i not in problem.values:
                xs.append(i)
        assert len(xs) <= 256
        while len(xs) < 256:
            while True:
                x = random_interesting_number()
                if x not in problem.values and x not in xs:
                    xs.append(x)
                    break

        problem.request_eval(xs)
        logger.info('{} data points'.format(len(problem.values)))

        candidate = next(candidates, None)

        assert candidate is not None

        program = (LAMBDA, ('x',), candidate)

        attempts += 1
        if problem.guess(term_to_str(program)):
            logger.info('solved!')
            stats.add_value(problem.kind()+'_time', time.time()-start)
            stats.add_value(problem.kind()+'_attempts', attempts)
            break

        logger.warning('wrong guess')
