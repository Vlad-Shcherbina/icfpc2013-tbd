import logging
logger = logging.getLogger('brute')

import sys
import time
from random import randrange
import itertools

from terms import *
from communicate import Problem, get_training_problem
from enum_terms import enumerate_terms


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
        return range(10, 10+1)

    @classmethod
    def is_applicable(cls, problem):
        if problem.size not in cls.supported_sizes():
            return False
        if 'if0' not in problem.operators:
            return False
        return True

    @classmethod
    def solve(cls, problem):
        assert cls.is_applicable(problem)

        def candidate_matches(candidate):
            return all(
                evaluate(candidate, dict(x=x)) == y
                for x, y in problem.values.items())

        candidates = enumerate_terms(problem.size-1, problem.operators)
        candidates = itertools.ifilter(candidate_matches, candidates)

        start = time.clock()
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

            logger.info(
                'time since start: {:.1f}s'.format(time.clock() - start))
            program = (LAMBDA, ('x',), candidate)
            if problem.guess(term_to_str(program)):
                logger.info('solved!')
                break

            logger.warning('wrong guess')
