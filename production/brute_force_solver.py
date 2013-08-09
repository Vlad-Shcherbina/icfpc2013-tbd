import logging
logger = logging.getLogger('brute')

import sys
import time
from random import randrange

from terms import *
from communicate import Problem, get_training_problem
from enum_terms import simple_terms


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
    @staticmethod
    def is_applicable(problem):
        if problem.size > 8:
            return False
        if 'if0' in problem.operators:
            return False
        if 'fold' in problem.operators:
            return False
        if 'tfold' in problem.operators:
            return False
        return True

    @staticmethod
    def solve(problem):
        candidates = simple_terms(
            problem.size-1, CONSTANTS + ['x'], UNARY_OPS, BINARY_OPS)

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
            logging.info('{} data points'.format(len(problem.values)))

            new_candidates = []
            for t in candidates:
                for x, y in problem.values.items():
                    if evaluate(t, dict(x=x)) != y:
                        break
                else:
                    new_candidates.append(t)

            candidates = new_candidates
            logging.info(
                '{} candidates(possibly eqivalent)'.format(len(candidates)))

            assert len(candidates) > 0

            logging.info(
                'time since start: {:.1f}s'.format(time.clock() - start))
            program = (LAMBDA, ('x',), candidates[0])
            if problem.guess(term_to_str(program)):
                logging.info('solved!')
                break

            logging.info('wrong guess')


if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO, stream=sys.stdout)

    while True:
        logging.info('----------- trying another problem ------------')
        p = get_training_problem(size=8)

        logging.info(str(p))

        if Solver.is_applicable(p):
            Solver.solve(p)
        else:
            logging.info('dunno how to solve')

        time.sleep(5)
