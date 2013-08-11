import logging
logger = logging.getLogger('brute')

import sys
import time
from random import randrange
import itertools

from terms import *
from simple_enum import top_level_enum, warmup_unique_db
import unique_db
import stats
import attach


NUMBERS_TO_TEST = [0] + [1 << i for i in [1, 2, 3, 4, 5, 15, 16, 31, 32, 63]]
NUMBERS_TO_TEST.extend([MASK ^ i for i in NUMBERS_TO_TEST])
NUMBERS_TO_TEST.extend(attach.POINTS)


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
    def solve(self, server, problem):
        def filter_candidates(candidates):
            num_tries = 0
            for candidate in candidates:
                fits = True
                for k, v in attach.get_attached_values(candidate).items():
                    if problem.values[k] != v:
                        fits = False
                        break
                if not fits:
                    continue
                num_tries += 1

                with stats.TimeIt('eval candidate'):
                    fits = True
                    cnt = 0
                    for x, y in problem.values.items():
                        cnt += 1
                        if evaluate(candidate, dict(x=x)) != y:
                            fits = False
                            #stats.add_value('filter_candidate evals', cnt)
                            break
                    #fits = all(
                    #    evaluate(candidate, dict(x=x)) == y
                    #    for x, y in problem.values.items())
                if fits:
                    stats.add_value(
                        problem.kind()+'_tries_to_find_candidate', num_tries)
                    yield candidate

        ops = problem.operators & unique_db.DB_OPS
        if 'fold' in problem.operators or 'tfold' in problem.operators:
            ops |= frozenset('yz')
            warmup_unique_db(min(3, problem.size-1), ops | frozenset('yz'))
        warmup_unique_db(min(4, problem.size-1), ops)

        candidates = itertools.chain(
            *(top_level_enum(size, problem.operators) for size in range(1, problem.size)))
        candidates = filter_candidates(candidates)

        return basic_solver_loop(server, problem, candidates, logger)


def basic_solver_loop(server, problem, candidates, logger):
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

        server.request_eval(problem, xs)
        logger.info('{} data points'.format(len(problem.values)))

        candidate = next(candidates, None)

        assert candidate is not None

        program = (LAMBDA, ('x',), candidate)

        attempts += 1
        if server.guess(problem, term_to_str(program)):
            logger.info('solved!')
            stats.add_value(problem.kind()+'_time', time.time()-start)
            stats.add_value(problem.kind()+'_attempts', attempts)

            size = term_size(program)
            stats.add_value('size_change_{}_{}'.format(problem.size, size), 1)

            return term_to_str(program)

        logger.warning('wrong guess')
