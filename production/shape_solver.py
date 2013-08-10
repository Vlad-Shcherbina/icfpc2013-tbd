import sys
import time
from random import randrange
import itertools

from z3_utils import *
from brute_force_solver import random_interesting_number, basic_solver_loop
from enum_terms import enumerate_terms
import stats

import logging
logger = logging.getLogger('shape')


class Solver(object):
    @classmethod
    def supported_sizes(cls):
        return range(7, 7+1)

    @classmethod
    def is_applicable(cls, problem):
        if problem.size not in cls.supported_sizes():
            return False
        return True

    @classmethod
    def solve(cls, problem):
        assert cls.is_applicable(problem)

        def find_candidates(shapes):
            num_tries = 0
            for shape in shapes:
                num_tries += 1

                logger.info('trying shape {}'.format(shape))

                input_var = z3.BitVec('input_var', 64)
                with stats.TimeIt('building controlled term'):
                    z3t = term_to_z3(shape, dict(x=input_var))
                with stats.TimeIt('z3.simplify(controlled term)'):
                    z3t = z3.simplify(z3t)

                def check(z3t, values):
                    K = 5
                    with PushPop():
                        candidate = 0

                        for i, (x, y) in enumerate(values):
                            instance = z3.substitute(
                                z3t, (input_var, z3.BitVecVal(x, 64)))
                            z3_solver.add(instance == y)

                            if evaluate(candidate, dict(x=x)) != y:
                                logging.debug('refining model at {}'.format(i))

                            with stats.TimeIt('toplevel z3.solve'):
                                result = z3_solver.check()

                            if result == z3.sat:
                                model = z3_solver.model()
                                candidate = instantiate_controls_from_model(shape, model)
                            elif result == z3.unsat:
                                return None
                            else:
                                assert False, result
                        return candidate

                while True:
                    candidate = check(z3t, problem.values.items())
                    if candidate is not None:
                        logging.info('candidate {}'.format(candidate))

                        stats.add_value(
                            problem.kind()+'_tries_to_find_candidate', num_tries)

                        yield candidate
                        # There is a possibility that our guess is wrong
                        # and we need to try other candidates form the same
                        # shape.
                    else:
                        logging.info('unsat')
                        break

        shapes = enumerate_terms(problem.size-1, problem.operators, shapes=True)
        candidates = find_candidates(shapes)

        #next(shape)

        basic_solver_loop(problem, candidates, logger)


if __name__ == '__main__':
    from communicate import Problem
    logging.basicConfig(level=logging.INFO)

    #problem = Problem(id='e2Px5WLEXSodoiEu4oERz7Id', size=4, operators=frozenset(['and']))
    solver = Solver()
    solver.solve(problem)
