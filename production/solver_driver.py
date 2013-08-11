import logging
logger = logging.getLogger('driver')

import sys
import time
import random

from terms import *
from communicate import get_status, Problem
from communicate import get_real_problems, get_training_problem
import stats
from solution_db import add_solved_problem

import brute_force_solver
import shape_solver


def train(server, solver):
    logger.info('================= training  ==================')
    while True:
        problem = server.get_problem()
        if problem is None:
            logger.info('No more problems to solve')
            break
        logger.info('----------- trying problem {} ------------'.format(problem))

        solver.solve(server, problem)
        stats.add_value('solved', 0)
        stats.log_stats()


def actually_fucking_solve(server, solver):
    problems = server.get_all_problems()

    # To ensure that in case of failure we return to the same problem.
    problems.sort(key=lambda p: (p.kind(), len(p.operators), p.id))

    logger.info(
        'following {} problems look amenable to {}'
        .format(len(problems), solver))
    for p in problems:
        logger.info(str(p))

    print '*'*50
    print 'Detailed logs are written to log.txt.'
    print 'Any failures have to be carefully investigated,'
    print 'because that\'s fucking POINTS we are talking about!'
    print 'Don\'t forget to ask teammates for '
    print 'exclusive access to the server!!!'
    print
    print 'Also, make sure that solver showed itself excellent in training'
    print '*'*50

    print 'do you think it\'s a good idea to try to solve all this shit'
    print 'with {}?'.format(solver)
    answer = raw_input()
    if answer != 'yes':
        exit()

    print '************'
    print 'DO NOT TERMINATE EXCEPT ON THE "waiting" MESSAGE!!!'

    for problem in problems:
        logger.info('----------- trying problem {} ------------'.format(problem))

        logger.info('solving {}'.format(problem))
        logger.info('using {}'.format(solver))
        solution = solver.solve(server, problem)

        add_solved_problem(problem.id, False, problem.size, problem.operators, solution)

        stats.add_value('solved', 0)
        stats.log_stats()

    print 'done'


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
    import real_server
    from communicate import get_training_problem_iter

    setup_dual_logging()

    solver = brute_force_solver.Solver()
    #solver = shape_solver.Solver()

    server = real_server.Server(get_training_problem_iter(size=12))
    train(server, solver)

    #actually_fucking_solve(server, solver)

