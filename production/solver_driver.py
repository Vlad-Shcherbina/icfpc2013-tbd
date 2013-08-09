import logging
logger = logging.getLogger('driver')

import sys
import time
import random
from collections import Counter

from terms import *
from communicate import get_status, Problem
from communicate import get_real_problems, get_training_problem
from enum_terms import simple_terms

import brute_force_solver


def train(solver):
    logger.info('================= training  ==================')
    solved = Counter()
    while True:
        logger.info('----------- trying another problem ------------')
        size = random.choice(solver.supported_sizes())
        p = get_training_problem(size=size) #, operators=['tfold'])

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


def actually_fucking_solve(solver):
    problems = get_real_problems()
    problems = [
        p for p in problems if p.solved is None and solver.is_applicable(p)]
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
        print 'waiting 20s...'
        time.sleep(20)  # sleep to clear any resource window for sure

        #print 'do you think it\'s a good idea to try to solve'
        #print problem
        #print 'with {}?'.format(solver)
        #answer = raw_input()
        #if answer != 'yes':
        #    exit()

        logger.info('solving {}'.format(problem))
        logger.info('using {}'.format(solver))
        solver.solve(problem)

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
    setup_dual_logging()

    solver = brute_force_solver.Solver()

    #print get_status()
    #time.sleep(5)

    #train(solver)

    actually_fucking_solve(solver)

