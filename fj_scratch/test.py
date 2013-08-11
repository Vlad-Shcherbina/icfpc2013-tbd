from common_initialization import log, settings
from pprint import pprint
from collections import namedtuple, Counter
import pickle, json, os, re
from os import path as os_path
from communicate import send, get_training_problem
from terms import parse_term
from problem import Problem
import local_server

# adjust log levels
import logging
logging.getLogger('unique_db').setLevel(logging.WARNING)
logging.getLogger('stats').setLevel(logging.WARNING)

log.info('Yo!')
        
 

import solver_driver
import brute_force_solver
from communicate import get_training_problem_iter


p = Problem('123', 10, ['not', 'xor', 'shr4', 'tfold'])
p.solution = '(lambda (x_6821) (fold x_6821 0 (lambda (x_6821 x_6822) (shr4 (xor (not x_6822) x_6821)))))' 
server = local_server.Server([p])
solver = brute_force_solver.Solver()
solver_driver.train(server, solver)

log.info('done')
