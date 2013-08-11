import sys, logging
logging.basicConfig(level=logging.DEBUG, stream=sys.stdout)

# disable annoying loggers (globally, unfortunately :/ )
logging.getLogger('unique_db').setLevel(logging.WARNING)
logging.getLogger('stats').setLevel(logging.WARNING)
logging.getLogger('solution_db').setLevel(logging.WARNING)
logging.getLogger('communicate').setLevel(logging.WARNING)

import solver_driver
import brute_force_solver
import local_server 
from communicate import get_training_problem_iter


server = local_server.Server(get_training_problem_iter(size=10), True)
solver = brute_force_solver.Solver()
solver_driver.train(server, solver)
