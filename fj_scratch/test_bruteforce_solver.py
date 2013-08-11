import solver_driver
solver_driver.setup_dual_logging()

import brute_force_solver
import real_server 
from communicate import get_training_problem_iter

server = real_server.Server(get_training_problem_iter(size=137))
solver = brute_force_solver.Solver()
solver_driver.train(server, solver)
