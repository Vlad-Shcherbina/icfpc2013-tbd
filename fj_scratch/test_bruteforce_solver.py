import solver_driver
solver_driver.setup_dual_logging()

import brute_force_solver
import real_server 

server = real_server.Server()
solver = brute_force_solver.Solver()
solver_driver.train(server, solver)
