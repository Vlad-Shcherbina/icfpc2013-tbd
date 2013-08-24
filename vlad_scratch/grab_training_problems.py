import sys
sys.path.insert(0, '../production')  # to run outside of eclipse

import time

from communicate import get_training_problem
from solver_driver import setup_dual_logging


if __name__ == '__main__':
    setup_dual_logging()
    for i in range(100):
        print '*'*10, i
        for size in [42, 137]*3 + range(30, 15-1, -1):
            print size
            get_training_problem(size)
            time.sleep(1)
