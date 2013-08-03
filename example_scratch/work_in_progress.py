import sys
sys.path.append('../production')  # to run outside of eclipse

import logging
logging.basicConfig(level=logging.WARNING, stream=sys.stdout)
logger = logging.getLogger('main')
logger.setLevel(logging.DEBUG)


import some_module


def g():
    return some_module.f()**2


if __name__ == '__main__':
    logger.debug('zzz')
    print g()
