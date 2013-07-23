import sys
import logging

import nose


if __name__ == '__main__':
    nose.run(argv=sys.argv + [
        '--verbose', '--with-doctest', '--with-coverage',
        '--logging-level=DEBUG'
        ])
