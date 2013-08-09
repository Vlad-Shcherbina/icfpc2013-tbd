import sys
sys.path.append('../production')  # to run outside of eclipse

import logging
logging.basicConfig(level=logging.DEBUG, stream=sys.stdout)
log = logging.getLogger('main')

from simple_settings import settings

