import logging
logger = logging.getLogger('some_module')


def f():
    '''
    Helpful usage example:
    >>> f()
    42
    '''
    logger.info('f...')
    return 42
