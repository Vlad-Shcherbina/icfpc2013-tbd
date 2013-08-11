import logging
logger = logging.getLogger('local_server')

class LocalServer(object):
    def __init__(self, problems):
        self.problems = problems
    def request_eval(self, problem, xs):
        assert False, 'Not implemented'

    def guess(self, problem, program):
        assert False, 'Not implemented'
        