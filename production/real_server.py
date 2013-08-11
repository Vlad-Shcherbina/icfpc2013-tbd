import logging
logger = logging.getLogger('real_server')

import communicate, statistics

class Server(object):
    def __init__(self, training=True):
        self.training = training
        
    def check_if_we_are_for_real(self, problem):
        if self.training:
            assert not statistics.is_actual_problem(problem.id), 'we are not ready for real world yet'
        
    def request_eval(self, problem, xs):
        self.check_if_we_are_for_real(problem)
        
        for x in xs:
            assert 0 <= x < 2 ** 64
            assert x not in problem.values, (x, 'already evaluated')
        assert len(xs) <= 256

        data = dict(id=problem.id, arguments=['0x{:x}'.format(x) for x in xs])
        r = communicate.send('eval', data)
        assert len(r['outputs']) == len(xs)
        for x, y in zip(xs, r['outputs']):
            problem.values[x] = int(y, 16)

    def guess(self, problem, program):
        self.check_if_we_are_for_real(problem)
        
        r = communicate.send('guess', dict(id=problem.id, program=program))
        if r['status'] == 'win':
            return True
        elif r['status']:
            x, y1, y2 = r['values']
            logger.info('wrong guess: f({}) = {}, not {}'.format(x, y1, y2))
            x = int(x, 16)
            y1 = int(y1, 16)
            problem.values[x] = y1
            return False

        assert False, r


