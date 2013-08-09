import logging
logger = logging.getLogger('communicate')

import urllib2
import json
import time
from pprint import pprint
from simple_settings import settings

BASE_URL = 'http://icfpc2013.cloudapp.net/'


class SendError(Exception):
    pass


# only used internally
def send(url, data = {}):
    data = json.dumps(data)
    while True:
        logger.debug('sending {} to {}'.format(data, url))
        try:
            response = urllib2.urlopen(
                BASE_URL + url + '?auth=' + settings['auth_token'] + 'vpsH1H',
                data=data)
        except urllib2.HTTPError as e:
            if e.code == 429:
                logger.warning('429: {}'.format(e.reason))
                time.sleep(10)
                continue
            raise
        response_text = response.read()
        logger.debug(
            'code: {}; response text: {}'.format(response.code, response_text))
        if response.code == 200:
            return json.loads(response_text)

        raise SendError(response.code, response_text)


def get_status():
    return send('status')


def eval_program(program, xs):
    assert program.startswith('(lambda')
    data = dict(program=program, arguments=['0x{:x}'.format(x) for x in xs])
    r = send('eval', data)
    assert len(r['outputs']) == len(xs)
    result = {}
    for x, y in zip(xs, r['outputs']):
        result[x] = int(y, 16)
    return result


class Problem(object):
    __slots__ = [
        'id',
        'size',
        'operators', # will be automatically converted to frozenset
        'solution',
        'values',
        'solved',
    ]

    def __init__(self, id, size, operators):
        self.id = id
        self.size = size
        self.operators = frozenset(operators)
        self.solution = None
        self.values = {}
        self.solved = None

    @staticmethod
    def from_json(js):
        result = Problem(
                str(js['id']),
                int(js['size']),
                map(str, js['operators']),
                )
        if 'solved' in js:
            result.solved = js['solved']
        return result

    def __repr__(self):
        attrs = ((s, getattr(self, s, None))
                for s in self.__slots__)
        return 'Problem({})'.format(', '.join(
            '{}={!r}'.format(s, it) for s, it in attrs if it is not None))

    def request_eval(self, xs):
        from statistics import is_actual_problem
        assert not is_actual_problem(self.id), 'we are not ready for real world yet'
        for x in xs:
            assert 0 <= x < 2**64
            assert x not in self.values, (x, 'already evaluated')
        assert len(xs) <= 256

        data = dict(id=self.id, arguments=['0x{:x}'.format(x) for x in xs])
        r = send('eval', data)
        assert len(r['outputs']) == len(xs)
        for x, y in zip(xs, r['outputs']):
            self.values[x] = int(y, 16)

    def guess(self, program):
        from statistics import is_actual_problem
        assert not is_actual_problem(self.id), 'we are not ready for real world yet'
        r = send('guess', dict(id=self.id, program=program))
        if r['status'] == 'win':
            return True
        elif r['status']:
            x, y1, y2 = r['values']
            logger.info('wrong guess: f({}) = {}, not {}'.format(x, y1, y2))
            x = int(x, 16)
            y1 = int(y1, 16)
            self.values[x] = y1
            return False

        assert False, r


def get_training_problem(size=None, operators=None):
    assert size is None or 3 <= size <= 20
    assert operators in [None, [], ['tfold'], ['fold']]

    data = {}
    if size is not None:
        data['size'] = size
    if operators is not None:
        data['operators'] = operators
    r = send('train', data)
    p = Problem.from_json(r)
    p.solution = str(r['challenge'])
    from statistics import is_actual_problem
    assert not is_actual_problem(p.id)

    return p

def get_real_problems():
    r = send('myproblems')
    return map(Problem.from_json, r)


if __name__ == '__main__':
    #logging.basicConfig(level=logging.DEBUG)

    pprint(get_status())
    #print get_training_problem(size=6)

    # p = Problem(
    #     id='X7yhOXLMakIJ1exPmd85dIwv',
    #     size=6,
    #     operators=['plus', 'shr1'])
    # p.solution = '(lambda (x_5126) (shr1 (plus 1 (shr1 x_5126))))'
    # print p
    # p.request_eval([1, 13, 2**64-1])
    # print p.values

    # If you guess right, problem will be removed and unavailable for guessing
    # anymore.
    #print p.guess('(lambda (x) x)')

    #print eval_program('(lambda (x) (plus x 1))', [1, 20])
