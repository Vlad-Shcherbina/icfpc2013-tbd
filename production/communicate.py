import logging
logger = logging.getLogger('communicate')

import urllib2
import json


BASE_URL = 'http://icfpc2013.cloudapp.net/'

with open('../data/auth_token.txt') as fin:
    auth = fin.read().strip()


class SendError(Exception):
    pass


# only used internally
def send(url, data):
    data = json.dumps(data)
    logger.debug('sending {} to {}'.format(data, url))
    response = urllib2.urlopen(
        BASE_URL + url + '?auth=' + auth + 'vpsH1H', data=data)
    response_text = response.read()
    logger.debug(
        'code: {}; response text: {}'.format(response.code, response_text))
    if response.code == 200:
        return json.loads(response_text)
    raise SendError(response.code, response_text)


def get_status():
    return send('status', {})


class Problem(object):
    __slots__ = [
        'id',
        'size',
        'operators',
        'solution',
        'training',  # bool
        'values',
    ]

    def __init__(self, **kwargs):
        self.values = {}
        for k, v in kwargs.items():
            setattr(self, k, v)

    def __str__(self):
        return 'Problem({})'.format(', '.join(
            '{}={!r}'.format(s, getattr(self, s))
            for s in self.__slots__
            if hasattr(self, s)))

    def request_eval(self, xs):
        assert self.training, 'we are not ready for real world yet'
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
    assert operators in [None, 'tfold', 'fold']

    data = {}
    if size is not None:
        data['size'] = size
    if operators is not None:
        data['operators'] = operators
    r = send('train', data)
    p = Problem(
        id=r['id'], size=r['size'], operators=r['operators'], training=True)
    p.solution = r['challenge']
    p.training = True
    return p


if __name__ == '__main__':
    #logging.basicConfig(level=logging.DEBUG)

    #print get_status()
    #print get_training_problem(size=6)

    p = Problem(
        id=u'X7yhOXLMakIJ1exPmd85dIwv',
        size=6, operators=[u'plus', u'shr1'],
        solution=u'(lambda (x_5126) (shr1 (plus 1 (shr1 x_5126))))',
        training=True)
    print p
    p.request_eval([1, 13, 2**64-1])
    print p.values

    # If you guess right, problem will be removed and unavailable for guessing
    # anymore.
    #print p.guess('(lambda (x) x)')
