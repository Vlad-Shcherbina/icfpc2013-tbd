from simple_settings import settings
import logging
logger = logging.getLogger('communicate')

import urllib2
import json
import time
from pprint import pprint
from problem import Problem

BASE_URL = 'http://icfpc2013.cloudapp.net/'


class SendError(Exception):
    pass


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


def get_training_problem(size=None, operators=None):
    assert size is None or 3 <= size <= 30 or size in (42, 137)
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
    from solution_db import add_solved_problem
    add_solved_problem(p.id, True, p.size, p.operators, p.solution)
    return p

def get_training_problem_iter(size=None, operators=None):
    while True:
        yield get_training_problem(size, operators)

def get_real_problems():
    r = send('myproblems')
    return map(Problem.from_json, r)


def get_real_problems_to_solve(sizes, operator_predicate=None):
    problems = get_real_problems()
    if isinstance(sizes, int):
        sizes = (sizes,)
    problems = [
            p for p in problems
            if p.solved is None
            and p.size in sizes
            and (operator_predicate is None or operator_predicate(p))]
    return problems



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
