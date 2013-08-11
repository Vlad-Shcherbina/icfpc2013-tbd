from common_initialization import log, settings
from pprint import pprint
from collections import namedtuple, Counter
import pickle, json, os, re
from os import path as os_path
from communicate import Problem, send, get_training_problem
from terms import parse_term



def update_problem_dump():
    with open('../data/myproblems.json', 'wb') as f:
        json.dump(send('myproblems'), f, indent=4)


def load_cached(fname, f):
    if os_path.exists(fname):
        with open(fname, 'rb') as f:
            return pickle.load(f)
    else:
        data = f()
        with open(fname, 'wb') as f:
            pickle.dump(data, f)
        return data
        

if __name__ == '__main__':
    log.info('Yo!')
    p = get_training_problem(137)
#    pprint(p.solution)
    pprint(parse_term(p.solution))
    log.info('done')
