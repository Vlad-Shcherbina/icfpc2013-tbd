from common_initialization import log, settings
from pprint import pprint
from collections import namedtuple, Counter
import pickle, json, os, re
from os import path as os_path
from communicate import Problem, send, get_training_problem

def load_cached(fname, f):
    if os_path.exists(fname):
        with open(fname, 'rb') as f:
            return pickle.load(f)
    else:
        data = f()
        with open(fname, 'wb') as f:
            pickle.dump(data, f)
        return data
        

def main():
    problems = load_cached('temp_problems.pickle', lambda: send('myproblems'))
    print len(problems)
#    p = get_training_problem(5, [])
#    p.solution = '(lambda (x_5126) (shr1 (plus 1 (shr1 x_5126))))'
#    print p
#    p.request_eval([1, 13, 2**64-1])
#    print p.values    
        
from terms import *


    

if __name__ == '__main__':
    log.info('Yo!')
    pprint(parse_term('(lambda (x_3199) (xor x_3199 (shl1 x_3199)))'))
    log.info('done')
