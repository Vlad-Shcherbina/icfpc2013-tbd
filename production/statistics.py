from pprint import pprint
from collections import Counter
from communicate import Problem, send
import json, pickle, re
import os
from os import path as os_path
import sys, logging 

MYPROBLEMS_FILE = '../data/myproblems.json'
CACHED_PROBLEM_IDS_FILE = '../data/cached_problem_ids.pickle'

_cached_problem_ids = None
_id_rx = re.compile(r'^[a-zA-Z0-9]{24}$')


def update_myproblems_file():
    r = send('myproblems')
    with open(MYPROBLEMS_FILE, 'wb') as f:
        json.dump(r, f, indent = 4)


def is_actual_problem(problem_id):
    # This is a very paranoid function
    global _cached_problem_ids
    assert _id_rx.match(problem_id), problem_id
    
    def sanity_check(ids):
        assert len(ids) == 1420 + 200 + 200
        assert all(_id_rx.match(id) for id in ids)
        
    if _cached_problem_ids is None:
        if not os_path.exists(MYPROBLEMS_FILE):
            # regenerate problems file
            update_myproblems_file()
            
        if (not os_path.exists(CACHED_PROBLEM_IDS_FILE) or
            os_path.getmtime(CACHED_PROBLEM_IDS_FILE) < os_path.getmtime(MYPROBLEMS_FILE)):
            # regenerate CACHED_PROBLEM_IDS_FILE
            problems = load_problems()
            ids = frozenset(problem.id for problem in problems)
            sanity_check(ids)
            with open(CACHED_PROBLEM_IDS_FILE, 'wb') as f:
                pickle.dump(ids, f)
        else:
            with open(CACHED_PROBLEM_IDS_FILE, 'rb') as f:
                ids = pickle.load(f)
            sanity_check(ids)
        _cached_problem_ids = ids
        
    return problem_id in _cached_problem_ids
        

def load_problems():
    with open(MYPROBLEMS_FILE) as f:
        problems = json.load(f)
    problems = map(Problem.from_json, problems)
    return problems


def print_count_of_problems(name, problems, predicate):
    print name
    counter = Counter()
    for p in problems:
        if predicate(p):
            counter[p.size] += 1
    total = sum(v for _k, v in counter.iteritems())
    print total, ':', ', '.join('{}:{}'.format(*kv) for kv in sorted(counter.iteritems()))

def make_predicate(s):
    conditions = s.split()
    present, absent = [], []
    for c in conditions:
        if c.startswith('!'):
            absent.append(c[1:])
        else:
            present.append(c)
    return lambda p: (
            all(c in p.operators for c in present) and 
            all(c not in p.operators for c in absent))

def print_problem_statistics():
    problems = load_problems() 
    assert not any('fold' in p.operators and 'tfold' in p.operators for p in problems)
    
    def print_count_of_problems_p(p, problems):
        return print_count_of_problems(p, problems, make_predicate(p))

    def print_categories(problems):
        print_count_of_problems_p('tfold !bonus', problems) 
        print_count_of_problems_p('fold !bonus', problems) 
        print_count_of_problems_p('if0 !fold !tfold !bonus', problems)
        print_count_of_problems_p('!if0 !fold !tfold !bonus', problems)
        print_count_of_problems_p('bonus', problems)
    
    solved = [p for p in problems if p.solved]
    remaining = [p for p in problems if not p.solved]
    print 'Total =', len(problems)
    print 
    print '---------- Solved:', len(solved)
    print_categories(solved)
    print
    print '---------- Remaining:', len(remaining)
    print_categories(remaining)
    print
    

def main():
    logging.basicConfig(level=logging.DEBUG, stream=sys.stdout)
#    update_myproblems_file()
    print_problem_statistics()

if __name__ == '__main__':
    main()
    
    