from pprint import pprint
from collections import Counter
from communicate import Problem 
import json, pickle, re
import os
from os import path as os_path

MYPROBLEMS_FILE = '../data/myproblems.json'
CACHED_PROBLEM_IDS_FILE = '../data/cached_problem_ids.pickle'

_cached_problem_ids = None
_id_rx = re.compile(r'^[a-zA-Z0-9]{24}$')

def is_actual_problem(problem_id):
    # This is a very paranoid function
    global _cached_problem_ids
    assert _id_rx.match(problem_id), problem_id
    
    def sanity_check(ids):
        assert all(_id_rx.match(id) for id in ids)
        
    if _cached_problem_ids is None:
        if (not os_path.exists(CACHED_PROBLEM_IDS_FILE) or
            os_path.getmtime(CACHED_PROBLEM_IDS_FILE) < os_path.getmtime(MYPROBLEMS_FILE)):
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
    pprint(sorted(counter.iteritems()))
    print


def print_problem_statistics():
    problems = load_problems()

    assert not any('fold' in p.operators and 'tfold' in p.operators for p in problems)
    print 'Total =', len(problems)
    print_count_of_problems('has fold', problems, lambda p: 'fold' in p.operators) 
    print_count_of_problems('has tfold', problems, lambda p: 'tfold' in p.operators) 
    print_count_of_problems('no folds', problems, 
        lambda p: not ('fold' in p.operators or 'tfold' in p.operators))
    print_count_of_problems('no if0, has folds', problems, 
        lambda p: not ('if0' in p.operators) and ('fold' in p.operators or 'tfold' in p.operators))
    print_count_of_problems('no if0 or folds', problems, 
        lambda p: not ('if0' in p.operators or 'fold' in p.operators or 'tfold' in p.operators))
    print_count_of_problems('has if0', problems, 
        lambda p: 'if0' in p.operators)
    print_count_of_problems('bonus', problems, 
        lambda p: 'bonus' in p.operators)
     

if __name__ == '__main__':
    print_problem_statistics()