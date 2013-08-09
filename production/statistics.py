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
        assert len(ids) == 1420
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


def print_problem_statistics():
    problems = load_problems()

    total = 0
    simple, tfold, fold = Counter(), Counter(), Counter()
    for p in problems:
        total += 1
        if 'fold' in p.operators:
            d = fold
        elif 'tfold' in p.operators:
            assert 'fold' not in p.operators
            d = tfold
        else:
            d = simple
        d[p.size] += 1
    assert total == sum(fold.itervalues()) + sum(tfold.itervalues()) + sum(simple.itervalues())
    print 'Total =', total
    def print_sizes(name, sizes):
        print name
        pprint(sorted(sizes.iteritems()))
        print
    print_sizes('simple', simple)
    print_sizes('tfold', tfold)
    print_sizes('fold', fold)

if __name__ == '__main__':
    print_problem_statistics()