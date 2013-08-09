from common_initialization import log, settings
from pprint import pprint
from collections import namedtuple, Counter

from communicate import Problem 

import json




def main():
    with open('../data/myproblems.json') as f:
        problems = json.load(f)
    print len(problems)
    pprint(problems[0])
    problems = map(Problem.from_json, problems)

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
    log.info('Yo!')
    main()
    log.info('done')
