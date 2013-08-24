import sys
sys.path.insert(0, '../production')  # to run outside of eclipse

import csv

from terms import *
from solution_db import get_problems


def main():
    with open('../data/problems.csv', 'w') as fout:
        writer = csv.writer(fout)
        writer.writerow(['id', 'size', 'operators', 'solution'])
        for size in range(3, 50):
            print size
            problems = get_problems(size=size)
            for p in problems:
                ops = p.operators.split()
                ops.sort(key=lambda op: '' if op in ['fold', 'tfold', 'bonus'] else op)
                ops = ' '.join(ops)
                t = parse_term(p.solution, normalize=True)
                t = term_to_str(t)
                # whitespace is added to make search in github csv viewer
                # more convenient
                writer.writerow([p.id, str(p.size)+' ', ops, t])
    print 'done'


if __name__ == '__main__':
    main()
