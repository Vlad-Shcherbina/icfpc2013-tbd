import json
from collections import defaultdict
import itertools

from utils import cached
from terms import *
import distinct

import logging
logger = logging.getLogger('unique_db')


DB_OPS = frozenset(['y', 'z', IF0] + UNARY_OPS + BINARY_OPS)


class Constraint(object):
    __slots__ = ['size', 'ops']
    def __init__(self, size, ops):
        assert size >= 0
        assert isinstance(ops, frozenset)
        assert all(op in DB_OPS for op in ops)
        self.size = size
        self.ops = ops

    def __repr__(self):
        return 'Constraint(size<={}, ops<={})'.format(self.size, self.ops)

    def implies(self, other):
        if self.size == 0:
            return True
        return self.size <= other.size and self.ops.issubset(other.ops)

    def __add__(self, other):
        return Constraint(self.size+other.size, self.ops|other.ops)

    def __eq__(self, other):
        return self.size == other.size and self.ops == other.ops

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.size, self.ops))

    # def to_js(self):
    #     return dict(size=self.size, ops=' '.join(sorted(ops)))

    # @staticmethod
    # def from_js(data):
    #     return Constraint(data['size'], frozenset(data['ops'].split()))


def remove_implied_constraints(cs):
    return list(set(c for c in cs if all(not c2.implies(c) for c2 in cs if c2 != c)))

def remove_implying_constraints(cs):
    return list(set(c for c in cs if all(not c.implies(c2) for c2 in cs if c2 != c)))


class FunctionInfo(object):
    __slots__ = [
        'minimal_implementation',
        'z3term',
        'signature',  # semantic hash for comparison
        'possible_in',  # list of constraints
        ]
    def __init__(self, minimal_implementation, signature, z3term):
        self.minimal_implementation = minimal_implementation
        self.signature = signature
        self.z3term = z3term
        self.possible_in = []

    def add_possible_implementations(self, constraints):
        #print '***** self.possible_in', self.possible_in
        #print '***** constraints', constraints
        self.possible_in = remove_implied_constraints(
            self.possible_in + constraints)
        #print '***** self.possible_in', self.possible_in

    def is_possible_in(self, constraint):
        return any(c.implies(constraint) for c in self.possible_in)


class UniqueDB(object):
    __slots__ = [
        'complete_for',  # list of constraints
        'buckets',  # {signature: [function, ...], ...}
        'by_impl',  # {minimal_implementation: function}

        'signature_computer',
        'term_to_z3',
        'z3comparer',
    ]
    def __init__(self):
        self.complete_for = []
        self.buckets = defaultdict(list)
        self.by_impl = {}

    def set_comparer(self, signature_computer, term_to_z3, z3comparer):
        self.signature_computer = signature_computer
        self.term_to_z3 = term_to_z3
        self.z3comparer = z3comparer
        # TODO: update z3 terms of all existing functions

    def remove_comparer(self):
        self.signature_computer = None
        self.term_to_z3 = None
        self.z3comparer = None
        # TODO: remove z3 terms from all existing functions for serialization

    def is_complete_for(self, constraint):
        if constraint.size == 0:
            return True
        return any(constraint.implies(c) for c in self.complete_for)

    def iter_functions(self):
        for fns in self.buckets.values():
            for fn in fns:
                yield fn

    def get_unique_terms(self, exact_size, ops):
        assert self.is_complete_for(Constraint(exact_size, ops))
        c = Constraint(exact_size, ops)
        smaller_c = Constraint(exact_size-1, ops)
        for fn in self.iter_functions():
            if fn.is_possible_in(c) and not fn.is_possible_in(smaller_c):
                yield fn.minimal_implementation

    def get_where_term_is_possible_in(self, term):
        #assert term not in self.by_impl
        if term in [0, 1, 'x', 'y', 'z']:
            return [Constraint(1, frozenset([term]) & DB_OPS)]
        else:
            assert isinstance(term, tuple)
            root_constraint = Constraint(1, frozenset([term[0]]))
            args = term[1:]
            args_possible_in = [self.by_impl[arg].possible_in for arg in args]
            result = []
            for cs in itertools.product(*args_possible_in):
                result.append(sum(cs, root_constraint))
            return result


    def complete(self, constraint, all_terms):
        logger.info('completing db for {}'.format(constraint))
        assert self.is_complete_for(Constraint(constraint.size-1, constraint.ops))
        # it is expected that immediate subterms are
        # canonical minimal implementations
        for term in all_terms:
            if term == (SHL1, 'x'):
                pass
            assert FOLD not in term_to_str(term), term
            signature = self.signature_computer(term)

            bucket = self.buckets[signature]

            z3term = self.term_to_z3(term)

            for fn in bucket:
                if self.z3comparer(fn.z3term, z3term):
                    if term_size(term) < term_size(fn.minimal_implementation):
                        logger.debug(
                            'replacing minimal impl {} with {}'
                            .format(fn.minimal_implementation, term))
                        del self.by_impl[fn.minimal_implementation]
                        fn.minimal_implementation = term
                        fn.z3term = z3term  # because it's probably shorter
                        self.by_impl[term] = fn
                    break
            else:
                fn = FunctionInfo(term, bucket, z3term)
                bucket.append(fn)
                self.by_impl[term] = fn

            fn.add_possible_implementations(
                self.get_where_term_is_possible_in(term))

        self.complete_for.append(constraint)
        self.complete_for = remove_implying_constraints(self.complete_for)

        num_entries = sum(1 for f in self.iter_functions())
        logger.info('db for {} is complete '.format(constraint))
        logger.info('({} entries)'.format(num_entries))

    def show(self):
        print repr(self)
        print 'db complete for', self.complete_for
        print 'functions:'
        for fn in self.iter_functions():
            print ' ',term_to_str(fn.minimal_implementation)
            print '    possible in', fn.possible_in
        print '---'


# signleton
@cached
def get_unique_db():
    # TODO
    db = UniqueDB()

    db.set_comparer(
        distinct.term_signature,
        distinct.nice_term_to_z3,
        lambda zt1, zt2: distinct.terms_equivalent(zt1, zt2, as_predicates=False))
    return db

if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)

    db = get_unique_db()


    db.show()

    db.complete(Constraint(1, DB_OPS), [0, 1, 'x', 'y', 'z'])

    db.show()

    db.complete(Constraint(2, frozenset([SHR1])), [(SHR1, 0), (SHR1, 1), (SHR1, 'x'), (SHR1, 'y')])

    db.show()


    exit()
    c1 = Constraint(4, frozenset())
    c2 = Constraint(2, frozenset([IF0]))
    print c1
    print c1.implies(c2), c2.implies(c1)