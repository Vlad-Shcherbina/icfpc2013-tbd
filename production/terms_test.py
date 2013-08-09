from nose.tools import eq_

from terms import *


def test_to_str():
    eq_(term_to_str(0), '0')
    eq_(term_to_str((LAMBDA, ('x',), (PLUS, 'x', (NOT, '1')))),
        '(lambda (x) (plus x (not 1)))')
    pass


def test_eval():
    eq_(evaluate((PLUS, 'x', 1), dict(x=42)), 43)


def test_size():
    eq_(term_size(0), 1)
    eq_(term_size((LAMBDA, ('x', ), 'x')), 2)
    eq_(term_size((PLUS, 0, 1)), 3)
    eq_(term_size((FOLD, 0, 1, (LAMBDA, ('x', 'y'), 0))), 5)


def test_op():
    eq_(term_op(0), set())
    eq_(term_op((LAMBDA, ('x',), (PLUS, 'x', (NOT, '1')))),
        set([PLUS, NOT]))


def test_operators():
    eq_(term_operators(0), set())
    eq_(term_operators((FOLD, 0, 1, (LAMBDA, ('x', 'y'), 0))),
        set(['fold', 'tfold']))
