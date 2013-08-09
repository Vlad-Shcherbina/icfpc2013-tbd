from nose.tools import eq_

from terms import *


def test_to_str():
    eq_(term_to_str(0), '0')
    eq_(term_to_str((LAMBDA, ('x',), ('plus', 'x', ('not', '1')))),
        '(lambda (x) (plus x (not 1)))')
    pass


def test_eval():
    eq_(evaluate((PLUS, 'x', 1), dict(x=42)), 43)