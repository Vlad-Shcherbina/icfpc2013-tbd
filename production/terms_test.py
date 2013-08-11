from nose.tools import eq_

from terms import *


def test_to_str():
    eq_(term_to_str(0), '0')
    eq_(term_to_str((LAMBDA, ('x',), (PLUS, 'x', (NOT, '1')))),
        '(lambda (x) (plus x (not 1)))')
    pass


def test_eval():
    eq_(evaluate((PLUS, 'x', 1), dict(x=42)), 43)

    eq_(evaluate((IF0, 0, 1, 0)), 1)
    eq_(evaluate((IF0, 1, 1, 0)), 0)

    eq_(apply(
            (LAMBDA, ('x',),
                (FOLD, 'x', 0, (LAMBDA, ('y', 'z'), (OR, 'y', 'z')))),
            {},
            0x1122334455667788),
        0x00000000000000ff)


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

def test_parse_term():
    tests = [
            '(lambda (x_77708) (fold (and (shr4 (not (shr16 (shr16 (shr1 (shr4 (plus (if0 (shr1 (plus (xor (xor 0 (not x_77708)) 1) x_77708)) x_77708 1) 1))))))) x_77708) x_77708 (lambda (x_77709 x_77710) (if0 x_77709 x_77710 x_77709))))',
            '(lambda (x_79511) (fold (xor (shr4 (shl1 (shr4 (or (if0 (xor x_79511 (or (shr4 (and (shl1 (plus x_79511 (shr4 x_79511))) x_79511)) x_79511)) 1 x_79511) x_79511)))) x_79511) 0 (lambda (x_79512 x_79513) (plus (shr16 x_79513) x_79512))))',
            '(lambda (x_78077) (fold (not (plus (shr16 (shl1 (or (or (plus (plus (if0 (plus (plus (shl1 x_78077) 0) x_78077) 0 x_78077) 1) x_78077) 1) 1))) x_78077)) x_78077 (lambda (x_78078 x_78079) (plus x_78078 (shr1 x_78079)))))',
            '(lambda (x_85865) (fold x_85865 0 (lambda (x_85865 x_85866) (or x_85865 (if0 (xor (shl1 (plus x_85865 (xor (plus (shr16 (and x_85865 (not (plus (xor (or x_85866 x_85865) x_85865) x_85866)))) x_85865) x_85866))) x_85866) 0 x_85865)))))',
            ]
    for t in tests:
        eq_(term_to_str(parse_term(t)), t)

    # test normalization
    t = '(lambda (x_77708) (fold (and (shr4 (not (shr16 (shr16 (shr1 (shr4 (plus (if0 (shr1 (plus (xor (xor 0 (not x_77708)) 1) x_77708)) x_77708 1) 1))))))) x_77708) x_77708 (lambda (x_77709 x_77710) (if0 x_77709 x_77710 x_77709))))'
    manually_normalized = t.replace('x_77708', 'x').replace('x_77709', 'y').replace('x_77710', 'z')
    normalized = '(lambda (x) ' + term_to_str(parse_term(t, True)) + ')' 
    eq_(normalized, manually_normalized)
    
    
    