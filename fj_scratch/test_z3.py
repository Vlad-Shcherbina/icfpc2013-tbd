from z3 import *

a, b = Bools('a b')
prove(Not(Xor(a, b)) == Xor(a, Not(b)))

a, b = BitVec('a', 64), BitVec('b', 64)
prove(~(a ^ b) == (a ^ ~b))
