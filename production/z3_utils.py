import z3

from terms import *


# Not namedtuple because it's descendant of tuple.
class Control(object):
    __slots__ = ['z3var', 'operations']
    def __init__(self, z3var, operations):
        assert len(operations) > 0
        self.z3var = z3var
        self.operations = operations

    def __repr__(self):
        return 'Control({!r}, {!r})'.format(self.z3var, self.operations)

    def decode(self, model):
        value = model[self.z3var]
        if value is None:
            value = 0
        else:
            value = int(value.as_string())

        if 0 <= value < len(self.operations):
            return self.operations[value]
        else:
            return self.operations[-1]


fresh_index = 0
def fresh_var_name(prefix='fresh'):
    global fresh_index
    fresh_index += 1
    return prefix+str(fresh_index)


def fresh_control(operations):
    if len(operations) == 1:
        return operations[0]
    return Control(z3.Int(fresh_var_name('control')), operations)


def inject_controls(t, control_map):
    """
    control_map is something like
    {'v': [0, 1, 'x'], 'u': ['not', 'shl1'], 'b': ['plus', 'or']}
    """

    controls = []
    def replacer(leaf):
        if leaf in control_map:
            c = fresh_control(control_map[leaf])
            controls.append(c)
            return c
        return leaf

    t = subst(t, leaf_replacer=replacer)

    return t, controls


def instantiate_controls_from_model(term, model):
    def replacer(leaf):
        if isinstance(leaf, Control):
            return leaf.decode(model)
        return leaf

    return subst(term, leaf_replacer=replacer)


def z3_switch(control, *options):
    def recur(offset):
        if offset == len(options) - 1: return options[offset]
        return z3.If(control == offset, options[offset], recur(offset + 1))
    return recur(0)


zero56 = z3.BitVecVal(0, 56)

def term_to_z3(t, vars={}):
    if not isinstance(t, tuple):
        t = (t,)
    op = t[0]
    if isinstance(op, Control):
        args = [term_to_z3(arg, vars) for arg in t[1:]]
        formal_args = tuple('tmp'+str(i) for i in range(len(args)))
        possibilities = []
        new_vars = dict(vars)
        new_vars.update(zip(formal_args, args))
        for operation in op.operations:
            possibilities.append(term_to_z3(
                (operation,) + formal_args,
                vars=new_vars))
        return z3_switch(op.z3var, *possibilities)
    elif isinstance(op, (int, long)):
        assert len(t) == 1
        return z3.BitVecVal(op, 64)
    elif op in vars:
        assert len(t) == 1
        return vars[op]
    elif op == PLUS:
        assert len(t) == 3
        return term_to_z3(t[1], vars) + term_to_z3(t[2], vars)
    if op == AND:
        assert len(t) == 3
        return term_to_z3(t[1], vars) & term_to_z3(t[2], vars)
    if op == OR:
        assert len(t) == 3
        return term_to_z3(t[1], vars) | term_to_z3(t[2], vars)
    if op == XOR:
        assert len(t) == 3
        return term_to_z3(t[1], vars) ^ term_to_z3(t[2], vars)
    elif op == SHL1:
        assert len(t) == 2
        return term_to_z3(t[1], vars) << 1
    elif op == SHR1:
        assert len(t) == 2
        return z3.LShR(term_to_z3(t[1], vars), 1)
    elif op == SHR4:
        assert len(t) == 2
        return z3.LShR(term_to_z3(t[1], vars), 4)
    elif op == SHR16:
        assert len(t) == 2
        return z3.LShR(term_to_z3(t[1], vars), 16)
    elif op == NOT:
        assert len(t) == 2
        return ~term_to_z3(t[1], vars)
    elif op == IF0:
        assert len(t) == 4
        return z3.If(
            term_to_z3(t[1], vars) == 0,
            term_to_z3(t[2], vars),
            term_to_z3(t[3], vars))
        pass
    elif op == FOLD:
        _, bytes, start, fn = t
        _, (formal_y, formal_z), body = fn

        bytes = term_to_z3(bytes, vars)
        accum = term_to_z3(start, vars)
        assert formal_y not in vars
        assert formal_z not in vars
        new_vars = dict(vars)
        for i in range(8):
            new_vars[formal_y] = \
                z3.Concat(zero56, z3.Extract(8*i+7, 8*i, bytes))
            new_vars[formal_z] = accum
            accum = term_to_z3(body, new_vars)
        return accum
    else:
        assert False, (op, t)


def z3_eval_term(t, context={}):
    context = {k:z3.BitVecVal(v, 64) for k, v in context.items()}
    t = term_to_z3(t, context)
    result = z3.BitVec('result', 64)

    with PushPop():
        z3_solver.add(result == t)
        assert z3_solver.check() == z3.sat
        result = z3_solver.model()[result]
        assert result is not None
        return int(result.as_string())


z3_solver = z3.Solver()


class PushPop(object):
    def __enter__(self):
        z3_solver.push()
    def __exit__(self, *args):
        z3_solver.pop()


if __name__ == '__main__':
    t = ('b', 0, 'v')
    print t
    t, controls = inject_controls(t, {'v': [0, 1],'b': [PLUS, OR]})
    print t
    print 'with controls', controls
    z3t = term_to_z3(t)
    print z3t

    z3_solver.add(controls[0].z3var == 0)
    z3_solver.add(controls[1].z3var == 1)
    result = z3_solver.check()
    assert result == z3.sat
    model = z3_solver.model()
    print model

    t = instantiate_controls_from_model(t, model)
    print t

    print

    exit()


    t = (FOLD, 'x', 0, (LAMBDA, ('y', 'z'), (OR, 'y', 'z')))
    r = z3_eval_term(t, dict(x=2**64-1))
    print r

    #################

    solution = (PLUS, 'x', 1)
    candidate1 = (PLUS, 1, 'x')
    candidate2 = (OR, 'x', 1)

    x = z3.BitVec('x', 64)

    for candidate in candidate1, candidate2:
        print
        print 'checking', candidate
        candidate_term = term_to_z3(candidate, dict(x=x))
        solution_term = term_to_z3(solution, dict(x=x))

        with PushPop():
            z3_solver.add(candidate_term != solution_term)

            result = z3_solver.check()
            if result == z3.unsat:
                print 'candidate is equivalent to solution'
            elif result == z3.sat:
                x = z3_solver.model()[x]
                if x is None:
                    x = 0
                else:
                    x = int(x.as_string())
                print 'counterexample:', x
            else:
                assert False, result
