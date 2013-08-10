import z3

from terms import *

from z3_utils import PushPop

zero56 = z3.BitVecVal(0, 56)

def decode_control(value, lst):
    return lst[value] if 0 <= value < lst(len) else lst[-1]

def z3_switch(control, *options):
    def recur(offset):
        if offset == len(options) - 1: return options[offset]
        return z3.If(control == offset, options[offset], recur(offset + 1))
    return recur(0)

UNARY_OP_PLACEHOLDER = 'u'
BINARY_OP_PLACEHOLDER = 'b'
VALUE_PLACEHOLDER = 'v'

class ControlList(list):
    __slots__ = ['reuse_idx']
    def __init__(self):
        self.reuse_idx = 0
    def get(self):
        control_idx = len(self)
        if self.reuse_idx == control_idx:
            control = z3.Int('control_' + str(control_idx))
            self.append(control)
        else:
            control = self[self.reuse_idx]
        self.reuse_idx += 1
        return control
        
        

def term_to_z3_controlled(t, vars, controls):
    if isinstance(t, tuple):
        op = t[0]
        if op == UNARY_OP_PLACEHOLDER:
            assert len(t) == 3 
            control = controls.get()
            arg1, arg1decoder = term_to_z3_controlled(t[1], vars, controls)
            arg2, arg2decoder = term_to_z3_controlled(t[2], vars, controls)
            
            z3term = z3_switch(control, arg1 + arg2, arg1 & arg2, arg1 | arg2, arg1 ^ arg2)
            decoder = lambda model: (decode_control(model[control], (PLUS, AND, OR, XOR)), arg1decoder(model), arg2decoder(model))
            return z3term, decoder
        elif op == BINARY_OP_PLACEHOLDER:
            assert len(t) == 2
            control = controls.get()
            arg1, arg1decoder = term_to_z3_controlled(t[1], vars, controls)
            
            z3term = z3_switch(control, arg1 << 1, z3.LShR(arg1, 1), z3.LShR(arg1, 4), z3.LShR(arg1, 16), ~arg1 ^ arg2)
            decoder = lambda model: (decode_control(model[control], (SHL1, SHR1, SHR4, SHR16, NOT)), arg1decoder(model))
            return z3term, decoder
        elif op == IF0:
            assert len(t) == 4
            arg1, arg1decoder = term_to_z3_controlled(t[1], vars, controls)
            arg2, arg2decoder = term_to_z3_controlled(t[2], vars, controls)
            arg3, arg3decoder = term_to_z3_controlled(t[3], vars, controls)
            
            z3term = z3.If(arg1 == 0, arg2, arg3)
            decoder = lambda model: (IF0, arg1decoder(model), arg2decoder(model), arg3decoder(model))
            return z3term, decoder
        elif op == FOLD:
            bytes, bytesdecoder = term_to_z3_controlled(t[1], vars, controls)
            accum, accumdecoder = term_to_z3_controlled(t[2], vars, controls)
            _, (formal_y, formal_z), body = t[3]

            assert formal_y not in vars
            assert formal_z not in vars
            new_vars = dict(vars)
            reuse_idx = None
            
            for i in range(8):
                new_vars[formal_y] = \
                    z3.Concat(zero56, z3.Extract(8*i+7, 8*i, bytes))
                new_vars[formal_z] = accum
                # on the first iteration proceed to add controls as usual, on the subsequent iterations
                # reset controls.reuse_idx to the captured base value. 
                if reuse_idx is not None:
                    controls.reuse_idx = reuse_idx
                else:
                    reuse_idx = controls.reuse_idx 
                accum, fn_decoder = term_to_z3_controlled(body, new_vars, controls)
            decoder = lambda model: (FOLD, bytesdecoder(model), accumdecoder(model), fn_decoder(model))
            return accum, decoder
    elif t == VALUE_PLACEHOLDER:
        control = controls.get()
        z3term = z3_switch(z3.BitVecVal(0, 64), z3.BitVecVal(1, 64), 
                *vars.values())
        decoder = lambda model: decode_control(model[control], [0, 1] + vars.keys()) 
        return z3term, decoder
    
    assert False, 'Invalid value: %r' % t

def find_model(candidate, solver, input_name, input_var, output_var):
    vars = {input_name: input_var}
    term, decoder  = term_to_z3_controlled(candidate, vars, ControlList())
    
    with PushPop():
        solver.add(output_var == term)
        return decoder(solver.model()) if solver.check() == z3.sat else None
