from common_initialization import log, settings
from pprint import pprint
from collections import namedtuple, Counter
import pickle, json, os, re
from os import path as os_path
from communicate import Problem, send, get_training_problem

def load_cached(fname, f):
    if os_path.exists(fname):
        with open(fname, 'rb') as f:
            return pickle.load(f)
    else:
        data = f()
        with open(fname, 'wb') as f:
            pickle.dump(data, f)
        return data
        

def main():
    problems = load_cached('temp_problems.pickle', lambda: send('myproblems'))
    print len(problems)
#    p = get_training_problem(5, [])
#    p.solution = '(lambda (x_5126) (shr1 (plus 1 (shr1 x_5126))))'
#    print p
#    p.request_eval([1, 13, 2**64-1])
#    print p.values    
        
from terms import *


tokenizer_rx = re.compile(r'\s* ([()] | \b \w+ \b) \s*', re.VERBOSE)
identifier_rx = re.compile(r'^[a-z][a-z_0-9]*$', re.VERBOSE)

def tokenize(s):
    res = []
    prev_end = 0
    for m in tokenizer_rx.finditer(s):
        assert m.start() == prev_end, 'Invalid token at %d: %r' % (prev_end, s[prev_end:m.start()])
        prev_end = m.end()
        res.append((m.group(1), m.start()))
    res.reverse()
    return res


def parse_term(s):
    tokens = tokenize(s)
    context = {}
    
    # parser functions
    def expect(expected):
        token, pos = tokens.pop()
        assert expected == token, 'Invalid token at %d: %r, expected %r' % (pos, token, expected)\
    
    def check_id_declaration(token, pos):
        assert identifier_rx.match(token), 'Expected identifier at %d, got %r' % (pos, token)

    def check_id_use(token, pos):
        check_id_declaration(token, pos)
        assert token in context, 'Undefined identifier at %d: %r (in scope: %r)' % (pos, token, context)
    
    def parse_expression(tokens):
        token, pos = tokens.pop()
        if token == '(':
            result = None
            token, pos = tokens.pop()
            if token in UNARY_OPS:
                arg1 = parse_expression(tokens)
                result = (token, arg1)
            elif token in BINARY_OPS:
                arg1 = parse_expression(tokens)
                arg2 = parse_expression(tokens)
                result = (token, arg1, arg2)
            elif token == IF0:
                cond = parse_expression(tokens)
                arg1 = parse_expression(tokens)
                arg2 = parse_expression(tokens)
                result = (token, cond, arg1, arg2)
            elif token == FOLD:
                e_in = parse_expression(tokens)
                e_acc = parse_expression(tokens)
                fn = parse_lambda(2, tokens)
                result = (token, e_in, e_acc, fn)
            else:
                assert False, 'Expected operation at %d, got %r' % (pos, token)
            expect(')')
            return result
        else:
            if token in '01':
                return int(token)
            else:
                check_id_use(token, pos)
                return token
    
    
    def parse_lambda(argcount, tokens):
        expect('(')
        expect('lambda')
        expect('(')
        # we need to restore old variable bindings in the context afterwards
        undefined = object()
        old_bindings = []
        ids = []
        for i in xrange(argcount):
            id, pos = tokens.pop()
            check_id_declaration(id, pos)
            ids.append(id)
            old_bindings.append((id, context.get(id, undefined)))
            context[id] = 'input' if argcount == 1 else 'fold_arg' + str(i) 
        expect(')')
        e = parse_expression(tokens)
        expect(')')
        # restore old bindings
        for id, value in reversed(old_bindings):
            if value is undefined:
                del context[id]
            else:
                context[id] = value
        return (LAMBDA, tuple(ids), e)
    
    # execution
    parsing_result = parse_lambda(1, tokens)
    assert not len(tokens), 'Trailing identifiers: %s' % ' '.join(
        '%r' % tok for tok, _ in reversed(tokens))
    return parsing_result
    

if __name__ == '__main__':
    log.info('Yo!')
    pprint(parse_term('(lambda (x_3199) (xor x_3199 (shl1 x_3199)))'))
    log.info('done')
