import re

LAMBDA = 'lambda'
IF0 = 'if0'
FOLD = 'fold'
NOT = 'not'
SHL1 = 'shl1'
SHR1 = 'shr1'
SHR4 = 'shr4'
SHR16 = 'shr16'
AND = 'and'
OR = 'or'
XOR = 'xor'
PLUS = 'plus'

CONSTANTS = [0, 1]
UNARY_OPS = [NOT, SHL1, SHR1, SHR4, SHR16]
BINARY_OPS = [AND, OR, XOR, PLUS]


MASK = 2**64-1

def term_to_str(t):
    if isinstance(t, tuple):
        return '({})'.format(' '.join(map(term_to_str, (elem for elem in t))))
    return str(t)


def apply(lambda_expr, context, *args):
    lam, formal_args, body = lambda_expr
    assert lam == LAMBDA, lambda_expr
    assert len(formal_args) == len(args), (formal_args, args)
    context = dict(context)
    for fa, a in zip(formal_args, args):
        assert fa not in context
        context[fa] = a
    return evaluate(body, context)


def evaluate(t, context={}):
    if isinstance(t, tuple):
        op = t[0]
        if op == NOT:
            assert len(t) == 2, t
            return MASK ^ evaluate(t[1], context)
        elif op == SHL1:
            assert len(t) == 2, t
            return MASK & (evaluate(t[1], context) << 1)
        elif op == SHR1:
            assert len(t) == 2, t
            return evaluate(t[1], context) >> 1
        elif op == SHR4:
            assert len(t) == 2, t
            return evaluate(t[1], context) >> 4
        elif op == SHR16:
            assert len(t) == 2, t
            return evaluate(t[1], context) >> 16
        elif op == AND:
            assert len(t) == 3
            return evaluate(t[1], context) & evaluate(t[2], context)
        elif op == OR:
            assert len(t) == 3
            return evaluate(t[1], context) | evaluate(t[2], context)
        elif op == XOR:
            assert len(t) == 3
            return evaluate(t[1], context) ^ evaluate(t[2], context)
        elif op == PLUS:
            assert len(t) == 3
            return (evaluate(t[1], context) + evaluate(t[2], context)) & MASK
        if op == IF0:
            _, cond, then, else_ = t
            if evaluate(cond, context) == 0:
                return evaluate(then, context)
            else:
                return evaluate(else_, context)
        elif op == FOLD:
            _, bytes, start, fn = t
            bytes = evaluate(bytes, context)
            accum = evaluate(start, context)
            for i in range(8):
                byte = (bytes >> i*8) & 255
                accum = apply(fn, context, byte, accum)
            return accum
        else:
            assert False, t
    else:
        if t in CONSTANTS:
            return t
        elif t in context:
            return context[t]
        else:
            assert False, t


# Test z3 eval (slow)
if False:
    import z3_utils
    evaluate1 = evaluate
    def evaluate(t, context={}):
        result = evaluate1(t, context)
        q = z3_utils.z3_eval_term(t, context)
        assert q == result
        return result


def subst(t, replacements={}, leaf_replacer=None):
    if t in replacements:
        return replacements[t]
    if isinstance(t, tuple):
        return tuple(
            subst(tt, replacements, leaf_replacer=leaf_replacer) for tt in t)

    if leaf_replacer is not None:
        return leaf_replacer(t)

    return t


def term_size(t):
    if isinstance(t, tuple):
        if t[0] == LAMBDA:
            assert len(t) == 3
            return 1 + term_size(t[2])
        else:
            # fold is covered by this case
            return sum(map(term_size, t))
    from z3_utils import Control
    if isinstance(t, Control):
        return term_size(t.operations[0])
    return 1


def term_op(t):
    '''
    Implementation of function Op from problem statement.
    '''
    if isinstance(t, tuple):
        if t[0] == LAMBDA:
            assert len(t) == 3
            return term_op(t[2])
        else:
            result = set([t[0]])
            for tt in t[1:]:
                result |= term_op(tt)
            return result
    return set()


def term_operators(t):
    '''
    Implementation of Operators relation from problem statement as function.
    '''
    if isinstance(t, tuple) and t[0] == FOLD:
        return term_op(t) | set(['tfold'])
    return term_op(t)


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


def parse_term(s, normalize=False):
    '''Specify normalize=True to output parse tree in the internal representation:
    no outermost lambda, input variable is assumbed to be called 'x'.
    Also rename FOLD variables to 'y' and 'z' for a good measure.'''
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
                return context[token] if normalize else token


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
            normalized_id = 'x' if argcount == 1 else 'yz'[i] 
            ids.append(normalized_id if normalize else id)
            old_bindings.append((id, context.get(id, undefined)))
            context[id] = normalized_id
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
    def main():
        result = parse_lambda(1, tokens)
        assert not len(tokens), 'Trailing identifiers: %s' % ' '.join(
            '%r' % tok for tok, _ in reversed(tokens))
        if normalize:
            # strip top-level lambda
            tag, _, body = result
            assert tag == LAMBDA
            result = body
        return result
     
    return main()


def parse_any_term(s):
    # no renaming

    tokens = tokenize(s)

    def expect(expected):
        token, pos = tokens.pop()
        assert expected == token, 'Invalid token at %d: %r, expected %r' % (pos, token, expected)\

    def check_id_declaration(token, pos):
        assert identifier_rx.match(token), 'Expected identifier at %d, got %r' % (pos, token)

    def parse_expression():
        token, pos = tokens.pop()
        if token == '(':
            result = None
            token, pos = tokens.pop()
            if token in UNARY_OPS:
                arg1 = parse_expression()
                result = (token, arg1)
            elif token in BINARY_OPS:
                arg1 = parse_expression()
                arg2 = parse_expression()
                result = (token, arg1, arg2)
            elif token == IF0:
                cond = parse_expression()
                arg1 = parse_expression()
                arg2 = parse_expression()
                result = (token, cond, arg1, arg2)
            elif token == FOLD:
                e_in = parse_expression()
                e_acc = parse_expression()
                fn = parse_lambda()
                result = (token, e_in, e_acc, fn)
            else:
                assert False, 'Expected operation at %d, got %r' % (pos, token)
            expect(')')
            return result
        else:
            if token in '01':
                return int(token)
            else:
                return token

    def parse_lambda():
        expect('(')
        expect('lambda')
        expect('(')

        args = []
        token, pos = tokens.pop()
        while token != ')':
            check_id_declaration(token, pos)
            args.append(token)
            token, pos = tokens.pop()

        body = parse_expression()
        expect(')')

        return (LAMBDA, tuple(args), body)

    parsing_result = parse_expression()
    assert not len(tokens), 'Trailing identifiers: %s' % ' '.join(
        '%r' % tok for tok, _ in reversed(tokens))
    return parsing_result
