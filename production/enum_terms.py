from terms import *


def simple_terms(size, leafs, unaries, binaries):
    if size == 0:
        return
    if size == 1:
        for t in leafs:
            yield t
        return
    for t in simple_terms(size-1, leafs, unaries, binaries):
        for op in unaries:
            yield (op, t)
    if size < 3:
        return
    for s in range(1, size-1):
        for t1 in simple_terms(s, leafs, unaries, binaries):
            for t2 in simple_terms(size-1-s, leafs, unaries, binaries):
                if t2 > t1:
                    continue
                for op in binaries:
                    yield (op, t1, t2)


if __name__ == '__main__':
    for size in range(2, 11):
        cnt = 0
        for t in simple_terms(size, CONSTANTS + ['x'], UNARY_OPS, BINARY_OPS):
            #print t
            cnt += 1
        print cnt, 'terms of size', size
    for size in range(2, 21):
        cnt = 0
        for t in simple_terms(size, ['*'], ['u'], ['b']):
            #print t
            cnt += 1
        print cnt, 'shapes of size', size