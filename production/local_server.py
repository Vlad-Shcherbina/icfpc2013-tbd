import logging
log = logging.getLogger('local_server')

import z3, terms, z3_utils



class LocalServer(object):
    def __init__(self, problems):
        self.problem_iter = iter(problems)
        self.compiled_problems = {}
        self.solver = z3.Solver()
        
    def get_problem(self):
        return next(self.problem_iter)
    
    def get_all_problems(self):
        return list(self.problem_iter)
    
    def request_eval(self, problem, xs):
        parsed, _compiled = self._get_compiled_problem(problem)
        
        # eval using native evaluator         
        assert len(xs) <= 256
        for x in xs:
            assert 0 <= x < 2 ** 64
            res = terms.evaluate(parsed, {'x': x})
            problem.values[x] = res

    def guess(self, problem, program):
        parsed, compiled = self._get_compiled_problem(problem)
        test_parsed = terms.parse_term(program, True)
        test_compiled = z3_utils.term_to_z3(test_parsed, {'x': z3.BitVec('x', 64)})
        solver = self.solver
        solver.reset()
        log.debug('Z3: checking program equivalence')
        solver.add(compiled != test_compiled)
        r = solver.check()
        if r == z3.unsat:
            log.info('Z3: yay, equivalent!\n    submitted: {!r}\n    secret   : {!r}'.format(
                    terms.term_to_str(test_parsed), terms.term_to_str(parsed)))
            # emulate the real server, refuse to do anything with a solved problem.
            self.parsed_problems[problem.id] = 'solved'
            return True
        elif r == z3.unknown:
            print 'failed to prove'
            print solver.model()
            assert False
        else:
            x = solver.model()['x']
            log.debug('Z3: counterexample: {!r}'.format(x))
            problem.values[x] = terms.evaluate(parsed, {'x': x})
            return False
        

    def _get_compiled_problem(self, problem):
        res = self.parsed_problems.get(problem.id, 'solved')
        assert res is not 'solved', 'LocalServer: problem {!r} already solved!'.format(problem.id)
        if res is not None: return res
        
        parsed = terms.parse_term(problem.solution, True)
        compiled = z3_utils.term_to_z3(parsed, {'x': z3.BitVec('x', 64)})
        return (parsed, compiled)
        