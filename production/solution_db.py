import sys
import psycopg2
from pprint import pprint
from contextlib import contextmanager
from collections import namedtuple
 
from simple_settings import settings
import logging
log = logging.getLogger('solution_db')

from communicate import get_training_problem

@contextmanager
def db_execute(db, *args, **kwargs):
    '''
    with pg_execute(db, sql): execute sql in a new cursor and return it for fetching results

    Never ever call outside the `with` statement (nothing will happen).

    Use `with db:` block to commit/rollback the transaction (this doesn't close the connection).

    Actually, always use `with db:`, because even simple selects start a transaction in psycopg2,
    so that will avoid idling transactions.
    '''
    cur = db.cursor()
    try:
        cur.execute(*args, **kwargs)
        yield cur
    finally:
        cur.close()

_db = None
def get_db():
    global _db
    if _db is None:
        db_host, db_password = settings['db_host'], settings['db_password']
        _db = psycopg2.connect(host=db_host, database='postgres', user='tbd', password=db_password, sslmode='require')
    return _db


def create_structure(db):
    '''For historical purposes'''
    with db:
        with db_execute(db, '''
            CREATE TABLE solved_problems
            (
               id character(24) NOT NULL UNIQUE PRIMARY KEY,
               training boolean NOT NULL,
               size smallint NOT NULL,
               operators text NOT NULL,
               solution text,
               extra text
            )'''): pass
        with db_execute(db, 'CREATE INDEX ON solved_problems (size)'): pass
        # going full retard with full text search index (yeah we really need that!)
        # note the 'simple' configuration: it just lowers the case and doesn't do stemming
        # or (contrary to the description!) ignore stopwords.
        with db_execute(db, "CREATE INDEX ON solved_problems USING gin(to_tsvector('simple', operators))"): pass
        
    
def add_solved_problem(id, training, size, operators, solution, extra = None):
    log.debug('Storing problem {}'
        .format((id, training, size, operators, solution, extra)))
    try:
        db = get_db()
        with db:
            with db_execute(db, '''
                insert into solved_problems (id, training, size, operators, solution, extra)
                values (%s, %s, %s, %s, %s, %s)''',
                (id, training, size, ' '.join(sorted(operators)), solution, extra)): pass
    except Exception:
        log.exception('Failed to store problem %r in the solution database', id)
        # don't reraise
    else:
        log.debug('Stored problem %r in the solution database', id)


ProblemDescription = namedtuple('ProblemDescription', 'id, training, size, operators, solution, extra')

def get_problems(size = None, operators = None, training = None, limit = None):
    '''get all problems satisfying criteria from the db.
    size: integer or a (min, max) tuple (inclusive).
    operators: a Postgres text search expression, such as 'fold' or '(fold | tfold) & !if0'
        (http://www.postgresql.org/docs/9.2/static/datatype-textsearch.html#DATATYPE-TSQUERY)
    training: True of False to select only training or actual problems.
    count: limit the number of results
    
    Returns a list of ProblemDescription namedtuples. Note: p.operators is a string there.
    ''' 
    log.debug('Retrieving problems from the database')
    sql = 'select {} from solved_problems where true'.format(', '.join(ProblemDescription._fields))
    params = []
    
    if size is not None:
        if isinstance(size, int):
            sql += ' and size = %s'
            params.append(size)
        else:
            assert len(size) == 2, 'Invalid size: {!r}'.format(size)
            sql += ' and size between %s and %s'
            params.extend(size)
    if operators is not None:
        sql += " and to_tsvector('simple', operators) @@ to_tsquery('simple', %s)"
        params.append(operators)
    if training is not None:
        sql += ' and training = %s'
        params.append(training)
    if limit is not None:
        sql += ' limit %s'
        params.append(limit)
    
    db = get_db()
    with db:
        with db_execute(db, sql, params) as cur:
            return map(lambda t: ProblemDescription(*t), cur.fetchall())

     
def main():
    logging.basicConfig(level=logging.DEBUG, stream=sys.stdout)
    log.info('Yo!')
    get_training_problem()
#    solutions = get_problems(training = True, limit = 20, operators = '(fold | tfold) & !if0')
#    print '\n'.join('{}, {}: {}'.format(p.id, p.size, p.solution) for p in solutions)
#    print len(solutions)
    log.info('done')


if __name__ == '__main__':
    main()
