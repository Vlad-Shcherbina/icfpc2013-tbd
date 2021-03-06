from common_initialization import log, settings
from pprint import pprint
from contextlib import contextmanager
import psycopg2

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
    
def main2():
    db_host, db_password = settings['db_host'], settings['db_password']
    sslmode = 'require'
    with psycopg2.connect(host=db_host, database='postgres', user='tbd', password=db_password, sslmode=sslmode) as db:
        with db_execute(db, 'select * from test') as cur:
            pprint(cur.fetchall())
    db.close()

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
        # going full retard with full text search indices
        with db_execute(db, 'CREATE INDEX ON solved_problems (size)'): pass
        with db_execute(db, "CREATE INDEX ON solved_problems USING gin(to_tsvector('english', operators));"): pass
        
    
def add_solved_problem(id, training, size, operators, solution, extra = None):
    db = get_db()
    with db:
        with db_execute(db, '''
            insert into solved_problems (id, training, size, operators, solution, extra)
            values (%s, %s, %s, %s, %s, %s)''',
            (id, training, size, ' '.join(sorted(operators)), solution, extra)): pass
    log.debug('Stored problem %r in the problem database', id)
    

def main():
    p = get_training_problem()
    add_solved_problem(p.id, True, p.size, p.operators, p.solution)


if __name__ == '__main__':
    log.info('Yo!')
    main()
    log.info('done')
