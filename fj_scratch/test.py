from common_initialization import log, settings
from pprint import pprint

import some_module

import psycopg2  


#print settings['db_password']


def main():
    db_host, db_password = settings['db_host'], settings['db_password']
    sslmode = 'require'
    db = psycopg2.connect(host=db_host, database='postgres', user='tbd', password=db_password, sslmode=sslmode)
    cur = db.cursor()
#    cur.execute('CREATE TABLE test (id serial PRIMARY KEY, num integer, data varchar);')
#    for i in xrange(10):
#        cur.execute('INSERT INTO test (num, data) VALUES (%s, %s)',
#                    (i, 'i.value = %r' % i))
    cur.execute('select * from test')
    pprint(cur.fetchall())
    db.commit()
    db.close()
        

if __name__ == '__main__':
    log.info('Yo!')
    main()
    log.info('done')
