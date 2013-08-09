import logging
logger = logging.getLogger('communicate')

import urllib2
import json


BASE_URL = 'http://icfpc2013.cloudapp.net/'

with open('../data/auth_token.txt') as fin:
    auth = fin.read().strip()


class SendError(Exception):
    pass


# It's not tested yet, obviously.
def send(url, data):
    data = json.dumps(data)
    response = urllib2.urlopen(BASE_URL + url + '?auth=' + auth, data=data)
    response_text = response.read()
    logger.debug(
        'code: {}; response text: {}'.format(response.code, response_text))
    if response.code == 200:
        return json.loads(response_text)
    raise SendError(response.code, response_text)


if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)
    print send('', {})