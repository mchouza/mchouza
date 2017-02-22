import pandas as pd
import random
import time

NUM_IDS = 10000
NUM_ROWS = 10000000

ids = ['AAA%d' % i for i in range(NUM_IDS)]
a = pd.DataFrame({
    'id': [random.choice(ids) for _ in xrange(NUM_ROWS)],
    'a': [random.random() for _ in xrange(NUM_ROWS)],
})
b = pd.DataFrame({
    'b': [random.random() for _ in xrange(NUM_IDS)]
}, index=ids)

start = time.time()
c = a.join(b, on='id').drop('id', axis=1)
print 'Join & drop, not in place:', time.time() - start

c = a.copy()
start = time.time()
c.merge(b, left_on='id', right_index=True, copy=False).drop('id', axis=1, inplace=True)
print 'Join & drop, in place:', time.time() - start

d = a.copy()
d['id'] = [int(i[3:]) for i in c['id']]
start = time.time()
d['b'] = b['b'].values[d['id']]
del d['id']
print 'Numpy:', time.time() - start
