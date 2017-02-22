import numpy as np
import pandas as pd
import random
import time

NUM_IDS = 10000
NUM_ROWS = 1000000
NUM_VALUE_COLS = 10

ids = ['AAA%d' % i for i in range(NUM_IDS)]
a = pd.DataFrame({
    'id': np.random.choice(ids, size=NUM_ROWS)
})
for i in xrange(NUM_VALUE_COLS):
    a['a%d' % i] = np.random.random(size=NUM_ROWS)
b = pd.DataFrame(index=ids)
for i in xrange(NUM_VALUE_COLS):
    b['b%d' % i] = np.random.random(size=NUM_IDS)

start = time.time()
c = a.join(b, on='id').drop('id', axis=1)
print time.time() - start
lhs = c[[cid for cid in c.columns if cid[0] == 'a']]
print time.time() - start
rhs = c[[cid for cid in c.columns if cid[0] == 'b']]
print time.time() - start
e = lhs * rhs
print time.time() - start
d = e.sum(axis=1)
print 'Baseline:', time.time() - start

start = time.time()
c = a.join(b, on='id').drop('id', axis=1)
print time.time() - start
lhs = c[[cid for cid in c.columns if cid[0] == 'a']].values
print time.time() - start
rhs = c[[cid for cid in c.columns if cid[0] == 'b']].values
print time.time() - start
e = lhs * rhs
print time.time() - start
d = np.sum(e, axis=1)
print 'Using values:', time.time() - start


start = time.time()
c = a.join(b, on='id').drop('id', axis=1)
print time.time() - start
lhs = c[[cid for cid in c.columns if cid[0] == 'a']].values
print time.time() - start
rhs = c[[cid for cid in c.columns if cid[0] == 'b']].values
print time.time() - start
e = np.einsum('ij,ij->i', lhs, rhs)
print 'Using values:', time.time() - start
