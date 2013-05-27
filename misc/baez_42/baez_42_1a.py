from itertools import count
for r in count(1):
    for q in xrange(1, r + 1):
        for p in xrange(1, q + 1):
            # 1/p + 1/q + 1/r = 1/2
            # qr + pr + pq = pqr/2
            # 2(qr + pr + pq) = pqr
            if 2*(q*r + p*r + p*q) == p*q*r:
                print p, q, r
