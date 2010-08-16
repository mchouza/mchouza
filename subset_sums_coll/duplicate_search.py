def find_duplicate_sort(g):
    sl = sorted(g)
    prev = None
    for e in sl:
        if e == prev:
            return e
        prev = e
    return None

def find_duplicate_set(g):
    es = set()
    for e in g:
        if e in es:
            return e
        es.add(e)
    return None

if __name__ == '__main__':
    import random
    random.seed(0)
    g = (random.randint(1, 1000000) for _ in xrange(2000))
    print find_duplicate_sort(g)
    random.seed(0)
    g = (random.randint(1, 1000000) for _ in xrange(2000))
    print find_duplicate_set(g)
