def swap(a, i, j):
    a[i], a[j] = a[j], a[i]

def rotate_naive(a, k):
    return a[-k:] + a[:-k]

def rrip_copied(a, k):
    n = len(a)
    for i in xrange(n // 2):
        swap(a, i, (n - 1) - i)
    for i in xrange(k // 2):
        swap(a, i, (k - 1) - i)
    for i in xrange((n - k) // 2):
        swap(a, k + i, (n - 1) - i)

def rrip_demian(a, k):
    import fractions
    def replace(a, i, x):
        old = a[i]
        a[i] = x
        return old
    n = len(a)
    gcd = fractions.gcd(n, k)
    for i in range(gcd):
        curr = i
        x = a[curr]
        for j in range(n // gcd):
            next = (curr + k) % n
            x = replace(a, next, x)
            curr = next

def rrip_demian2(a, k):
    import fractions
    n = len(a)
    gcd = fractions.gcd(n, k)
    for i in range(gcd):
        for j in range(1, n // gcd):
            swap(a, i, (i + j * k) % n)

def rrip_mariano(a, k, offset=0, n=None):
    n = len(a) if n is None else n
    k %= n
    if k == 0:
        return
    if k * 2 > n:
        s = n % k
        for i in xrange(0, n - 2 * s, s):
            for j in xrange(s):
                swap(a, i + j + offset, i + j + s + offset)
        if n > i + 2 * s:
            rrip_mariano(a, n - (i + 2 * s), offset + i + s, n - (i + s))
    else:
        s = k
        for i in xrange(n - s, s - 1, -s):
            for j in xrange(s):
                swap(a, i + j + offset, i + j - s + offset)
        if i > s:
            rrip_mariano(a, s, offset, i)

RRIP_IMPS = (rrip_copied, rrip_demian, rrip_demian2, rrip_mariano)
TEST_VECTORS = [range(12), range(45), range(97)]

def test_validity():
    for tv in TEST_VECTORS:
        for k in range(len(tv)):
            ref_res = rotate_naive(tv, k)
            for imp in RRIP_IMPS:
                tvc = tv[:]
                imp(tvc, k)
                assert tvc == ref_res
    print 'All results are valid.'

NUM_SWAPS_TV_LEN = 97
NUM_SWAPS_K = 43

def test_req_swaps(n, k, print_res=True):
    global swap
    old_swap = swap
    swap_counter = [0]
    def instrum_swap(a, i, j):
        swap_counter[0] += 1
        old_swap(a, i, j)
    swap = instrum_swap
    tv = range(n)
    if print_res:
        print 'Number of swaps (len(a) = %d, k = %d)' % (n, k)
    ret = {}
    for imp in RRIP_IMPS:
        tvc = tv[:]
        swap_counter[0] = 0
        imp(tvc, k)
        if print_res:
            print '  %s: %d' % (imp.func_name, swap_counter[0])
        ret[imp.func_name] = swap_counter[0]
    swap = old_swap
    return ret

def test_req_swaps_in_general():
    for tv in TEST_VECTORS:
        for k in range(1, len(tv)):
            assert all(len(tv) >= v or v == 0
                       for v in test_req_swaps(len(tv), k, False).values())
    print 'Rotating an array of "n" values always takes no more than "n" swaps.'

def main():
    test_validity()
    test_req_swaps(NUM_SWAPS_TV_LEN, NUM_SWAPS_K)
    test_req_swaps_in_general()

if __name__ == '__main__':
    main()
