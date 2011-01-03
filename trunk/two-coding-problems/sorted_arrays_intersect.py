def basic_intersect(a, b):
    m = len(a)
    n = len(b)
    i = j = 0
    ret = []
    while i < m and j < n:
        if a[i] == b[j]:
            ret.append(a[i])
            i += 1
            j += 1
        elif a[i] < b[j]:
            i += 1
        elif a[i] > b[j]:
            j += 1
    return ret

def bin_search_intersect(a, b):
    def bin_search(e, a):
        # adapted from Python docs
        from bisect import bisect_left
        i = bisect_left(a, e)
        if i != len(a) and a[i] == e:
            return i
        return None
    if len(a) > len(b):
        a, b = b, a
    return [e for e in a if bin_search(e, b) is not None]

def look_fwd_intersect(a, b):
    from bisect import bisect_left
    def ubound_search(a, m, i, e):
        k = 1
        while i < m and a[i] <= e:
            i += k
            k *= 2
        if i >= m:
            return m if a[m-1] >= e else None
        else:
            return i
    if len(a) > len(b):
        a, b = b, a
    m = len(a)
    n = len(b)
    i = j1 = 0
    ret = []
    while i < m and j1 < n:
        j2 = ubound_search(b, n, j1, a[i])
        if j2 is None:
            break
        k = bisect_left(b, a[i], j1, j2)
        if k < n and b[k] == a[i]:
            ret.append(a[i])
            j1 = k + 1
        else:
            j1 = k
        i += 1
    return ret

def test(f, m, n):
    print 'Testing "%s" with m = %d and n = %d.' % (f.func_name, m, n)
    import random
    random.seed(0)
    assert n >= m
    a = random.sample(range(2 * n), m)
    b = random.sample(range(2 * n), n)
    a.sort()
    b.sort()
    a_int_b = [e for e in a if e in b]
    a_int_b_by_f = f(a, b)
    assert a_int_b == a_int_b_by_f

def main():
    test(basic_intersect, 1000, 1000)
    test(basic_intersect, 100, 20000)
    test(bin_search_intersect, 1000, 1000)
    test(bin_search_intersect, 100, 20000)
    test(look_fwd_intersect, 1000, 1000)
    test(look_fwd_intersect, 100, 20000)

if __name__ == '__main__':
    main()
