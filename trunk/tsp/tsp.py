from itertools import permutations

def tour_len(t, d):
    assert len(t) == len(d) - 1
    return d[0][t[0]] + sum(d[t[i]][t[i+1]] for i in range(len(t) - 1)) +\
           d[t[-1]][0]

def tsp_naive_solve(d):
    btl, best_tour = min((tour_len(t, d), t)
                         for t in permutations(range(1, len(d))))
    return best_tour

def tsp_dp_solve(d):
    
    def memoize(f):
        memo_dict = {}
        def memo_func(*args):
            return memo_dict.get(args, f(*args))
        memo_func.clear = lambda: memo_dict.clear()
        return memo_func

    @memoize
    def rec_tsp_solve(c, ts):
        assert c not in ts
        if ts:
            return min((d[lc][c] + rec_tsp_solve(lc, ts - frozenset([lc]))[0],
                        lc)
                       for lc in ts)
        else:
            return (d[0][c], 0)

    best_tour = []
    c = 0
    cs = frozenset(range(1, len(d)))
    while True:
        l, lc = rec_tsp_solve(c, cs)
        if lc == 0:
            break
        best_tour.append(lc)
        c = lc
        cs = cs - frozenset([lc])

    best_tour = tuple(reversed(best_tour))

    return best_tour

if __name__ == '__main__':   
    #
    # tour length tests
    #

    # 2 cities
    d = [[0, 1, 2],
         [3, 0, 4],
         [5, 6, 0]]
    # 0 -(+1)-> 1 -(+4)-> 2 -(+5)-> 0 => Total: 10
    assert tour_len((1, 2), d) == 10
    # 0 -(+2)-> 2 -(+6)-> 1 -(+3)-> 0 => Total: 11
    assert tour_len((2, 1), d) == 11

    # 3 cities
    d2 = [[ 0,  5, 17,  3],
          [13,  0,  7, 15],
          [15,  3,  0,  3],
          [16, 14,  6,  0]]

    # 0 -(+3)-> 3 -(+14)-> 1 -(+7)-> 2 -(+15)-> 0 => Total: 39
    assert tour_len((3, 1, 2), d2) == 39

    #
    # naive TSP tests
    #

    # 2 cities
    assert tsp_naive_solve(d) == (1, 2)
    
    # 3 cities
    assert tsp_naive_solve(d2) == (3, 2, 1)

    #
    # DP TSP tests
    #

    # 2 cities
    assert tsp_dp_solve(d) == (1, 2)
    
    # 3 cities
    assert tsp_dp_solve(d2) == (3, 2, 1)

    #
    # Mixed big tests
    #
    import random
    random.seed(0)
    
    d3 = [[random.randint(1, 10) if i != j else 0 for i in range(7)]
          for j in range(7)]

    assert tsp_naive_solve(d3) == tsp_dp_solve(d3)

    d4 = [[random.randint(1, 10) if i != j else 0 for i in range(10)]
          for j in range(10)]

    assert tsp_naive_solve(d4) == tsp_dp_solve(d4)
