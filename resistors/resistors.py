TOL = 1e-6
K = 1.5

def solve(n):
    assert n >= 4
    v = [[0.5 for y in range(n)] for x in range(n)]
    delta = 2 * TOL
    FIXED_VALUES = {
        (0, 0): 1,
        (2, 1): 0
    }
    while delta > TOL:
        delta = 0
        for x in range(n):
            for y in range(n):
                if (x, y) in FIXED_VALUES:
                    v[x][y] = FIXED_VALUES[(x, y)]
                    continue
                vo = v[x][y]
                vn = (v[x - 1][y] + v[(x + 1) % n][y] +
                      v[x][y - 1] + v[x][(y + 1) % n]) / 4.0
                v[x][y] = vn * K + vo * (1 - K)
                delta = max(abs(vn - vo), delta)
    return 1.0 / (4 * v[0][0] - v[-1][0] - v[1][0] - v[0][-1] - v[0][1])

if __name__ == '__main__':
    from time import time
    for n in (8, 16, 32, 64, 128):
        start = time()
        print 'N = %d - R = %f - Time: %f s' % (n, solve(n), time() - start)
