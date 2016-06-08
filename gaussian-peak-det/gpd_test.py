import numpy as np

def phi(z):
    from scipy.special import erf
    return 0.5 * (1 + erf(z / np.sqrt(2)))

def gp_gnbg_gen(n, h, na, gslo, gshi):
    assert n >= 20
    data = np.sqrt(np.random.normal(loc=0.0, scale=na, size=n) ** 2)
    mu = np.random.random() * n / 2.0 + n / 4.0
    sigma = (np.random.random() * (gshi - gslo) + gslo) / 2
    k = sigma * np.sqrt(2 * np.pi) * h
    for i in xrange(len(data)):
        data[i] += k * (phi(((i + 1) - mu) / sigma) -  phi((i - mu) / sigma))
    return data, mu, sigma


def small_peaky_gn_gen():
    return gp_gnbg_gen(20, 3, 1.0 / 3.0, 3, 4)


def big_peaky_gn_gen():
    return gp_gnbg_gen(1000, 3, 1.0 / 3.0, 3, 4)


def crude_max(tv):
    return np.argmax(tv)


def weighted_max(tv):
    i1, i2 = tv.argsort()[-2:][::-1]
    return (i1 * tv[i1] + i2 * tv[i2]) / (tv[i1] + tv[i2])


def naive_centroid(tv):
    i = np.argmax(tv)
    m = 0
    s = 0
    for d in range(-5, 5):
        m += tv[i+d] * (i + d + 0.5)
        s += tv[i+d]
    return m / s


NUM_TESTS = 100

TEST_GENS = (small_peaky_gn_gen, big_peaky_gn_gen)

PEAK_DETECTORS = (crude_max, weighted_max, naive_centroid)


if __name__ == '__main__':
    np.random.seed(42)
    for tg in TEST_GENS:
        pd_biases = [np.zeros(NUM_TESTS) for _ in PEAK_DETECTORS]
        for n in xrange(NUM_TESTS):
            tv, tmu, tsigma = tg()
            for m, pd in enumerate(PEAK_DETECTORS):
                pd_biases[m][n] = pd(tv) - tmu
        print 'Test %s' % tg.__name__
        for m, pd in enumerate(PEAK_DETECTORS):
            print '  Peak detector %s' % pd.__name__
            print '    Average bias: %f' % np.mean(pd_biases[m])
            print '    Average abs error: %f' % np.mean(np.abs(pd_biases[m]))
            print '    STD of abs error: %f' % np.std(np.abs(pd_biases[m]))
 



