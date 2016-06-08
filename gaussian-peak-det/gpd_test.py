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
    return data

small_peaky_gn_gen = lambda: gp_gnbg_gen(20, 3, 1.0 / 3.0, 3, 4)

NUM_TESTS = 100

TEST_GENS = (small_peaky_gn_gen,)

if __name__ == '__main__':
    print small_peaky_gn_gen()
