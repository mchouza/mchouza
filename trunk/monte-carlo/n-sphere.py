LOG_10_MAX_EVALS = 6
NUM_DIMS = 8

def in_unit_sphere(x):
    """Checks if the 'x' vector is inside the unit sphere."""
    return 1.0 if sum(c * c for c in x) <= 1.0 else 0.0

def mul(s):
    """Multiplying analog to the 'sum()' built-in function."""
    from operator import mul as opmul
    from functools import reduce
    return reduce(opmul, s)

def rec_int(f, ranges, max_num_evals):
    """Evaluates the integral of the function 'f' over the coordinate ranges
    indicated by 'ranges'. Uses the rectangle rule and no more than
    'max_num_evals' evaluations."""

    from itertools import product as iterprod
    from math import pow, floor, fsum
    
    num_dims = len(ranges)
    points_per_dim = floor(pow(max_num_evals, 1.0 / num_dims))
    num_evals = points_per_dim ** num_dims
    
    coord_ranges = [[lo + (hi - lo) / (2 * points_per_dim) +\
                     ((hi - lo) / points_per_dim) * i
                     for i in range(points_per_dim)]
                    for lo, hi in ranges]

    accum = fsum(f(x) for x in iterprod(*coord_ranges))
    volume = mul(hi - lo for lo, hi in ranges)

    return accum * volume / num_evals

def mc_int(f, ranges, max_num_evals):
    """Evaluates the integral of the function 'f' over the coordinate ranges
    indicated by 'ranges'. Uses the Monte Carlo method and no more than
    'max_num_evals' evaluations."""

    from math import fsum
    
    def random_x():
        from random import uniform
        return tuple(uniform(lo, hi) for lo, hi in ranges)

    accum = fsum(f(random_x()) for i in range(max_num_evals))
    volume = mul(hi - lo for lo, hi in ranges)

    return accum * volume / max_num_evals

def n_sphere_rec_vol(n, r, max_num_evals):
    """Gets the the volume of a n-sphere with radius 'r' by integrating using
    the rectangle rule and using no more than 'max_num_evaluations' of the
    'in_unit_sphere()' function."""
    return rec_int(in_unit_sphere, [[-1, 1]] * n, max_num_evals) * (r ** n)

def n_sphere_mc_vol(n, r, max_num_evals):
    """Gets the the volume of a n-sphere with radius 'r' by integrating using
    the Monte Carlo method and using no more than 'max_num_evaluations' of the
    'in_unit_sphere()' function."""
    return mc_int(in_unit_sphere, [[-1, 1]] * n, max_num_evals) * (r ** n)

def n_sphere_analyt_vol(n, r):
    """Gets the analytic result for the volume of a n-sphere with radius 'r'."""
    from math import pow, pi, gamma
    return pow(pi, n / 2.0) / gamma(n / 2.0 + 1) * (r ** n)

def main():
    """Entry point."""

    import random

    random.seed(0)
    
    print('Analytical result: %f' % n_sphere_analyt_vol(NUM_DIMS, 1.0))

    print('Numerical results:')
    for n in (10 ** i for i in range(2, LOG_10_MAX_EVALS + 1)):
        print('n = %d' % n)
        print('  Rectangle rule volume: %f' %\
              n_sphere_rec_vol(NUM_DIMS, 1.0, n))
        print('  MC method volume: %f' %\
              n_sphere_mc_vol(NUM_DIMS, 1.0, n))

if __name__ == '__main__':
    main()
