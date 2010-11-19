import timeit

TARGET_TIME = 0.1
N_RANGE = (2, 10)

def time_test_naive(n, rep):
    setup_stmt = """
import random
from tsp import tsp_naive_solve
random.seed(0)
d = [[random.randint(1, 10) if i != j else 0 for i in range(%(n)d + 1)]
     for j in range(%(n)d + 1)]
""" % {'n': n}
    naive_timed_stmt = 'tsp_naive_solve(d)'
    naive_time = timeit.timeit(naive_timed_stmt, setup_stmt, number=rep) / rep
    return naive_time

def time_test_dp(n, rep):
    setup_stmt = """
import random
from tsp import tsp_dp_solve
random.seed(0)
d = [[random.randint(1, 10) if i != j else 0 for i in range(%(n)d + 1)]
     for j in range(%(n)d + 1)]
""" % {'n': n}
    dp_timed_stmt = 'tsp_dp_solve(d)'
    dp_time = timeit.timeit(dp_timed_stmt, setup_stmt, number=rep) / rep
    return dp_time

def get_reliable_times(n):
    naive_time = 0
    naive_rep = 1
    while True:
        naive_time = time_test_naive(n, naive_rep)
        if naive_time * naive_rep >= TARGET_TIME:
            break
        naive_rep *= 10
    dp_time = 0
    dp_rep = 1
    while True:
        dp_time = time_test_dp(n, dp_rep)
        if dp_time * dp_rep >= TARGET_TIME:
            break
        dp_rep *= 10
    return naive_time, dp_time

def main():
    print 'n\tnaive time\tdp time'
    for n in range(N_RANGE[0], N_RANGE[1] + 1):
        naive_time, dp_time = get_reliable_times(n)
        print '%d\t%.4e\t%.4e' % (n, naive_time, dp_time)

if __name__ == '__main__':
    main()
