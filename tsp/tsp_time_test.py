import timeit

TARGET_TIME = 0.1
N_RANGE = (2, 10)

def time_test(n, rep, func_name):
    setup_stmt = """
import random
from tsp import %(func_name)s
random.seed(0)
d = [[random.randint(1, 10) if i != j else 0 for i in range(%(n)d + 1)]
     for j in range(%(n)d + 1)]
""" % {'n': n, 'func_name': func_name}
    timed_stmt = '%s(d)' % func_name
    time = timeit.timeit(timed_stmt, setup_stmt, number=rep) / rep
    return time

def get_reliable_time(n, func_name):
    time = 0
    rep = 1
    while True:
        time = time_test(n, rep, func_name)
        if time * rep >= TARGET_TIME:
            break
        rep *= 10
    return time

def main():
    print 'n\tnaive time\trec time  \tdp time'
    for n in range(N_RANGE[0], N_RANGE[1] + 1):
        naive_time = get_reliable_time(n, 'tsp_naive_solve')
        rec_time = get_reliable_time(n, 'tsp_rec_solve')
        dp_time = get_reliable_time(n, 'tsp_dp_solve')
        print '%d\t%.4e\t%.4e\t%.4e' % (n, naive_time, rec_time, dp_time)

if __name__ == '__main__':
    main()
