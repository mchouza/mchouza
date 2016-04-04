import numpy as np
import sys


def do_plot(output_fpath, mult_times, plot_title):
    import matplotlib.pyplot as plt
    from collections import OrderedDict

    plt.figure()
    plt.xscale('log')
    plt.yscale('log')

    alg_ids = mult_times.keys()

    legends = []

    for a_id in alg_ids:
        n_vec, t_vec = zip(*mult_times[a_id])
        linear_fit = np.polyfit(np.log(n_vec), np.log(t_vec), 1)
        color = next(plt.gca()._get_lines.color_cycle)
        points, = plt.plot(n_vec, t_vec, 'o', color=color)
        line, = plt.plot(n_vec, np.exp(np.poly1d(linear_fit)(np.log(n_vec))), '-', color=color)
        legends.append((points, line))

    plt.legend(legends, alg_ids, 'lower right')

    plt.title(plot_title)
    
    plt.xlabel('Operand size (bits)')
    plt.ylabel('Execution time (seconds)')

    plt.savefig(output_fpath)


if __name__ == '__main__':

    mult_times = {}
    with open(sys.argv[1]) as csv_fp:
        for l in csv_fp:
            alg, size, time = l.split(',')
            size = int(size)
            time = float(time)
            mult_times.setdefault(alg, []).append((size, time))

    do_plot('test.png', mult_times, 'Test plot')