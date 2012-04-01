import math
import matplotlib.pyplot as plt

N = 100000

def do_hist(output_fpath, digits_as_frac):
    plt.figure()
    plt.hist(digits_as_frac, 90, facecolor='green')
    plt.xlabel('Leading digits expressed as a fraction')
    plt.ylabel('Number of powers of two per bin')
    plt.savefig(output_fpath)

def do_benford_hist(output_fpath, digits_as_frac):
    import numpy
    plt.figure()
    n, bins, patches = plt.hist(digits_as_frac, 90, facecolor='green')
    y = numpy.log10(1.0 + 1.0 / (100.0 * bins)) * N
    plt.plot(bins, y, 'r', linewidth=2)
    plt.legend(['Benford\'s law prediction'], 'upper right')
    plt.xlabel('Leading digits expressed as a fraction')
    plt.ylabel('Number of powers of two per bin')
    plt.savefig(output_fpath)

def do_log_hist(output_fpath, digits_as_frac):
    import numpy
    plt.figure()
    logspace = numpy.logspace(numpy.log10(0.1), numpy.log10(1.0), 90)
    n, bins, patches = plt.hist(digits_as_frac, logspace, facecolor='green')
    plt.xlabel('Leading digits expressed as a fraction (log bins)')
    plt.ylabel('Number of powers of two per bin')
    plt.savefig(output_fpath)

def main():
    po2_first_digits = [pow(10.0, math.modf(math.log10(2 ** n))[0] - 1)
                        for n in xrange(N)]
    do_hist('plot_1.png', po2_first_digits)
    do_benford_hist('plot_2.png', po2_first_digits)
    do_log_hist('plot_3.png', po2_first_digits)

if __name__ == '__main__':
    main()
