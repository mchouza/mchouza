PLOTS = (
    ('k30p_ip', '$k = 0.3 \cdot n$ (in-place algorithms)',
     lambda an: not an.endswith('_cp'), lambda n, k: k * 10 / 3 == n),
    ('k30p_cp', '$k = 0.3 \cdot n$ (copying algorithms)',
     lambda an: an.endswith('_cp'), lambda n, k: k * 10 / 3 == n),
    ('k30f_ip', '$k = 30$ (in-place algorithms)',
     lambda an: not an.endswith('_cp'), lambda n, k: k == 30),
    ('k30f_cp', '$k = 30$ (copying algorithms)',
     lambda an: an.endswith('_cp'), lambda n, k: k == 30),
    ('k3kf_ip', '$k = 3000$ (in-place algorithms)',
     lambda an: not an.endswith('_cp'), lambda n, k: k == 3000),
    ('k3kf_cp', '$k = 3000$ (copying algorithms)',
     lambda an: an.endswith('_cp'), lambda n, k: k == 3000),
    ('k30p_all', '$k = 0.3 \cdot n$ (all algorithms)',
     lambda an: True, lambda n, k: k * 10 / 3 == n),
    ('k30f_all', '$k = 30$ (all algorithms)',
     lambda an: True, lambda n, k: k == 30),
)

AN_ORDER = {
    'top_k_nlogn_cp': 0,
    'top_k_nlogk_cp': 1,
    'top_k_n_cp': 2,
    'top_k_nlogn_ip': 3,
    'top_k_n_ip': 4,
    'top_k_n_ip_cpp': 5
}

FMT_BY_AN = {
    'top_k_nlogn_cp': 'k-',
    'top_k_nlogk_cp': 'k--',
    'top_k_n_cp': 'k-.',
    'top_k_nlogn_ip': 'r-',
    'top_k_n_ip': 'r--',
    'top_k_n_ip_cpp': 'g-'
}

FULL_NAME_BY_AN = {
    'top_k_nlogn_cp': '$n\,\log\,n$ (copying)',
    'top_k_nlogk_cp': '$n\,\log\,k$ (copying)',
    'top_k_n_cp': '$n$ (copying)',
    'top_k_nlogn_ip': '$n\,\log\,n$ (in-place)',
    'top_k_n_ip': '$n$ (in-place)',
    'top_k_n_ip_cpp': '$n$ (in-place, C++)'
}

def get_alg_data(input_fpath):
    alg_name = None
    n = None
    k = None
    input_fp = open(input_fpath)

    alg_data = {}
    
    for l in input_fp:
        desc, data = [e.strip() for e in l.split(':')]
        if desc == 'alg_name':
            alg_name = data
        elif desc == 'n':
            n = int(data)
        elif desc == 'k':
            k = int(data)
        elif desc == 'times':
            times = [float(e) for e in data.split()]
            if alg_name not in alg_data:
                alg_data[alg_name] = {}
            assert (n, k) not in alg_data[alg_name]
            alg_data[alg_name][(n, k)] = times
        else:
            assert 0
    
    input_fp.close()

    return alg_data

def do_single_plot(output_fpath, alg_data, plot_title, an_pred, nk_pred):
    import matplotlib.pyplot as plt
    from collections import OrderedDict

    # gets the data to be used
    plot_alg_data = dict((an, dict((n, t)
                                   for (n, k), t in ad.iteritems()
                                   if nk_pred(n, k)))
                         for an, ad in alg_data.iteritems()
                         if an_pred(an))

    # makes the data vectors
    n_vec = sorted(n for n in plot_alg_data.itervalues().next().iterkeys())
    data_by_alg = dict((an, [sorted(av[n]) for n in n_vec])
                       for an, av in plot_alg_data.iteritems())
    data_vecs = OrderedDict((an, zip(*[(t[2], t[4] - t[2], t[2] - t[0])
                                       for t in av]))
                            for an, av in\
                            sorted(data_by_alg.iteritems(),
                                   key = lambda ai: AN_ORDER[ai[0]]))

    plt.figure()
    plt.xscale('log')
    plt.yscale('log')
    for an, ad in data_vecs.iteritems():
        #plt.errorbar(n_vec, ad[0], yerr=ad[1:]) -- Error bars are too small
        plt.errorbar(n_vec, ad[0], fmt=FMT_BY_AN[an])
    plt.legend([FULL_NAME_BY_AN[an] for an in data_vecs.iterkeys()],
               'lower right')
    plt.title(plot_title)
    
    plt.xlabel('$n$')
    plt.ylabel('Execution time (seconds)')

    plt.savefig(output_fpath)

def plot_alg_data(alg_data):
    for plot_id, plot_title, an_pred, nk_pred in PLOTS:
        do_single_plot('%s.png' % plot_id, alg_data, plot_title, an_pred,
                       nk_pred)

def main(argv):
    assert len(argv) == 2
    plot_alg_data(get_alg_data(argv[1]))

if __name__ == '__main__':
    import sys
    sys.exit(main(sys.argv))
