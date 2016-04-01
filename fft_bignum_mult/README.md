# Current status

## Current output

    mchouza@saturn:~/Desktop/mchouza/fft_bignum_mult$ python mult.py
    {'mult_base': [(32768, 0.0004470348358154297), (65536, 0.0013301372528076172), (131072, 0.0038518905639648438), (262144, 0.011514902114868164), (524288, 0.034249067306518555), (1048576, 0.10196304321289062), (2097152, 0.30523204803466797), (4194304, 0.9167530536651611), (8388608, 2.757009983062744), (16777216, 8.26206088066101), (33554432, 24.817260026931763)], 'mult_fft': [(32768, 0.27057981491088867), (65536, 0.5822098255157471), (131072, 1.1803271770477295), (262144, 2.5790810585021973), (524288, 5.3474249839782715), (1048576, 10.833239078521729), (2097152, 22.697999000549316), (4194304, 47.595081090927124), (8388608, 99.12497806549072), (16777216, 206.95449495315552), (33554432, 431.21220898628235)]}

## Analysis

It's currently too slow to be competitive with feasible sizes. If we assume that each doubling of input size triples the execution time of the normal algorithm and doubles the time of the FFT-based one, we would expect to reach parity in:

    log (431/25) / log(3/2) ~= 7 size doublings

As that's not feasible due to the memory requirements, we should work in make the FFT method faster.
