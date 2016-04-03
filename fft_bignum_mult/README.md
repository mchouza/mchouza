# Current status

## Current output

### CPython 2.7.6 (included in Ubuntu 14.04)

    mchouza@nbmchouza:~/Desktop/personal/mchouza/fft_bignum_mult$ python mult.py 
    mult_base,32768,0.001067
    mult_base,65536,0.003249
    mult_base,131072,0.009323
    mult_base,262144,0.022952
    mult_base,524288,0.047091
    mult_base,1048576,0.112633
    mult_base,2097152,0.333627
    mult_base,4194304,0.999614
    mult_base,8388608,2.996164
    mult_base,16777216,9.014925
    mult_base,33554432,26.953920
    mult_fft,32768,0.281757
    mult_fft,65536,0.598452
    mult_fft,131072,1.267990
    mult_fft,262144,2.684053
    mult_fft,524288,5.658688
    mult_fft,1048576,12.572459
    mult_fft,2097152,25.081326
    mult_fft,4194304,52.820544
    mult_fft,8388608,120.842286
    mult_fft,16777216,243.313017
    mult_fft,33554432,477.752420

### PyPy 2.2.1 (included in Ubuntu 14.04)

    mchouza@nbmchouza:~/Desktop/personal/mchouza/fft_bignum_mult$ pypy mult.py 
    mult_base,32768,0.000625
    mult_base,65536,0.001896
    mult_base,131072,0.005748
    mult_base,262144,0.015004
    mult_base,524288,0.035236
    mult_base,1048576,0.091066
    mult_base,2097152,0.271232
    mult_base,4194304,0.801769
    mult_base,8388608,2.377286
    mult_base,16777216,7.086744
    mult_base,33554432,21.343788
    mult_fft,32768,0.162012
    mult_fft,65536,0.176300
    mult_fft,131072,0.363371
    mult_fft,262144,0.813834
    mult_fft,524288,1.878709
    mult_fft,1048576,5.626539
    mult_fft,2097152,17.979627
    mult_fft,4194304,61.414743
    mult_fft,8388608,225.767057

Interrupted after 20 minutes of execution.

## Analysis

It's currently too slow to be competitive with feasible sizes. If we assume that each doubling of input size triples the execution time of the normal algorithm and doubles the time of the FFT-based one, we would expect to reach parity in:

    log (477/27) / log(3/2) ~= 7 size doublings

As that's not feasible due to the memory requirements, we should work in making the FFT method faster.
