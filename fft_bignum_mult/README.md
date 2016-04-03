# Current status

## Current output

### CPython 2.7.6 (included in Ubuntu 14.04)

    mchouza@nbmchouza:~/Desktop/personal/mchouza/fft_bignum_mult$ python mult.py 
    mult_base,32768,0.000627
    mult_base,65536,0.001814
    mult_base,131072,0.005441
    mult_base,262144,0.015961
    mult_base,524288,0.037798
    mult_base,1048576,0.110735
    mult_base,2097152,0.330120
    mult_base,4194304,0.989377
    mult_base,8388608,2.973934
    mult_base,16777216,8.930586
    mult_base,33554432,27.207421
    mult_fft,32768,0.323228
    mult_fft,65536,0.696468
    mult_fft,131072,1.433753
    mult_fft,262144,2.885332
    mult_fft,524288,6.057370
    mult_fft,1048576,12.760847
    mult_fft,2097152,26.800665
    mult_fft,4194304,56.181455
    mult_fft,8388608,118.566333
    mult_fft,16777216,244.990205
    mult_fft,33554432,511.547788
    mult_np_fft,32768,0.024970
    mult_np_fft,65536,0.049963
    mult_np_fft,131072,0.098622
    mult_np_fft,262144,0.197670
    mult_np_fft,524288,0.399104
    mult_np_fft,1048576,0.816445
    mult_np_fft,2097152,1.590597
    mult_np_fft,4194304,3.162171
    mult_np_fft,8388608,6.468384
    mult_np_fft,16777216,13.199233
    mult_np_fft,33554432,26.326776
    mult_gmpy2,32768,0.000119
    mult_gmpy2,65536,0.000208
    mult_gmpy2,131072,0.000519
    mult_gmpy2,262144,0.001273
    mult_gmpy2,524288,0.003295
    mult_gmpy2,1048576,0.006677
    mult_gmpy2,2097152,0.020278
    mult_gmpy2,4194304,0.038238
    mult_gmpy2,8388608,0.080400
    mult_gmpy2,16777216,0.177419
    mult_gmpy2,33554432,0.373259

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
