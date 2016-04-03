import array
import cmath
import gmpy2
import math
import numpy as np
import random
import time


MIN_BITS = 32 << 10
MAX_BITS = 32 << 20


def mult_base(a, b):
    """Computes the product of 'a' and 'b' by using the normal Python multiplication."""

    return a * b


def fft(a):
    """Computes the FFT of 'a'.

    Conceptually speaking,
    fft(a)_j = \sum_{k=0}^{n-1} e^{-i \frac{2 k j \pi}{n}} a_k
    but that would require O(n^2) operations.

    We can split the sum in odd-even terms:
    fft(a)_j = \sum_{k=0}^{n/2-1} e^{-i \frac{4 k j \pi}{n}} a_{2 k} +
               \sum_{k=0}^{n/2-1} e^{-i \frac{2 (2 k + 1) j \pi}{n}} a_{2 k + 1}
    fft(a)_j = \sum_{k=0}^{n/2-1} e^{-i \frac{4 k j \pi}{n}} a_{2 k} +
               e^{-i \frac{2 j \pi}{n} \sum_{k=0}^{n/2-1} e^{-i \frac{4 k j \pi}{n}} a_{2 k + 1}
    fft(a)_j = fft(a_{even})_j + e^{-i \frac{2 j \pi}{n} fft(a_{odd})_j

    This recursion will have linear cost at each level and logarithmic depth,
    so we end with O(n log n) operations.
    """

    # ensures the length is a power of 2
    n = len(a)
    assert n & (n - 1) == 0

    # base case
    if n == 1:
        return a

    # gets the even and odd arrays
    a_even = a[::2]
    a_odd = a[1::2]

    # computes their FFTs
    a_fft_even = fft(a_even)
    a_fft_odd = fft(a_odd)

    # combines their values
    return [a_fft_even[j % (n / 2)] +
            cmath.exp(-1.0j * (2.0 * j * cmath.pi) / n) *
                a_fft_odd[j % (n / 2)]
            for j in range(n)]


def ifft(a):
    """Computes the inverse FFT of 'a'."""

    def unnormalized_ifft(a):
        """Unnormalized version of the inverse IFFT. It works as the FFT with
        only a sign difference."""

        n = len(a)
        assert n & (n - 1) == 0
        if n == 1:
            return a
        a_ifft_even = unnormalized_ifft(a[::2])
        a_ifft_odd = unnormalized_ifft(a[1::2])
        return [a_ifft_even[j % (n / 2)] +
                cmath.exp(1.0j * (2.0 * j * cmath.pi) / n) *
                a_ifft_odd[j % (n / 2)]
                for j in range(n)]

    # just normalizes the result
    n = len(a)
    return [b_i / n for b_i in unnormalized_ifft(a)]


def get_byte_digits_array(a):
    """Given an integer 'a', returns the associated byte digits array."""

    a_hex = hex(a)[2:].rstrip('L')
    num_digits = (len(a_hex) - 1) // 2 + 1
    a_hex = '0' * (num_digits * 2 - len(a_hex)) + a_hex
    return [int(a_hex[2 * (num_digits - i) - 2 : 2 * (num_digits - i)], 16) 
            for i in xrange(num_digits)]


def int_from_byte_digits_array(arr):
    """Given a byte digits array 'arr', returns an integer."""

    num_digits = len(arr)
    return int(''.join('%02x' % arr[i] for i in range(num_digits - 1, -1, -1)), 16)


def mult_fft(a, b):
    """Computes the product of 'a' and 'b' by using the FFT."""

    # converts them to digit arrays
    a_digits = get_byte_digits_array(a)
    b_digits = get_byte_digits_array(b)

    # pads them to a power of two length beyond the one needed
    # (because we don't want a circular convolution)
    n = 1
    while n < len(a_digits) or n < len(b_digits):
        n *= 2
    n *= 2
    a_digits += [0] * (n - len(a_digits))
    b_digits += [0] * (n - len(b_digits))

    # we can express each value in terms of its digits as follows:
    # a = a_0 * 2^{8 * 0} + a_1 * 2^{8 * 1} + ... + a_n * 2^{8 * n}
    # b = b_0 * 2^{8 * 0} + b_1 * 2^{8 * 1} + ... + b_n * 2^{8 * n}
    # FIXME: EXPLAIN

    a_digits_fft = fft(a_digits)
    b_digits_fft = fft(b_digits)

    # then we have
    # a * b = (a_0 * b_0) * 2^{8 * 0} + (a_0 * b_1 + a_1 * b_0) * 2^{8 * 1} + ... +
    #         (a_n * b_n) * 2^{8 * (2 * n)}
    # that's just a convolution and we can accelerate it with the FFT:

    ab_digits_fft = [a_digits_fft[i] * b_digits_fft[i] for i in xrange(n)]

    # now we recover the digits
    ab_digits_complex = ifft(ab_digits_fft)
    ab_digits = [int(round(abs(abcd))) for abcd in ab_digits_complex]

    # checks the maximum rounding error
    assert max(abs(ab_digits_complex[i] - ab_digits[i]) for i in xrange(len(ab_digits))) < 0.1
    #print n, max(abs(ab_digits_complex[i] - ab_digits[i]) for i in xrange(len(ab_digits)))

    # goes over the digits doing the carrying
    carry = 0
    for i in xrange(n):
        carry += ab_digits[i]
        ab_digits[i] = carry & 0xff
        carry >>= 8
    assert carry == 0

    # returns the integer
    return int_from_byte_digits_array(ab_digits)


def mult_np_fft(a, b):
    """Computes the product of 'a' and 'b' by using the numpy FFT."""

    a_digits = get_byte_digits_array(a)
    b_digits = get_byte_digits_array(b)

    n = 1
    while n < len(a_digits) or n < len(b_digits):
        n *= 2
    n *= 2
    a_digits += [0] * (n - len(a_digits))
    b_digits += [0] * (n - len(b_digits))

    a_digits_fft = np.fft.fft(a_digits)
    b_digits_fft = np.fft.fft(b_digits)

    ab_digits_fft = a_digits_fft * b_digits_fft

    ab_digits_complex = np.fft.ifft(ab_digits_fft)
    ab_digits = [int(round(abs(abcd))) for abcd in ab_digits_complex]

    # checks the maximum rounding error
    assert max(abs(ab_digits_complex[i] - ab_digits[i]) for i in xrange(len(ab_digits))) < 0.1
    #print n, max(abs(ab_digits_complex[i] - ab_digits[i]) for i in xrange(len(ab_digits)))

    # goes over the digits doing the carrying
    carry = 0
    for i in xrange(n):
        carry += ab_digits[i]
        ab_digits[i] = carry & 0xff
        carry >>= 8
    assert carry == 0

    # returns the integer
    return int_from_byte_digits_array(ab_digits)


def mult_gmpy2(a, b):
    """Computes the product of 'a' and 'b' by using gmpy2."""

    return int(gmpy2.mul(a, b))


def print_timings(min_bits, max_bits, mult_funcs):
    results = []
    for mf in mult_funcs:
        random.seed(0)
        num_bits = min_bits
        step_num = 0
        while num_bits <= max_bits:
            a = random.getrandbits(num_bits)
            b = random.getrandbits(num_bits)
            start = time.time()
            c = mf(a, b)
            dt = time.time() - start
            if len(results) <= step_num:
                results.append(c)
            else:
                assert c == results[step_num]
            print '%s,%u,%f' % (mf.__name__, num_bits, dt)
            num_bits *= 2
            step_num += 1


if __name__ == '__main__':
    print_timings(MIN_BITS, MAX_BITS, (mult_base, mult_fft, mult_np_fft, mult_gmpy2))
