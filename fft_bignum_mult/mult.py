import array
import cmath
import math
import random
import time


MIN_BITS = 32 << 10
MAX_BITS = 32 << 12


def mult_base(a, b):
    """Computes the product of 'a' and 'b' by using the normal Python multiplication."""

    return a * b


def get_timings(min_bits, max_bits, mult_funcs):
    timings = {}
    results = []
    for mf in mult_funcs:
        random.seed(0)
        timings[mf.__name__] = []
        num_bits = min_bits
        while num_bits <= max_bits:
            a = random.getrandbits(num_bits)
            b = random.getrandbits(num_bits)
            start = time.time()
            c = mf(a, b)
            dt = time.time() - start
            timings[mf.__name__].append((num_bits, dt))
            if len(results) < len(timings[mf.__name__]):
                results.append(c)
            else:
                assert c == results[len(timings[mf.__name__]) - 1]
            num_bits *= 2
    return timings


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


def complex_arr_mult(a, b):
    """Multiplies two arrays of doubles 'a' and 'b' by interpreting them as
    complex arrays."""

    # checks lengths
    n = len(a)
    assert n == len(b)
    assert n % 2 == 0

    return array.array('d', (a[i] * b[i] - a[i + 1] * b[i + 1]
                             if i % 2 == 0 else
                             a[i - 1] * b[i] + a[i] * b[i - 1]
                             for i in xrange(n)))


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


def arr_fft(a):
    """Computes the FFT of 'a' using arrays."""

    # ensures the length is a power of 2
    n = len(a) / 2
    assert n & (n - 1) == 0

    # base case
    if n == 1:
        return a

    # gets the even and odd arrays
    a_even = array.array('d', (a[i] for i in xrange(2 * n) if i % 4 < 2))
    a_odd = array.array('d', (a[i] for i in xrange(2 * n) if i % 4 >= 2))

    # computes their FFTs
    a_fft_even = arr_fft(a_even)
    a_fft_odd = arr_fft(a_odd)

    # builds the twiddle array
    twiddle = array.array('d', (math.cos(2.0 * (i / 2) * math.pi / n)
                                if i % 2 == 0 else
                                -math.sin(2.0 * (i / 2) * math.pi / n)
                                for i in xrange(n)))

    # twiddles the odd part
    twiddled_a_fft_odd = complex_arr_mult(a_fft_odd, twiddle)

    # builds the result
    return array.array('d', (a_fft_even[i] + twiddled_a_fft_odd[i]
                             for i in xrange(n))) +\
           array.array('d', (a_fft_even[i] - twiddled_a_fft_odd[i]
                             for i in xrange(n)))


def arr_ifft(a):
    """Computes the inverse FFT of 'a' using arrays."""

    def unnormalized_arr_ifft(a):
        """Computes the unnormalized version of 'arr_ifft'."""

        # ensures the length is a power of 2
        n = len(a) / 2
        assert n & (n - 1) == 0

        # base case
        if n == 1:
            return a

        # gets the even and odd arrays
        a_even = array.array('d', (a[i] for i in xrange(2 * n) if i % 4 < 2))
        a_odd = array.array('d', (a[i] for i in xrange(2 * n) if i % 4 >= 2))

        # computes their FFTs
        a_fft_even = arr_fft(a_even)
        a_fft_odd = arr_fft(a_odd)

        # builds the twiddle array
        twiddle = array.array('d', (math.cos(2.0 * (i / 2) * math.pi / n)
                                    if i % 2 == 0 else
                                    math.sin(2.0 * (i / 2) * math.pi / n)
                                    for i in xrange(n)))

        # twiddles the odd part
        twiddled_a_fft_odd = complex_arr_mult(a_fft_odd, twiddle)

        # builds the result
        return array.array('d', (a_fft_even[i] + twiddled_a_fft_odd[i]
                                 for i in xrange(n))) +\
               array.array('d', (a_fft_even[i] - twiddled_a_fft_odd[i]
                                 for i in xrange(n)))

    # gets the unnormalized result and normalizes it
    n = len(a) / 2
    return array.array('d', (a_ifft_i / n for a_ifft_i in unnormalized_arr_ifft(a)))


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
    print ab_digits_fft

    # now we recover the digits
    ab_digits_complex = ifft(ab_digits_fft)
    print ab_digits_complex
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


def mult_arr_fft(a, b):
    """Computes the product of 'a' and 'b' by using the array FFT."""

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

    # builds the arrays
    a_digits = array.array('d', (a_digits[i // 2] if i % 2 == 0 else 0.0
                                 for i in xrange(2 * n)))
    b_digits = array.array('d', (b_digits[i // 2] if i % 2 == 0 else 0.0
                                 for i in xrange(2 * n)))

    # computes the FFTs
    a_digits_fft = arr_fft(a_digits)
    b_digits_fft = arr_fft(b_digits)

    # gets the convolution
    ab_digits_fft = complex_arr_mult(a_digits_fft, b_digits_fft)
    print ab_digits_fft    

    # now we recover the digits
    ab_digits_complex = arr_ifft(ab_digits_fft)
    print ab_digits_complex
    ab_digits = [int(round(ab_digits_complex[i])) for i in xrange(0, 2 * n, 2)]

    # goes over the digits doing the carrying
    carry = 0
    for i in xrange(n):
        carry += ab_digits[i]
        ab_digits[i] = carry & 0xff
        carry >>= 8
    assert carry == 0

    # returns the integer
    return int_from_byte_digits_array(ab_digits)


if __name__ == '__main__':
    print get_timings(MIN_BITS, MAX_BITS, (mult_base, mult_arr_fft))
    #print hex(mult_arr_fft(0x10000, 0x1111))
    #print hex(mult_fft(0x10000, 0x1111))
