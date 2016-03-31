import cmath
import random
import time


MIN_BITS = 32 << 10
MAX_BITS = 32 << 20


def mult_base(a, b):
    """Computes the product of 'a' and 'b' by using the normal Python multiplication."""

    return a * b


def get_timings(min_bits, max_bits, mult_func):
    timings = []
    random.seed(0)
    num_bits = min_bits
    while num_bits <= max_bits:
        a = random.getrandbits(num_bits)
        b = random.getrandbits(num_bits)
        start = time.time()
        c = mult_func(a, b)
        dt = time.time() - start
        timings.append((num_bits, dt))
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



def fft_mul(a, b):
    """Computes the product of 'a' and 'b' by using the FFT."""

    # converts them to digit arrays
    # FIXME: USE hex() TO AVOID O(n^2) behavior
    a_digits = []
    b_digits = []
    while a != 0 or b != 0:
        a_digits.append(a & ((1 << 32) - 1))
        b_digits.append(b & ((1 << 32) - 1))
        a >>= 32
        b >>= 32

    # pads them to a power of two length beyond the one needed
    # (because we don't want a circular convolution)
    n = 1
    while n < len(a_digits) or n < len(b_digits):
        n *= 2
    n *= 2
    a_digits += [0] * (n - len(a_digits))
    b_digits += [0] * (n - len(b_digits))

    # we can express each value in terms of its digits as follows:
    # a = a_0 * 2^{32 * 0} + a_1 * 2^{32 * 1} + ... + a_n * 2^{32 * n}
    # b = b_0 * 2^{32 * 0} + b_1 * 2^{32 * 1} + ... + b_n * 2^{32 * n}
    # then we have
    # a * b = (a_0 * b_0) * 2^{32 * 0} + (a_0 * b_1 + a_1 * b_0) * 2^{32 * 1} + ... +
    #         (a_n * b_n) * 2^{32 * (2 * n)}
    # that's just a convolution and we can accelerate it with the FFT:
    # FIXME: EXPLAIN

    a_digits_fft = fft(a_digits)
    b_digits_fft = fft(b_digits)

    # FIXME: FINISH IMPLEMENTATION
    assert 0


if __name__ == '__main__':

    # FIXME: DO A PROPER TIMING COMPARISON
    #print ifft(fft(range(128)))
    start = time.time()
    fft([45 for _ in xrange(MAX_BITS / 32)])
    print time.time() - start

    #for nb, t in get_timings(MIN_BITS, MAX_BITS, mult_base):
    #    print nb, t
