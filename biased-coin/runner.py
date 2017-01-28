import hashlib
import math
import os
import struct
import sys


RUN_LENGTH = 300
NUM_RUNS = 1000
P_RANGE = (0.4, 0.6)


class DumbCryptoPRNG(object):
    """Very simple, naive, inefficient SHA-1 based PRNG."""

    def __init__(self, seed):
        """Initializes the PRNG with a seed."""
        
        self._state = hashlib.sha1(seed).digest()

    def value(self):
        """Returns a pseudo-random value as a double in [0, 1)."""

        ret = struct.unpack('<Q', self._state[:8])[0] / float(2 ** 64)
        self._state = hashlib.sha1(self._state).digest()
        return ret


def simulate_run(prng, bettor_class, initial_wealth):
    """Returns the final wealth of the bettor."""

    bettor = bettor_class(initial_wealth)
    w = initial_wealth
    p = prng.value() * (P_RANGE[1] - P_RANGE[0]) + P_RANGE[0]

    for i in range(RUN_LENGTH):
        b = bettor.bet()
        assert abs(b) <= w
        r = 1 if prng.value() < p else -1
        dw = r * b
        w += dw
        bettor.show_results(r, dw)
        if w <= 0.0:
            break

    return max(w, 0.0)


def simulate_multi_run(prng, bettor_class, initial_wealth):
    """Returns the mean of ln(wealth) after running multiple runs."""

    return sum(math.log(simulate_run(prng, bettor_class, initial_wealth))
               for i in range(NUM_RUNS)) / float(NUM_RUNS)


if __name__ == '__main__':
    prng = DumbCryptoPRNG('AAA')

    bettor_classes = []

    for bm_path in sys.argv[1:]:
        ns = {}
        execfile(bm_path, ns)
        bm_candidates = [v 
                         for v in ns.itervalues() 
                         if type(v) == type(DumbCryptoPRNG)]
        assert len(bm_candidates) == 1
        bettor_classes.append(bm_candidates[0])

    for bc in bettor_classes:
        print bc.__name__, simulate_multi_run(prng, bc, 1.0)
