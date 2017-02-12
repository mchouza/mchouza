import numpy as np
import pandas as pd
import string
import time


NUM_TEST_ROWS = 100000


def generate_test_df(n, inc_obj_columns=False):
    """Generates a test DataFrame with 'n' rows, optionally including some
    object columns."""

    dfd = {'f%d' % i: np.random.random(size=n) for i in range(100)}
    if inc_obj_columns:
        dfd.update({
            'o%d' % i: np.random.choice(list(string.printable), size=n)
            for i in range(10)
        })
    return pd.DataFrame(dfd)


def main():
    test_df = generate_test_df(NUM_TEST_ROWS)
    test_df.to_hdf('test.h5', 'key')
    start = time.time()
    test_df_2 = pd.read_hdf('test.h5')
    print 'Reading base array:', time.time() - start
    assert test_df_2.equals(test_df)
    test_df = generate_test_df(NUM_TEST_ROWS, True)
    test_df.to_hdf('test2.h5', 'key')
    start = time.time()
    test_df_2 = pd.read_hdf('test2.h5')
    print 'Reading array with object:', time.time() - start
    assert test_df_2.equals(test_df)


if __name__ == '__main__':
    main()
