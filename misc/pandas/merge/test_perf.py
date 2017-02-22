import numpy as np
import pandas as pd
import sys
import time


def create_test_frames(num_frames, num_rows, num_data_cols):
    ret = [pd.DataFrame(index=np.arange(i, num_rows * num_frames, num_frames))
           for i in xrange(num_frames)]
    for df in ret:
        for i in xrange(num_data_cols):
            df['d%d' % i] = np.random.random(size=num_rows)
    return ret


def merge_resort(frames):
    ret = pd.concat(frames)
    ret.sort_index(inplace=True, kind='mergesort')


if __name__ == '__main__':
    assert len(sys.argv) == 4
    num_frames = int(sys.argv[1])
    num_rows = int(sys.argv[2])
    num_data_columns = int(sys.argv[3])
    print 'num_frames:', num_frames, 'num_rows:', num_rows, 'num_data_columns:', num_data_columns
    frames = create_test_frames(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
    start = time.time()
    res_1 = merge_resort(frames)
    print 'merge_resort:', time.time() - start
