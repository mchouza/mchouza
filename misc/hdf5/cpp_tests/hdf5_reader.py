import h5py

with h5py.File('many_jsons.h5', 'r') as h5fp:
    for ds_name, ds in h5fp.iteritems():
        print ds_name, ds.dtype
