import h5py
import json
import random
import string

def create_random_dataset():
    ret = {}
    for i in range(random.randint(50, 100)):
        k = ''.join(random.choice(string.ascii_lowercase)
                    for _ in range(random.randint(5, 20)))
        if random.choice([False, True]):
            ret[k] = random.randint(1, 1000)
        else:
            ret[k] = ''.join(random.choice(string.ascii_lowercase)
                             for _ in range(random.randint(5, 20)))
    return ret

with h5py.File('many_jsons.h5', 'w') as hf:
    for k in string.ascii_lowercase:
        hf.create_dataset(k, data=json.dumps(create_random_dataset()))
