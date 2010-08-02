import math, random

N = 1000

NUMBERS = [4401501, 1984319, 1064736, 6495167,
           6402639, 7578056, 9301342, 6042069,
           1144375, 5680006, 7450344, 9099174,
           2011586, 8039920, 3010493, 1658370,
           5927190, 3880633, 1318068, 9594698,
           2877906, 1792394, 9120086, 7372216,
           2141103, 7256943, 6603598, 8565018,
           1698346, 3004879]

def run_until_collision():
    combs_dict = {}
    i = 0
    while True:
        comb = random.sample(NUMBERS, 15)
        s = sum(comb)
        if s in combs_dict:
            return i, comb, combs_dict[s]
        combs_dict[s] = comb
        i += 1

def show_stats():
    total = 0.0
    sq_total = 0.0
    print 'Please wait until the count reaches 100...'
    for i in range(N):
        tries, dum, dum = run_until_collision()
        total += tries
        sq_total += tries ** 2
        if i % math.ceil(N / 100.0) == 0:
            print '%d' % (i * 100.0 / N),
    print '\n\nTries statistics'
    print '  Average: %f' % (total / N)
    print '  SD: %f' % math.sqrt(sq_total / N -
                                 (total / N) ** 2)

if __name__ == '__main__':
    show_stats()
