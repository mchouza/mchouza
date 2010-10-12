import random

N = 10000

def get_tosses_until_head():
    tosses = 0
    while True:
        coin = random.randint(0, 1)
        tosses += 1
        if coin == 0:
            break
    return tosses

def get_balance():
    balance = -100
    tosses = get_tosses_until_head()
    balance += 2 ** tosses
    return balance

def main():
    random.seed(0)
    min_balance = max_balance = accum_balance = get_balance()
    for i in xrange(1, N):
        balance = get_balance()
        if balance < min_balance:
            min_balance = balance
        if balance > max_balance:
            max_balance = balance
        accum_balance += balance
    print 'Statistics after %d tries:' % N
    print '  Minimum balance: %d' % min_balance
    print '  Average balance: %d' % (float(accum_balance) / N)
    print '  Maximum balance: %d' % max_balance

if __name__ == '__main__':
    main()
