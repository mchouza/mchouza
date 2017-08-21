import time
with open('a.txt', 'wb') as fp:
    for i in range(1000):
        fp.write('%d\n' % i)
        fp.flush()
        time.sleep(0.5)
