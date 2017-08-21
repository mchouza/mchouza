import sys, time
with open('a.txt', 'rb') as fp:
    while True:
        data = fp.read(1024)
        sys.stdout.write(data)
        time.sleep(2)
