import os, sys

p = set()
for i in xrange(int(sys.argv[1])):
    p.add(i)

os.system("ps aux | egrep \"(USER|$PPID)\\s\"")
