import sys
print 'int main(void)\n{    unsigned x0 = 1234;\n'
for i in range(int(sys.argv[1])):
    j = i + 1
    print '    unsigned x%(j)d = x%(i)d * %(i)d * %(j)d;' % locals()
print '    return (int)x%(j)d;\n}\n' % locals()
