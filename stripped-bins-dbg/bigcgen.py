import sys
print 'int main(void)\n{\n    unsigned x0 = 1234;'
for i in range(int(sys.argv[1])):
    j = i + 1
    print '    unsigned x%(j)d = x%(i)d * %(j)d * %(j)d;' % locals()
print '    return (int)x%(j)d;\n}' % locals()
