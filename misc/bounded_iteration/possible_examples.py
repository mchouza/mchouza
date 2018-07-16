def identity(a):
    return a

def add(a, b):
    c = identity(a)
    for i in range(b):
        c += 1
    return c

def min(a, b):
    c = add(a, b)
    for i in range(c):
        if i == a:
            return i
        if i == b:
            return i
    return a

def sub(a, b):
    c = identity(b)
    d = identity(a)
    d += 1
    for i in range(d):
        if c == a:
            return i
        c += 1
    return 0

def max(a, b):
    s = add(a, b)
    m = min(a, b)
    r = sub(s, m)
    return r

def mul(a, b):
    c = 0
    for i in range(b):
        c = add(c, a)
    return c

def power(a, b):
    c = 1
    for i in range(b):
        c = mul(c, a)
    return c

def shl_one(a):
    return add(a, a)

def shr_one(a):
    c = 0
    for i in range(a):
        if c == a:
            return i
        c += 1
        if c == a:
            return i
        c += 1
    return 0

def is_even(a):
    o = 1
    z = 0
    b = shr_one(a)
    b = shl_one(b)
    if b == a:
        return o
    return z

def is_odd(a):
    o = 1
    z = 0
    e = is_even(a)
    if e == z:
        return o
    return z

def reverse_bits(a):
    z = 0
    r = 0
    o = 0
    o += 1
    for i in range(a):
        if a == z:
            return r
        r = shl_one(r)
        ao = is_odd(a)
        if ao == o:
            r += 1
        a = shr_one(a)
    return r

def reverse_bits_n(a, n):
    r = 0
    o = 0
    o += 1
    for i in range(n):
        r = shl_one(r)
        ao = is_odd(a)
        if ao == o:
            r += 1
        a = shr_one(a)
    return r

def log2(a): # 0 returns 0
    r = 0
    for i in range(a):
        a = shr_one(a)
        if a == 0:
            return r
        r += 1
    return r

def xor_bits_n(a, b, n):
    r = 0
    o = 0
    o += 1
    for i in range(n):
        al = is_odd(a)
        bl = is_odd(b)
        blc = sub(o, bl)
        a = shr_one(a)
        b = shr_one(b)
        r = shl_one(r)
        if al == blc:
            r += 1
    r = reverse_bits_n(r, n)
    return r

def c_1():
    r = 0
    r += 1
    return r

def c_2():
    r = c_1()
    r += 1
    return r

def c_5():
    r = c_2()
    r = add(r, r)
    r += 1
    return r

def c_10():
    r = c_2()
    f = c_5()
    r = mul(r, f)
    return r

def c_11():
    r = c_10()
    r += 1
    return r

def c_997():
    t = c_2()
    t += 1
    r = c_10()
    r = power(r, t)
    r = sub(r, t)
    return r

def c_1234():
    t = c_10()
    r = 0
    d = c_1()
    r = add(r, d)
    r = mul(r, 10)
    d += 1
    r = add(r, d)
    r = mul(r, 10)
    d += 1
    r = add(r, d)
    r = mul(r, 10)
    d += 1
    r = add(r, d)
    return r

# meta language
def print_eval(s):
    print('%s = %d' % (s, eval(s)))

def print_eval_bin(s):
    print('%s = %s' % (s, bin(eval(s))))

print_eval('c_997()')
print_eval('c_1234()')
print_eval('add(c_997(), c_5())')
print_eval('sub(c_1(), 0)')
print_eval('sub(c_997(), c_5())')
print_eval('min(c_997(), c_1234())')
print_eval('max(c_997(), c_1234())')
print_eval('mul(c_5(), c_1234())')
print_eval('is_odd(c_1234())')
print_eval('is_odd(c_997())')
print_eval_bin('c_997()')
print_eval_bin('reverse_bits(c_997())')
print_eval_bin('reverse_bits(c_2())')
print_eval_bin('reverse_bits_n(c_2(), c_5())')
print_eval_bin('c_1234()')
print_eval_bin('xor_bits_n(c_1234(), c_997(), c_11())')
print_eval('log2(c_997())')
