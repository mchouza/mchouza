from math import cos, pi

# integrates \frac{1}{4\pi^2} \int_0^{2\pi} dp \int_0^{2\pi} dq
# \frac{1 - \cos(2 p + q)}{2 - \cos p - \cos q} using n x n points
def calc_num_integral(n):
    accum = 0
    f = lambda p, q: (1 - cos(2*p + q)) / (2 - cos(p) - cos(q))
    for i in range(n):
        for j in range(n):
            accum += f((i + 0.5)*2*pi / n, (j + 0.5)*2*pi / n)
    return accum / (n*n) # the 4 \pi^2 factors cancel

if __name__ == '__main__':
    print calc_num_integral(100)
