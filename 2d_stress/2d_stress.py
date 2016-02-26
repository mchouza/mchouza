N = 10
OMEGA = 1.0
MAX_ITERS = 10000
EPSILON = 1e-6
K = 1.0
G = 0.01
MU = G
LAMBDA = K - 2 * G / 3

u_1 = [[0.0 for j in range(N)] for i in range(N)]
for j in range(N//3, 2*N//3 + 1):
    u_1[0][j] = 1.0
    u_1[N-1][j] = 1.0
u_2 = [[0.0 for j in range(N)] for i in range(N)]
m = [[MU for j in range(N)] for i in range(N)]
l = [[LAMBDA for j in range(N)] for i in range(N)]


for _ in xrange(MAX_ITERS):
    abs_delta = 0.0
    for i in range(1, N-1):
        for j in range(1, N-1):
            u_1_new  = (2 * m[i][j] + l[i][j]) * u_1[i + 1][j]
            u_1_new += (2 * m[i][j] + l[i][j]) * u_1[i - 1][j]
            u_1_new += m[i][j] * u_1[i][j + 1]
            u_1_new += m[i][j] * u_1[i][j - 1]
            u_1_new += (m[i][j] + l[i][j]) * u_2[i + 1][j + 1] / 4
            u_1_new += (m[i][j] + l[i][j]) * u_2[i - 1][j - 1] / 4
            u_1_new -= (m[i][j] + l[i][j]) * u_2[i + 1][j - 1] / 4
            u_1_new -= (m[i][j] + l[i][j]) * u_2[i - 1][j + 1] / 4
            u_1_new /= (6 * m[i][j] + 2 * l[i][j])
            u_2_new  = (2 * m[i][j] + l[i][j]) * u_2[i][j + 1]
            u_2_new += (2 * m[i][j] + l[i][j]) * u_2[i][j - 1]
            u_2_new += m[i][j] * u_2[i + 1][j]
            u_2_new += m[i][j] * u_2[i - 1][j]
            u_2_new += (m[i][j] + l[i][j]) * u_1[i + 1][j + 1] / 4
            u_2_new += (m[i][j] + l[i][j]) * u_1[i - 1][j - 1] / 4
            u_2_new -= (m[i][j] + l[i][j]) * u_1[i + 1][j - 1] / 4
            u_2_new -= (m[i][j] + l[i][j]) * u_1[i - 1][j + 1] / 4
            u_2_new /= (6 * m[i][j] + 2 * l[i][j])
            abs_delta += abs(u_1_new - u_1[i][j])
            abs_delta += abs(u_2_new - u_2[i][j])
            u_1[i][j] = (1 - OMEGA) * u_1[i][j] + OMEGA * u_1_new
            u_2[i][j] = (1 - OMEGA) * u_2[i][j] + OMEGA * u_2_new
    if abs_delta <= EPSILON:
        break
else:
    print 'Maximum number of iterations reached without convergence!'

def print_cell(cv):
    print '%s%.03f' % (' ' if cv >= 0.0 else '', cv),

for j in range(N):
    for i in range(N):
        print_cell(u_1[i][N-j-1])
    print
print '-' * 40
for j in range(N):
    for i in range(N):
        print_cell(u_2[i][N-j-1])
    print