NT = 1000
NX = 40

L = 0.5
K = 5.0
M = 1.0
G = 1.0
T = 1.0

def initial_x():
    sl0 = L / (NX - 1)
    mm = M / NX
    sk = K * (NX - 1)
    w = M - mm
    x = [0.0 for i in range(2 * NX)]
    for i in range(1, NX):
        x[i] = x[i - 1] + sl0 + w / sk
        w -= mm
    return x

def get_xdot(x):
    sk = K * (NX - 1)
    sl = L / (NX - 1)
    mm = M / NX
    xdot = [x[NX + i] if i < NX else G
            for i in range(2 * NX)]
    for i in range(NX - 1):
        a = sk * (x[i + 1] - x[i] - sl) / mm
        xdot[NX + i] += a
        xdot[NX + i + 1] -= a
    return xdot

def rk4_step(x, dt):
    k1 = get_xdot(x)
    k2 = get_xdot([x[i] + dt * k1[i] / 2.0 for i in range(len(x))])
    k3 = get_xdot([x[i] + dt * k2[i] / 2.0 for i in range(len(x))])
    k4 = get_xdot([x[i] + dt * k3[i] for i in range(len(x))])
    return [x[i] + dt * (k1[i] + 2.0 * (k2[i] + k3[i]) + k4[i]) / 6.0
            for i in range(len(x))]

def sim_slinky():
    dt = T / NT
    xhist = [initial_x()]
    for i in range(NT):
        xhist.append(rk4_step(xhist[-1], dt))
    return xhist

def do_plot(output_fpath, hist):
    import matplotlib.pyplot as plt
    f = plt.figure()
    ax = f.add_subplot(111)
    ax.invert_yaxis()
    for j in range(NX):
        plt.plot([i * T / NT for i in range(NT+1)],
                 [x[j] for x in hist],
                 color=('black' if j == 0 or j == NX-1 else 'gray'))
    plt.savefig(output_fpath)

if __name__ == '__main__':
    hist = sim_slinky()
    do_plot('slinky.png', hist)

