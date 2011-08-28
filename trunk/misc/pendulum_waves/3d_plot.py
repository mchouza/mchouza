# based on mplot3d example code: surface3d_radial_demo.py
# http://matplotlib.sourceforge.net/examples/mplot3d/surface3d_radial_demo.html
# and the experiment at
# http://www.youtube.com/watch?v=yVkdfJ9PkRQ
from mpl_toolkits.mplot3d import Axes3D
import matplotlib
import numpy as np
from matplotlib import cm
from matplotlib import pyplot as plt

FINAL_TIME = 60.0
FPS = 25
#STEPS = 15
STEPS = 15 + 14 * 3

# create supporting points
x = np.linspace(0.0, 1.00, STEPS)
z = np.linspace(0.0, 1.00, STEPS)
X, Z = np.meshgrid(x, z)

num_frames = int(np.ceil(FINAL_TIME * FPS))

for n in range(num_frames + 1):
    t = float(n) / FPS
    print '%d/%d' % (n, num_frames)
    
    Y = 0.5 - 0.25 * (1.0 - Z) *\
        np.cos(2.0 * np.pi * ((51.0 + (65.0 - 51.0) * X) / 60.0) * t)

    fig = plt.figure()
    ax = fig.add_subplot(111, projection='3d')
    ax.plot_surface(X, Y, Z, rstride=1, cstride=1, cmap=cm.jet)
    ax.set_xlim3d(0, 1)
    ax.set_ylim3d(0, 1)
    ax.set_zlim3d(0, 1)
    plt.savefig('output_images/fig%04d.png' % n)
    plt.close()
