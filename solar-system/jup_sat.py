import math

# time lapse to simulate
TIME_LAPSE = 1000 * 365.25 * 86400.0 # s

# tolerance
TOLERANCE = 10000

# we start with position referred to the Solar System barycenter
# the positions of Jupiter and Saturn are those of their barycenters, extracted
# from http://ssd.jpl.nasa.gov/horizons.cgi
# the gravitational parameters were obtained from 
# http://en.wikipedia.org/wiki/Standard_gravitational_parameter
# the position of the Sun is initialized to keep the barycenter at [0, 0, 0]
START_DATE = 2457040.500000000 # A.D. 2015-Jan-18 00:00:00.0000 (CT)
SUN_GM = 132712440018.0 # km^3/s^2
SUN_POS = [None] * 3
SUN_VEL = [None] * 3
JUPITER_GM = 126686534.0 # km^3/s^2
JUPITER_POS = [-5.712691376315312E+08, 5.547583934246618E+08, 1.046755216594735E+07] # km
JUPITER_VEL = [-9.257840749848828E+00, -8.757974578956960E+00, 2.435497684120232E-01] # km/s
SATURN_GM = 37931187.0 # km^3/s^2
SATURN_POS = [-7.974531328912680E+08, -1.256851655647483E+09, 5.359079344390164E+07] # km
SATURN_VEL = [7.628458343886854E+00, -5.202188329401300E+00, -2.131421966153313E-01] # km/s

# calculates the difference a - b of two vectors
def vec_sub(a, b):
    return [a_i - b_i for a_i, b_i in zip(a, b)]

# calculates the sum a + b of two vectors
def vec_add(a, b):
    return [a_i + b_i for a_i, b_i in zip(a, b)]

# multiplies a vector 'a' by a scalar 'k'
def sc_mult(k, a):
    return [k * a_i for a_i in a]

# calculates the norm squared of a vector
def sq_norm(vec):
    return sum(vec_i * vec_i for vec_i in vec)

# calculates the norm of a vector
def norm(vec):
    return math.sqrt(sq_norm(vec))

# normalizes a vector, a / ||a||
def normalize(a):
    return sc_mult(1.0 / norm(a), a)

# calculates the acceleration of a planet given its position and a list of
# gravitational parameters and positions of other objects
def calc_grav_acc(pos, objects):
    acc = [0.0, 0.0, 0.0]
    for obj_gm, obj_pos in objects:
        obj_rel_pos = vec_sub(obj_pos, pos)
        obj_dir_vec = normalize(obj_rel_pos)
        obj_sq_dist = sq_norm(obj_rel_pos)
        acc_from_obj_mag = obj_gm / obj_sq_dist
        acc_from_obj = sc_mult(acc_from_obj_mag, obj_dir_vec)
        acc = vec_add(acc, acc_from_obj)
    return acc

# calculates the derivative of the state vector
def calc_state_vec_deriv(state_vec):
    # state_vec = [obj_0_gm, obj_0_x, obj_0_y, obj_0_z, obj_0_vx, obj_0_vy, obj_0_vz, obj_1_gm, ...]
    assert len(state_vec) % 7 == 0
    state_vec_deriv = []
    for i in range(len(state_vec) // 7):
        other_obj_data = [[state_vec[j * 7], state_vec[j * 7 + 1: j * 7 + 4]]
                          for j in range(len(state_vec) // 7)
                          if j != i]
        obj_i_acc = calc_grav_acc(state_vec[i * 7 + 1: i * 7 + 4], other_obj_data)
        state_vec_deriv.append(0.0)
        state_vec_deriv.extend(state_vec[i * 7 + 4: i * 7 + 7])
        state_vec_deriv.extend(obj_i_acc)
    return state_vec_deriv

# calculates the semimajor axes of a planet
# (follows http://en.wikipedia.org/wiki/Semi-major_axis#Energy.3B_calculation_of_semi-major_axis_from_state_vectors)
def calc_a(sun_gm, planet_gm, sun_pos, sun_vel, planet_pos, planet_vel):
    rel_pos = vec_sub(planet_pos, sun_pos)
    rel_vel = vec_sub(planet_vel, sun_vel)
    specific_orbital_energy = 0.5 * sq_norm(rel_vel) - (sun_gm + planet_gm) / norm(rel_pos)
    return -(sun_gm + planet_gm) / (2.0 * specific_orbital_energy)

# calculates the mean motion of a planet
# (follows http://en.wikipedia.org/wiki/Mean_motion)
def calc_n(sun_gm, planet_gm, sun_pos, sun_vel, planet_pos, planet_vel):
    return math.sqrt((sun_gm + planet_gm) / calc_a(sun_gm, planet_gm, sun_pos, sun_vel, planet_pos, planet_vel) ** 3)

# calculates G * total energy
def calc_energy(state_vec):
    assert len(state_vec) % 7 == 0
    total_energy = 0.0
    for i in range(len(state_vec) // 7):
        total_energy += 0.5 * state_vec[7*i] * sq_norm(state_vec[7*i+4:7*i+7])
        for j in range(i):
            dist = norm(vec_sub(state_vec[7*i+1:7*i+4], state_vec[7*j+1:7*j+4]))
            total_energy -= state_vec[7*i] * state_vec[7*j] / dist
    return total_energy

# calculates G * total momentum
def calc_momentum(state_vec):
    assert len(state_vec) % 7 == 0
    total_momentum = [0.0, 0.0, 0.0]
    for i in range(len(state_vec) // 7):
        total_momentum = vec_add(total_momentum, sc_mult(state_vec[7*i], state_vec[7*i+4:7*i+7]))
    return total_momentum

# changes the Sun state vector to force the barycenter to stay at 0
def force_barycenter(state_vec):
    assert len(state_vec) % 7 == 0 and len(state_vec) > 0
    total_pos_mom = [0.0, 0.0, 0.0]
    total_momentum = [0.0, 0.0, 0.0]
    for i in range(1, len(state_vec) // 7):
        total_pos_mom = vec_add(total_pos_mom, sc_mult(state_vec[7*i], state_vec[7*i+1:7*i+4]))
        total_momentum = vec_add(total_momentum, sc_mult(state_vec[7*i], state_vec[7*i+4:7*i+7]))
    state_vec[1:4] = sc_mult(-1.0 / state_vec[0], total_pos_mom)
    state_vec[4:7] = sc_mult(-1.0 / state_vec[0], total_momentum)

# executes a RK4 step
def rk4_step(state_vec, calc_deriv, dt):
    k1 = calc_deriv(state_vec)
    k2 = calc_deriv(vec_add(state_vec, sc_mult(dt / 2.0, k1)))
    k3 = calc_deriv(vec_add(state_vec, sc_mult(dt / 2.0, k2)))
    k4 = calc_deriv(vec_add(state_vec, sc_mult(dt, k3)))
    k1_p_k4 = vec_add(k1, k4)
    two_k2_p_k3 = sc_mult(2.0, vec_add(k2, k3))
    return vec_add(state_vec, sc_mult(dt / 6.0, vec_add(k1_p_k4, two_k2_p_k3)))

# creates a plot from a time axis and a list of series
def do_plot(output_fpath, times, series, title, x_axis_name, y_axis_name, series_names=None):
    import matplotlib.pyplot as plt

    plt.figure()
    for s in series:
        plt.plot(times, s)
    if series_names is not None:
        plt.legend(series_names, 'lower right')
    plt.title(title)
    
    plt.xlabel(x_axis_name)
    plt.ylabel(y_axis_name)

    plt.savefig(output_fpath)

# simulates the system for a given time lapse, starting from an initial state 
# vector and reducing the time step until the final results stay within a given
# tolerance
def do_sim(initial_state_vec, time_lapse, tolerance, print_progress_info=False):

    # initialization
    force_barycenter(initial_state_vec)
    dt = time_lapse
    prev_final_state_vec = None

    # reduces time step until final state vectors match closely
    while True:
        num_steps = int(time_lapse / dt)
        state_vec = initial_state_vec[:]
        hist_state_vec = [(0, initial_state_vec)]

        for i in range(num_steps):
            new_state_vec = rk4_step(state_vec, calc_state_vec_deriv, dt)
            hist_state_vec.append(((i + 1) * dt, new_state_vec))
            state_vec = new_state_vec

        if print_progress_info:
            print 'Number of steps: %d' % num_steps
            print 'Timestep: %f' % dt
        if prev_final_state_vec is not None:
            error = norm(vec_sub(prev_final_state_vec, state_vec))
            if print_progress_info:
                print 'Error: %f' % error
            if error < tolerance:
                break

        prev_final_state_vec = state_vec
        dt /= 2.0

    # returns the history of state vectors
    return hist_state_vec

if __name__ == '__main__':
    import time

    # initial state vector
    initial_state_vec = [SUN_GM] + SUN_POS + SUN_VEL + [JUPITER_GM] + JUPITER_POS +\
        JUPITER_VEL + [SATURN_GM] + SATURN_POS + SATURN_VEL

    # does the simulation
    start_machine_time = time.time()
    hist_state_vec = do_sim(initial_state_vec, TIME_LAPSE, TOLERANCE, True)

    print 'Elapsed machine time: %f' % (time.time() - start_machine_time)
    print 'Initial energy: %f' % calc_energy(hist_state_vec[0][1])
    print 'Initial momentum: %s' % calc_momentum(hist_state_vec[0][1])
    print 'Final energy: %f' % calc_energy(hist_state_vec[-1][1])
    print 'Final momentum: %s' % calc_momentum(hist_state_vec[-1][1])

    times = [t for t, sv in hist_state_vec]
    hist_energy = [calc_energy(sv) for t, sv in hist_state_vec]
    jupiter_hist_a = [calc_a(SUN_GM, JUPITER_GM,
                             sv[7*0+1:7*0+4], sv[7*0+4:7*0+7],
                             sv[7*1+1:7*1+4], sv[7*1+4:7*1+7]) for t, sv in hist_state_vec]
    saturn_hist_a = [calc_a(SUN_GM, SATURN_GM,
                            sv[7*0+1:7*0+4], sv[7*0+4:7*0+7],
                            sv[7*2+1:7*2+4], sv[7*2+4:7*2+7]) for t, sv in hist_state_vec]
    jupiter_hist_n = [calc_n(SUN_GM, JUPITER_GM,
                             sv[7*0+1:7*0+4], sv[7*0+4:7*0+7],
                             sv[7*1+1:7*1+4], sv[7*1+4:7*1+7]) for t, sv in hist_state_vec]
    saturn_hist_n = [calc_n(SUN_GM, SATURN_GM,
                            sv[7*0+1:7*0+4], sv[7*0+4:7*0+7],
                            sv[7*2+1:7*2+4], sv[7*2+4:7*2+7]) for t, sv in hist_state_vec]

    do_plot('hist_energy.png', times, [hist_energy], 'Energy conservation plot', 'Time (s)', 'G * energy (km^5 / s^4)')
    do_plot('jupiter_hist_a.png', times, [jupiter_hist_a], 'Jupiter osculating semimajor axis', 'Time (s)', 'Semimajor axis (km)')
    do_plot('saturn_hist_a.png', times, [saturn_hist_a], 'Saturn osculating semimajor axis', 'Time (s)', 'Semimajor axis (km)')
    do_plot('jupiter_hist_n.png', times, [jupiter_hist_n], 'Jupiter osculating mean motion', 'Time (s)', 'Mean motion (rad/s)')
    do_plot('saturn_hist_n.png', times, [saturn_hist_n], 'Saturn osculating mean motion', 'Time (s)', 'Mean motion (rad/s)')

    import numpy as np
    saturn_hist_dl = np.cumsum(np.subtract(saturn_hist_n, np.average(saturn_hist_n)) *(times[1] - times[0])) * 180.0 / np.pi * 60.0
    do_plot('saturn_hist_dl.png', times, [saturn_hist_dl], 'Saturn longitude anomaly', 'Time (s)', 'Anomaly (rad)')

    from numpy.fft import rfft
    from numpy import abs as np_abs
    jupiter_n_spectrum = np_abs(rfft(jupiter_hist_n)) / (len(jupiter_hist_n) / 2)
    saturn_n_spectrum = np_abs(rfft(saturn_hist_n)) / (len(saturn_hist_n) / 2)

    do_plot('jupiter_n_spectrum.png', range(1, 20), [jupiter_n_spectrum[1:20]], 'Jupiter mean motion spectrum', 'Component number', 'Amplitude (rad/s)')
    do_plot('saturn_n_spectrum.png', range(1, 20), [saturn_n_spectrum[1:20]], 'Saturn mean motion spectrum', 'Component number', 'Amplitude (rad/s)')
