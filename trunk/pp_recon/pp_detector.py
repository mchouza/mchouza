"""Detects parallelepipeds in the testcase input file.

Reads the testcase input file ('input.txt'), taking each line as a list of
point coordinates to be checked. If the points in the line can be seen as the
projection of a parallelepiped, writes an "YES" line to the output file
('output.txt'). Else, write a "NO" line to the same file."""

TOL = 1e-4

import math

def index_ext(seq, f, exc_ind):
    """Gets the indices of the elements of the sequence 'seq' with the minimum
    and maximum value of 'f', skipping indices in 'exc_ind'. Returns (-1, -1)
    if all the indices are excluded."""

    # gets the first non-excluded element
    start_i = None
    for i in xrange(len(seq)):
        if i not in exc_ind:
            start_i = i
            break
    if start_i is None:
        return -1, -1

    # searches for the extreme values of 'f'
    min_i = max_i = start_i
    min_val = max_val = f(seq[start_i])
    for i in xrange(start_i + 1, len(seq)):
        if i in exc_ind:
            continue
        val = f(seq[i])
        if val < min_val:
            min_val = val
            min_i = i
        if val > max_val:
            max_val = val
            max_i = i

    # returns the indices
    return min_i, max_i

def find_nearest(points, point, exc_ind, tol):
    """Returns the index of the point in 'points' that is nearest to 'point',
    excluding the points with indices in 'exc_ind' or whose distances to 'point'
    are bigger that 'tol'. If no point can be found, returns -1."""

    def dist(p1, p2):
        """Returns the distance between two points."""

        return math.sqrt(sum((p1c - p2c) ** 2 for p1c, p2c in zip(p1, p2)))

    def dist_to_point(p):
        """Returns the distance from 'p' to 'point'."""

        return dist(p, point)

    cand_i, dummy = index_ext(points, dist_to_point, exc_ind)
    if cand_i < 0:
        return -1
    if dist(points[cand_i], point) > tol:
        return -1
    return cand_i

class NotPPException(Exception):
    pass

def step0(points):
    """Checks number of vertices."""

    if len(points) != 8:
        raise NotPPException()

def step1(points):
    """Returns the index of the leftmost-topmost (in this order) point, p0."""

    p0_i, dummy = index_ext(points, lambda p: p, ())
    if p0_i < 0:
        assert 0
    return p0_i

def step2(points, p0_i):
    """Returns the indices of the points with extreme angles with respect to a
    semi-axis starting at p0 with direction +X, p1 and p2."""

    def angle(p):
        """Returns the angle of p with respect to a semi-axis starting at p0
        with direction +X."""

        p0 = points[p0_i]
        return math.atan2(p[1] - p0[1], p[0] - p0[0])

    p1_i, p2_i = index_ext(points, angle, (p0_i,))
    if p1_i < 0 or p2_i < 0:
        assert 0
    return p1_i, p2_i

def step3(points, p0_i, p1_i, p2_i):
    """Returns the index of p12, the point that forms a parallelogram with p0,
    p1 and p2."""

    p0, p1, p2 = [points[i] for i in (p0_i, p1_i, p2_i)]
    exp_p12 = (p1[0] + p2[0] - p0[0], p1[1] + p2[1] - p0[1])
    p12_i = find_nearest(points, exp_p12, (p0_i, p1_i, p2_i), TOL)
    if p12_i < 0:
        raise NotPPException()
    return p12_i

def step4(points, p0_i, p1_i, p2_i, p12_i):
    """Returns the index of p3, the remaining point that is directly connected
    to p0."""

    p3_i, dummy = index_ext(points, lambda p: p, (p0_i, p1_i, p2_i, p12_i))
    if p3_i < 0:
        assert 0
    return p3_i

def step5(points, p0_i, p1_i, p2_i, p12_i, p3_i):
    """Returns the indices of the remaining points: p13, p23 and p123."""

    p0, p1, p2, p12, p3 = [points[i] for i in (p0_i, p1_i, p2_i, p12_i, p3_i)]
    exp_p13 = (p1[0] + p3[0] - p0[0], p1[1] + p3[1] - p0[1])
    exp_p23 = (p2[0] + p3[0] - p0[0], p2[1] + p3[1] - p0[1])
    exp_p123 = (p1[0] + p2[0] + p3[0] - 2 * p0[0],
                p1[1] + p2[1] + p3[1] - 2 * p0[1])
    p13_i = find_nearest(points, exp_p13, (p0_i, p1_i, p2_i, p12_i, p3_i), TOL)
    p23_i = find_nearest(points, exp_p23,
                         (p0_i, p1_i, p2_i, p12_i, p3_i, p13_i), TOL)
    p123_i = find_nearest(points, exp_p123,
                          (p0_i, p1_i, p2_i, p12_i, p3_i, p13_i, p23_i), TOL)
    if p13_i < 0 or p23_i < 0 or p123_i < 0:
        raise NotPPException()
    return p13_i, p23_i, p123_i

def is_pp(points):
    """Checks if the points can be the parallel projection of a
    parallelepiped. Returns 'True' if they can."""

    try:
        step0(points)
        p0_i = step1(points)
        p1_i, p2_i = step2(points, p0_i)
        p12_i = step3(points, p0_i, p1_i, p2_i)
        p3_i = step4(points, p0_i, p1_i, p2_i, p12_i)
        p13_i, p23_i, p123_i = step5(points, p0_i, p1_i, p2_i, p12_i, p3_i)
        return True
    except NotPPException:
        return False

def read_points_from_line(line):
    """Given a line, reads a series of 2D points."""

    comps = [float(sc) for sc in line.split()]
    assert len(comps) % 2 == 0
    return [(comps[i], comps[i+1]) for i in range(0, len(comps), 2)]

def main():
    input_fp = open('input.txt')
    output_fp = open('output.txt', 'w')
    for l in input_fp:
        points = read_points_from_line(l)
        output_fp.write('YES\n' if is_pp(points) else 'NO\n')
    input_fp.close()
    output_fp.close()

if __name__ == '__main__':
    main()
