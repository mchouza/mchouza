"""Generates the testcase files.

Generates two files: an input file ('input.txt'), each of whose lines is a list
of points that can or not be the projection of a parallelepiped, and a key file
('key.txt'), containing "YES" if the associated line in teh input file is the
prokjection of a parallelepiped and "NO" in the other case."""

NUM_TESTS = 10000

import math
import random

def get_random_unit_vector():
    while True:
        rf = lambda: 2.0 * random.random() - 1.0
        x, y, z = rf(), rf(), rf()
        norm = math.sqrt(x * x + y * y + z * z)
        if norm <= 1.0:
            return x / norm, y / norm, z / norm

def get_random_vec_with_norm(norm):
    ux, uy, uz = get_random_unit_vector()
    return ux * norm, uy * norm, uz * norm

def vec_add(v1, v2):
    return [v1c + v2c for v1c, v2c in zip(v1, v2)]

def get_3d_pp_vertices():
    vrf = lambda: get_random_vec_with_norm(random.random() * 2.0 + 0.5)
    p0, v1, v2, v3 = vrf(), vrf(), vrf(), vrf()
    p1 = vec_add(p0, v1)
    p2 = vec_add(p0, v2)
    p3 = vec_add(p0, v3)
    p12 = vec_add(p1, v2)
    p13 = vec_add(p1, v3)
    p23 = vec_add(p2, v3)
    p123 = vec_add(p12, v3)
    points = [p0, p1, p2, p3, p12, p13, p23, p123]
    random.shuffle(points)
    return points

def proj_2d(points):
    return [p[:2] for p in points]

def get_pp_vertices():
    return proj_2d(get_3d_pp_vertices())

def get_random_points():
    num_points = 8 if random.random() < 0.95 else random.randint(1, 16)
    return [[random.random() * 6.0 - 3.0 for j in range(2)]
            for i in range(num_points)]

def get_one_vertex_dist_pp():
    points = get_pp_vertices()
    shift = get_random_vec_with_norm(random.random() * 0.05 + 0.01)
    index = random.randint(0, len(points) - 1)
    points[index] = vec_add(points[index], shift)
    return points

NOT_PP_GENS = (
    (get_random_points, 'Just random points.'),
    (get_one_vertex_dist_pp, 'A single vertex shifted.'),
)

def get_not_pp_vertices():
    not_pp_gen, desc = random.choice(NOT_PP_GENS)
    return not_pp_gen(), desc

def add_points_line(tc_fp, points):
    tc_fp.write('%s\n' % ' '.join('%f' % c for p in points for c in p))

def add_key_line(key_fp, is_valid_pp, failure_desc):
    key_fp.write('YES\n' if is_valid_pp else 'NO # %s\n' % failure_desc)

def add_test(tc_fp, key_fp):
    is_valid_pp = random.choice((False, True))
    failure_desc = None
    if is_valid_pp:
        points = get_pp_vertices()
    else:
        points, failure_desc = get_not_pp_vertices()
    add_points_line(tc_fp, points)
    add_key_line(key_fp, is_valid_pp, failure_desc)

def main():
    tc_fp = open('input.txt', 'w')
    key_fp = open('key.txt', 'w')
    random.seed(0)
    for i in xrange(NUM_TESTS):
        add_test(tc_fp, key_fp)
    tc_fp.close()
    key_fp.close()

if __name__ == '__main__':
    main()
