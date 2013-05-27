from itertools import count
for p in count(1):
    # checks if we are leaving room for 1/q + 1/r
    # 1/p >= 1/2
    if 2 >= p:
        continue # we need smaller values of 1/p
    # checks if we can reach 1/2 with the biggest legal values for 1/q and 1/r
    # 1/p + 1/p + 1/p < 1/2
    if 3 * 2 < p: 
        break
    for q in count(p):
        # checks if we are leaving room for 1/r
        # 1/p + 1/q >= 1/2
        if 2 * (q + p) >= p * q: 
            continue
        # checks if we can reach 1/2 with the biggest legal value for 1/r
        # 1/p + 1/q + 1/q < 1/2
        if 2 * (q + 2 * p) < p * q:
            break
        for r in count(q):
            lhs = 2 * (q * r + p * r + p * q)
            rhs = p * q * r
            # 1/p + 1/q + 1/r > 1/2
            if lhs > rhs:
                continue
            # 1/p + 1/q + 1/r < 1/2
            elif lhs < rhs:
                break
            # 1/p + 1/q + 1/r = 1/2
            else:
                print p, q, r
