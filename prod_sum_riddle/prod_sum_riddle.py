# "Impossible Puzzle"

# Source of the problem:
# http://en.wikipedia.org/wiki/Impossible_Puzzle

# The problem text follows as comments.

# Given are X and Y, two integers, greater than 1, are not equal, and their sum
# is less than 100. S and P are two mathematicians; S is given the sum X+Y, and
# P is given the product X*Y of these numbers.
all_pairs = [(x, y)
             for y in range(2, 100) for x in range(2, y)
             if x + y < 100]

#  - P says "I cannot find these numbers."
num_pairs_by_prod = {}
for x, y in all_pairs:
    if x * y not in num_pairs_by_prod:
        num_pairs_by_prod[x * y] = 0
    num_pairs_by_prod[x * y] += 1
pairs_1 = [(x, y) for x, y in all_pairs if num_pairs_by_prod[x * y] > 1]

#  - S says "I was sure that you could not find them."
identif_by_prod_pairs_sums = set(x + y for x, y in all_pairs
                                 if num_pairs_by_prod[x * y] == 1)
pairs_2 = [(x, y) for x, y in pairs_1
           if x + y not in identif_by_prod_pairs_sums]

#  - P says "Then, I found these numbers."
num_pairs_by_prod_2 = {}
for x, y in pairs_2:
    if x * y not in num_pairs_by_prod_2:
        num_pairs_by_prod_2[x * y] = 0
    num_pairs_by_prod_2[x * y] += 1
pairs_3 = [(x, y) for x, y in pairs_2 if num_pairs_by_prod_2[x * y] == 1]

#  - S says "If you could find them, then I also found them."
num_pairs_by_sum_3 = {}
for x, y in pairs_3:
    if x + y not in num_pairs_by_sum_3:
        num_pairs_by_sum_3[x + y] = 0
    num_pairs_by_sum_3[x + y] += 1
pairs_4 = [(x, y) for x, y in pairs_3 if num_pairs_by_sum_3[x + y] == 1]

# What are the numbers?
print pairs_4
