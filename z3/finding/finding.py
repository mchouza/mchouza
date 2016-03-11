from z3 import *

# Solver object.
s = Solver()

# Defines the input variable 'b' and the delimiter byte variable 'd'.
b = BitVec('b', 64)
d = BitVec('d', 64)
s.add(d > 0x00, d <= 0xff)

# Defines some constants.
mask_0x01 = UDiv(~BitVecVal(0, 64), 0xff)
mask_0x7f = mask_0x01 * 0x7f
mask_0x80 = mask_0x01 * 0x80

# Defines the delimiter mask.
mask_d = mask_0x01 * d

# Defines the 'matches_as_0x00' variable.
matches_as_0x00 = b ^ mask_d

# Defines the 'matches_as_0x80' variable.
matches_as_0x80 = (mask_0x80 - (matches_as_0x00 & mask_0x7f)) &\
                  ~matches_as_0x00 & mask_0x80

# Defines an auxiliary byte position variable and the associated extracted
# bytes.
def get_byte(bv, n):
	return (bv >> (n * 8)) & 0xff
n = BitVec('n', 64)
s.add(0 <= n, n < 8)
matches_as_0x80_n = get_byte(matches_as_0x80, n)
b_n = get_byte(b, n)

# Tries to find a case where the byte of 'b' is different from 'd' and the
# match byte is 0x80
s.push()
s.add(b_n != d, matches_as_0x80_n == 0x80)
assert s.check() == unsat, s.model()
s.pop()

# Tries to find a case where the byte of 'b' is 'd' and the match byte is
# different from 0x80
s.push()
s.add(b_n == d, matches_as_0x80_n != 0x80)
assert s.check() == unsat, s.model()
s.pop()
