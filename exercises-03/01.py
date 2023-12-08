#!/usr/bin/env python3
from z3 import *

# Declare variables
a, b, c, d = Ints('a b c d')

# Declare optimizer
opt = Optimize()

# Add constraints regarding how many A or B sheets can be cut from each 6x13 sheet
opt.add(a*3 + b*2 + c >= 800)  # for A sheets
opt.add(a + 6*b + 9*c + 13*d >= 400)  # for B sheets

# Add constraints regarding the non-negativity of variables
opt.add(a >= 0, b >= 0, c >= 0, d >= 0)

# Declare objective function (minimize the number of 6x13 sheets needed)
obj = a + b + c + d
opt.minimize(obj)

# Find solution
if opt.check() == sat:
    m = opt.model()
    print("Minimum sheets needed:", m.evaluate(obj))
    print("Cut sheets in the following ways:")
    print("Cut A (3A, 1B) pieces: ", m[a])
    print("Cut B (2A, 6B) pieces: ", m[b])
    print("Cut C (1A, 9B) pieces: ", m[c])
    print("Cut D (0A, 13B) pieces: ", m[d])
else:
    print("No solution found")
