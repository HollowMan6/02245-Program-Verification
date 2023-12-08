# applying SMT solvers to https://xkcd.com/287
# can we get all solutions? Yes, we can also iterate over all solutions (here using the python API)
from z3 import *

X = IntVector('x', 6)

s = Solver()

s.add( 
  1505 == 215 * X[0] + 275 * X[1] + 335 * X[2] + 420 * X[3] + 580 * X[4] + 355 * X[5]
)

for i in range(6):
    s.add(X[i] >= 0)


while s.check() == sat:
    model = s.model()
    print( model )
    s.add(Or(
        [X[i] != model[X[i]] for i in range(6)]
    ))


