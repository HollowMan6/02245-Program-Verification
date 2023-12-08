from z3 import *
xal, xam, xar, xbl, xbm, xbr, xcl, xcm, xcr = Bools('xal xam xar xbl xbm xbr xcl xcm xcr')
s = Solver()

# Alice does not sit next to Charlie
s.add( And( Implies( Or(xal, xar), Not(xcm) ), Implies( xam, And( Not(xcl), Not(xcr)))))

# Alice does not sit on the leftmost chair
s.add( Not(xal) )

# Bob does not sit to the right of Charlie
s.add( And( Implies(xcl, Not(xbm)), Implies(xcm, Not(xbr))))

# Each person gets a chair
s.add( Or( xal, xam, xar) )
s.add( Or( xbl, xbm, xbr) )
s.add( Or( xcl, xcm, xcr) )

# Every person gets at most one chair

s.add( Or( Not(xal), Not(xam) ) )
s.add( Or( Not(xal), Not(xar) ) )
s.add( Or( Not(xam), Not(xar) ) )    

s.add( Or( Not(xbl), Not(xbm) ) )
s.add( Or( Not(xbl), Not(xbr) ) )
s.add( Or( Not(xbm), Not(xbr) ) )    

s.add( Or( Not(xcl), Not(xcm) ) )
s.add( Or( Not(xcl), Not(xcr) ) )
s.add( Or( Not(xcm), Not(xcr) ) )    


# Every chair gets at most one person

s.add( Or( Not(xal), Not(xbl) ) )
s.add( Or( Not(xal), Not(xcl) ) )
s.add( Or( Not(xbl), Not(xcl) ) )

s.add( Or( Not(xam), Not(xbm) ) )
s.add( Or( Not(xam), Not(xcm) ) )
s.add( Or( Not(xbm), Not(xcm) ) )

s.add( Or( Not(xar), Not(xbr) ) )
s.add( Or( Not(xar), Not(xcr) ) )
s.add( Or( Not(xbr), Not(xcr) ) )


print( s.check() )
