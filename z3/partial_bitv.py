from z3 import *

Opt = Datatype('Opt')
Opt.declare('none')
Opt.declare('some', ('value', BitVecSort(32)))

Opt = Opt.create()
none = Opt.none
some = Opt.some


add = Function('add', BitVecSort(32), BitVecSort(32), Opt)
add_nsw = Function('add_nsw', BitVecSort(32), BitVecSort(32), Opt)

s = Solver()

y, z = BitVecs('y z', 32)
intmax = BitVecVal(2147483647,32);
intmin = BitVecVal(-2147483648,32);
s_add_overflow = Function('s_add_overflow', BitVecSort(32), BitVecSort(32), BoolSort())
s.add(ForAll([y, z], s_add_overflow(y, z) ==
             Or (And (z > 0, y > (intmax - z)),
                 And (z < 0, y < (intmin - z)))))

s.add(ForAll([y, z], add(y, z) == some (y + z)))
s.add(ForAll([y, z], Implies (Not (s_add_overflow (y, z)), add_nsw(y, z) == some (y + z))))

s.add(ForAll([y, z], Implies (s_add_overflow (y, z), add_nsw(y, z) == none)))

# now we want to prove that add() refines add_nsw() 
s.add(ForAll([y, z], Implies (add_nsw(y, z) != none, add_nsw(y, z) == add(y, z))))

print s.check()
