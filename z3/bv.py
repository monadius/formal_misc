from z3 import *

s = Solver()

x = BitVec('x', 32)

intmax = BitVecVal(2147483647,32);
intmin = BitVecVal(-2147483648,32);

#s.add(x <= 2)
s.add(x - x != 0)

print s.sexpr()
print s.check()
print s.model()

