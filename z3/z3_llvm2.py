from z3 import *

Opt = Datatype('Opt')
Opt.declare('none')
Opt.declare('some', ('value', BitVecSort(32)))

Opt = Opt.create()
none = Opt.none
some = Opt.some
value = Opt.value

#add = Function('add', Opt, Opt, Opt)
#add_nsw = Function('add_nsw', Opt, Opt, Opt)

s = Solver()

#y, z = BitVecs('y z', 32)
t = Const('t', Opt)
r = Const('r', Opt)

intmax = BitVecVal(2147483647,32);
intmin = BitVecVal(-2147483648,32);

def s_add_overflow(y, z):
    return Or(And(z > 0, y > (intmax - z)),
              And(z < 0, y < (intmin - z)))

def add(y, z):
    return If(Or(t == none, r == none), 
              none, 
              some (value(t) + value(r)))
              
def add_nsw(y, z):
    return If(Or(y == none, z == none), 
              none, 
              If(s_add_overflow(value(y), value(z)), 
                 none, 
                 some (value(y) + value(z))))
 
# print "sat" if f is refined by g
def check_refined(f,g):
    s.push()
    s.add(ForAll([t, r], Implies(f(t, r) != none, f(t, r) == g(t, r))))
    print s.sexpr()
    print s.check()
    s.pop()

check_refined(add, add_nsw)
check_refined(add_nsw, add)
