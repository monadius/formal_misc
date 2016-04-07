from z3 import *

def opt(n):
    opt = Datatype('Opt%d' % n)
    opt.declare('none')
    opt.declare('some', ('value', BitVecSort(n)))
    return opt.create()

none1 = opt(32).none
none2 = opt(32).none
some3 = opt(32).some(1)
some4 = opt(32).some(1)

print simplify(none1 == none2)
print simplify(some3 == some4)


s = Solver()

intmax = BitVecVal(2147483647,32);
intmin = BitVecVal(-2147483648,32);

def s_add_overflow(y, z):
    return Or(And(z > 0, y > (intmax - z)),
              And(z < 0, y < (intmin - z)))

def add(t, r):
    return If(Or(t == none, r == none), 
              none, 
              some (value(t) + value(r)))
              
def add_nsw(t, r):
    return If(Or(t == none, r == none), 
              none, 
              If(s_add_overflow(value(t), value(r)), 
                 none, 
                 some (value(t) + value(r))))
 
# print "sat" if f is refined by g
def check_refined(f,g):
#    s.push()
#    s.add(ForAll([t, r, u], 
#                 Implies(f(t, r, u) != none, f(t, r, u) == g(t, r, u))))
    s.add(And(f(t, r, u) != none,
              f(t, r, u) != g(t, r, u)))
    print s.sexpr()
    print s.check()
#    s.pop()

def add3(f):
    return (lambda a,b,c: f(f(a, b), c))

