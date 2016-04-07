from z3 import *

#add = Function('add', Opt, Opt, Opt)
#add_nsw = Function('add_nsw', Opt, Opt, Opt)

def declare(x):
    return Const(x, BitVecSort(33))

def is_none(x):
    return Extract(32, 32, x) == 1

def some(x):
    return Concat(BitVecVal(0, 1), x)

def value(x):
    return Extract(31, 0, x)
    
none = BitVecVal(1 << 32, 33)

s = Solver()

y, z = BitVecs('y z', 32)
t = declare('t')
r = declare('r')
u = declare('u')

intmax = BitVecVal(2147483647,32);
intmin = BitVecVal(-2147483648,32);

add = Function('add', BitVecSort(33), BitVecSort(33), BitVecSort(33))
add_nsw = Function('add', BitVecSort(33), BitVecSort(33), BitVecSort(33))
s_add_overflow = Function('s_add_overflow', BitVecSort(32), BitVecSort(32), BoolSort())

s.add(ForAll([y, z], s_add_overflow(y, z) ==
             Or(And(z > 0, y > (intmax - z)),
                And(z < 0, y < (intmin - z)))))
                
#s.add(ForAll([y, z], add(some(y), some(z)) == some(y + z)))
#s.add(ForAll([t, r], Implies(Or(is_none(t), is_none(r)),
#             add(t, r) == none)))
#s.add(ForAll([t, r], add(t, r) ==
#             If(Or(is_none(t), is_none(r)),
#                none,
#                some (value(t) + value(r)))))
s.add(ForAll([t, r], Implies(Or(is_none(t), is_none(r)),
             add(t, r) == none)))
s.add(ForAll([t, r], Implies(Not(Or(is_none(t), is_none(r))),
             add(t, r) == t)))

print s.check()
print s.model()

#s.add(ForAll([y, z], Implies(Not(s_add_overflow(y, z)), 
#             add_nsw(some(y), some(z)) == some(y + z))))

#s.add(ForAll([y, z], Implies(    s_add_overflow(y, z),  
#             add_nsw(some(y), some(z)) == none)))
#s.add(ForAll([t, r], Implies(Or(is_none(t), is_none(r)),
#             add_nsw(t, r) == none)))


def refined2(f, g):
    s.push()
    s.add(Not(is_none(f(t,r))))
    s.add(f(t,r) != g(t,r))
#    s.add(ForAll([t, r],
#                 Implies(Not(is_none(f(t,r))), f(t,r) == g(t,r))))
    print s.check()
    s.pop()

#refined2(add, add_nsw)
