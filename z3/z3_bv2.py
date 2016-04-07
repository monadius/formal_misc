from z3 import *

def declare(n, x):
    return Const(x, BitVecSort(n + 1))

def is_none(x):
    return Extract(x.size() - 1, x.size() - 1, x) == 1

def some(x):
    return Concat(BitVecVal(0, 1), x)

def value(x):
    return Extract(x.size() - 2, 0, x)

def extend(x):
    return SignExt(x.size(), x)
    
def none(x):
    return BitVecVal(1 << (x.size() - 1), x.size())
    
s = Solver()

t = declare(32, 't')
r = declare(32, 'r')
u = declare(32, 'u')

intmax = BitVecVal(2147483647,32)
intmin = BitVecVal(-2147483648,32)

intmax_ext = extend(intmax)
intmin_ext = extend(intmin)

def s_add_overflow(y, z):
#    return Or(And(z > 0, y > (intmax - z)),
#              And(z < 0, y < (intmin - z)))
    return Or(extend(y) + extend(z) > intmax_ext,
              extend(y) + extend(z) < intmin_ext)
              
def s_mul_overflow(y, z):
#    return Or(And(z > 0, y > (intmax - z)),
#              And(z < 0, y < (intmin - z)))
    return Or(extend(y) * extend(z) > intmax_ext,
              extend(y) * extend(z) < intmin_ext)
    
 
def add(t, r):
    return If(Or(is_none(t), is_none(r)), 
              none(t), 
              some (value(t) + value(r)))
              
def mul(t, r):
    return If(Or(is_none(t), is_none(r)),
              none(t),
              some (value(t) * value(r)))
              
def add_nsw(t, r):
    return If(Or(is_none(t), is_none(r)), 
              none(t), 
              If(s_add_overflow(value(t), value(r)), 
                 none(t), 
                 some (value(t) + value(r))))
                 
def mul_nsw(t, r):
    return If(Or(is_none(t), is_none(r)), 
              none(t), 
              If(s_mul_overflow(value(t), value(r)), 
                 none(t), 
                 some (value(t) * value(r))))
                 
three = some(BitVecVal(3, 32))

def org(a, b):
    return add_nsw(a, add_nsw(a, a))
    
def opt(a, b):
    return mul(a, three)
                 
def add3(f):
    return (lambda a,b,c: f(f(a, b), c))

def refined3(f, g):
    s.push()
    s.add(ForAll([t, r, u],
                 Implies(Not(is_none(f(t,r,u))), f(t,r,u) == g(t,r,u))))
    print s.check()
    s.pop()

def refined3_ex(f, g):
    s.push()
    s.add(Not(is_none(f(t,r,u))))
    s.add(f(t,r,u) != g(t,r,u))
    if (s.check() == sat):
        print "sat"
        print s.model()
    else:
        print "unsat"
    s.pop()


def refined2(f, g):
    s.push()
    s.add(Not(is_none(f(t,r))))
    s.add(f(t,r) != g(t,r))
#    s.add(ForAll([t, r],
#                 Implies(Not(is_none(f(t,r))), f(t,r) == g(t,r))))
    if s.check() == sat:
        print "sat"
        print s.model()
    else:
        print "unsat"
    s.pop()



#refined2(add, add_nsw)
#refined2(add_nsw, add)
refined2(org, opt)
refined2(opt, org)

#refined3(add3(add), add3(add_nsw))
#refined3(add3(add_nsw), add3(add))

#refined3_ex(add3(add), add3(add_nsw))
#refined3_ex(add3(add_nsw), add3(add))

#refined3_ex(lambda a,b,c: add_nsw(add_nsw(a, b), c),
#            lambda a,b,c: add_nsw(a, add_nsw(b, c)))
