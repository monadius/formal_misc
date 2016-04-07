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
gg = Goal()

#y, z = BitVecs('y z', 32)
t = Const('t', Opt)
r = Const('r', Opt)
u = Const('u', Opt)

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

#check_refined(add, add_nsw)
#check_refined(add_nsw, add)
#check_refined(add3(add), add3(add_nsw))
check_refined(add3(add_nsw), add3(add))

#def add_refined(f1,f2):
#    s.add(ForAll([t, r, u], 
#                 Implies(f1(t, r, u) != none, f1(t, r, u) == f2(t, r, u))))
    
#add_refined(add3(add_nsw), add3(add))

#print g.as_expr()
#t = Tactic('qe')
#print t(g)
#print t(g).as_expr()

#s.add(g)

#print s.sexpr()
#print s.check()
