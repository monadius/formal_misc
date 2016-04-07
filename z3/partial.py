from z3 import *

s = Solver()
Opt = Datatype('Opt')
Opt.declare('none')
Opt.declare('some', ('value', IntSort()))

Opt = Opt.create()
none = Opt.none
some = Opt.some
value = Opt.value

x = Int('x')

f = Function('f', IntSort(), Opt)
s.add(ForAll([x], f(x) == some (x+1)))

g = Function('g', IntSort(), Opt)
s.add(ForAll([x], Implies (x>=0, g(x) == some (x+1))))
s.add(ForAll([x], Implies (x < 0, g(x) == none)))

s.add(ForAll([x], Implies (g(x) != none, g(x) == f(x))))

print s.check()