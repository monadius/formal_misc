from z3 import *

Opt = Datatype('Opt')
Opt.declare('none')
Opt.declare('some', ('value', IntSort()))

Opt = Opt.create()
none = Opt.none
some = Opt.some
value = Opt.value

s = Solver()

y, z = Consts('y z', IntSort())
t = Const('t', Opt)
r = Const('r', Opt)

#s.set(auto_config = False, mbqi = False, mbqi_trace = True)
#s.set(mbqi_max_iterations = 1)

#s.add(ForAll([t], Or(Exists([y], t == some(y)), t == none)))
s.add(ForAll([t], Or(Exists([y], t == some(y)), t == none), 
             patterns = [MultiPattern(value(t), none, some(z))]))


print s.sexpr()
print s.check()


