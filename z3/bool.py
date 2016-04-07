from z3 import *

boolean = Datatype('boolean')
boolean.declare('b_true')
boolean.declare('b_false')

boolean = boolean.create()
b_true = boolean.b_true
b_false = boolean.b_false

b_and = Function('b_and', boolean, boolean, boolean)

s = Solver()
a = Const('a', boolean)
x, y = Consts('x y', boolean)

s.add(ForAll([a], b_and(b_false, a) == b_false))
s.add(ForAll([a], b_and(b_true, a) == a))

s.add(ForAll([x, y], b_and(x, y) == b_and(y, x)))

print s.sexpr()
print s.check()

