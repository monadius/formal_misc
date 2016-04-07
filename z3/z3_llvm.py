from z3 import *

Opt = Datatype('Opt')
Opt.declare('none')
Opt.declare('some', ('value', BitVecSort(32)))

Opt = Opt.create()
none = Opt.none
some = Opt.some
value = Opt.value

add = Function('add', Opt, Opt, Opt)
add_nsw = Function('add_nsw', Opt, Opt, Opt)

#s = Solver()
s = Goal()

y, z = BitVecs('y z', 32)
t = Const('t', Opt)
r = Const('r', Opt)

intmax = BitVecVal(2147483647,32);
intmin = BitVecVal(-2147483648,32);
s_add_overflow = Function('s_add_overflow', BitVecSort(32), BitVecSort(32), BoolSort())

s.add(ForAll([y, z], s_add_overflow(y, z) ==
             Or(And(z > 0, y > (intmax - z)),
                And(z < 0, y < (intmin - z)))))

s.add(ForAll([y, z], add(some(y), some(z)) == some(y + z)))
s.add(ForAll([t], add(t, none) == none))
s.add(ForAll([t], add(none, t) == none))
s.add(add(none, none) == none)

#s.add(ForAll([t, r], add(t, r) == If(Or(t == none, r == none), none, some (value(t) + value(r)))))


s.add(ForAll([y, z], Implies(Not(s_add_overflow(y, z)), add_nsw(some(y), some(z)) == some(y + z))))
s.add(ForAll([y, z], Implies(    s_add_overflow(y, z),  add_nsw(some(y), some(z)) == none)))
s.add(ForAll([t], add_nsw(t, none) == none))
s.add(ForAll([t], add_nsw(none, t) == none))
s.add(add_nsw(none, none) == none)

#s.add(ForAll([t, r], add_nsw(t, r) == If(Or(t == none, r == none), none, If(s_add_overflow(value(t), value(r)), none, some (value(t) + value(r))))))

#s.add(ForAll([t], Or(Exists([y], t == some(y)), t == none)))

# print "sat" if f is refined by g
def check_refined(f,g):
#    s.add(ForAll([y, z], Implies(f(some(y),some(z)) != none, f(some(y),some(z)) == g(some(y),some(z)))))
    s.add(ForAll([t, r], Implies(f(t, r) != none, f(t, r) == g(t, r))))
#    print s.check()

check_refined(add_nsw, add)
#check_refined(add, add_nsw)

#print s.sexpr()
#print s.check()
print s.as_expr()
tac = Tactic('qe')
print tac(s)


#a, b = BitVecs('a b', 32)
#orig = add_nsw (add_nsw (some(a), some(a)), some(a))
#opt  = 3 * a
#check_refined (orig, opt)

