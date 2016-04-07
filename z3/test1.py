from z3 import *

def find_upper_bound(f, constraints, u):
    s = Solver()
    while (1):
#        print u
        s.reset()
        s.add(constraints)
        s.add(f > u)
        r = s.check()
#        print r
        if r == sat:
            if u < 10:
                u = 10
            else:
                u = 2 * u
        else:
            return u

  
def maximize(f, constraints, lb, ub, tol):
    s = Solver()
#    s.add(constraints)
    while (ub - lb > tol):
        m = (ub + lb) / 2.0
#        print m, lb, ub
        s.reset()
        s.add(constraints)
        s.add(f > m)
#        s.push()
#        s.add(f > m)
        r = s.check()
#        print r
#        s.pop()
        if r == sat:
            lb = m
        else:
            ub = m
    return lb, ub
    

def find_bounds(f, constraints, tol):
    ub = find_upper_bound(f, constraints, 0)
    lb = -find_upper_bound(-f, constraints, 0)
    u1, u2 = maximize(f, constraints, lb, ub, tol)
    l1, l2 = maximize(-f, constraints, -ub, -lb, tol)
    return -l2, u2

#x = Real('x')
#f = x * (1 - ((x * x) * ((1 / 6) - ((x * x) / 120))))
    
#l, u = maximize(f, [x >= 0, x <= 1], 0, 10, 0.0001)
#print l, u


#x1, x2, x3, x4, x5, x6 = Reals('x1 x2 x3 x4 x5 x6')
#l = 4
#u = 2.52 * 2.52
#cs = [x1 >= l, x1 <= u, x2 >= l, x2 <= u, x3 >= l, x3 <= u, x4 >= l, x4 <= u, x5 >= l, x5 <= u, x6 >= l, x6 <= u]

#delta4 = -x2 * x3 -x1 * x4 + x2 * x5 + x3 * x6 -x5 * x6 + x1 * (-x1 + x2 + x3 - x4 + x5 + x6)
#delta = x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6) + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) + (-x2) * x3 * x4 + (-x1) * x3 * x5 + (-x1) * x2 * x6 + (-x4) * x5 * x6
#l, u = maximize(-delta, cs, 0, 100, 1)

#[x2, x1] = Reals('x2 x1')
#constraints = [x2 > -20.000000, x1 > -5.000000, x2 < 5.000000, x1 < 5.000000]
#f = (x1 + (((((((((2.000000 * x1) * (((((3.000000 * x1) * x1) + (2.000000 * x2)) - x1) * (1.000000 / ((x1 * x1) + 1.000000)))) * ((((((3.000000 * x1) * x1) + (2.000000 * x2)) - x1) * (1.000000 / ((x1 * x1) + 1.000000))) - 3.000000)) + ((x1 * x1) * ((4.000000 * (((((3.000000 * x1) * x1) + (2.000000 * x2)) - x1) * (1.000000 / ((x1 * x1) + 1.000000)))) - 6.000000))) * ((x1 * x1) + 1.000000)) + (((3.000000 * x1) * x1) * (((((3.000000 * x1) * x1) + (2.000000 * x2)) - x1) * (1.000000 / ((x1 * x1) + 1.000000))))) + ((x1 * x1) * x1)) + x1) + (3.000000 * (((((3.000000 * x1) * x1) + (2.000000 * x2)) - x1) * (1.000000 / ((x1 * x1) + 1.000000))))))
#print f
#print find_bounds(f, constraints, 0.001)
#l, u = maximize(f, constraints, 0, 10000, 0.0001)