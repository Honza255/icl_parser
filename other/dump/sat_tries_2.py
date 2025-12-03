import pysat
from pysat.formula import *
from pysat.solvers import Minisat22
from pysat.solvers import Solver

A = Atom(1)
B = Atom(2)
C = Atom(3)
D = Atom(4)
R = Atom(5)

#my_formula = (~R) & ((~R)>>(A==C)) & ((~R)>>(B==D))
my_formula = (~R) & ((~R)>>(A)) & ((~R)>>(B))
my_formula = (~R) & ((~R)>>A)

with Solver(bootstrap_with=my_formula) as solver:
    print(solver.solve())
    print(solver.get_model()) 
    
true = Atom("ttt")

X1_0 = Atom("X1_0")
X2_0 = Atom("X2_0")
X3_0 = Atom("X3_0")
X4_0 = Atom("X4_0")

X1_0_sel = true
X2_0_sel = true
X3_0_sel = X2_0
X4_0_sel = ~X2_0

X1_1 = Atom("X1_1")
X2_1 = Atom("X2_1")
X3_1 = Atom("X3_1")
X4_1 = Atom("X4_1")

X1_1_sel = true
X2_1_sel = true
X3_1_sel = X2_1
X4_1_sel = ~X2_1

X1_2 = Atom("X1_2")
X2_2 = Atom("X2_2")
X3_2 = Atom("X3_2")
X4_2 = Atom("X4_2")

X1_2_sel = true
X2_2_sel = true
X3_2_sel = X2_2
X4_2_sel = ~X2_2

init = true & X1_0 & X2_0 & X3_0 & ~X4_0
end = X4_2
t_0 = ((~X1_0_sel) >> Equals(X1_0, X1_1)) & ((~X2_0_sel) >>  Equals(X2_0, X2_1)) & ((~X3_0_sel) >>  Equals(X3_0, X3_1)) & ((~X4_0_sel) >>  Equals(X4_0, X4_1)) 
t_1 = ((~X1_1_sel) >> Equals(X1_1, X1_2)) & ((~X2_1_sel) >>  Equals(X2_1, X2_2)) & ((~X3_1_sel) >>  Equals(X3_1, X3_2)) & ((~X4_1_sel) >>  Equals(X4_1, X4_2)) 

cnf = init & t_0 & X4_1
cnf =  ((~(X1_0_sel)) | (~X1_0 & X1_1 | X1_0 & ~X1_1)) & ((~X2_0_sel) | (~X2_0 & X2_1 | X2_0 & ~X2_1)) & (true)



print(id(cnf))
print(cnf)
cnf.clausify()
print(cnf)
#cnf = cnf.simplified()
#print(cnf)
#cnf.clausify()
print(cnf.clauses)
print("x")
for x in cnf:
    print(x)
print("x")

with Solver(bootstrap_with=cnf) as solver:
    #for x in cnf.clauses:
    #    solver.add_clause(x)
    clausess = [i for x in cnf.clauses for i in x]
    print(clausess)
    print(Formula.export_vpool().id2obj)
    for i,x in Formula.export_vpool().id2obj.items():
        print(i,x, x.clauses)
        if(i in clausess):
            for z in  x.clauses:
                pass
                #solver.add_clause(z)
    print(solver.solve())
    print(solver.get_model())   
    i = 0 
    for model in solver.enum_models():
        # using method formulas to map the model back to atoms
        print(model)
        print(Formula.formulas(model, atoms_only=True))
        #print(solver.accum_stats())
        if(i > 10): 
            break
        i += 1

print()
print()
print()
print()
print()

cnf = (X1_0 | X1_0_sel | ~X1_1) & (X1_1 | X1_0_sel | ~X1_0) & (X2_0 | X2_0_sel | ~X2_1) & (X2_1 | X1_0_sel | ~X1_0) & ~X1_0_sel
x = [[1,5,-2],[2,5,-1],[3,5,-4],[4,5,-3],[-5]]
print(x)
cnf = CNF(from_clauses=x)
print(cnf)

#cnf = CNF(from_clauses=[[1,2], [3]])
cnf.clausify()
print(cnf.clauses)
with Solver(bootstrap_with=cnf.clauses) as solver:

    print(solver.solve())
    print(solver.get_model())  
    print(Formula.formulas(solver.get_model(), atoms_only=True))  
    for model in solver.enum_models():
    #    # using method formulas to map the model back to atoms
        print(model)
        #print(Formula.formulas(model, atoms_only=True))
    #    #print(solver.accum_stats())

from sympy.logic.boolalg import to_cnf, to_nnf, Equivalent
from sympy.abc import A, B, D, X, Q, W, E
print(to_cnf(~(A | B) | D))

print(to_cnf(to_nnf((X) >> (A))))
print(to_cnf(to_nnf((~X) >> (A))))
print(to_cnf(to_nnf(Equivalent(A, B))))

print(to_cnf(to_nnf((~X) >> Equivalent(A, B))))
print(to_cnf(to_nnf((~(Q&W&E)) >> Equivalent(A, B))))



