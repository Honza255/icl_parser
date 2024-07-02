import pysat
from pysat.formula import *
from pysat.solvers import Minisat22
from pysat.solvers import Solver
from itertools import islice
import copy

status = {
    "true": 1,
    "false": -1
}
# REG NAME: reg id, sel vector, reset value, control bit
registers_start = [{
    "REG_0#0": (2,  1, -2, 0),
    "REG_1#0": (3,  1, -3, 1),
    "REG_2#0": (4,  3, -4, 0), 
    "REG_3#0": (5, -3, -5, 0),
    "REG_5#0": (6,  1,  6, 0),
    "REG_6#0": (7,  1,  7, 0),
    "REG_7#0": (8,  1,  8, 0)    
}]
last_key = list(registers_start[0])[-1]
registers_end_state = [-2,-3, 4, -5,6,7,8]


for current_step in range(12):
    print("CURRNET STEP", current_step)
    
    if(current_step > 3):
        break
        raise RuntimeError("Failed to find JTAG vector")

    registers = copy.deepcopy(registers_start)
    last_idx = registers_start[0][last_key][0]
    number_of_regs = len(registers[0].keys())
    
    cnf_init = []
    for reg_name, reg_tuple in registers[0].items():
        cnf_init.append([reg_tuple[2]])
    cnf_init.append([1])
   
    cnf_transion = []
    steps = list(range(0,current_step+1))
    for step in steps:
        print("STEP", step)
        new_registers = {}
        for reg_name, reg_tuple in registers[step].items():
            reg_idx = reg_tuple[0]
            sel_bit = reg_tuple[1]
            init_bit = reg_tuple[2]      
            control_bit = reg_tuple[3]

            last_idx = last_idx + 1
            new_idx = last_idx
            new_name = "{}#{}".format(reg_name.split("#")[0], step+1)
            new_sel = 1 if abs(sel_bit)==1 else abs(sel_bit)+number_of_regs
            new_sel = -new_sel if sel_bit < 0 else new_sel
            new_registers[new_name] = (new_idx, new_sel, 0, control_bit)       
            if((not control_bit) & (step != steps[-1])):
                cnf_transion.append([reg_idx, -last_idx])
                cnf_transion.append([-reg_idx, last_idx])

            #~X >> Equivalent(A, B)
            cnf_transion.append([sel_bit, -(reg_idx),  (last_idx)])
            cnf_transion.append([sel_bit,  (reg_idx), -(last_idx)])
        registers.append(new_registers)

    cnf_end = []
    for end_state in registers_end_state:
        new_end = abs(end_state) + number_of_regs*(current_step+1)
        new_end = -new_end if end_state < 0 else new_end        
        cnf_end.append([new_end])

    print(status)
    for register_set in registers:
        print(register_set)
    print()
    print("INIT", cnf_init)
    print("TRANS", cnf_transion)
    print("END", cnf_end)
    print(cnf_init + cnf_transion + cnf_end)
    print()
        
    cnf = cnf_init + cnf_transion + cnf_end
    solved = 0
    with Solver(bootstrap_with=cnf) as solver:
        solved = solver.solve()
        print(solved)
        print(solver.get_model()) 
        
        for model in list(islice(solver.enum_models(), 10)):
            print(model)

    if(solved):
        break


from sympy import sympify, to_cnf, symbols
        
# Boolean expression in string format
boolean_expr_str = "(Equivalent(A, B))"

# Convert the string expression to a SymPy expression
boolean_expr = sympify(boolean_expr_str)

cnf_expr = to_cnf(boolean_expr)

print("Boolean Expression:", boolean_expr)
print("CNF Form:", cnf_expr)
        