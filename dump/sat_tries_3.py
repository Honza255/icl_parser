import re
from z3 import *
import time

register_map = {
#   REG/TDI/TDO  Selection   mux(bit) next bit selection [(sel->reg)]    
    "REG_0":      ( "true",        1, [("true",)]),
    "REG_1":      ( "true",        1, [("true","REG_0")]),
    "REG_2":      ( "REG_1",       0, [("true","REG_1")]),
    "MUX_1":      ( "true",        2, [("sel_MUX_1_2","REG_2"), ("sel_MUX_1_1","REG1") ]),
    "sel_MUX_1_2":( "true",        3, "REG_1"),
    "sel_MUX_1_1":( "true",        3, "(not REG_1)"),
    "REG_3":      ( "sel_MUX_2_2", 0, [("true","MUX_1")]),    
    "MUX_2":      ( "true",        2, [("sel_MUX_2_2","REG3"), ("sel_MUX_2_1","MUX1")]),
    "sel_MUX_2_2":( "true",        3, "REG_0"),
    "sel_MUX_2_1":( "true",        3, "(not REG_0)"),

}


register_start = "REG_0"
registers = {
#   REG/TDI/TDO  Selection   mux(bit) next bit selection [(sel->reg)]    
    "REG_0_0":  ( "true",          0, [("true","REG_1_0")]),
    "REG_1_0":  ( "true",          1, [("sel_REG_2_0","REG_2_0"), ("sel_REG_3_0","REG_3_0") ]),
    "REG_2_0":  ( "REG_1_0",       0, [("true","REG_21_0")]),
    "REG_21_0": ( "REG_1_0",       0, [("true","")]),    
    "REG_3_0":  ( "(not REG_1_0)", 0, [("true","REG_31_0")]),
    "REG_31_0": ( "(not REG_1_0)", 0, [("true","")])
}

registers_init = {
    "REG_0_0": 0,
    "REG_1_0": 0,
    "REG_2_0": 0,
    "REG_3_0": 1,
    "REG_21_0": 0,        
    "REG_31_0": 1,    
}

registers_end = {
    "REG_0_0": 1,
    "REG_1_0": 1,
    "REG_2_0": 1,
    "REG_21_0": 0,            
    "REG_3_0": 1,
    "REG_31_0": 1,    
}

class IclRetargeting:

    def __init__(self, start_reg: str, desing_registers : dict[str:tuple[str,bool,list[tuple[str,str]]]], max_allowed_steps: int) -> None:

        self.start_reg = start_reg
        self.desing_registers = desing_registers
        self.max_allowed_steps = max_allowed_steps
        self.end_state = None
        self.end_step = None
        
        # Allowed steps: smt2(cnf)        
        self.smt2 = {}

        self.new_registers = {}
                
        for allowed_steps in range(self.max_allowed_steps):
            registers = []
            reg_selecs = []

            smt2_string = ""
            for reg_name, reg_tuple in self.desing_registers.items():
                sel_bit = reg_tuple[0]
                sel_bit_var = "sel_"+reg_name
                reg_selecs.append(sel_bit)
                smt2_string += "(declare-const {0} Bool)\n".format(reg_name)
                smt2_string += "(declare-const {0} Bool)\n".format(sel_bit_var)
                smt2_string += "(assert (= {} {}))\n".format(sel_bit_var, sel_bit)
            registers.append(copy.deepcopy(self.desing_registers))
            
            steps = list(range(0,allowed_steps+1))
            for step in steps:
                new_registers = {}
                for reg_name, reg_tuple in registers[step].items():
                    sel_bit = reg_tuple[0]
                    control_bit = reg_tuple[1]
                    paths = reg_tuple[2]

                    # Formulate new register names for current step
                    new_reg_name = re.sub(r'(\w+)(_\d+)', r'\1_{0}'.format(step+1), reg_name)
                    new_sel_bit = re.sub(r'(\w+)(_\d+)', r'\1_{0}'.format(step+1), sel_bit)
                    sel_bit_var = "sel_"+reg_name
                    new_sel_bit_var = "sel_"+new_reg_name

                    # Update path for usage in current step
                    new_paths = []
                    for path in paths:
                        tmp = []
                        for item in path:
                            tmp.append( re.sub(r'(\w+)(_\d+)', r'\1_{0}'.format(step+1), item))
                        new_paths.append((tmp[0],tmp[1]))
                        
                    # Declare new smt2 variables
                    smt2_string += "(declare-const {0} Bool)\n".format(new_reg_name)
                    smt2_string += "(declare-const {0} Bool)\n".format(new_sel_bit_var)

                    # Active control bits can change in all steps but normal register can only change on last step                
                    if((not control_bit) & (step != steps[-1])):
                        smt2_string += "(assert (= {} {}))\n".format(reg_name, new_reg_name)

                    # Transition clause: ~X >> Equivalent(A, B)               
                    smt2_string += "(assert (= {} {}))\n".format(new_sel_bit_var, new_sel_bit)
                    smt2_string += "(assert (=> (not {}) (= {} {})))\n".format(sel_bit_var, reg_name, new_reg_name)
                    
                    new_registers[new_reg_name] = (new_sel_bit, control_bit, new_paths)
                    reg_selecs.append(new_sel_bit)

                registers.append(new_registers)

            # Consruct variable for counting all active bits throughout all steps 
            smt2_all_sel_bits_sum = "(declare-const sel_bits Real) \n(assert (= sel_bits (+ {})))\n".format(" ".join(reg_selecs))
            smt2_string += smt2_all_sel_bits_sum
    
            # Save constructed and parsed smt2(cnf) for later use           
            self.smt2[allowed_steps] = smt2_string
            
            for item,x in new_registers.items():
                print(item,x)   
            print("XDXXXXXX", allowed_steps)
        
            # Save
            self.new_registers[step+1] = new_registers
        self.new_registers[0] = copy.deepcopy(self.desing_registers)        
        
    def retarget(self, start_state: dict[str:bool], end_state:dict[str:bool]) -> bool: 
        
        cnf_init = []
        for reg_name, state in start_state.items():
            cnf_init.append(reg_name if state else "(not {})".format(reg_name))
        smt2_init = "(assert (and {}))".format(" ".join(cnf_init))

        for step, smt2 in self.smt2.items():

            cnf_end = []
            for reg_name, state in end_state.items():
                new_reg_name = re.sub(r'(\w+)(_\d+)', r'\1_{0}'.format(step+1), reg_name)
                cnf_end.append(new_reg_name if state else "(not {})".format(new_reg_name))
            smt2_end = "(assert (and {}))".format(" ".join(cnf_end))            

            # Create whole CNF clause                
            clause = smt2 + smt2_end + smt2_init
            print(clause)
            cnf = parse_smt2_string(clause)
            # Add CNF clauses to the solver and check if it is SAT
            solver = Solver()
            solver.add(cnf)        
            solver_status = solver.check()
            if solver_status != sat:
                continue

            self.end_model = solver.model()
            self.end_sates = {}
            for var in self.end_model:
                self.end_sates[var] = self.end_model[var]
                print("Var: ", var, "Value:", self.end_model[var])

            # Add CNF clauses to the optimize solver and run it, it should not fail            
            optimize = Optimize()
            optimize.add(cnf)
            cost = Real('sel_bits')
            optimize.minimize(cost)
            optimize_status = optimize.check()
            if optimize_status != sat:
                raise RuntimeError("Optimized failed failed???")


            self.end_step = step
            self.end_model = optimize.model()
            self.end_sates = {}
            print(step)
            for var in self.end_model:
                self.end_sates[str(var)] = self.end_model[var]
                print("Var: ", var, "Value:", self.end_model[var])
            return 0 
            
        print("Retargeting is unable to get from init state to end state, max allowed JTAG vectros:{}".format(self.max_allowed_steps))
        return 1
    
    def get_end_state(self) -> dict[str:bool]: 
        end_stae = {}
        for reg_name, item in self.new_registers[self.end_step+1].items():
            end_stae[reg_name] = is_true(self.end_sates[reg_name])
        return end_stae

    def get_retargeting_vectros(self) -> dict[list[bool]]: 
        print("XXX")
        print("XXX")      
        print(self.end_sates)
        print(self.new_registers)

        print("XXX")
        print("XXX")
        
        vector = {}                   
        for step in range(1, self.end_step+2):
            print("STEP:", step)

            current_reg = "{}_{}".format(self.start_reg,step)
            curren_value = is_true(self.end_sates[current_reg])
            current_item = self.new_registers[step][current_reg]
            current_paths = current_item[2]

            prev_reg = "{}_{}".format(self.start_reg,step-1)
            prev_item = self.new_registers[step-1][prev_reg]
            prev_paths = prev_item[2]

            vector[step] = [curren_value]

            print("A")
            print(current_reg, curren_value)
            print(current_item, current_paths)
            print(vector[step])            
            print("B")

            while 1:
                sum = 0
                for path in prev_paths:
                    activation = path[0]
                    if   activation == "true": sel_act = 1
                    elif activation == "false": sel_act = 0
                    else: sel_act = is_true(self.end_sates[activation])
                    if sel_act:
                        next_reg =  re.sub(r'(\w+)(_\d+)', r'\1_{0}'.format(step), path[1])
                    sum += sel_act
                print(sum)
                assert(sum == 1)
                
                if not next_reg:
                    break
            
                current_reg = next_reg
                curren_value = is_true(self.end_sates[current_reg])
                current_item = self.new_registers[step][current_reg]
                current_paths = current_item[2]
                
                prev_reg = re.sub(r'(\w+)(_\d+)', r'\1_{0}'.format(step-1), current_reg)
                prev_item = self.new_registers[step-1][prev_reg]
                prev_paths = prev_item[2]
                            
                vector[step].append(curren_value)
                
                print("AX")
                print("Next", next_reg)      
                print(current_reg, "XXX", curren_value)
                print(current_item, "XXX", current_paths)
                print(vector[step])            
                print("BX")          

            
            print("Vector", vector)
            print("Vector", "".join( ['1' if elem else '0' for elem in vector[step]]))          
            
            
            print()

        return vector

    
start_time = time.time()      


retargeting = IclRetargeting(register_start, registers, 10)
retargeting.retarget(registers_init, registers_end)
end_state = retargeting.get_end_state()
vectors = retargeting.get_retargeting_vectros()

print("Final Vector:")
for step, vector in vectors.items():
    print(step, vector)

print("End State:")
for reg,value in end_state.items():
    print(reg, value)


print("--- %s seconds ---" % (time.time() - start_time))
