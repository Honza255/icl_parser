import re
from z3 import *

class IclRetargeting:


    def mod_reg(self, register: dict, number: int) -> dict:
        reg_modded = {}
        for reg_name, reg_tuple in register.items():
            reg_name = reg_name.replace('.', '_')
            items = []
            for item in reg_tuple:
                if(type(item) == str):
                    modded_selection = self.add_step(item, 0)
                else:
                    modded_selection = item
                items.append(modded_selection)
            modded_reg_name = self.add_step(reg_name, number)
            reg_modded[modded_reg_name] = tuple(items)
        #print(reg_modded)
        return reg_modded
    
    def add_step(self, input: str, step: int) -> str:
        return re.sub(r'(\w+)(_\d+)', r'\1\2_{0}'.format(step), input)

    def modify_step(self, input: str, step: int) -> str:
        return re.sub(r'(\w+)(_\d+)', r'\1_{0}'.format(step), input)
    
    def strip_step(self, input: str) -> str:
        return re.sub(r'(\w+)(_\d+)', r'\1', input)

    def __init__(
            self,
            desing_registers : dict[str:tuple[str,bool,list[tuple[str,str]]]],
            sel_muxes : dict[str,str],
            max_allowed_steps: int
            ) -> None:
        
        self.desing_registers = desing_registers
        self.sel_muxes = sel_muxes
        self.reg_modded = self.mod_reg(self.desing_registers, 0)
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
            for reg_name, reg_tuple in self.reg_modded.items():
                sel_bit = reg_tuple[0]
                sel_bit_var = "sel_"+reg_name
                reg_selecs.append(sel_bit)
                smt2_string += "(declare-const {0} Bool)\n".format(reg_name)
                smt2_string += "(declare-const {0} Bool)\n".format(sel_bit_var)
                smt2_string += "(assert (= {} {}))\n".format(sel_bit_var, sel_bit)
            registers.append(copy.deepcopy(self.reg_modded))

            
            for reg_name, selection in sel_muxes.items():
                smt2_string += "(declare-const {0}_{1} Bool)\n".format(reg_name, 0)
                smt2_string += "(assert (= {0}_{1} {2}))\n".format(reg_name, 0, self.add_step(selection, 0))

            steps = list(range(0,allowed_steps+1))
            for step in steps:
                new_sel_muxes = {}


                new_registers = {}
                for reg_name, reg_tuple in registers[step].items():
                    sel_bit = reg_tuple[0]
                    control_bit = reg_tuple[1]

                    # Formulate new register names for current step
                    modded_reg_name = re.sub(r'(\w+)(_\d+)', r'\1_{0}'.format(step+1), reg_name)
                    new_sel_bit = re.sub(r'(\w+)(_\d+)', r'\1_{0}'.format(step+1), sel_bit)
                    sel_bit_var = "sel_"+reg_name
                    new_sel_bit_var = "sel_"+modded_reg_name

                    # Declare new smt2 variables
                    smt2_string += "(declare-const {0} Bool)\n".format(modded_reg_name)
                    smt2_string += "(declare-const {0} Bool)\n".format(new_sel_bit_var)

                    # Active control bits can change in all steps but normal register can only change on last step                
                    if((not control_bit) & (step != steps[-1])):
                        smt2_string += "(assert (= {} {}))\n".format(reg_name, modded_reg_name)

                    # Transition clause: ~X >> Equivalent(A, B)               
                    smt2_string += "(assert (= {} {}))\n".format(new_sel_bit_var, new_sel_bit)
                    smt2_string += "(assert (=> (not {}) (= {} {})))\n".format(sel_bit_var, reg_name, modded_reg_name)
                    
                    #new_registers[new_reg_name] = (new_sel_bit, control_bit, new_paths)
                    new_registers[modded_reg_name] = (new_sel_bit, control_bit)
                    reg_selecs.append(new_sel_bit)

                registers.append(new_registers)

                for reg_name, selection in sel_muxes.items():
                    smt2_string += "(declare-const {0}_{1} Bool)\n".format(reg_name, step+1)
                    smt2_string += "(assert (= {0}_{1} {2}))\n".format(reg_name, step+1, self.add_step(selection, step+1))

            # Consruct variable for counting all active bits throughout all steps 
            smt2_all_sel_bits_sum = "(declare-const sel_bits Real) \n(assert (= sel_bits (+ {})))\n".format(" ".join(reg_selecs))
            smt2_string += smt2_all_sel_bits_sum
    
            # Save constructed and parsed smt2(cnf) for later use           
            self.smt2[allowed_steps] = smt2_string
            
            #for item,x in new_registers.items():
            #    print(item,x)   
            #print("STEP", allowed_steps)
        
            # Save
            self.new_registers[step+1] = new_registers
        self.new_registers[0] = copy.deepcopy(self.reg_modded)

        self.solvers = {}                
        for step, smt2 in self.smt2.items():
            cnf = z3.parse_smt2_string(smt2)
            
            solver = Solver()
            solver.add(cnf)   

            optimize = Optimize()
            optimize.add(cnf)        
        
            self.solvers[step] = {"solver":solver, "optmizier": optimize}
            
    def retarget(self, start_state: dict[str:bool], end_state:dict[str:bool]) -> bool: 
        modded_start_state = self.mod_reg(start_state, 0)

        cnf_init = []
        cnf_declare = []
        for reg_name, state in modded_start_state.items():
            cnf_init.append(reg_name if state[0] == "1" else "(not {})".format(reg_name))
            cnf_declare.append("(declare-const {0} Bool)\n".format(reg_name))
        smt2_init = "".join(cnf_declare) + "\n" 
        smt2_init += "(assert (and {}))\n".format(" ".join(cnf_init))
        
        
        for step, solvers in self.solvers.items():
            solver = solvers["solver"]
            optimizer = solvers["optmizier"]
            
            cnf_end = []
            cnf_declare = []
            
            modded_end_state = self.mod_reg(end_state, step+1)
            for reg_name, state in modded_end_state.items():
                cnf_end.append(reg_name if state[0] == "1" else  "(not {})".format(reg_name))
                cnf_declare.append("(declare-const {0} Bool)\n".format(reg_name))          
            smt2_end = "".join(cnf_declare) + "\n" 
            smt2_end += "(assert (and {}))\n".format(" ".join(cnf_end))            

            clause = smt2_init + smt2_end
            cnf = z3.parse_smt2_string(clause)

            solver.push()
            solver.add(cnf)     
            solver_status = solver.check()
            if solver_status != sat:
                continue
            solver.pop()

            optimizer.push()
            optimizer.add(cnf)
            cost = Real('sel_bits')     
            optimizer.minimize(cost)
            optimize_status = optimizer.check()
            if optimize_status != sat:
                raise RuntimeError("Optimized failed failed???")

            self.end_step = step+1
            self.end_model = optimizer.model()
            optimizer.pop()
            return 0 


            
        print("Retargeting is unable to get from init state to end state, max allowed JTAG vectros:{}".format(self.max_allowed_steps))
        return 1

    def print_model_states(self, model, prefix: str=""):
        for var in model:
            print(prefix, " Var: ", var, "Value:", model[var])

    def get_steps(self) -> int:
        return list(range(0, self.end_step+1))
    
    def get_bit(self, name:str, step: int) -> bool:
        #bit_name = self.add_step(name, step)
        bit = z3.Bool("{}_{}".format(name,step))
        
        return is_true(self.end_model[bit])

    def get_data(self) -> dict[int, dict[str, bool]]:
        
        #for node, items in sorted(self.new_registers.items()):
        #    for item in items:
        #        print(node, item)
        
        #print(self.end_model.eval(Bool("A_0000_0"), model_completion=True)) 
        #print(self.end_model.eval(Bool("A_6450000_0"), model_completion=True))  
                
        data = {}
        for var in self.end_model:
            name = str(var)
            match = re.search(r'_(\d+)$', name)
            if(match):
                number = int(match.group(1))  # Convert the found number to integer
                base = name[:match.start()]   # Get the base part before the pattern
                if number in data:
                    data[number][base] = is_true(self.end_model[var])
                else:
                    data[number] = {}
                    data[number][base] = is_true(self.end_model[var])

        #data_2 = {}
        #for step in range(self.end_step+2):
        #    if(step not in data_2):
        #        data_2[step] = {}
        #    for reg_name in self.desing_registers:
        #        data_2[step][reg_name] = None
        #    for sel_name in self.sel_muxes:
        #        data_2[step][sel_name] = None

        #print(data_2)               
        #for var in self.end_model:
        #    name = str(var)
        #    match = re.search(r'_(\d+)$', name)
        #    if(match):
        #        number = int(match.group(1))  # Convert the found number to integer
        #        base = name[:match.start()]   # Get the base part before the pattern
        #        if number in data_2:
        #            if(base in data_2[number]):
        #                data_2[number][base] = is_true(self.end_model[var])
        #for a,b in data_2.items():
        #    for x,y in b.items():                
        #        print(a,x,y)
        #input()
        # get_data

        #for step, item in sorted(data.items()):
        #    for name, state in item.items():
        #        print(step, name, state)
        #print("get_data_end")

        return data