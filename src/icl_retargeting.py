import re
import os

from z3 import *

from .icl_common import *
from .icl_items import *

# Get the directory containing the current file
current_dir = os.path.dirname(os.path.abspath(__file__))

class IclRetargeting:

    C_IR_DR_STATE = "IS_IT_IR_DATA_CHAIN"

    def mod_reg(self, register: dict, number: int) -> dict:
        reg_modded = {}
        for reg_name, reg_tuple in register.items():
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
        return re.sub(r'([\w.]+)(_\d+)', r'\1\2_{0}'.format(step), input)

    def modify_step(self, input: str, step: int) -> str:
        return re.sub(r'([\w.]+)(_\d+)', r'\1_{0}'.format(step), input)
    
    def strip_step(self, input: str) -> str:
        return re.sub(r'([\w.]+)(_\d+)', r'\1', input)

    def define_data_registres(self, old_step, new_step, include_constrains):
        smt2_declar = ""
        smt2_string = ""
        soft_constrain = []

        for _ , data_reg in self.data_registers.items():
            data_reg: smtDataReg = data_reg
            
            print()
            print()
            print("full_name", data_reg.full_name)
            print("data_reg", data_reg.data_reg)
            print("sel_en", data_reg.sel_en)
            print("write_en", data_reg.write_en)
            print("write_en_sel", data_reg.write_en_sel)
            print("read_en", data_reg.read_en)
            print("read_en_sel", data_reg.read_en_sel)            
            print("data_in_reg", data_reg.data_in_reg)
            print("read_path_ready", data_reg.read_path_ready)
            print()
            print()
            #input()
            
            new_data_select_variable = self.add_step(f"selected_{data_reg.full_name}_0000", new_step)
            new_data_select_variable_smt = self.add_step(data_reg.sel_en, new_step)

            smt2_declar += "(declare-const {0} Bool)\n".format(new_data_select_variable)
            smt2_string += "(assert (= {0} {1}))\n".format(new_data_select_variable, new_data_select_variable_smt)
            
            new_data_wite_en_val = self.add_step(f"write_en_val_{data_reg.full_name}_0000", new_step)           
            new_data_wite_en_val_smt = self.add_step(data_reg.write_en, new_step)

            smt2_declar += "(declare-const {0} Bool)\n".format(new_data_wite_en_val)
            smt2_string += "(assert (= {0} {1}))\n".format(new_data_wite_en_val, new_data_wite_en_val_smt)

            new_data_read_en_val = self.add_step(f"read_en_val_{data_reg.full_name}_0000", new_step)           
            new_data_read_en_val_smt = self.add_step(data_reg.read_en, new_step)

            smt2_declar += "(declare-const {0} Bool)\n".format(new_data_read_en_val)
            smt2_string += "(assert (= {0} {1}))\n".format(new_data_read_en_val, new_data_read_en_val_smt)
                                              
            new_data_write_en_sel = self.add_step(f"write_en_sel_{data_reg.full_name}_0000", new_step)
            new_data_write_en_sel_smt = self.add_step(f"sel_{data_reg.write_en_sel}_0000", new_step)

            smt2_declar += "(declare-const {0} Bool)\n".format(new_data_write_en_sel)
            smt2_string += "(assert (= {0} {1}))\n".format(new_data_write_en_sel, new_data_write_en_sel_smt)

            new_data_read_en_sel = self.add_step(f"read_en_sel_{data_reg.full_name}_0000", new_step)
            new_data_read_en_sel_smt = self.add_step(f"sel_{data_reg.read_en_sel}_0000", new_step)

            smt2_declar += "(declare-const {0} Bool)\n".format(new_data_read_en_sel)
            smt2_string += "(assert (= {0} {1}))\n".format(new_data_read_en_sel, new_data_read_en_sel_smt)
            
            old_data_write_en_sel = self.add_step(f"write_en_sel_{data_reg.full_name}_0000", old_step)
            write_en = f"(and {old_data_write_en_sel} {new_data_wite_en_val} {new_data_select_variable})"          

            old_data_read_en_sel = self.add_step(f"read_en_sel_{data_reg.full_name}_0000", old_step)
            read_en = f"(and {old_data_read_en_sel} {new_data_read_en_val} {new_data_select_variable})"          


            # Bit that indicate if data register is supposed to be read or not
            # This bit shall be set initally by user and at the end of retargeting it must be a zero
            xxx = self.add_step(f"to_read_val_{data_reg.full_name}_0000", new_step)            
            smt2_declar += "(declare-const {0} Bool)\n".format(xxx)




                        
            if(include_constrains):
                write_enabled = self.add_step(f"write_enabled_{data_reg.full_name}_0000", new_step)
                smt2_declar += "(declare-const {0} Bool)\n".format(write_enabled)
                smt2_string += f"(assert (= {write_enabled} {write_en}))\n"

                read_enabled = self.add_step(f"read_enabled_{data_reg.full_name}_0000", new_step)
                smt2_declar += "(declare-const {0} Bool)\n".format(read_enabled)
                smt2_string += f"(assert (= {read_enabled} {read_en}))\n"

            for data_reg_bit_variable in data_reg.data_in_reg:
                data_source, data_destination = data_reg_bit_variable

                old_data_reg_variable = self.add_step(data_destination, old_step)
                new_data_reg_variable = self.add_step(data_destination, new_step)

                old_read_data_reg_variable = self.add_step(f"read_{data_destination}", old_step)
                new_read_data_reg_variable = self.add_step(f"read_{data_destination}", new_step)
                
                new_data_in = self.add_step(data_source, new_step)

                new_data_reg_soft_variable = f"soft_{new_data_reg_variable}"

                # Declare new smt2 reg variabler
                smt2_declar += "(declare-const {0} Bool)\n".format(new_data_reg_variable)
                smt2_declar += "(declare-const {0} Bool)\n".format(new_read_data_reg_variable)

                if(include_constrains):
                    #### Active control bits can change in all steps but normal register can only change on last step                
                    ###if((not control_bit) & (step != steps[-1])):
                    ###    smt2_string += "(assert (= {} {}))\n".format(old_scan_reg_variable, new_scan_reg_variable)

                    # Determine when data reg can change and where it gets its data, 
                    smt2_string += f"(assert (= {new_data_reg_variable} (ite {write_enabled} {new_data_in} {old_data_reg_variable})))\n"

                    ## Add constrain to help us count data reg bit changes
                    soft_constrain.append(new_data_reg_soft_variable)
                    smt2_declar += "(declare-const {0} Bool)\n".format(new_data_reg_soft_variable)
                    smt2_string += "(assert (not (= {0} (= {1} {2}))))\n".format(new_data_reg_soft_variable, old_data_reg_variable, new_data_reg_variable)
                    
                    # data_reg.read_path_ready: list[tuple[str, list[tuple[str:str]]]] = []
                    for data_reg_bit, data in data_reg.read_path_ready:
                        read_expressions = []
                        if(data_reg_bit in data_destination):
                            for sel_sink_tdr_reg, read_path_expression in data:
                                sel_sink_tdr_reg = f"sel_{self.strip_step(sel_sink_tdr_reg)}_0000"
                                read_expressions.append(f'(and {self.add_step(sel_sink_tdr_reg, old_step)} {self.add_step(read_path_expression, new_step)})')
                            read_expressions = " ".join(read_expressions)
                            read_expressions = f'(and {read_enabled} (or {read_expressions}))'
                            #print(read_expressions)
 
                            # Determine when read can be cleared                           
                            # Transition clause: ~X >> Equivalent(A, B)          
                            smt2_string += "(assert (=> (not {}) (= {} {})))\n".format(read_expressions, old_read_data_reg_variable, new_read_data_reg_variable)

                            #print(read_expressions)
                            #print("(assert (=> (not {}) (= {} {})))\n".format(read_expressions, old_read_data_reg_variable, new_read_data_reg_variable))                            
                            #input()

        return (smt2_declar, smt2_string, soft_constrain)



    def define_scan_registres(self, old_step, new_step, include_constrains):
        smt2_declar = ""
        smt2_string = ""
        soft_constrain = []

        for _ , scan_reg in self.scan_registers.items():
            scan_reg: IclScanRegister = scan_reg
            old_scan_reg_sel_variable = self.add_step(f"sel_{scan_reg.get_name_with_hier()}_0000", old_step)
            new_scan_reg_sel_variable = self.add_step(f"sel_{scan_reg.get_name_with_hier()}_0000", new_step)
            new_scan_reg_sel_smt      = self.add_step(scan_reg.scan_selection_smt, new_step)

            # Declare new smt2 scan reg selection variable
            smt2_declar += "(declare-const {0} Bool)\n".format(new_scan_reg_sel_variable)
            smt2_string += "(assert (= {0} {1}))\n".format(new_scan_reg_sel_variable, new_scan_reg_sel_smt)

            for scan_reg_bit_variable in scan_reg.get_all_named_indexes():
                old_scan_reg_variable = self.add_step(scan_reg_bit_variable, old_step)
                new_scan_reg_variable = self.add_step(scan_reg_bit_variable, new_step)
                new_scan_reg_soft_variable = f"soft_{new_scan_reg_variable}"

                # Declare new smt2 reg variabler
                smt2_declar += "(declare-const {0} Bool)\n".format(new_scan_reg_variable)

                if(include_constrains):
                    #### Active control bits can change in all steps but normal register can only change on last step                
                    ###if((not control_bit) & (step != steps[-1])):
                    ###    smt2_string += "(assert (= {} {}))\n".format(old_scan_reg_variable, new_scan_reg_variable)

                    # Transition clause: ~X >> Equivalent(A, B)          
                    smt2_string += "(assert (=> (not {}) (= {} {})))\n".format(old_scan_reg_sel_variable, old_scan_reg_variable, new_scan_reg_variable)

                    # Add constrain to help us count scan reg bit changes
                    soft_constrain.append(new_scan_reg_soft_variable)
                    smt2_declar += "(declare-const {0} Bool)\n".format(new_scan_reg_soft_variable)
                    smt2_string += "(assert (not (= {0} (= {1} {2}))))\n".format(new_scan_reg_soft_variable, old_scan_reg_variable, new_scan_reg_variable)


        return (smt2_declar, smt2_string, soft_constrain)

    def __init__(
            self,
            scan_registers: dict[str:IclScanRegister],
            data_registers : dict[str:smtDataReg],
            sel_muxes : dict[str,str],
            ono_hot_groups: list[smtOneHotGroup],
            ir_out_ports:list[str],           
            max_allowed_steps: int
            ) -> None:
        
        self.scan_registers = scan_registers
        self.data_registers = data_registers
        self.sel_muxes = sel_muxes

        self.max_allowed_steps = max_allowed_steps
        self.end_state = None
        self.end_step = None
        self.ono_hot_groups: list[smtOneHotGroup] = ono_hot_groups
        self.ir_out_ports: list[str] = ir_out_ports
        # Allowed steps: smt2(cnf)        
        self.smt2 = {}
        self.all_variables = {}

        for allowed_steps in range(self.max_allowed_steps):
            soft_constrain = []

            smt2_declar = ""
            smt2_string = ""

            # New way of scan register initialization
            smt_var_declaration, smt_exprssion, soft = self.define_scan_registres(0, 0, False)
            smt2_declar += smt_var_declaration
            smt2_string += smt_exprssion
            soft_constrain.extend(soft)

            # New way of data register initialization
            smt_var_declaration, smt_exprssion, soft = self.define_data_registres(0, 0, False)
            smt2_declar += smt_var_declaration
            smt2_string += smt_exprssion
            soft_constrain.extend(soft)

            # Sel muxes - variables used as indication which mux is open when reconstructing scan path
            # Not actually needed for retargeting, but it helps for easy scan path reconstruction
            for old_reg_name, selection in sel_muxes.items():
                smt2_declar += "(declare-const {0}_{1} Bool)\n".format(old_reg_name, 0)
                smt2_string += "(assert (= {0}_{1} {2}))\n".format(old_reg_name, 0, self.add_step(selection, 0))

            # One-hot constraint: exactly one of x0, x1, x2 is true
            # (assert (= (+ (ite x0 1 0) (ite x1 1 0) (ite x2 1 0)) 1))
            new_step = 0
            for group in self.ono_hot_groups:
                tmp: list[str] = []
                for variable in group.one_hot_bits:
                    mod_var = self.add_step(variable, 0)
                    mod_var = self.modify_step(mod_var, new_step)
                    tmp.append(f'(ite {mod_var} 1 0)')
                    smt2_declar += "(declare-const {0} Bool)\n".format(mod_var)
                smt2_string += f'(assert (= (+ {" ".join(tmp)} ) 1))\n'

            # Determines if current step is IR or DR
            tmp: list[str] = []
            new_step = 0
            for variable in self.ir_out_ports:
                mod_var = self.add_step(variable, 0)
                mod_var = self.modify_step(mod_var, new_step)
                tmp.append(mod_var)
                smt2_declar += "(declare-const {0} Bool)\n".format(mod_var)
            smt2_declar += "(declare-const {0}_{1} Bool)\n".format(self.C_IR_DR_STATE, new_step)
            if(tmp):                               
                smt2_string += f'(assert (=> {self.C_IR_DR_STATE}_{new_step} (and {" ".join(tmp)} )))\n'            
                smt2_string += f'(assert (=> (not {self.C_IR_DR_STATE}_{new_step} ) (not (or {" ".join(tmp)} ))))\n'  
            else:
                smt2_string += f'(assert (not {self.C_IR_DR_STATE}_{new_step} ))\n'            


            steps = list(range(0,allowed_steps+1))
            for step in steps:

                # One-hot constraint: exactly one of x0, x1, x2 is true
                # (assert (= (+ (ite x0 1 0) (ite x1 1 0) (ite x2 1 0)) 1))
                new_step = step + 1
                for group in self.ono_hot_groups:
                    tmp: list[str] = []
                    for variable in group.one_hot_bits:
                        mod_var = self.add_step(variable, 0)
                        mod_var = self.modify_step(mod_var, new_step)
                        tmp.append(f'(ite {mod_var} 1 0)')
                        smt2_declar += "(declare-const {0} Bool)\n".format(mod_var)
                    smt2_string += f'(assert (= (+ {" ".join(tmp)} ) 1))\n'

                # Determines if current step is IR or DR
                tmp: list[str] = []
                new_step = step + 1
                for variable in self.ir_out_ports:
                    mod_var = self.add_step(variable, 0)
                    mod_var = self.modify_step(mod_var, new_step)
                    tmp.append(mod_var)
                    smt2_declar += "(declare-const {0} Bool)\n".format(mod_var)
                smt2_declar += "(declare-const {0}_{1} Bool)\n".format(self.C_IR_DR_STATE, new_step)                               
                if(tmp):
                    smt2_string += f'(assert (=> {self.C_IR_DR_STATE}_{new_step} (and {" ".join(tmp)} )))\n'            
                    smt2_string += f'(assert (=> (not {self.C_IR_DR_STATE}_{new_step} ) (not (or {" ".join(tmp)} ))))\n'  
                else:
                    smt2_string += f'(assert (not {self.C_IR_DR_STATE}_{new_step} ))\n'            


                # New way of scan register initialization
                smt_var_declaration, smt_exprssion, soft = self.define_scan_registres(step, step + 1, True)
                smt2_declar += smt_var_declaration
                smt2_string += smt_exprssion
                soft_constrain.extend(soft)

                # New way of data register initialization
                smt_var_declaration, smt_exprssion, soft = self.define_data_registres(step, step + 1, True)
                smt2_declar += smt_var_declaration
                smt2_string += smt_exprssion
                soft_constrain.extend(soft)

                # Sel muxes - variables used as indication which mux is open when reconstructing scan path
                # Not actually needed for retargeting, but it helps for easy scan path reconstruction
                for old_reg_name, selection in sel_muxes.items():
                    smt2_declar += "(declare-const {0}_{1} Bool)\n".format(old_reg_name, step+1)
                    smt2_string += "(assert (= {0}_{1} {2}))\n".format(old_reg_name, step+1, self.add_step(selection, step+1))


            # Construct variables that will indicate if scan_reg was part of scan path during retargeting
            for _ , scan_reg in self.scan_registers.items():
                tmp = []
                scan_reg_active_path = f"sel_group_{scan_reg.get_name_with_hier()}"
                smt2_declar += "(declare-const {0} Bool)\n".format(scan_reg_active_path)

                for step in steps:
                    new_scan_reg_sel_variable = self.add_step(f"sel_{scan_reg.get_name_with_hier()}_0000", step)
                    tmp.append(new_scan_reg_sel_variable)
                smt2_string += "(assert (= {0} (or {1})))\n".format(scan_reg_active_path, " ".join(tmp))

            # Construct variables that will indicate if data_reg was written during retargeting
            for _ , data_reg in self.data_registers.items():
                tmp = []
                data_reg_written = f"sel_group_data_reg_written_{data_reg.full_name}"
                smt2_declar += "(declare-const {0} Bool)\n".format(data_reg_written)

                for step in steps:
                        written_data_reg = self.add_step(f"write_enabled_{data_reg.full_name}_0000", step+1)
                        tmp.append(written_data_reg)
                smt2_string += "(assert (= {0} (or {1})))\n".format(data_reg_written, " ".join(tmp))

            ### Consruct variable for counting all active bits throughout all steps 
            ## smt2_declar += "(declare-const sel_bits Real) \n"
            ## smt2_all_sel_bits_sum = "(assert (= sel_bits (+ {})))\n".format(" ".join(reg_selecs))
            ## smt2_string += smt2_all_sel_bits_sum

            # Consruct variable for counting all soft constrains met
            smt2_declar += "(declare-const soft_all Real) \n"
            tmp = "(assert (= soft_all (+ {})))\n".format(" ".join(soft_constrain))
            smt2_string += tmp

            # Save constructed and parsed smt2(cnf) for later use           
            self.smt2[allowed_steps] = smt2_declar + smt2_string
            self.all_variables[allowed_steps] = re.findall(r'\(declare-const\s+(\S+)\s+Bool\)', smt2_declar.replace('.', '_'))

            #for item,x in new_registers.items():
            #    print(item,x)   
            #print("STEP", allowed_steps)

        self.solvers = {}                
        for step, smt2 in self.smt2.items():
            smt2 = smt2.replace('.', '_')
            with open(f"{current_dir}/tmp/latest_{step}_smt2.txt", "w") as f:
                f.write(smt2)            

  
            cnf = z3.parse_smt2_string(smt2)
            
            solver = Solver()
            solver.add(cnf)   

            optimize = Optimize()
            optimize.add(cnf)        
        
            self.solvers[step] = {"solver":solver, "optmizier": optimize}


    def retarget(self, start_state: dict[str:bool], end_state:dict[str:bool], other:dict[str:bool] ) -> bool: 
        modded_start_state = self.mod_reg(start_state, 0)

        cnf_init = []
        cnf_declare = []
        for reg_name, state in modded_start_state.items():
            cnf_init.append(reg_name if state[0] == "1" else "(not {})".format(reg_name))
            cnf_declare.append("(declare-const {0} Bool)\n".format(reg_name))
        smt2_init = "".join(cnf_declare) + "\n" 
        smt2_init += "(assert (and {}))\n".format(" ".join(cnf_init))

        cnf_other_init = []
        cnf_other_declare = []
        if(other):
            for item, state in other.items():
                cnf_other_init.append(item if state == 1 else "(not {})".format(item))
                cnf_other_declare.append("(declare-const {0} Bool)\n".format(item))
            smt2_init += "".join(cnf_other_declare) + "\n" 
            smt2_init += "(assert (and {}))\n".format(" ".join(cnf_other_init))

        for step, solvers in self.solvers.items():
            solver = solvers["solver"]
            optimizer = solvers["optmizier"]

            print(f"solve step {step}")

            cnf_end = []
            cnf_declare = []
            
            modded_end_state = self.mod_reg(end_state, step+1)
            for reg_name, state in modded_end_state.items():
                cnf_end.append(reg_name if state[0] == "1" else  "(not {})".format(reg_name))
                cnf_declare.append("(declare-const {0} Bool)\n".format(reg_name))          
            smt2_end = "".join(cnf_declare) + "\n" 

            smt2_end += "(assert (and {}))\n".format(" ".join(cnf_end))            

            clause = smt2_init + smt2_end
            clause = clause.replace('.', '_')
            with open(f"{current_dir}/tmp/init_end_smt2.txt", "w") as f:
                f.write(clause)

            cnf = z3.parse_smt2_string(clause)

            # Solver will ingnore soft constrains
            solver.push()
            solver.add(cnf)     
            solver_status = solver.check()
            if solver_status == sat:
                self.end_step = step+1
                solver.pop()
            else:
                solver.pop()
                continue

            if(1):
                optimizer.push()
                optimizer.add(cnf)
                cost = Real('soft_all')     
                optimizer.minimize(cost)
                optimize_status = optimizer.check()
                if optimize_status != sat:
                    optimizer.pop()
                    raise RuntimeError("Optimized failed failed???")
                self.end_step = step+1
                self.end_model = optimizer.model()
                print("Bit changes", self.end_model.evaluate(cost))
                optimizer.pop()
                return 0 
            else:
                return 0

            
        print("Retargeting is unable to get from init state to end state, max allowed JTAG vectros:{}".format(self.max_allowed_steps))
        return 1

    def print_model_states(self, model, prefix: str=""):
        for var in model:
            print(prefix, " Var: ", var, "Value:", model[var])

    def get_steps(self) -> int:
        return list(range(0, self.end_step+1))
    
    def get_bit(self, name:str, step: int) -> bool:
        name = name.replace('.', '_')
        name = "{}_{}".format(name,step)

        if(not (name in self.all_variables[step])):
            raise ValueError(f"Variable: {name} -> is not in retargeter for step: {step}")

        bit = z3.Bool(name)
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