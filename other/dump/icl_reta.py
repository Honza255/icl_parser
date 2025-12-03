        for step, smt2 in self.smt2.items():

            cnf_end = []
            modded_end_state = self.mod_reg(end_state, step+1)
            for reg_name, state in modded_end_state.items():
                cnf_end.append(reg_name if state[0] == "1" else  "(not {})".format(reg_name))
            smt2_end = "(assert (and {}))\n".format(" ".join(cnf_end))            

            
            # Create whole CNF clause                
            clause = smt2 + smt2_end + smt2_init
            ###print(clause)
            cnf = z3.parse_smt2_string(clause)
            # Add CNF clauses to the solver and check if it is SAT
            solver = Solver()
            solver.add(cnf)     
               
            solver_status = solver.check()
            if solver_status != sat:
                continue

            #print(clause)
            ###self.print_model_states(solver.model(), "Solver")

            # Add CNF clauses to the optimize solver and run it, it should not fail            
            optimize = Optimize()
            optimize.add(cnf)
            cost = Real('sel_bits')
       
            optimize.minimize(cost)
            optimize_status = optimize.check()
            if optimize_status != sat:
                raise RuntimeError("Optimized failed failed???")
            
            #self.print_model_states(optimize.model(), "Optimize")

            self.end_step = step
            self.end_model = optimize.model()

            #print("nooo")
            #model = optimize.model()
            #for d in model.decls():
            #    print(f"{type(d)} {d.name()} = {model[d]}")
            #input()     
            
            return 0 