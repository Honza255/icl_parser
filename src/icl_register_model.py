import networkx as nx
import re

from sympy import sympify, srepr, simplify_logic

from .icl_retargeting import IclRetargeting
from .icl_items import *
from .icl_common import *

class IclRegisterModel():
    IMPLICIT_SOURCE: str = "?implicit?"
    SCAN_REG_TYPE: str = "reg"
    SCAN_MUX_TYPE: str = "mux"

    def __init__(self, icl_instance: IclInstance) -> None:
        self.icl_instance = icl_instance
        self.icl_graph: nx.DiGraph = None
        # dict[string: IclRegister]

        self.input_port_types = [
            IclDataInPort, IclScanInPort, IclShiftEnable,
            IclCaptureEnable, IclUpdateEnable, IclSelectPort,
            IclResetPort, IclClockPort, IclTckPort, IclTmsPort,
            IclTrstPort, IclReadEnPort, IclWriteEnPort, IclAddressPort]

        self.output_port_types = [
            IclToIrSelectPort, IclDataOutPort, IclScanOutPort,
            IclToShiftEnable, IclToCaptureEnable, IclToUpdateEnable,
            IclToSelectPort, IclToResetPort, IclToClockPort, IclToTmsPort,
            IclToTrstPort, IclToTckPort]

        self.retargeter = None
        self.scan_registers: dict[str:IclScanRegister] = {}
        self.data_registers = {}
        self.data_registers_smt: dict[str:smtDataReg] = {}
        self.tdr_sink_of_data_reg: dict = {}
        self.tdr_bit_data_reg_read_sink: dict = {}
        self.jtag_steps: list[jtagStep] = []

        self.global_temp = None

        self.first_nodes = []
        self.last_nodes = []
        self.ir_out_names = []
       
        eval_list = self.icl_instance.list_instances()
        for item in eval_list:
            print(item)


        for item in eval_list:
            _, _ = item.popitem()
            _, instance = item.popitem()
            
            for icl_item in instance.icl_items:
                icl_item: IclItem

                if(type(icl_item) in [IclInstance, IclEnum]):
                    continue

                #if(type(icl_item) in self.input_port_types):                  
                #    for drives in icl_item.get_all_named_indexes():
                #        print(self.get_element_driver(drives),"->",  drives)
                #        print(self.get_main_expression(drives),"->", drives)

                #if(type(icl_item) in self.output_port_types):                  
                #    for recieving_connection in icl_item.get_all_named_indexes():
                #        print(self.get_element_driver(recieving_connection),"->",  recieving_connection)
                #
                #if(type(icl_item) in [IclScanRegister]):                  
                #    for recieving_connection in icl_item.get_all_named_indexes():
                #        print(self.get_element_driver(recieving_connection),"->",  recieving_connection)
                #
                #if(type(icl_item) in [IclScanMux]):                  
                #    for recieving_connection in icl_item.get_all_named_indexes():
                #        print(self.get_element_driver(recieving_connection),"->",  recieving_connection)
                #        print(self.get_expression(recieving_connection),"->",  recieving_connection)

                if(type(icl_item) in [IclToIrSelectPort]):                  
                    self.ir_out_names = self.ir_out_names + icl_item.get_all_named_indexes()

                if(type(icl_item) in [IclScanRegister]): 
                    data_reg_sinks = {}
                    data_reg_sinks_expression = {}
                    icl_item: IclScanRegister = icl_item
                     
                    full_name = icl_item.get_name_with_hier()               
                    self.scan_registers[full_name] = icl_item
                    
                    source: ConcatSig | EnumRef
                    source = icl_item.get_capture_source()
                    
                    tdr_size = icl_item.get_vector_size()

                    if(source):
                        if(not (type(source) in [EnumRef])):                         
                            source_bits: list[str]  = source.get_all_named_indexes_with_prefix(max_size=tdr_size, neg_on=0)
                            # tdr_bit_sel: str  = icl_item.get_all_named_indexes()[-1]

                            print(f"{full_name} -> source_bit")
                            for idx, source_bit in enumerate(source_bits):
                                tdr_bit: str  = icl_item.get_all_named_indexes()[idx]
                                data_reg_sinks_expression[source_bit] = self.trace_to_primaries(source_bit, 0)
                                data_reg_sinks[source_bit] = self.trace_to_primaries(source_bit, 1)

                                print(f"{source_bit} -> {data_reg_sinks_expression[source_bit]}")
                                print(f"{source_bit} -> {data_reg_sinks[source_bit]}")

                                if(data_reg_sinks[source_bit] == self.IMPLICIT_SOURCE):
                                    continue

                                for data_reg_bit in data_reg_sinks[source_bit].split():
                                        print("for data_reg_bit in data_reg_sinks[source_bit].split():")

                                        if(data_reg_bit in ["0", "1"]):
                                            continue
                                        icl_item_1: IclItem = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(data_reg_bit))
                                        print(icl_item_1)
                                        print(type(icl_item_1))
                                        if(type(icl_item_1) in [IclDataRegister]):
                                            if(icl_item_1.get_reg_type() != "addressable"):
                                                continue

                                            if(data_reg_bit == data_reg_sinks_expression[source_bit]):
                                                extracted_expr = "always_true"
                                            else:
                                                extracted_expr = self.extract_block_expression(data_reg_sinks_expression[source_bit], f"(And {data_reg_bit}")

                                            if(tdr_bit in self.tdr_bit_data_reg_read_sink):
                                                self.tdr_bit_data_reg_read_sink[tdr_bit].append(data_reg_bit)
                                            else:
                                                self.tdr_bit_data_reg_read_sink[tdr_bit] = [data_reg_bit]


                                            if(data_reg_bit in self.tdr_sink_of_data_reg):
                                                self.tdr_sink_of_data_reg[data_reg_bit].append((tdr_bit, extracted_expr))
                                            else:
                                                self.tdr_sink_of_data_reg[data_reg_bit] = [(tdr_bit, extracted_expr)]
                                            #print("self.tdr_sink_of_data_reg[data_reg_bit]", data_reg_bit, "->",self.tdr_sink_of_data_reg[data_reg_bit])
                                            print("extract_block_expression", extracted_expr)                               


                            #input()

                    #for x,a in self.tdr_sink_of_data_reg.items():
                    #    print(x,a)
                    #input()

                if(type(icl_item) in [IclDataRegister]):
                    print("if(type(icl_item) in [IclDataRegister]):")

                    icl_item: IclDataRegister = icl_item
                    data_reg_smt: smtDataReg = smtDataReg()
 
                    if(icl_item.get_reg_type() != "addressable"):
                        continue
                    
                    full_name = icl_item.get_name_with_hier()               
                    self.data_registers[full_name] = icl_item
                    self.data_registers_smt[full_name] = data_reg_smt

                    data_in : ConcatSig = icl_item.get_data_in()
                    data_inn: list[str] = data_in.get_all_named_indexes_with_prefix(max_size=data_in.get_sized_bits_size(), neg_on=0)
                    if(data_inn):
                        data_inn.reverse()

                    write_en : ConcatSig = icl_item.get_write_en()
                    write_enn : list[str] = write_en.get_all_named_indexes_with_prefix(max_size=write_en.get_sized_bits_size(), neg_on=0)

                    read_en : ConcatSig = icl_item.get_read_en()
                    read_enn : list[str] = read_en.get_all_named_indexes_with_prefix(max_size=read_en.get_sized_bits_size(), neg_on=0)

                    data_out : ConcatSig = icl_item.get_data_out()
                    print(f"IclDataRegister: {full_name}")
                    print(icl_item.get_name())
                    print(data_out)
                    print(data_out.get_vector_min_size())
                    print(icl_item.get_vector_size())
                    print(data_out.get_all_named_indexes_with_prefix(max_size=data_out.get_vector_min_size(), neg_on=0))
                    
                    #tmp = []
                    #for idx, out in enumerate(reversed(data_out.get_all_named_indexes_with_prefix(max_size=data_out.get_vector_min_size(), neg_on=0))):
                    #    if(idx >= icl_item.get_vector_size()):
                    #        break
                    #    print(f'self.get_expression -> {self.get_expression(out)}')
                    #    print(f'self.get_main_expression -> {self.get_main_expression(out)}')   
                    #    primary = self.get_expression(out)
                    #    print(idx, icl_item.get_vector_size(), out, "->", primary)
                    #    tmp.append(self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(primary)).get_name_with_hier())
                    #tmp = set(tmp)
                    #print(tmp)
                    #input()


                    data_reg_smt.full_name = icl_item.get_name_with_hier()
                    data_reg_smt.sel_en = self.trace_to_primaries(icl_item.get_reg_select())
                    data_reg_smt.write_en = self.trace_to_primaries(write_enn[0])
                    data_reg_smt.write_en_sel = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(data_reg_smt.write_en)).get_name_with_hier()                   
                    data_reg_smt.read_en = self.trace_to_primaries(read_enn[0])
                    data_reg_smt.read_en_sel = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(data_reg_smt.read_en)).get_name_with_hier()                   

                    for idx, recieving_connection in enumerate(reversed(icl_item.get_all_named_indexes())):
                        
                        primary = self.trace_to_primaries(data_inn[idx])
                        #print(idx, recieving_connection, data_inn[idx], primary)
                        
                        data_reg_smt.data_reg.append(recieving_connection)
                        data_reg_smt.data_in_reg.append((primary, recieving_connection ))
                        if(recieving_connection in self.tdr_sink_of_data_reg):
                            data_reg_smt.read_path_ready.append((recieving_connection, self.tdr_sink_of_data_reg[recieving_connection]))
                            # data_reg_smt.read_path_ready_2.append((recieving_connection, self.tdr_sink_of_data_reg[recieving_connection][0], self.tdr_sink_of_data_reg[recieving_connection][0]))
                            
                    #print(data_reg_smt.sel_en)
                    #print(data_reg_smt.write_en)
                    #print(data_reg_smt.data_reg)
                    #print(data_reg_smt.data_in_reg)

                #if(type(icl_item) in [IclLogicSignal]):                  
                #    for recieving_connection in icl_item.get_all_named_indexes():
                #        print(self.get_element_driver(recieving_connection),"->",  recieving_connection)

        #print("END")
        #print(self.get_main_expression("u_regs_nvm_atc_cut_10.select_0000"),"-> u_regs_nvm_atc_cut_10.select_0000")
        #print(self.get_main_expression("u_tdr_bypass.select_0000"),"-> u_tdr_bypass.select_0000")
        #print(self.get_main_expression("u_nvm_atc_cut_10.wdata_0068"),"-> u_nvm_atc_cut_10.wdata_0068")
        #print(self.get_main_expression("u_nvm_atc_cut_10.rst_n_0000"),"-> u_nvm_atc_cut_10.rst_n_0000")

        self.icl_graph = self.create_scan_path()
        # self.plotGraph()

        #sccs = nx.strongly_connected_components(self.icl_graph)
        #cyclic_sccs = [s for s in sccs if len(s) > 1]
        #print(cyclic_sccs)
        # input()
        





        #for node in self.icl_graph:
        #    in_nodes = [pred for pred in self.icl_graph.predecessors(node)]
        #    out_nodes = [succ for succ in self.icl_graph.successors(node)]
        #    print(f'{node} - Inputs: {in_nodes}, Ooutputs: {out_nodes}')      

        last_scan_port_nodes = []
        for node, degree in self.icl_graph.out_degree():
            try:
                node_type = self.icl_graph.nodes[node]["icl_type"]
                if (node_type == "scan_port" and degree == 0):
                    last_scan_port_nodes.append(node)
            except:
                pass
        print(last_scan_port_nodes)     
              
        for last_node in last_scan_port_nodes:
            self.traverse_iterative(last_node, last_node, self.icl_graph)


        #for node in self.icl_graph:
        #    print(node, self.icl_graph.nodes[node]["scan_port"])

        self.retargeter = self.create_retageter(self.icl_graph)

    def create_scan_path(self) -> nx.DiGraph:
        icl_graph: nx.DiGraph = nx.DiGraph()
        eval_list = self.icl_instance.list_instances()

        for item in eval_list:
            _, _ = item.popitem()
            _, instance = item.popitem()
            
            # ICL network connection creation
            for icl_item in instance.icl_items:
                icl_item: IclItem
                node_type: str = "Unknown"
                node_color: str = "Unknown"

                if(type(icl_item) in [IclScanInPort, IclScanOutPort] ):
                    node_type = "scan_port"   
                    node_color = "green"
        
                if(type(icl_item) in [IclScanMux] ):
                    node_type = self.SCAN_MUX_TYPE   
                    node_color = "blue"
       
                if(type(icl_item) in [IclScanRegister] ):
                    node_type = self.SCAN_REG_TYPE  
                    node_color = "red"

                if(type(icl_item) == IclScanMux):
                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node, icl_type=node_type, color=node_color, mux=1, icl_item=icl_item)

                    idx = 0
                    for a,b, expr_smt, expr_py in icl_item.get_all_connections():
                        #print(a,b)
                        #print(f"{expr_smt} -> {self.trace_to_primaries(expr_smt)}")
                        #print(f"{expr_py} -> {self.trace_to_primaries(expr_py)}")
                        #input()

                        link = "sel_{}_{}".format(idx, b)
                        icl_graph.add_node(link, icl_type="mux_sel", color="lightblue", expr_smt=self.trace_to_primaries(expr_smt), expr_py=self.trace_to_primaries(expr_py), icl_item=icl_item)
                        icl_graph.add_edge(a, link)
                        icl_graph.add_edge(link, b) 
                        idx += 1

                if(type(icl_item) in [IclScanInPort, IclScanOutPort]):
                    for recieving_connection in icl_item.get_all_named_indexes():
                        to_point = recieving_connection
                        for from_point in self.get_element_driver(recieving_connection):
                            icl_graph.add_node(to_point, icl_type=node_type, color=node_color, icl_item=icl_item)
                            if(from_point != self.IMPLICIT_SOURCE):
                                icl_graph.add_edge(from_point, to_point)

                #  Normal case
                if(type(icl_item) in [IclScanRegister]):
                    regs = icl_item.get_all_named_indexes()
                    first = regs[0]
                    last  = regs[-1]
                    #regs  = [first, last]

                    for reg in regs:
                        icl_graph.add_node(reg, icl_type=node_type, color=node_color, icl_item=icl_item)

                    for idx, reg in enumerate(regs):
                        if(reg != last):
                            icl_graph.add_edge(regs[idx], regs[idx+1])        
                    icl_graph.add_edge(self.get_element_driver(first)[0], first)


                        
                ## Special case as want to have only one or two nodes belonging to the same register
                #if(type(icl_item) in [IclScanRegister]):
                #    first_and_last = icl_item.get_all_named_indexes()
                #    first = first_and_last[0]
                #    last = first_and_last[-1]

                #    icl_graph.add_node(first, icl_type=node_type, color=node_color)
                #    icl_graph.add_edge(self.get_element_driver(first)[0], first)
                #    if(first != last):
                #        icl_graph.add_node(last, icl_type=node_type, color=node_color)
                #        icl_graph.add_edge(first, last)
                            

        return icl_graph

    def get_main_expression(self, start_name:str) -> str:
        start: str = self.get_expression(start_name)
        return self.trace_to_primaries(start)

    # Tries to find all primary inputs of tracable icl items
    # It tracer finds some kind of mux (scan_mux, data_mux, one_hot)
    # Selection of these muxes is also traced if not disabed with
    # Option skip_sel==1 
    def trace_to_primaries(self, tmp:str, skip_sel:bool = 0) -> str:
        while True:
            replace: list[tuple[str,str]] = []

            names = self.extract_names(tmp)
            names = list(set(names))

            for name in names:
                if(name == self.IMPLICIT_SOURCE):
                    continue
                
                if(self.is_it_top_input(name)):
                    continue

                icl_item: IclItem = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(name))

                # We can think of IclToIrSelectPort as top port
                if(type(icl_item) in [IclToIrSelectPort]):
                    continue

                # Stop tracing at bits that store values (scan/data) 
                if(type(icl_item) in [IclScanRegister, IclDataRegister]):
                    continue

                if(skip_sel):
                    get_element_driver: list[str] = self.get_element_driver(name)
                    expr = ' '.join(get_element_driver)
                    replace.append((name, expr))
                else:
                    expr = self.get_expression(name)
                    replace.append((name, expr))

            if(len(replace) == 0):
                break

            for name, expr in replace:
                tmp = tmp.replace(name, expr)

        return tmp
    
    def extract_block_expression(self, in_str: str, start_expr :str = "(or x") -> str:
        start = in_str.find(start_expr)
        if start == -1:
            raise ValueError(f"No '{start_expr}' found in '{in_str}'")

        depth = 0
        for i in range(start, len(in_str)):
            if in_str[i] == '(':
                depth += 1
            elif in_str[i] == ')':
                depth -= 1
                if depth == 0:
                    end = i
                    break

        return in_str[start + len(start_expr):end]

    # Extract names
    # From: "(and u_tap.ir_0004 u_tap.ir_0003 u_tap.ir_0002 u_tap.ir_0001 (not u_tap.ir_0000) ab_0050)"
    # To ["u_tap.ir_0004", "u_tap.ir_0003", "u_tap.ir_0002", "u_tap.ir_0001", "u_tap.ir_0000", "ab_0050"]
    def extract_names(self, expression: str) -> list[str]:
        # Use regex to find all variable names in the expression
        # Match words that start with a letter or underscore and may contain alphanumeric characters or underscores
        return re.findall(r'[a-zA-Z_.0-9]+_[0-9]{4,}', expression)

    def remove_trailing_numbers(self, s):
        return re.sub(r'_\d+$', '', s)

    def is_it_top_input(self, name:str) -> bool:
        tmp:bool = False
        if(name.find(".") == -1):
            icl_item: IclItem = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(name))
            if((type(icl_item) in self.input_port_types) or (type(icl_item) in self.output_port_types)):
                tmp = True
        return tmp

    def get_step(self, input: str) -> str:
        return re.sub(r'([\w.]+)_(\d+)', r'\2', input)
    
    def get_expression(self, name:str) -> str:
        icl_item: IclItem = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(name))
        expression: str = ""

        if(type(icl_item) in [IclLogicSignal]):                  
            expression = icl_item.processed_expression

        elif(type(icl_item) in [IclScanMux]):
            for mux_in, mux_out, expr_smt, expr_py in icl_item.get_all_connections():
                if(name == mux_out):
                    expression = f"(And {mux_in} {expr_smt}) {expression}"
            expression = f"(Or {expression})"	

        elif (type(icl_item) in [IclOneHotDataGroup]):
            full_expression = ""
            step_idx = self.get_step(name)
            for sel in icl_item.selectee:
                for name_idx in sel.get_all_named_indexes():      
                    if(not (step_idx in name_idx)):
                        continue                   
                    tmp_expression = f"(And {name_idx} {sel.get_reg_select()}) "
                    full_expression +=  tmp_expression
        

            assert(full_expression != "")
            expression = f"(or {full_expression})"
        else:
            get_element_driver: list[str] = self.get_element_driver(name)
            expression = get_element_driver

            expression = ' '.join(expression)

        #print(name)
        #print("END", expression)

        return expression
    
    
    def get_element_driver(self, name:str) -> list[str]:
        icl_item: IclItem = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(name))
        icl_item_size = len(icl_item.get_all_indexes())
        icl_item_short_name = icl_item.get_name()
       
        assert(name in icl_item.get_all_named_indexes())
        name_idx: int = icl_item.get_all_named_indexes().index(name)

        source_connection: str = None
        
        if(type(icl_item) in self.output_port_types):                             
            if(icl_item.has_port_source()):
                assert(len(icl_item.get_named_sourced_indexes()) == len(icl_item.get_all_indexes()))
                source_connection = icl_item.get_named_sourced_indexes()[name_idx]
               
        elif(type(icl_item) in [IclScanRegister]):
            if(icl_item.get_named_msb() == name):
                source_connection = icl_item.get_scanin_named_index()
            else:
                source_connection = icl_item.get_all_named_indexes()[name_idx-1]

        elif(type(icl_item) in [IclScanMux]):                             
            source_connection: str = ""
            for mux_in, mux_out, expr_smt, expr_py in icl_item.get_all_connections():
                if(name == mux_out):
                    source_connection = f"{mux_in} {source_connection}"
        
        elif(type(icl_item) in [IclDataRegister]):                             
            assert(0)

        elif (type(icl_item) in [IclOneHotDataGroup]):
            source_connection = ""
            step_idx = self.get_step(name)
            for sel in icl_item.selectee:
                for name_idx in sel.get_all_named_indexes():      
                    if(not (step_idx in name_idx)):
                        continue                   
                    source_connection +=  f"{name_idx} "
            assert(source_connection != "")


        elif(type(icl_item) in [IclLogicSignal]):                             
            source_connection = " ".join(self.extract_names(icl_item.processed_expression))

        elif(type(icl_item) in [IclDataMux]):
            source_connection: str = ""
            for mux_in, mux_out, expr_smt, expr_py in icl_item.get_all_connections():
                source_connection = f"{mux_in} {source_connection}"

        elif(type(icl_item) in self.input_port_types):
            connections: list[dict[IclSignal, ConcatSig]] = icl_item.get_instance().connections
            input_connection: ConcatSig = None

            for connection in connections:
                connect_to: IclSignal = list(connection.keys())[0]
                input_connection: ConcatSig = list(connection.values())[0]

                conn_name = connect_to.get_name()
                unsized = (connect_to.get_size() == 0)

                if(conn_name == icl_item_short_name):

                    if(unsized):
                        connect_to_size = icl_item_size
                    else:
                        connect_to_size = connect_to.get_size()
                    input_connection.check_fit(connect_to_size)

                    init_pol = 0
                    if((type(icl_item) == IclResetPort) or (type(icl_item) == IclToResetPort)):
                        init_pol = 1 
                    
                    if(unsized):
                        input_connection = input_connection.get_all_named_indexes_with_prefix(max_size=icl_item_size, neg_on=init_pol)
                    else:
                        input_connection.resize(connect_to.get_size())
                        input_connection = input_connection.get_all_named_indexes_with_prefix(max_size=connect_to.get_size(), neg_on=init_pol)
        
                    input_connection = input_connection[name_idx]                   
                    break
                else:
                    input_connection = None
            source_connection = input_connection
        else:
            raise ValueError(f"Not programmed for {type(icl_item)}")

        if(source_connection == None):
            source_connection = self.IMPLICIT_SOURCE
            
        source_connection = source_connection.split()

        return source_connection

    def traverse_iterative(self, start_node, sel, icl_graph):
        print("\n traverse_iterative start", start_node, sel)
        
        node_visits = {}
        stack = [(start_node, sel, [])]

        unfinised_nodes = []        
        speculative_start = []
        tag_table = []

        while stack:
            node, sel, scan_out = stack.pop()

            
            if node in node_visits:
                node_visits[node] += 1
            else:
                node_visits[node] = 1
            

            in_nodes = []
            for pred in icl_graph.predecessors(node):
                in_nodes.append(pred)

            out_nodes = []
            for succ in icl_graph.successors(node):
                out_nodes.append(succ)
                                                    
            in_nodes = [pred for pred in icl_graph.predecessors(node)]
            out_nodes = [succ for succ in icl_graph.successors(node)]
            out_node_num = len(out_nodes)

            #print("traverse", node, "stack", stack, "sel", sel)
            #if "sel_py_items" in icl_graph.nodes[node]:
            #    print("traverse", node, "stack", stack,  icl_graph.nodes[node]["sel_py_items"])
            print("IN", in_nodes, "OUT", out_nodes, "node_visits", node_visits[node])
            #input()

            if "sel_py_items" in icl_graph.nodes[node]:
                icl_graph.nodes[node]["sel_py_items"].append(sel)
            else:
                icl_graph.nodes[node]["sel_py_items"] = [sel]

            #if(icl_graph.nodes[node]["icl_type"] == "data_port"):
            #    continue

            if out_node_num > 0:
                assert(node_visits[node] <= out_node_num)

                if node_visits[node] != out_node_num:
                    if(node_visits[node] == 1):
                        unfinised_nodes.append((node, out_node_num))
                    else:
                        # Update unfinised_node data
                        for idx, unfinised_node in enumerate(unfinised_nodes):
                            node_name, visits = unfinised_node
                            if(node == node_name):
                                unfinised_nodes[idx] = (node_visits[node], out_node_num)
                                break
                        
                    if(not stack):
                        print(unfinised_nodes)
                        node_name, visits = unfinised_nodes.pop(0)
                        print("unfinised_nodes, node_name, visits", unfinised_nodes, node_name, visits)

                        in_nodes = [pred for pred in icl_graph.predecessors(node_name)]
                        print(f"speculative_start add {in_nodes} from {node_name}, sel {node_name}")
                        speculative_start.append(node_name)

                        # Reverse the order to maintain the original call order in recursive version
                        for next_node in reversed(in_nodes):
                            stack.append((next_node, node_name, []))
                        # input()

                    print("out_node_num > 0,", node_visits[node], out_node_num)
                    continue
                else:
                    for idx, unfinised_node in enumerate(unfinised_nodes):
                        node_name, visits = unfinised_node
                        if(node == node_name):
                            print(f"break{unfinised_nodes}")
                            unfinised_nodes.pop(idx)
                            print(f"break{unfinised_nodes}")

                            #input()
                            break


            ## Mark name of scan out port which visits this node on module level
            #if("icl_type" in icl_graph.nodes[node]):
            #    if(not (icl_graph.nodes[node]["icl_type"] in ["mux_sel", "mux"] )):
            #        icl_item: IclItem = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(node))
            #        if(type(icl_item) in [IclScanInPort] ):
            #            scan_out.pop()
            #        if(type(icl_item) in [IclScanOutPort] ):
            #            scan_out.append(icl_item.get_name_with_hier())
            #icl_graph.nodes[node]["scan_port"] = scan_out

            if "expr_py" in icl_graph.nodes[node]:
                icl_graph.nodes[node]["sel_py_items"].append(icl_graph.nodes[node]["expr_py"])

            if len(icl_graph.nodes[node]["sel_py_items"]) > 1:
                if out_node_num in [0, 1]:
                    icl_graph.nodes[node]["expr_py"] = "And({})".format(",".join(icl_graph.nodes[node]["sel_py_items"]))
                else:
                    icl_graph.nodes[node]["expr_py"] = "Or({})".format(",".join(icl_graph.nodes[node]["sel_py_items"]))
            else:
                icl_graph.nodes[node]["expr_py"] = "".join(icl_graph.nodes[node]["sel_py_items"])

            # Simplify the expression in certain nodes
            if( len(out_nodes) > 1):
                exp_py = icl_graph.nodes[node]["expr_py"]
                print(f"Simplify selection logic of node: {node} - {exp_py}")
                exp_py = exp_py.replace(".", "_w__q_")
                exp_py = self.simplify_symbol_repr(srepr(simplify_logic(sympify(exp_py))))
                exp_py = exp_py.replace("_w__q_", ".")
                icl_graph.nodes[node]["expr_py"] = exp_py
                print(f"Simplified selection logic of node: {node} - {exp_py}")

            icl_graph.nodes[node]["expr_smt"] = self.refine_to_smt2(icl_graph.nodes[node]["expr_py"])
            #icl_graph.nodes[node]["sel_py_items"] = []
            #print(icl_graph.nodes[node])

            # Update scan register selection
            if(icl_graph.nodes[node]["icl_type"] == self.SCAN_REG_TYPE):
                icl_graph.nodes[node]["icl_item"].scan_selection_smt = icl_graph.nodes[node]["expr_smt"]

            if(not (node in speculative_start)):
                # Reverse the order to maintain the original call order in recursive version
                for next_node in reversed(in_nodes):
                    stack.append((next_node, icl_graph.nodes[node]["expr_py"], scan_out.copy()))

            if(node in speculative_start):
                tag_table.append((node, icl_graph.nodes[node]["expr_smt"]))
                print(f"Tag table: {tag_table}")
                


        print(f"Traverse_iterative results")
        print(f"unfinised_nodes - {unfinised_nodes}")
        print(f"speculative_start - {speculative_start}")              
        print(f"tag table - {tag_table}")
        for idx, tag in enumerate(tag_table):
            name, exp = tag
            x = icl_graph.nodes[name]["sel_py_items"]
            print(f"Speculative tag: {idx} - {x}")
            print(f"Speculative tag: {idx} - {name} - {exp}")
            print(icl_graph.nodes[name]["sel_py_items"])
            print(exp)
            exp = exp.replace(name, " ")
            print(exp)
            tag_table[idx] = (name, exp)
            if name in exp:
                raise ValueError(f"Self reference of {name} in {exp}")

        for node in self.icl_graph:
            for tag in tag_table:
                tag_name, tag_exp = tag
                pattern = r'({0}\b)'.format(tag_name.replace(".", "\."))
                if "expr_smt" in icl_graph.nodes[node]:
                    print("pattern", pattern, tag_exp)
                    print("Simplify selection logic of node:", icl_graph.nodes[node]["expr_smt"])
                    icl_graph.nodes[node]["expr_smt"] = re.sub(pattern, tag_exp, icl_graph.nodes[node]["expr_smt"])
                    if(tag_name in icl_graph.nodes[node]["expr_smt"]):
                        print("Simplify selection logic of node:", icl_graph.nodes[node]["expr_smt"])
                    assert(not (tag_name in icl_graph.nodes[node]["expr_smt"] ))

            # Update scan register selection
            if(icl_graph.nodes[node]["icl_type"] == self.SCAN_REG_TYPE):
                if("expr_smt" in icl_graph.nodes[node]):
                    icl_graph.nodes[node]["icl_item"].scan_selection_smt = icl_graph.nodes[node]["expr_smt"]

    def refine_to_smt2(self, expr):
        # Replace logical operators with their SMT2 format
        replacements = {
            "And": "and",
            "Or": "or",
            "Not": "not",
            ",": " "
        }

        for old, new in replacements.items():
            expr = expr.replace(old, new)

        # Correctly format the expression with spaces and parentheses for SMT2
        expr = expr.replace("and(", "(and ").replace("or(", "(or ").replace("not(", "(not ")
        expr = expr.replace(") ", ")").replace("  ", " ")  # Remove extra spaces and adjust closing parentheses

        # Encapsulate the entire expression with an additional set of parentheses if not already present
        #if not expr.startswith("("):
        #    expr = f"({expr})"

        if "(true)" in expr:
            expr = "true"
        if "(false)" in expr:
            expr = "false"

        return expr


    def simplify_symbol_repr(self, expression_str):
        # Replace Symbol('...') with '...'
        return re.sub(r"Symbol\('([^']+)'\)", r"\1", expression_str)
        
    def plotGraph(self):
        import matplotlib.pyplot as plt        

        icl_graph = self.icl_graph
        assert(icl_graph)

        #print(icl_graph)
        # Spring layout
        #pos = nx.spring_layout(icl_graph)
        # You can try other layouts like:
        # pos = nx.circular_layout(icl_graph)
        pos = nx.kamada_kawai_layout(icl_graph)
        # pos = nx.spectral_layout(icl_graph)

        # Extracting the color attribute for each node
        node_colors = [data['color'] if "color" in data else "gray" for node, data in icl_graph.nodes(data=True)]

        nx.draw(icl_graph, pos, with_labels=True, node_size=1500, node_color=node_colors, font_size=10, font_weight="bold")

        edge_labels = nx.get_edge_attributes(icl_graph, 'sel')
        nx.draw_networkx_edge_labels(icl_graph, pos, edge_labels=edge_labels)

        #nx.draw(icl_graph, with_labels=True)
        plt.show()  # Display the graph

    def create_retageter(self, scan_path_graph: nx.DiGraph):

        # Extract all scan reg. nodes that pariticipate in scan path reconfiguration
        control_bits: list[str] = []
        for node in scan_path_graph.nodes(data=True):
            node_data = node[1]  # Addional information about scan path node

            if "expr_py" in node_data: 
                temp = set(re.findall(r"[\w.]+\d+", node_data["expr_py"]))
                control_bits += temp

        control_bits = sorted(set(control_bits))
        print("Scan reg. nodes that pariticipate in scan path reconfiguration:", control_bits)

        # Gather information about muxes, muxs selections and scan registers for retargeting solver
        # reg_map = {}
        sel_muxes_smt = {}
        for node in scan_path_graph.nodes(data=True):
            node_name = node[0]  # Name of scan path node
            node_data = node[1]  # Addional information about scan path node

            # print("node_name", node_name)           
            # print("node_data", node_data)
            
            if node_data["icl_type"] == "mux":
                pass
                #reg_map[node_name] = (node_data["expr_smt"], 2) 
            elif node_data["icl_type"] == "mux_sel":
                sel_muxes_smt[node_name] = node_data["expr_smt"]
            elif node_data["icl_type"] == "reg":
                ctrl_bit = 1 if node_name in control_bits else 0
                #reg_map[node_name] = (node_data["expr_smt"], ctrl_bit)

            #if "expr_py" in node_data:
            #    print(f"Node name: {node_name}, Data: {node_data['expr_py']}, Connections: {connections}")


        #print("Regs and muxes:")
        #for name, map_item in reg_map.items():
        #    print(name, map_item)

        #print("Select of a mux:")
        #for name, map_item in sel_muxes_smt.items():
        #    print(name, map_item)

        self.first_nodes = [node for node, degree in scan_path_graph.in_degree() if degree == 0]
        self.last_nodes = [node for node, degree in scan_path_graph.out_degree() if degree == 0]

        print("First Node:", self.first_nodes)
        print("Last Node:",  self.last_nodes) 

        ono_hot_data_groups: list = []

        # Only allow one data out to be active in one cylce
        ono_hot_data_out = smtOneHotGroup()
        ono_hot_data_out.one_hot_bits = self.last_nodes
        ono_hot_data_groups.append(ono_hot_data_out)
        
        self.icl_graph = scan_path_graph
        
        return IclRetargeting(self.scan_registers, self.data_registers_smt, sel_muxes_smt, ono_hot_data_groups, self.ir_out_names, 6)
    
    def iReset(self):
        for _ ,reg in self.scan_registers.items():
            reg.reset()
        for _ ,reg in self.data_registers.items():
            reg.reset()

    def iWrite(self, name: str, value: int):
        print(f"iWrite {name} {value}")

        if(name in self.scan_registers):
            scan_register: IclScanRegister = self.scan_registers[name]
            scan_register.set_next_value(value)
            scan_register.set_next_iapply()
        elif(name in self.data_registers): 
            data_register: IclDataRegister = self.data_registers[name]
            data_register.set_next_value(value)
            data_register.set_next_write_iapply()       
        else:
            raise ValueError("iWrite register: {} not found in ICL register model".format(name))

    def iRead(self, name: str, value: int):
        print(f"iRead {name} {value}")

        if(name in self.scan_registers):
            scan_register: IclScanRegister = self.scan_registers[name]

            # TODO: For now we assume all data bits need to be read
            scan_register.set_read_bits((1 << scan_register.scan_reg_size) - 1)

            scan_register.set_expected_bits(value)
            scan_register.set_next_iapply()
        elif(name in self.data_registers): 
            data_register: IclDataRegister = self.data_registers[name]

            # TODO: For now we assume all data bits need to be read
            data_register.set_read_bits((1 << data_register.data_reg_size) - 1)

            data_register.set_expected_bits(value)
            data_register.set_next_read_iapply()       
        else:
            raise ValueError("iRead register: {} not found in ICL register model".format(name))
        


    def iApply(self) -> bool:
        print("iApply")
        self.jtag_steps = []
        network_start = {}
        network_end = {}
        network_other = {}

        #reg:IclScanRegister = self.icl_instance.get_icl_item_name("u_tap.ir")
        #print(reg.get_name_with_hier(),  reg.get_all_named_indexes(), (reg.current_value), "direction", reg.scan_reg.get_direction())

        #reg:IclScanRegister = self.icl_instance.get_icl_item_name("u_nvm_atc_cut_9.mem_inst.address")
        #print(reg.get_name_with_hier(),  reg.get_all_named_indexes(), (reg.current_value), "direction", reg.scan_reg.get_direction())
        
        for _ ,scan_reg in self.scan_registers.items():
            scan_reg: IclScanRegister = scan_reg
            reg_bits:list[str] = scan_reg.get_all_named_indexes()
            size = len(reg_bits) - 1
            direction:bool = scan_reg.scan_reg.get_direction()
            for idx, reg_bit in enumerate(reg_bits):
                reg_bit = reg_bit.replace('.', '_')
                network_start[reg_bit] = scan_reg.current_value.get_bin_bit_str(size - idx) if direction else scan_reg.current_value.get_bin_bit_str(idx)

                #if(scan_reg.get_name_with_hier() == "u_tap.ir"):
                #    print(reg_bit, idx, scan_reg, network_start[reg_bit])

                if(scan_reg.is_in_next_iapply()):
                    network_end[reg_bit] = scan_reg.next_value.get_bin_bit_str(size - idx) if direction else scan_reg.next_value.get_bin_bit_str(idx)
                    # print(reg_bit, idx, reg, network_start[reg_bit], "->", network_end[reg_bit])
                    network_other[f"sel_group_{scan_reg.get_name_with_hier()}"] = 1
                    
        for _ ,reg in self.data_registers.items():
            reg: IclDataRegister = reg
            reg_bits:list[str] = reg.get_all_named_indexes()
            size = len(reg_bits) - 1
            direction:bool = reg.icl_name.get_direction()
            for idx, reg_bit in enumerate(reg_bits):
                reg_bit = reg_bit.replace('.', '_')
                read_indication_bit = f"read_{reg_bit}"

                network_start[reg_bit] = reg.current_value.get_bin_bit_str(size - idx) if direction else reg.current_value.get_bin_bit_str(idx)
                network_start[read_indication_bit] = reg.bits_to_read.get_bin_bit_str(size - idx) if direction else reg.bits_to_read.get_bin_bit_str(idx)

                #if(reg.get_name_with_hier() == "u_tap.ir"):
                #    print(reg_bit, idx, reg, network_start[reg_bit])

                if(reg.is_in_next_read_iapply()):
                    network_end[read_indication_bit] = "0"
                    network_end[reg_bit] = reg.next_value.get_bin_bit_str(size - idx) if direction else reg.next_value.get_bin_bit_str(idx)

                if(reg.is_in_next_write_iapply()):
                    network_end[reg_bit] = reg.next_value.get_bin_bit_str(size - idx) if direction else reg.next_value.get_bin_bit_str(idx)

                    # print(reg_bit, idx, reg, network_start[reg_bit], "->", network_end[reg_bit])
                    network_other[f"sel_group_data_reg_written_{reg.get_name_with_hier()}".replace('.', '_')] = 1

        #for name, reg_bit in self.registers_smt.items():
        #    print(name, reg_bit)
        #print(network_start)
        #print(network_end)

        self.retargeter.retarget(network_start, network_end, network_other)
        steps = self.retargeter.get_steps()

        vectors = {}
        # print("steps", steps)
        for step in steps:
            jtag_step: jtagStep = jtagStep()

            if(step == 0):
                continue

            from_data = step-1
            to_data =   step
            jtag_step.step = step
   
            # Determine if current data chain is DR or IR
            jtag_step.type_of_chain = "IR" if (self.retargeter.get_bit(self.retargeter.C_IR_DR_STATE, from_data)) else "DR"

            # Determine which scan_in -> scan_out is used
            used_tdo_name = ""
            for tdo_name in self.last_nodes:
                if(self.retargeter.get_bit(tdo_name, to_data)):
                    used_tdo_name = tdo_name
                    break
            assert(used_tdo_name != "")
            jtag_step.tdo_port = used_tdo_name


            # Get DR/IR chain of current data
            reg_bit_name_list, vector_string = self.traverse_graph_2(used_tdo_name, self.icl_graph, self.retargeter, from_data, from_data)
            print(f'FROM -> Type: {jtag_step.type_of_chain}, vector {vector_string}, step: {step}, scan_regs: {compress_signal_list(reg_bit_name_list)}')

            # Get DR/IR chain of new data
            reg_bit_name_list, vector_string = self.traverse_graph_2(used_tdo_name, self.icl_graph, self.retargeter, from_data, to_data)
            print(f'TO   -> Type: {jtag_step.type_of_chain}, vector {vector_string}, step: {step}, scan_regs: {compress_signal_list(reg_bit_name_list)}')
            jtag_step.in_data = vector_string
            jtag_step.in_data_names = reg_bit_name_list

            # Get TDI PORT
            in_nodes = [reg_bit_name_list[0]]
            while(len(in_nodes) > 0):
                tmp = in_nodes.pop()
                for pred in self.icl_graph.predecessors(tmp):
                    in_nodes.append(pred)
            jtag_step.tdi_port = tmp

            # Get data reg bit read chain, where it indicate if bit contatins any read data from data register
            data_reg_bit_read_list = []
            debug = []
            #print(self.tdr_bit_data_reg_read_sink)
            for reg_bit_name in reg_bit_name_list:
                #print(reg_bit_name)
                valid_read_paths = 0
                if(reg_bit_name in self.tdr_bit_data_reg_read_sink):
                    tmp = []
                    true_data_source = "-"
                    for data_source in self.tdr_bit_data_reg_read_sink[reg_bit_name]:
                        read: bool = False
                        read_path_en: bool = False   
                        first: bool = self.retargeter.get_bit(f"read_{data_source}", from_data)
                        second: bool = self.retargeter.get_bit(f"read_{data_source}", to_data)
                        if(first and (not second)):
                            read = True
                            for tdr_bit, path_expression in self.tdr_sink_of_data_reg[data_source]:
                                if(reg_bit_name == tdr_bit):
                                    read_path_en = self.solve_simple_expression(path_expression, to_data)
                                    if(read_path_en):
                                        valid_read_paths += 1
                                        true_data_source = data_source

                        tmp.append((data_source, read, read_path_en))
                    debug.append(f"{reg_bit_name} - {tmp}")

                    assert(valid_read_paths in [0,1])
                    data_reg_bit_read_list.append(true_data_source)
                else:
                    data_reg_bit_read_list.append("-")
                    debug.append("-")
            print(f"data_reg_bit_read_list -> {compress_signal_list(data_reg_bit_read_list)}")
            #print(f"data_reg_bit_read_list -> {debug}")
            jtag_step.read_data_bit_names = data_reg_bit_read_list

            # Get expected read data
            data_reg_read_vector = []
            for read_bit in jtag_step.read_data_bit_names:
                if(read_bit == "-"):
                    data_reg_read_vector.append("X")
                else:
                    icl_item_idx: int = get_last_number(read_bit)
                    data_reg: IclDataRegister = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(read_bit))
                    expected_value : IclNumber = data_reg.get_expected_bits()
                    bits_to_read : IclNumber = data_reg.get_bits_to_read()

                    if(bits_to_read.get_bin_bit_str(icl_item_idx) == "1"):
                        bits_to_read.set_bit(0, icl_item_idx)
                        data_reg_read_vector.append(expected_value.get_bin_bit_str(icl_item_idx))
                    else:
                        data_reg_read_vector.append("X")

            test_reg_read_vector = []
            for read_bit in jtag_step.in_data_names:
                    icl_item_idx: int = get_last_number(read_bit)
                    scan_reg: IclScanRegister = self.icl_instance.get_icl_item_name(self.remove_trailing_numbers(read_bit))
                    expected_value : IclNumber = scan_reg.get_expected_bits()
                    bits_to_read : IclNumber = scan_reg.get_bits_to_read()
                    if(bits_to_read.get_bin_bit_str(icl_item_idx) == "1"):
                        bits_to_read.set_bit(0, icl_item_idx)
                        test_reg_read_vector.append(expected_value.get_bin_bit_str(icl_item_idx))
                    else:
                        test_reg_read_vector.append("X")

            final_read_vector = []
            for idx, test_reg_bit in enumerate(test_reg_read_vector):
                data_reg_bit = data_reg_read_vector[idx]
                if(test_reg_bit == "X"):
                    final_read_vector.append(data_reg_bit)
                elif(test_reg_bit in ["1"]):
                    final_read_vector.append(test_reg_bit)
                    assert(data_reg_bit != 0)
                elif(test_reg_bit in ["0"]):
                    final_read_vector.append(test_reg_bit)
                    assert(data_reg_bit != 1)

            final_read_vector = "".join(final_read_vector)
            jtag_step.exp_data = final_read_vector
            print(f"jtag_step.exp_data -> {jtag_step.exp_data}")                    

            # print(f"from u_regs_rosc_cut_lvt.u_sib_data.sib_0000 -> {self.retargeter.get_bit('u_regs_rosc_cut_lvt.u_sib_data.sib_0000', from_data)}")
            # print(f"to   u_regs_rosc_cut_lvt.u_sib_data.sib_0000 -> {self.retargeter.get_bit('u_regs_rosc_cut_lvt.u_sib_data.sib_0000', to_data)}")
            # print(f"from sel_u_regs_rosc_cut_lvt.u_sib_data.sib_0000 -> {self.retargeter.get_bit('sel_u_regs_rosc_cut_lvt.u_sib_data.sib_0000', from_data)}")
            # print(f"to   sel_u_regs_rosc_cut_lvt.u_sib_data.sib_0000 -> {self.retargeter.get_bit('sel_u_regs_rosc_cut_lvt.u_sib_data.sib_0000', to_data)}")

            # Update scan registers
            idx = 0
            for name in reg_bit_name_list:
                reg_name = re.search(r'(.+?)_(\d+)$', name).group(1)
                number = re.findall(r'\d+', name)[-1]
                # print(reg_name, number, int(vector_string[idx]))
                if(reg_name in self.scan_registers):
                    self.scan_registers[reg_name].set_current_bit(int(vector_string[idx]), int(number))
                    self.scan_registers[reg_name].set_next_bit(int(vector_string[idx]), int(number))
                else:
                    raise ValueError(f"Register name: {reg_name}, not found")
                idx += 1
        
            self.jtag_steps.append(jtag_step)

        # Clear any iWrite to do Flag
        for _ ,reg in self.scan_registers.items():
            reg: IclScanRegister = reg
            reg.disable_next_iapply()

        for _ ,reg in self.data_registers.items():
            reg: IclDataRegister = reg
            if(reg.is_in_next_write_iapply()):
                reg.disable_next_write_iapply()
                reg.set_next_value_to_current()

            reg.set_read_bits(0)
            reg.set_expected_bits(0)
            reg.disable_next_read_iapply()

        return vectors
    
    # Get vectors that iApply calculated
    def getiApplyVectors(self) -> list[jtagStep]:
        return self.jtag_steps

    def traverse_graph_2(self, start_node, icl_graph, data, from_step, to_step):
        reg_name_sequence = []
        reg_bit_sequence = []

        stack = [start_node]
        
        while stack:
            node = stack.pop()
            node_type = icl_graph.nodes[node]["icl_type"]
            in_nodes = [pred for pred in icl_graph.predecessors(node)]

            #print("traverse node", node, stack, "in_nodes", in_nodes, node_type, "val", data.get_bit(node, from_step), data.get_bit(node, to_step))

            if(node_type == "reg"):
                reg_name_sequence.append(node)
                #print(step, node)
                reg_bit_sequence.append(data.get_bit(node, to_step))
            elif(node_type == "mux_sel"):
                if(data.get_bit(node, from_step)):
                    stack = []
                else:
                    continue
            # Reverse the order to maintain the original call order in recursive version
            for next_node in reversed(in_nodes):
                stack.append((next_node))        
        #print(reg_bit_sequence)
        reg_name_sequence.reverse()
        reg_bit_sequence.reverse()
        return (reg_name_sequence, "".join(["1" if bit else "0" for bit in reg_bit_sequence]))



    # Solve simple SMT expression, variable values are extracted from retargeter of given step
    # and then whole expression is evaluated
    # Example:
    #   "(and (not tdr_addr_0000))" -> bool(1/0)
    def solve_simple_expression(self, expression, step) -> bool:  
        expression_with_values = self.fill_expression_with_values(expression, step)
        tokens = tokenize(expression_with_values)
        #print(tokens)
        parsed = parse(tokens)
        #print(parsed)
        return eval_sexpr(parsed)

    def fill_expression_with_values(self, expression, step):
        def modify_piece(match):
            piece = match.group(0)
            return f'{self.retargeter.get_bit(piece, step)}'

        return re.sub(r'[a-zA-Z_.0-9]+_[0-9]{4,}', modify_piece, expression)


def tokenize(s):
    # space out parentheses then split
    return s.replace('(', ' ( ').replace(')', ' ) ').split()

def parse(tokens):
    if not tokens:
        raise ValueError("Unexpected EOF")
    token = tokens.pop(0)
    if token == '(':
        lst = []
        while tokens[0] != ')':
            lst.append(parse(tokens))
        tokens.pop(0)  # remove ')'
        return lst
    elif token == ')':
        raise ValueError("Unexpected )")
    else:
        if(token in ["True", "true", "False", "False"]):
            return bool(token)
        else:
            return token

def eval_sexpr(node):
    # node is either int or a list like ['and', ...]
    if isinstance(node, bool):
        return node
    if not isinstance(node, list) or not node:
        raise ValueError("Invalid node: " + repr(node))

    op = node[0]
    args = node[1:]

    if op == 'and':
        for a in args:
            if eval_sexpr(a) == 0:
                return bool(0)
        return bool(1)
    elif op == 'not':
        assert(len(node) == 2)
        if eval_sexpr(node[1]) == 0:
            return bool(0)
        else:
            return bool(1) 
    elif op == 'or':
        for a in args:
            if eval_sexpr(a) == 1:
                return bool(1)
        return bool(0)
    else:
        raise ValueError(f"Unsupported operator: {op}")
    
import re

def compress_signal_list(signals):
    result = []
    n = len(signals)
    i = 0

    while i < n:
        if signals[i] == "-":
            # Count consecutive '-'
            start = i
            while i < n and signals[i] == "-":
                i += 1
            count = i - start - 1
            result.append(f"-( {count}:0 )" if count > 0 else "-(0)")
        else:
            # Collect consecutive non-dash signals
            start = i
            while i < n and signals[i] != "-":
                i += 1
            segment = signals[start:i]

            # Group signals by prefix (before numeric suffix)
            groups = {}
            for sig in segment:
                match = re.match(r"(.+?)(\d+)$", sig)
                if match:
                    prefix = match.group(1)
                    num = int(match.group(2))
                    groups.setdefault(prefix, []).append(num)
                else:
                    groups.setdefault(sig, [])

            # Create condensed forms, preserving natural order
            for prefix, nums in groups.items():
                if nums:
                    # Determine if sequence is ascending or descending
                    if nums == sorted(nums):
                        result.append(f"{prefix}({min(nums)}:{max(nums)})")
                    else:
                        result.append(f"{prefix}({max(nums)}:{min(nums)})")
                else:
                    result.append(prefix)

    # Clean up spacing
    return [r.replace(" ", "") for r in result]
