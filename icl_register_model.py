

import matplotlib.pyplot as plt
import networkx as nx

from sympy import sympify, srepr, simplify_logic
from icl_retargeting import IclRetargeting
from icl_items import *
import re

class IclRegisterModel():

    def __init__(self, icl_instance: IclInstance) -> None:
        self.icl_instance = icl_instance
        self.icl_graph = None
        # dict[string: IclRegister]

        self.retargeter = None
        self.registers = {}
        self.registers_smt = {}
        self.sel_muxes_smt = {}
        self.first_nodes = []
        self.last_nodes = []


        icl_graph = nx.DiGraph()
        eval_list = icl_instance.list_instances()
        for item in eval_list:
            print(item)

        for item in eval_list:
            _, _ = item.popitem()
            _, instance = item.popitem()
            
            # ICL network connection creation
            for icl_item in instance.icl_items:
                if(type(icl_item) == IclScanInPort):
                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node, icl_type="scan_port", color="green")



                if(type(icl_item) == IclScanOutPort):
                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node, icl_type="scan_port", color="green")

                    source_idxes = icl_item.get_named_sourced_indexes()
                    port_idxes = icl_item.get_all_named_indexes()
                    result = [list(pair) for pair in zip(source_idxes, port_idxes)]
                    for a in result:
                        icl_graph.add_edge(a[0],a[1])  



                if(type(icl_item) == IclDataInPort):
                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node, icl_type="data_port", color="lightgreen")



                if(type(icl_item) == IclDataOutPort):
                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node, icl_type="data_port", color="lightgreen")

                    source_idxes = icl_item.get_named_sourced_indexes()
                    port_idxes = icl_item.get_all_named_indexes()
                    result = [list(pair) for pair in zip(source_idxes, port_idxes)]
                    for a in result:
                        icl_graph.add_edge(a[0],a[1])  
                        


                if(type(icl_item) == IclScanRegister):
                 
                    full_name = icl_item.get_name_with_hier()
                    self.registers[full_name] = icl_item

                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node, icl_type="reg", color="red")

                    named_indexes = icl_item.get_all_named_indexes()
                    pairs = list(zip(named_indexes, named_indexes[1:]))
                    print(pairs)                    
                    for pair in pairs:
                        icl_graph.add_edge(pair[0], pair[1])
                        
                    if(icl_item.scan_in):
                        print(instance.__dict__)
                        print(icl_item.__dict__)
                        print("type", type(icl_item.scan_in))
                        scan_from = icl_item.get_scanin_named_index()
                        scan_to = icl_item.get_named_msb()
                        print(scan_from, scan_to)
                        icl_graph.add_edge(scan_from, scan_to)


                    #if(icl_item.capture_source):
                    #    capture = icl_item.capture_source.get_all_named_indexes(icl_item.get_vector_size())
                    #    result = [list(pair) for pair in zip(named_indexes, capture)]
                    #    
                    #    for a in result:
                    #        icl_graph.add_edge(a[1],a[0])
                    #    print(result)                    

                    icl_graph.add_edge(icl_item.get_scanin_named_index(), icl_item.get_named_msb())    
                    print(icl_item.get_scanin_named_index(), icl_item.get_named_msb())                    


                if(type(icl_item) == IclScanMux):
                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node, icl_type="mux", color="blue", mux=1)

                    idx = 0
                    for a,b, expr_smt, expr_py in icl_item.get_all_connections():
                        print(expr_smt)
                        link = "sel_{}_{}".format(idx, b)
                        icl_graph.add_node(link, icl_type="mux_sel", color="lightblue", expr_smt=expr_smt, expr_py=expr_py)
                        icl_graph.add_edge(a, link)
                        icl_graph.add_edge(link, b) 
                        idx += 1   



                if(type(icl_item) == IclInstance):
                    for connection in icl_item.connections:
                        for to_sig, from_sig in connection.items():
                            print(icl_item, to_sig, from_sig, instance)
                            print(from_sig.concat_sigs)
                            x = instance.get_signal_all_named_indexes(icl_item, [to_sig])
                            y = instance.get_signal_all_named_indexes(instance, from_sig.concat_sigs)
                            assert(len(x) == len(y))
                            result = [list(pair) for pair in zip(x, y)]
                            print(result)
                            for a in result:
                                icl_graph.add_edge(a[1], a[0])    

        for a in icl_graph:
            in_nodes = [pred for pred in icl_graph.predecessors(a)]
            out_nodes = [succ for succ in icl_graph.successors(a)]
            print(a, in_nodes, out_nodes)         



        def traverse_iterative(start_node, sel):
            print("\n traverse_iterative start", start_node)
            
            node_visits = {}
            stack = [(start_node, sel)]
            
            while stack:
                node, sel = stack.pop()
                print("traverse", node, "stack", stack)
               
                if node in node_visits:
                    node_visits[node] += 1
                else:
                    node_visits[node] = 1
                

                in_nodes = []
                for pred in icl_graph.predecessors(node):
                    #print("icl_type icl_type icl_type icl_type", node, pred,  icl_graph.nodes[pred])                                  
                    node_type = icl_graph.nodes[pred]["icl_type"]
                    if (node_type != "data_port"):
                        in_nodes.append(pred)

                out_nodes = []
                for succ in icl_graph.successors(node):
                    node_type = icl_graph.nodes[succ]["icl_type"]
                    if (node_type != "data_port"):
                        out_nodes.append(succ)
                                                        
                #in_nodes = [pred for pred in icl_graph.predecessors(node)]
                #out_nodes = [succ for succ in icl_graph.successors(node)]
                out_node_num = len(out_nodes)

                print(in_nodes, out_nodes, node_visits[node])

                if "sel_py_items" in icl_graph.nodes[node]:
                    icl_graph.nodes[node]["sel_py_items"].append(sel)
                else:
                    icl_graph.nodes[node]["sel_py_items"] = [sel]

                #if(icl_graph.nodes[node]["icl_type"] == "data_port"):
                #    continue

                if out_node_num > 0:
                    assert(node_visits[node] <= out_node_num)
                    if node_visits[node] != out_node_num:
                        print(node_visits[node], out_node_num)
                        continue

                if "expr_py" in icl_graph.nodes[node]:
                    icl_graph.nodes[node]["sel_py_items"].append(icl_graph.nodes[node]["expr_py"])

                if len(icl_graph.nodes[node]["sel_py_items"]) > 1:
                    if out_node_num in [0, 1]:
                        icl_graph.nodes[node]["expr_py"] = "And({})".format(",".join(icl_graph.nodes[node]["sel_py_items"]))
                    else:
                        icl_graph.nodes[node]["expr_py"] = "Or({})".format(",".join(icl_graph.nodes[node]["sel_py_items"]))
                else:
                    icl_graph.nodes[node]["expr_py"] = "".join(icl_graph.nodes[node]["sel_py_items"])



                icl_graph.nodes[node]["expr_py"] = self.simplify_symbol_repr(srepr(simplify_logic(sympify(icl_graph.nodes[node]["expr_py"]))))
                icl_graph.nodes[node]["expr_smt"] = self.refine_to_smt2(icl_graph.nodes[node]["expr_py"])
                icl_graph.nodes[node]["sel_py_items"] = []
                print(icl_graph.nodes[node])

                # Reverse the order to maintain the original call order in recursive version
                for next_node in reversed(in_nodes):
                    stack.append((next_node, icl_graph.nodes[node]["expr_py"]))

        last_scan_port_nodes = []
        for node, degree in icl_graph.out_degree():
            try:
                node_type = icl_graph.nodes[node]["icl_type"]
                if (node_type == "scan_port" and degree == 0):
                    last_scan_port_nodes.append(node)
            except:
                pass
        print(last_scan_port_nodes)     
        

              
        for last_node in last_scan_port_nodes:
            traverse_iterative(last_node, "true")
            
        self.plotGraph(icl_graph)


        
        control_bits = []
        node_info = {}

        for node in icl_graph.nodes(data=True):
            node_id = node[0]  # Node ID
            node_data = node[1]  # Node data (attributes)
            neighbors = list(icl_graph.neighbors(node_id))  # Get neighbors (connections)
            node_info[node_id] = {'data': node_data, 'connections': neighbors}

            if "expr_py" not in node_data:
                continue
            
            temp = set(re.findall(r"\b[A-Za-z_]\w*\b", node_data["expr_py"]))
            function_names = {"Or", "And", "Not", "true", "false"}
            temp = list(temp - function_names)
            control_bits += temp
        control_bits = set(control_bits)
        print("control bits", control_bits)

        # Print the information
        reg_map = {}
        for node_id, info in node_info.items():
            if info['data']["icl_type"] == "mux":
                reg_map[node_id] = (info['data']["expr_smt"], 2) 
            elif info['data']["icl_type"] == "mux_sel":
                self.sel_muxes_smt[node_id] = info['data']["expr_smt"]
            elif info['data']["icl_type"] == "reg":
                ctrl_bit = 1 if node_id in control_bits else 0
                reg_map[node_id] = (info['data']["expr_smt"], ctrl_bit)
                self.registers_smt[node_id] = reg_map[node_id]
            if "expr_py" not in info['data']:
                continue
                            
            print(f"Node {node_id}: Data = {info['data']['expr_py']}, Connections = {info['connections']}")

        for name, map_item in reg_map.items():
            print(name, map_item)

        self.first_nodes = [node for node, degree in icl_graph.in_degree() if degree == 0]
        self.last_nodes = [node for node, degree in icl_graph.out_degree() if degree == 0]

        print("First Node:", self.first_nodes)
        print("Last Node:",  self.last_nodes)
        
        
        self.icl_graph = icl_graph
        self.retargeter = IclRetargeting(self.registers_smt, self.sel_muxes_smt, 10)



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
        if not expr.startswith("("):
            expr = f"({expr})"

        if "(true)" in expr:
            expr = "true"

        return expr




    def simplify_symbol_repr(self, expression_str):
        # Replace Symbol('...') with '...'
        return re.sub(r"Symbol\('([^']+)'\)", r"\1", expression_str)
        
    def plotGraph(self, icl_graph=None):
        if(not icl_graph):
            icl_graph = self.icl_graph

        print(icl_graph)
        # Spring layout
        # pos = nx.spring_layout(icl_graph)
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

    def traverse_graph(self, start_node, icl_graph, from_data, to_data):
        reg_name_sequence = []
        reg_bit_sequence = []

        stack = [start_node]
        
        while stack:
            node = stack.pop()
            #print("traverse node", node, stack)

            in_nodes = [pred for pred in icl_graph.predecessors(node)]

            node_type = icl_graph.nodes[node]["icl_type"]
            if(node_type == "reg"):
                reg_name_sequence.append(node)
                #print(step, node)
                reg_bit_sequence.append(to_data[node])
            elif(node_type == "mux_sel"):
                if(from_data[node]):
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
    
    def traverse_graph_2(self, start_node, icl_graph, data, from_step, to_step):
        reg_name_sequence = []
        reg_bit_sequence = []

        stack = [start_node]
        
        while stack:
            node = stack.pop()
            #print("traverse node", node, stack)

            in_nodes = [pred for pred in icl_graph.predecessors(node)]

            node_type = icl_graph.nodes[node]["icl_type"]
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
        
    def iReset(self):
        for _ ,reg in self.registers.items():
            reg.reset()

    def iWrite(self, name: str, value: int):
        if(name in self.registers):
            self.registers[name].set_next_value(value)
        else:
            raise ValueError("iWrite register: {} not found in ICL register model".format(name))
    
    def iApply(self) -> bool:
        network_start = {}
        network_end = {}
        
        for _ ,reg in self.registers.items():
            reg_bits = reg.get_all_named_indexes()
            for idx, reg_bit in enumerate(reg_bits):
                reg_bit = reg_bit.replace('.', '_')
                print(reg_bit, idx, reg, reg.current_value)
                network_start[reg_bit] = reg.current_value.get_bin_bit_str(idx)
                network_end[reg_bit] = reg.next_value.get_bin_bit_str(idx)                
        
        #for name, reg_bit in self.registers_smt.items():
        #    print(name, reg_bit)
        #print(network_start)
        #print(network_end)

        self.retargeter.retarget(network_start, network_end)
        steps = self.retargeter.get_steps()
        
        vectors = {}
        for step in steps:
            if(step == 0):
                from_data = step
                to_data =   step
                reg_bit_name_list, vector_string = self.traverse_graph_2("TDO_0000", self.icl_graph, self.retargeter, from_data, to_data)
                print(step, reg_bit_name_list, vector_string)
                continue
            else:
                from_data = step-1
                to_data =   step
                reg_bit_name_list, vector_string = self.traverse_graph_2("TDO_0000", self.icl_graph, self.retargeter, from_data, to_data)
                print(step, reg_bit_name_list, vector_string)
                vectors[step] = vector_string

            idx = 0
            for name in reg_bit_name_list:
                reg_name = re.search(r'(.+?)_(\d+)$', name).group(1)
                number = re.findall(r'\d+', name)[-1]
                self.registers[reg_name].set_current_bit(int(vector_string[idx]), int(number))
                self.registers[reg_name].set_next_bit(int(vector_string[idx]), int(number))

                idx += 1
        return vectors