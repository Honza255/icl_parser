from typing import Any

from icl_number import *
from icl_signal import *

class IclItem:

    def __init__(self, icl_name: str, icl_hier: str, module_scope: str, ctx) -> None:
        self.ctx = ctx
        self.name = icl_name
        self.hier = icl_hier
        self.module_scope = module_scope
        self.icl_items = []
        
    def get_hier(self) -> str:    
        return self.hier

    def get_name(self):
        return self.name
    
    def get_module_scope(self):
        return self.module_scope
       
    def get_name_with_hier(self):
        return "{}.{}".format(self.hier, self.name) if self.hier else self.name 

    def get_item_all_indexes(self, icl_sig: IclSignal) -> list[int]:
        if(type(icl_sig) == list):
            indexes = [port.get_indexes() for port in self.ports]
            all_numbers = [num if num else 0 for sublist in indexes for num in sublist]      
        else:
            all_numbers = icl_sig.get_indexes()
            if(not all_numbers):
                all_numbers = [0]
        all_numbers.sort()
        return all_numbers
    
    def get_item_all_named_indexes(self, icl_sig: IclSignal) -> list[str]:
        named_indexes = []
        for index in self.get_item_all_indexes(icl_sig):
            named_indexes.append("{}_{}".format(self.get_name_with_hier(),index))
        named_indexes.sort()
        return named_indexes
    
    def get_signal_all_named_indexes(self, instance, all_sigs: list[list[IclSignal]]) -> list[str]:
        named_indexes = []
        for source_signal in all_sigs:
            indexes = []
            source_signal_name = source_signal.get_relative_name()
            # Get Item(fails if item is not found)
            source_item = instance.get_icl_item_name(source_signal_name)  

            if(source_signal.get_size()):
                indexes = source_signal.get_indexes()
            else:
                for index in range(source_item.get_vector_size()):
                    indexes.append(index)
            indexes.sort()
            for index in indexes:
                named_indexes.append("{}_{}".format(source_item.get_name_with_hier(),index))
                            
        return named_indexes
    
             
class IclInstance(IclItem):

    def __init__(self, icl_name: str, icl_hier: str, module_scope: str, ctx) -> None:
        super().__init__(icl_name, icl_hier, module_scope, ctx)
        self.attributes = {}
        self.connections = []
        self.parameters_override = {}
        self.parameters = {}

    def add_icl_item(self, icl_item: IclItem):
        for curr_icl_item in self.icl_items:
            if curr_icl_item.get_name() == icl_item.get_name:
                raise ValueError("ICL item {} already exists in instane of {} modue {}".format(curr_icl_item.get_name(), self.get_name(), self.get_module_scope()))
        self.icl_items.append(icl_item)

    def get_icl_item_name(self, name: str) -> IclItem:
        name_seq = name.split(".")
        while(len(name_seq) > 0):
            item_to_search = name_seq.pop(0)
            for icl_item in self.icl_items:
                if icl_item.get_name() == item_to_search:
                    if(len(name_seq) == 0):
                        return icl_item
                    else:
                        return icl_item.get_icl_item_name(".".join(name_seq))
            raise ValueError("Item {} not found in instace of {} module {}".format(name,self.get_name(), self.get_module_scope()))
    
    def get_icl_item_type(self, item_type) -> list[IclItem]:
        icl_items = []
        for item in self.icl_items:
            if(item_type == type(item)):
                icl_items.append(item)
        return icl_items
    
    def add_parameter_override(self, name, value):
        if(self.parameters_override == {}):
            self.parameters_override = {}

        if(name in self.parameters_override):
            raise ValueError("Parameter override already defined in current module")
        else:
            self.parameters_override[name] = value

    def get_parameter_override(self, name):
        if(self.parameters_override == {}):
            self.parameters_override = {}

        if(name in self.parameters_override):
            return self.parameters_override[name]
        else:
            return {}

    def add_parameter(self, name, value):
        if(self.parameters == {}):
            self.parameters = {}

        if(name in self.parameters):
            print(self)
            raise ValueError("Parameter already defined in current module")
        else:
            if(name in self.parameters_override):
                if(type(self.parameters_override[name]) != type(value)):
                    print(self)
                    raise ValueError(
                        type(self.parameters_override[name]),
                        type(value),                        
                        "Parameter override is diffrent type than parameter"
                     )
            self.parameters[name] = value
    
    def get_parameter(self, name):
        if(self.parameters == {}):
            self.parameters = {}

        if(name in self.parameters):
            return self.parameters[name]
        else:
            return {}
        

    def add_attribute(self, attr_name, attr_data):
        if(attr_name in self.attributes):
            raise ValueError("Attribut {} instatenation for instane {} already defiend".format(attr_name,self.get_name()))         
        else:
            self.attributes[attr_name] = attr_data
    
    def add_connection(self, conn: dict[IclSignal:IclSignal]):
        self.connections.append(conn)

    def check(self):
        for item in self.icl_items:
            item.check()

    def create_tree_diagram(self):
        import matplotlib.pyplot as plt  # Import Matplotlib
        import networkx as nx
        icl_graph = nx.Graph()  

        eval_list = self.list_instances()
        for item in eval_list:
            print(item)

        for item in eval_list:
            _, _ = item.popitem()
            _, instance = item.popitem()
            
            # ICL network connection creation
            for icl_item in instance.icl_items:
                if(type(icl_item) == IclScanInPort):
                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node)

                if(type(icl_item) == IclScanOutPort or type(icl_item) == IclDataOutPort):
                    source_idxes = icl_item.get_named_sourced_indexes()
                    port_idxes = icl_item.get_all_named_indexes()
                    result = [list(pair) for pair in zip(source_idxes, port_idxes)]
                    print(result)                    
                    for a in result:
                        icl_graph.add_edge(a[0],a[1])  

                if(type(icl_item) == IclDataInPort):
                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node)

                if(type(icl_item) == IclScanRegister):
                    named_indexes = icl_item.get_all_named_indexes()
                    pairs = list(zip(named_indexes, named_indexes[1:]))
                    print(pairs)                    
                    for pair in pairs:
                        icl_graph.add_edge(pair[0], pair[1])
                        
                    capture = self.get_signal_all_named_indexes(instance,icl_item.scan_capture)
                    result = [list(pair) for pair in zip(named_indexes, capture)]
                    
                    for a in result:
                        icl_graph.add_edge(a[0],a[1])
                    print(result)                    

                    icl_graph.add_edge(icl_item.get_last_named_indexes(),  icl_item.get_scanin_named_index())    
                    
                if(type(icl_item) == IclScanMux):
                    for node in icl_item.get_all_named_indexes():
                        icl_graph.add_node(node)

                    print("ABA", icl_item.get_all_connections())
                    for a,b in icl_item.get_all_connections():
                        icl_graph.add_edge(a, b)    

                if(type(icl_item) == IclInstance):
                    for connection in icl_item.connections:
                        for to_sig, from_sig in connection.items():
                            x = self.get_signal_all_named_indexes(icl_item, [to_sig])
                            y = self.get_signal_all_named_indexes(instance, from_sig)
                            assert(len(x) == len(y))
                            result = [list(pair) for pair in zip(x, y)]
                            print(result)
                            for a in result:
                                icl_graph.add_edge(a[0],a[1])    



        print(icl_graph)
        nx.draw(icl_graph, with_labels=True)
        plt.show()  # Display the graph
                

    # Create list of instances sorted from most nested instances to least nested instances
    def list_instances(self, lvl=0, hier="") -> list:
        icl_instance_items = self.get_icl_item_type(IclInstance)
        if not icl_instance_items:
            return [{"lvl": lvl, "inst": self, "hier": hier}]

        inst_list = [{"lvl": lvl, "inst": self, "hier": hier}]
        lvl += 1
        for instance in icl_instance_items:
            name = instance.get_name()
            inst_list += instance.list_instances(lvl, hier + "." + name if hier else name)

        # Remove duplicates
        unique_dicts = [inst_list[0]]
        for d in inst_list[1:]:
            check = [str(u['inst']) == str(d['inst']) and u['hier'] == d['hier'] and u["lvl"] == d["lvl"] for u in unique_dicts]
            if not any(check):
                unique_dicts.append(d)

        # Sort by lvl
        unique_dicts = sorted(inst_list, key=lambda d: d["lvl"], reverse=True)

        return unique_dicts
    
class IclScanRegister(IclItem):

    def __init__(self, instance: IclInstance, ctx, scan_reg: IclSignal) -> None:
        super().__init__(scan_reg.get_name(), instance.get_hier(), instance.get_hier(), ctx)
        self.instance = instance
        self.scan_reg = scan_reg
        self.mux_sel = None
        self.scan_in = None
        self.scan_out = None
        self.scan_capture = None
        self.reset_value = None
        self.default_value = None
        self.attributes = []

    def add_mux_sel(self, mux_sel):
        if(not self.mux_sel):
            self.mux_sel = mux_sel
        else:
            raise ValueError("Already have mux_sel reg")

    def add_scan_in(self, scan_in):
        if(not self.scan_in):
            self.scan_in = scan_in
        else:
            raise ValueError("Already have scan_in reg")

    def add_scan_out(self, scan_out):
        if(not self.scan_out):
            self.scan_out = scan_out
        else:
            raise ValueError("Already have scan_out reg")

    def add_scan_capture(self, scan_capture):
        if(not self.scan_capture):
            self.scan_capture = scan_capture
        else:
            raise ValueError("Already have scan_capture reg")

    def add_reset_value(self, reset_value):
        if(not self.reset_value):
            self.reset_value = reset_value
        else:
            raise ValueError("Already have reset_value reg")

    def add_default_value(self, default_value):
        if(not self.default_value):
            self.default_value = default_value
        else:
            raise ValueError("Already have default_value reg")
        
    def add_attribure(self, attribure):
        self.attributes.append(attribure)

    def get_vector_size(self) -> int:
        vector_size = 0
        if(self.scan_reg.get_size()):
            vector_size += self.scan_reg.get_size()
        else:
            vector_size += 1
        return vector_size

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.scan_reg)
    
    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.scan_reg)
    
    def get_msb_index(self) -> int:
        return self.get_all_indexes()[-1]
    
    def get_lsb_index(self) -> int:
        return self.get_all_indexes()[0]

    def get_last_named_indexes(self) -> str:
        return self.get_item_all_named_indexes(self.scan_reg)[-1]

    def get_first_named_indexes(self) -> str:
        return self.get_item_all_named_indexes(self.scan_reg)[0]
        
    def get_scanin_named_index(self) -> str:
        scan_in = self.get_signal_all_named_indexes(self.instance, [self.scan_in])
        assert(len(scan_in) == 1)
        return scan_in[0]

    def get_scancapture_named_index(self) -> str:
        scan_in = self.get_signal_all_named_indexes(self.instance, [self.scan_capture])
        assert(len(scan_in) == 1)
        return scan_in[0]
    
    def check(self):
        pass


def checkSigExistance(instance: IclInstance, singal:IclSignal):
    icl_item = instance.get_icl_item_name(singal.get_name())
    item_indexes = icl_item.get_all_indexes()
    signal_indexes = singal.get_indexes()
    ls1 = [element for element in item_indexes if element in signal_indexes]
    ls2 = [element for element in signal_indexes if element in item_indexes]
    if (sorted(ls1) != sorted(ls2)):
        raise ValueError(signal_indexes, "not present in", icl_item.get_name_with_hier(), item_indexes, signal_indexes, ls1, ls2)

class ConcatSig():
    
    def __init__(self, instance: IclInstance, concat_sigs: list[IclSignal], type) -> None:
        self.type = type
        self.instance = instance
        self.concat_sigs = concat_sigs

    def check(self):
        for sig in self.concat_sigs:
            checkSigExistance(self.instance, sig)
            icl_item = self.instance.get_icl_item_name(sig.get_name())
            if(type(sig) == IclNumber):
                pass
            else:
                if(self.type == "scan"):
                    assert(type(icl_item) in [IclScanInPort, IclScanRegister, IclScanMux, IclScanOutPort])
                elif(self.type == "data"):
                    assert(type(icl_item) in [IclDataInPort, IclDataOutPort])

    def get_all_named_indexes(self, max_size: int) -> list[str]:
        # Check than only one unsized item is present in concatenation
        self.check()

        size = 0
        named_list = []
        for sig in self.concat_sigs:
            if(type(sig) == IclSignal):
                sel_item = self.instance.get_icl_item_name(sig.get_name())
                if (not sig.get_indexes()):                   
                    named_list += [sig]
                    size += 1
                else:
                    sel_named_idxs = sel_item.get_signal_all_named_indexes(self.instance, [sig])
                    named_list += sel_named_idxs
                    size += len(sel_named_idxs)
            
            elif(type(sig) == IclNumber):
                if(not sig.sized_number()):
                   for idx in range(sig.get_size()):
                        size += 1
                        named_list += ["{}".format(sig.get_bit(idx))]
                else:
                    named_list += [sig]
                    size += 1

        assert(max_size >= size)
        size_to_fill = max_size - size
        full_list = []
        for item in named_list:
            if(type(item) == str):
                full_list += [item]
            elif(type(sig) == IclSignal):
                size -=  1                
                icl_item = self.instance.get_icl_item_name(sig.get_name())
                sel_named_idxs = icl_item.get_all_named_indexes()
                for idx in range(size_to_fill+1):
                    full_list += [sel_named_idxs[idx]]
                    size += 1
            elif(type(sig) == IclNumber):
                size -=  1
                for idx in range(size_to_fill+1):
                    full_list += ["{}".format(sig.get_bit(idx))]
                    size += 1

        assert(max_size == size)
        return full_list
    
    def get_vector_size(self) -> int:
        unsized_items = 0
        vector_size = 0
        for sig in self.concat_sigs:
            if(type(sig) == IclSignal):

                if (not sig.get_indexes()):                   
                    sel_item = self.instance.get_icl_item_name(sig.get_name())
                    vector_size += sel_item.get_vector_size()
                    unsized_items += 1
                else:
                    vector_size += sig.get_size()
            
            elif(type(sig) == IclNumber):
                if(not sig.sized_number()):
                   vector_size += sig.get_size()
                else:
                   unsized_items += 1 

        if(unsized_items > 1 ):
            raise ValueError("More than two unsized items in concat signal")
                             
        return vector_size

        
class IclScanMux(IclItem):
    
    def __init__(self, instance: IclInstance, ctx, scan_mux: IclSignal, scan_select: ConcatSig, mux_selects: list[tuple[IclNumber,ConcatSig]]) -> None:
        super().__init__(scan_mux.get_name(), instance.get_hier(), instance.get_module_scope(), ctx)
        self.instance = instance
        self.scan_mux = scan_mux
        self.scan_select = scan_select
        self.mux_selects = mux_selects
        self.connections = []

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.scan_mux)

    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.scan_mux)
    
    def get_all_connections(self) -> list[tuple[str]]:
        return self.connections
    
    def check(self):
        self.scan_select.check()
        scan_sel_size = self.scan_select.get_vector_size()

        scan_mux_names = self.get_all_named_indexes()
        scan_mux_size = 1 if self.scan_mux.get_size() == 0 else self.scan_mux.get_size()

        self.connections = []

        for selectee, tos in self.mux_selects:
            selectee_size = selectee.get_size()
            tos.check()      
            to_size = tos.get_vector_size()

            assert(selectee_size == scan_sel_size)
            assert(scan_mux_size == to_size)

            tos_names = tos.get_all_named_indexes(scan_mux_size)
            self.connections += (list(zip(tos_names, scan_mux_names)))

class IclAttribute(IclItem):

    def __init__(self, instance: IclInstance, ctx, att_name: str, att_data: str | IclNumber) -> None:
        super().__init__(att_name, instance.get_hier(), instance.get_module_scope(), ctx)
        self.att_data = att_data

    def check(self):
        pass
    
class IclPort(IclItem):

    def __init__(self, instance: IclInstance, ctx, port: IclSignal) -> None:
        super().__init__(port.get_name(), instance.get_hier(), instance.get_module_scope(), ctx)
        self.ports = [port]
        self.attributes = []
        self.instace = instance

    def add_attribute(self, port: IclSignal, attribure: IclAttribute):
        self.attributes.append = {port:attribure}

    def get_attributes(self, port_name: str)-> list[IclAttribute]:
        pass

    def get_instance(self) -> IclInstance:
        return self.instace
    
    def get_vector_size(self) -> int:
        vector_size = 0
        for port in self.ports:
            if(port.get_size()):
                vector_size += port.get_size()
            else:
                vector_size += 1
        return vector_size

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.ports)

    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.ports)
    
    def get_msb_index(self) -> int:
        return self.get_all_indexes()[-1]
    
    def get_lsb_index(self) -> int:
        return self.get_all_indexes()[0]
    
    
    # Only one unsized port can exist
    # Multiple sized ports can exist
    # Multiple sized ports can not have overlapping indexes
    # Concated multiple sized ports can not have gaps between highest and lowest indexes    
    def check_port_size(self, same_ports: list[IclSignal]) -> int:
        indexes = [port.get_indexes() for port in same_ports]
        all_numbers = [num if num else 0 for sublist in indexes for num in sublist]
        sized = 1 if len(all_numbers) > 0 else 0
        if(sized):
            for port in same_ports:
                if(port.get_size() == 0):
                    raise Exception("Found unisized port in multiple port defintion of {}".format(port.get_name()))
            if(not self.check_no_overlap(*indexes)):
                raise Exception("Found overlapping indexes in multiple port defintion of {}".format(port.get_name()))
            if(not self.check_no_gaps(*indexes)):
                raise Exception("Found gaps in multiple port defintion of {}".format(port.get_name()))  
        else:
            if(same_ports[0].get_size() not in (0,1)):
                raise Exception("Found sized port in single port defintion of {}".format(same_ports[0].get_name()))
            else:
                same_ports[0].ovveride_indexes([0])
        
    def check_no_overlap(self, *lists):
        #print("check_no_overlap", lists)
        all_numbers = [num if num else 0 for sublist in lists for num in sublist]
        return len(set(all_numbers)) == len(all_numbers)
        
    def check_no_gaps(self, *lists):
        #print("check_no_gaps", lists)        
        all_numbers = [num if num else 0 for sublist in lists for num in sublist]
        return set(range(min(all_numbers), max(all_numbers) + 1)) == set(all_numbers)
        
    # 0 Pass / 1 Fail
    def check(self) -> int:
        # Check port size and indexes
        self.check_port_size(self.ports)

    def merge(self, icl_port: "IclPort"):
        for port in icl_port.ports:
            self.ports.append(port)
        for att in icl_port.attributes:
            self.attributes.append(att)

class IclScanInPort(IclPort):

    def __init__(self, instance: IclInstance, ctx, port: IclSignal) -> None:
        super().__init__(instance, ctx, port)
        self.type = IclScanInPort

    # 0 Pass / 1 Fail
    def check(self) -> int:
        super().check()



class IclScanOutPort(IclPort):

    def __init__(self, instance: IclInstance, ctx, port: IclSignal) -> None:
        super().__init__(instance, ctx, port)
        self.type = IclScanOutPort
        self.source = {};        

    def add_source(self, port: IclSignal, source: IclSignal):
        if(port in self.source):
            raise ValueError("{} has already source {}".format(port, self.source))
        else:
            self.source[port] = source

    def get_named_sourced_indexes(self) -> list[str]:
        signals = [sigs for port_item in self.ports for sigs in self.source[port_item]]        
        return self.get_signal_all_named_indexes(self.instace, signals)

    def check(self) -> int:
        super().check()
        for port_item in self.ports:
            source_signal_list = self.source[port_item]
            port_size = port_item.get_size()
            source_size = 0

            for source_signal in source_signal_list:
                source_signal_name = source_signal.get_name()
                # Get Item(fails if item is not found)
                source_item = self.instace.get_icl_item_name(source_signal_name)                
                if(source_signal.get_size()):
                    source_size += source_signal.get_size()
                else:
                    source_size += source_item.get_vector_size()

            # Check size
            assert(port_size == source_size)

        #self.check_port_size(sources)
        
    def get_connect_name(self, index):
        pass

    def get_conectee_name(self, index):
        pass

class IclDataInPort(IclPort):

    def __init__(self, instance: IclInstance, ctx, port: IclSignal) -> None:
        super().__init__(instance, ctx, port)
        self.type = IclDataInPort

    # 0 Pass / 1 Fail
    def check(self) -> int:
        super().check()
        
class IclDataOutPort(IclPort):

    def __init__(self, instance: IclInstance, ctx, port: IclSignal) -> None:
        super().__init__(instance, ctx, port)
        self.type = IclDataOutPort
        self.source = {};        

    def add_source(self, port: IclSignal, source: IclSignal):
        if(port in self.source):
            raise ValueError("{} has already source {}".format(port, self.source))
        else:
            self.source[port] = source

    def get_named_sourced_indexes(self) -> list[str]:
        signals = [sigs for port_item in self.ports for sigs in self.source[port_item]]        
        return self.get_signal_all_named_indexes(self.instace, signals)
            
    def check(self) -> int:
        super().check()
        for port_item in self.ports:
            source_signal_list = self.source[port_item]
            port_size = port_item.get_size()
            source_size = 0

            for source_signal in source_signal_list:
                source_signal_name = source_signal.get_name()
                # Get Item(fails if item is not found)
                source_item = self.instace.get_icl_item_name(source_signal_name)                
                if(source_signal.get_size()):
                    source_size += source_signal.get_size()
                else:
                    source_size += source_item.get_vector_size()

            # Check size
            assert(port_size == source_size)

    def get_connect_name(self, index):
        pass
    
    def get_conectee_name(self, index):
        pass
        