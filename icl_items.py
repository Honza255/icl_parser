from typing import Any
from parser.iclParser import iclParser

class IclSignal:
    
    def fill_numbers(self, index_l: int, index_h: int) -> list:
        tmp = None
        if index_l <= index_h:
            tmp =  list(range(index_l, index_h + 1))
        else:
            tmp =  list(range(index_l, index_h - 1, -1))
        return tmp   
     
    def __init__(self, name: str,  index_l=None, index_h = None):
        self.hier = []
        self.name = name
        self.negation: bool = 0
        if((index_h is not None) and (index_l is not None)):
            self.indexes = self.fill_numbers(index_l, index_h)
        elif((index_h is None) and (index_l is not None)):
            self.indexes = [index_l]
        elif((index_h is not None) and (index_l is None)):            
            raise ValueError("Index high defined but index low is not defined")
        else:
            self.indexes = []


    def add_hiearachy(self, hier_lvl: str):
        self.hier.append(hier_lvl)

    def has_hier(self) -> bool:
        if(self.hier):
            return 1
        else:
            return 0
        
    def ovveride_indexes(self, indexes: list):
        self.indexes = indexes
       
    def get_indexes(self) -> list:
        return list(self.indexes)
    
    def get_name(self) -> str:
        return self.name
    
    def get_relative_name(self) -> str:
        str = ""
        for item in self.hier:
            str += item + "."
        str += self.name
        return str

    def get_size(self) -> int:
        return len(self.indexes)

    def get_negation(self) -> bool:
        return self.negation
        
    def negate(self):
        self.__invert__()

    def __invert__(self):
        self.negation = self.negation ^ 1

    def __str__(self) -> str:
        str = "~" if self.negation else ""
        for item in self.hier:
            str += item + "."
        str += self.name
        if(self.indexes):
            str += "{}".format(self.indexes)
        return str
    
    def __repr__(self) -> str:
        return self.__str__()
    
class IclNumber:
    
    def __init__(self, in_value: str, value_type: str, size:int=-1):
        assert((size > 0 ) or (size == -1))
        assert(value_type in ["dec", "hex", "bin"])

        self.r_number = 0
        self.x_number = 0
        self.icl_size = size
        self.bit_size = 0
        self.last_bit = ""
        self.negation: bool = 0

        # Remove symbols
        source = in_value
        for remove_char in "_' DdHhBb":
            source = source.replace(remove_char, "")

        # Allowed symbols
        allowed_symbols = "Xx0123456789AaBbCcDdEeFf"
        assert(all(char in allowed_symbols for char in source))

        # Translate string to number            
        if(value_type == "dec"):           
            self.r_number = int(source)
            self.last_bit = "0"
        elif(value_type == "hex"):
            for index, value in enumerate(reversed(source)):
                if(value in ["X","x"]):
                    self.x_number += 15 << index*4 
                    self.last_bit = "x"
                else:
                    self.r_number +=  int(value, 16) << index*4
                    self.last_bit = "0"    
        elif(value_type == "bin"):
            for index, value in enumerate(reversed(source)):
                if(value in ["X","x"]):
                    self.x_number += 1 << index
                    self.last_bit = "x"
                else:
                    self.r_number += int(value, 2) << index
                    self.last_bit = "0"

        # Calculate how many 3-state bits to contain this ICL number
        r_bits = self.r_number.bit_length()
        x_bits = self.x_number.bit_length()
        self.bit_size = r_bits if r_bits > x_bits  else x_bits
        self.bit_size = self.bit_size if self.bit_size > 0 else 1
                                
        # Padd sized number with x's if last bit was x 
        # and passed number string did not fill all bits
        if self.sized_number():
            self.resize(self.icl_size)

    def get_negation(self):
        return self.negation
        
    def negate(self):
        self.negation = self.negation ^ 1
        
    def resize(self, size:int, check:bool=1):
        assert(size > 0)
        lower_mask =  (1 << size)-1
        upper_mask = ~lower_mask      
                    
        while self.bit_size < size:
            self.bit_size += 1
            if self.last_bit == "x":
                self.x_number += 1 << (self.bit_size-1)  
                               
        if(check):
            try:
                assert(not (self.x_number & upper_mask))
                assert(not (self.r_number & upper_mask))
            except:
                raise ValueError("ICL number bin:{} cannot be resized into {} bits because it would be truncating 1 or x".format(self.get_bin_str(), size))
            
        self.x_number &= lower_mask
        self.r_number &= lower_mask
        self.bit_size = size   
        self.icl_size = size
        self.last_bit = "x" if self.x_number & (1 << (size-1))  else "0"
        
        assert(self.bit_size  == self.icl_size)
        assert((2**self.icl_size - 1) >= self.x_number)
        assert((2**self.icl_size - 1) >= self.r_number)
                        
    def concat(self, icl_number: "IclNumber"):
        if(not isinstance (icl_number, IclNumber)):
            raise ValueError("Object of class {0} can not be concated with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.icl_size == -1) or (icl_number.icl_size == -1)):
            raise ValueError("Unsized variables cannot be concated")
        
        new_number = self.get_bin_str() + icl_number.get_bin_str()
        new_size = self.icl_size + icl_number.icl_size

        return IclNumber(new_number, "bin", new_size) 

    def get_icl_size(self):
        return self.icl_size
    
    def get_bit_size(self):
        return self.bit_size    
    
    def get_number(self):
        if(self.x_number > 0):
            raise ValueError("{}:number cannot be converted to pure number, it contrains x".format(self.__str__()))
        return self.r_number
        
    def sized_number(self):
        return 1 if self.icl_size > -1 else 0

    def copy(self) -> "IclNumber":
        return IclNumber(self.get_bin_str(), "bin", self.get_bit_size())
    
    def set_value(self, value: int):
        self.x_number = 0
        self.r_number = value
        if self.sized_number():
            self.r_number = self.r_number & ((1 << self.icl_size)-1)

                               
    def set_bit(self, value: int, index: int):
        if((index >= self.icl_size) and (self.icl_size != -1)):
            raise ValueError("Index {} is bigger than size {}".format(index, self.icl_size))
        else:
            if value not in (0, 1):
                raise ValueError("The bit value must be 0 or 1.")
            mask = ~(1 << index)
            self.r_number &= mask
            self.x_number &= mask
            self.r_number = self.r_number | (value << index)     

    def get_bit(self, index):
        if((index >= self.icl_size) and (self.icl_size != -1)):
            raise ValueError("Index {} is bigger than size {}".format(index, self.icl_size))
        else:
            num = IclNumber("0", "dec",1)
            num.r_number = (self.r_number >> index) & 1
            num.x_number = (self.x_number >> index) & 1
            return num
    
    def get_bin_str(self) -> str:
        str_repr = ""
        for idx in range(self.bit_size-1, -1, -1):
            mask = 1 << idx
            if(self.x_number & mask):
                str_repr += "x"
            elif(self.r_number & mask):
                str_repr += "1"
            else:
                str_repr += "0"
        return str_repr

    def get_bin_bit_str(self, idx) -> str:
        return self.get_bin_str()[-(idx+1)]
    
            
    def __str__(self):
        str_repr = self.get_bin_str()
        return "Number bit Size:{0}, R:0b{1:b}, X:0b{2:b}, repr:{3:}, bits:{4:}".format(self.icl_size, self.r_number, self.x_number, str_repr, self.bit_size)

    def __repr__(self):
        return self.get_bin_str()
    
    def __add__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be added with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_number > 0) or (obj_2.x_number > 0)):
            raise ValueError("Numbers with x(UNKNOWN) cannot be added")
        return IclNumber(str(self.r_number + obj_2.r_number), "dec") 


    def __sub__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be substracted with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_number > 0) or (obj_2.x_number > 0)):
            raise("Numbers with x(UNKNOWN) cannot be substracted")
        return IclNumber(str(self.r_number - obj_2.r_number), "dec") 

    def __mul__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be multiplayed with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_number > 0) or (obj_2.x_number > 0)):
            raise ValueError("Numbers with x(UNKNOWN) cannot be substracted")
        return IclNumber(str(self.r_number * obj_2.r_number), "dec") 

    def __truediv__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be divided with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_number > 0) or (obj_2.x_number > 0)):
            raise ValueError("Numbers with x(UNKNOWN) cannot be divided")
        return IclNumber(str(self.r_number // obj_2.r_number), "dec") 

    def __floordiv__(self, obj_2):
        return self.__truediv__(self, obj_2)
    
    def __mod__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be modulo with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_number > 0) or (obj_2.x_number > 0)):
            raise ValueError("Numbers with x(UNKNOWN) cannot be modulo")
        return IclNumber(str(self.r_number % obj_2.r_number), "dec") 

    def __invert__(self):
        if(self.icl_size == -1):
            bit_len  = self.r_number.bit_length()
            number = (~self.r_number) & ((1<< bit_len) - 1)            
        else:
            number = (~self.r_number) & ((1<< self.icl_size) - 1)
        
        return IclNumber(str(number), "dec", self.icl_size) 
    

class EnumRef():
    def __init__(self, instance: "IclInstance", enum_name: str) -> None:
        self.instance = instance
        self.enum_name:str = enum_name
        
    def get_name(self) -> str:
        return self.enum_name

class ConcatSig():   
    def __init__(self, instance: "IclInstance", concat_sigs: list[IclSignal, IclNumber], concat_type) -> None:
        self.type: str = concat_type
        self.instance: "IclInstance" = instance
        self.concat_sigs: list[IclSignal,IclNumber] = concat_sigs

        # Unsized check can be done immediately
        self.check_unsized_numbers()
        
    def check(self) -> None:
        valid_types = {
            "scan": [IclScanInPort, IclScanRegister, IclScanMux, IclScanOutPort, IclAlias],
            "data": [IclDataInPort, IclSelectPort, IclScanRegister,  IclLogicSignal, IclAlias, IclDataRegister],
            "alias": [IclDataInPort, IclDataOutPort, IclScanRegister]
        }

        for sig in self.concat_sigs:
            if isinstance(sig, IclNumber):
                continue
            checkSigExistance(self.instance, sig)
            icl_item = self.instance.get_icl_item_name(sig.get_relative_name())
            assert type(icl_item) in valid_types[self.type], f"invalid type {type(icl_item)} for {self.type} in ConcatSig {self.concat_sigs}" 

    def check_unsized_numbers(self) -> int:
        unsized_numbers = sum(1 for sig in self.concat_sigs if isinstance(sig, IclNumber) and not sig.sized_number())
        assert unsized_numbers in {0, 1}
        return unsized_numbers

    def negate(self):
        for sig in self.concat_sigs:
            sig.negate()

    def get_all_icl_items(self) -> list["IclItem",IclNumber]:
        items = []
        for sig in self.concat_sigs:
            if(type(sig) == IclNumber):
                items.append(sig)
            else:
                items.append(self.instance.get_icl_item_name(sig.get_relative_name()))
        return items
    
    def get_icl_number(self) -> IclNumber:
        items = self.get_all_icl_items()
        assert len(items) == 1
        assert isinstance(items[0], IclNumber)
        return items[0]
    
    # Resize, un-sized number, only one unsized number allowed in concat
    def resize(self, new_size):
        if self.sized_number():
            raise ValueError(f"Concat {self} can not resize already sized number")
        
        self.check()
        self.check_fit(new_size)
        
        sized_bits  = self.get_sized_bits_size()
        size_to_fill = new_size - sized_bits
        for sig in self.concat_sigs:
            if isinstance(sig, IclNumber): 
                sig.resize(size_to_fill)
            
    def get_list_for_expr(self) -> list[str,IclNumber]:
        self.check()
                
        named_list = []              
        for sig in self.concat_sigs:
            
            if isinstance(sig, IclSignal):
                temp_list = []
                item: IclItem = self.instance.get_icl_item_name(sig.get_relative_name())
                if (sig.get_indexes()):                   
                    sel_named_idxs = item.get_signal_all_named_indexes(self.instance, [sig])
                    temp_list += sel_named_idxs
                else:
                    sel_named_idxs = item.get_all_named_indexes()
                    temp_list += sel_named_idxs
            
                if sig.get_negation():
                    for idx, item in enumerate(temp_list):
                        temp_list[idx] = f"(not {temp_list[idx]})"

                named_list += temp_list

            elif isinstance(sig, IclNumber): 
                temp_list = []
                if sig.sized_number():                  
                    for idx in range(sig.get_icl_size()):
                        temp_list.append("{}".format(sig.get_bit(idx).get_bin_str()))                      
                    temp_list.reverse()

                    if sig.get_negation():
                        for idx, number in enumerate(temp_list):
                            temp_list[idx] = "1" if number == "0" else "0"
                    
                    named_list += temp_list
                else:
                    named_list += [sig]
            else:
                raise ValueError(f"Unknown sig {sig}")
        
        return named_list
    
    def get_all_named_indexes_with_prefix(self, max_size: int, neg_on: bool) -> list[str]:
        self.check()
        self.check_fit(max_size)
        
        sized_bits  = self.get_sized_bits_size()
        size_to_fill = max_size - sized_bits

        named_list = []       
        for sig in self.concat_sigs:
            
            if isinstance(sig, IclSignal):
                temp_list = []
                item: IclItem = self.instance.get_icl_item_name(sig.get_relative_name())
                if (sig.get_indexes()):                   
                    sel_named_idxs = item.get_signal_all_named_indexes(self.instance, [sig])
                    temp_list += sel_named_idxs
                else:
                    sel_named_idxs = item.get_all_named_indexes()
                    temp_list += sel_named_idxs
            
                if sig.get_negation() and neg_on:
                    for idx, item in enumerate(temp_list):
                        temp_list[idx] = f"(not {temp_list[idx]})"

                named_list += temp_list

            elif isinstance(sig, IclNumber): 
                temp_list = []
                idx_iterator = range(sig.get_icl_size()) if sig.sized_number() else range(size_to_fill)
                for idx in idx_iterator:
                    temp_list.append("{}".format(sig.get_bit(idx).get_bin_str()))                      
                temp_list.reverse()

                if sig.get_negation() and neg_on:
                    for idx, number in enumerate(temp_list):
                        temp_list[idx] = "1" if number == "0" else "0"
                
                named_list += temp_list
                    
            else:
                raise ValueError(f"Unknown sig {sig}")

        #print()
        #print(named_list)
        #for x in named_list:
        #    print("{}".format(type(x)))
        #print(named_list)
        #print(f"Max size {max_size}, actual size {len(named_list)}, size to fill {size_to_fill}, sized bits {sized_bits}")
        
        assert(max_size >= sized_bits)       
        assert(max_size == len(named_list))

        return named_list
        
    def get_all_named_indexes(self, max_size: int) -> list[str]:
        return self.get_all_named_indexes_with_prefix(max_size, 0)
       
    def sized_number(self) -> bool:
        unsized_numbers = self.check_unsized_numbers()
        return 1 if unsized_numbers == 0 else 0
    
    def get_size_common(self, sized_or_min) -> int:
        sized_bits = 0
        min_size = 0
        
        for sig in self.concat_sigs:
            
            if isinstance(sig, IclSignal):
                if (sig.get_indexes()):                   
                    min_size   += sig.get_size()
                    sized_bits += sig.get_size()
                else:
                    sel_item = self.instance.get_icl_item_name(sig.get_relative_name())
                    min_size   += sel_item.get_vector_size()
                    sized_bits += sel_item.get_vector_size()
                    
            elif isinstance(sig, IclNumber): 
                if (sig.sized_number()):
                   min_size   += sig.get_icl_size()
                   sized_bits += sig.get_icl_size()
                else:
                   min_size   += sig.get_bit_size()
                   sized_bits += 0

        return sized_bits if sized_or_min else min_size
        
    def get_sized_bits_size(self) -> int:
        return self.get_size_common(1)

    def get_vector_min_size(self) -> int:
        return self.get_size_common(0)
    
    def check_fit(self, source_size: int):
        min_size = self.get_vector_min_size()
        if self.sized_number():
            assert min_size == source_size
        else:
            difference = source_size - min_size
            assert(difference >= 0)
        
def checkSigExistance(instance: "IclInstance", singal:IclSignal):
    # print(singal.get_relative_name())
    icl_item = instance.get_icl_item_name(singal.get_relative_name())

    item_indexes = icl_item.get_all_indexes()
    signal_indexes = singal.get_indexes()
    ls1 = [element for element in item_indexes if element in signal_indexes]
    ls2 = [element for element in signal_indexes if element in item_indexes]
    if (sorted(ls1) != sorted(ls2)):
        raise ValueError(signal_indexes, "not present in", icl_item.get_name_with_hier(), item_indexes, signal_indexes, ls1, ls2)
    
class IclItem:

    def __init__(
            self,
            icl_name: str,
            icl_hier: str,
            module_scope: str,
            ctx: str
        ) -> None:
            
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
 
        return all_numbers
    
    def get_item_all_named_indexes(self, icl_sig: IclSignal) -> list[str]:
        named_indexes = []
        for index in self.get_item_all_indexes(icl_sig):
            named_indexes.append("{}_{:04}".format(self.get_name_with_hier(),index))
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
                    indexes.reverse()
                    
            for index in indexes:
                named_indexes.append("{}_{:04}".format(source_item.get_name_with_hier(),index))
        
        return named_indexes


class IclInstance(IclItem):

    def __init__(self, icl_name: str, icl_hier: str, module_scope: str, ctx) -> None:
        super().__init__(icl_name, icl_hier, module_scope, ctx)
        self.attributes = {}
        self.connections = []
        self.parameters_override = {}
        self.parameters = {}

        icl_graph = None
        
    def add_icl_item(self, icl_item: IclItem):
        for curr_icl_item in self.icl_items:
            if curr_icl_item.get_name() == icl_item.get_name():
                raise ValueError("ICL item {} already exists in instane of {} modue {}".format(curr_icl_item.get_name(), self.get_name(), self.get_module_scope()))
        self.icl_items.append(icl_item)

    def get_icl_item_name(self, name: str) -> IclItem:
        #print("start", name)
        name_seq = name.split(".")
        while(len(name_seq) > 0):
            item_to_search = name_seq.pop(0)
            for icl_item in self.icl_items:
                #print(self.get_name_with_hier(), len(name_seq), icl_item.get_name(), item_to_search, icl_item.get_name() == item_to_search)
                if icl_item.get_name() == item_to_search:
                    if(len(name_seq) == 0):
                        #print("A-1")
                        return icl_item
                    else:
                        #print("B-1")
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
        instances = []
        non_instaces = []
        for item in self.icl_items:
            if(type(item) != IclInstance):
                non_instaces.append(item)
            else:
                instances.append(item)

        print(instances)
        for item in instances:
            print("Check", item, item.get_name())
            item.check()

        print(non_instaces)
        for item in non_instaces:
            print("Check", item, item.get_name())
            item.check()

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

class IclEnum(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            enum_name: str,
            enum_items: list[tuple[str,IclNumber]],
            ctx: str
        ) -> None:
        super().__init__(enum_name, instance.get_hier(), instance.get_hier(), ctx)

        self.enum_items: list[tuple[str,IclNumber]] = enum_items
        self.enum_table = {}
        self.enum_bit_size = 0
        self.check()                    

    def get_enum_number(self, enum_name: str) -> IclNumber:
        if enum_name in self.enum_table:
            return  self.enum_table[enum_name]
        else:
            raise ValueError("{} is not present in IclEnum:{}, {}".format(enum_name, self.get_name_with_hier(), self.ctx))

    def get_enums(self) -> list[str]:
        return self.enum_table.keys()

    def get_enum_size(self) -> int:
        return self.enum_bit_size

    def check(self):
        self.enum_table = {}
        self.enum_bit_size = 0

        # Init check
        for enum_name, enum_number in self.enum_items:

            # An enum_symbol shall be unique among all enum_symbol entries within an enum_def.
            if enum_name in self.enum_table:
                raise ValueError("Enum duplicate({}) in IclEnum:{}, {}".format(enum_name, self.get_name_with_hier(), self.ctx ))
            
            if not enum_number.sized_number():
                raise ValueError("Enum ({}) in IclEnum:{}, has unsized number {}, {}".format(enum_name, self.get_name_with_hier(), enum_number, self.ctx ))             

            if len(self.enum_table) == 0:
                self.enum_bit_size = enum_number.get_bit_size()

            # The width of each enum_value shall be the same within an enum_def.
            if self.enum_bit_size != enum_number.get_bit_size():
                raise ValueError("In IclEnum:{}, emums have different bit sizes, {}".format(enum_name, self.ctx ))             
                
            self.enum_table[enum_name] = enum_number
        
class IclAlias(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            alias_name: IclSignal,
            concat_sig: ConcatSig,
            items: dict,
            ctx: str
        ) -> None:
        super().__init__(alias_name.get_name(), instance.get_hier(), instance.get_hier(), ctx)
        self.instance: IclInstance = instance

        self.alias_sig: IclSignal = alias_name
        self.concat_sig: ConcatSig = concat_sig

        self.attributes: list[IclAttribute] = items["att"] 
        self.access_togeteher: bool = items["ace"] 
        self.end_state: IclNumber =  items["end"] 
        self.enum_ref: str = items["ref"] 
    
    def get_vector_size(self) -> int:
        return self.alias_sig.get_size()
    
    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.alias_sig)
    
    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.alias_sig)
    
    def get_all_connections(self) -> list[tuple[str]]:
        side_1 = self.get_all_named_indexes()
        side_2 = self.concat_sig.get_all_named_indexes(self.alias_sig.get_size())
        print(side_1, side_2)
        return list(zip(side_1, side_2))

    def get_enum_reference(self) -> str:
        return self.enum_ref
             
    def check(self):
        self.concat_sig.check()
       
        # When alias is unsized, assume bit width of one
        if self.alias_sig.get_size() == 0:
            self.alias_sig.ovveride_indexes([0])
   
        alias_size = self.alias_sig.get_size()
        alias_concat_sig_size = self.concat_sig.get_vector_min_size()

        # Check size of alias and signal
        assert alias_size == alias_concat_sig_size, f"Alias {self.alias_sig.get_name()} with size of {alias_size} is not same as size as assigned singnal {self.concat_sig} with size of {alias_concat_sig_size}"

        # Check size of alias and ref enum
        if self.enum_ref:
            enum: IclEnum = self.instance.get_icl_item_name(self.enum_ref)
            enum_size = enum.get_enum_size()
            assert enum_size == alias_size, f"Alias {self.alias_sig.get_name()} with size of {alias_size} is not same as size as assigned enum {enum} with size of {enum_size}"

class IclAttribute(IclItem):

    def __init__(self, instance: IclInstance, ctx, att_name: str, att_data: str | IclNumber) -> None:
        super().__init__(att_name, instance.get_hier(), instance.get_module_scope(), ctx)
        self.att_data = att_data

    def check(self):
        pass

class IclScanRegister(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            scan_reg: IclSignal,
            in_attributes: list[IclAttribute],
            in_scan_in_source: IclSignal,
            in_default_value: ConcatSig | EnumRef,
            in_capture_source: ConcatSig | EnumRef,
            in_reset_value: ConcatSig | EnumRef,
            in_ref_enum: str,
            ctx: str
        ) -> None:
        
        super().__init__(scan_reg.get_name(), instance.get_hier(), instance.get_hier(), ctx)

        self.instance = instance

        # Inital values
        self.scan_reg = scan_reg
        self.in_attributes: list[IclAttribute] = in_attributes
        self.in_scan_in_source: IclSignal = in_scan_in_source
        self.in_default_value: ConcatSig | EnumRef = in_default_value
        self.in_capture_source: ConcatSig | EnumRef = in_capture_source
        self.in_reset_value: ConcatSig | EnumRef = in_reset_value
        self.in_ref_enum: str = in_ref_enum

        # Assigned by function check (transforming EnumRef to ConcatSig + size checks)
        self.scan_in: IclSignal = in_scan_in_source
        self.capture_source: ConcatSig = None
        self.reset_source: ConcatSig = None
        self.default_value_source: ConcatSig = None

        # Register values
        self.scan_reg_size = len(self.get_all_named_indexes())
        self.current_value = IclNumber("x", "bin", self.scan_reg_size)
        self.next_value    = IclNumber("x", "bin", self.scan_reg_size)
        self.activate = 0
        self.select_clause = ""

    def set_current_bit(self, value: int, index:int):
        self.current_value.set_bit(value, index)

    def set_current_value(self, value: int):
        self.current_value.set_value(value)
    
    def set_next_bit(self, value: int, index:int):
        self.next_value.set_bit(value, index)

    def set_next_value(self, value: int):
        self.next_value.set_value(value)

    def set_next_value_to_current(self):
        self.current_value = self.next_value.copy()
        
    def reset(self):
        if(self.reset_source):
            self.current_value = self.reset_source.get_icl_number()
            self.next_value = self.reset_source.get_icl_number()

    def get_vector_size(self) -> int:
        # vector_size = 0
        # if(self.scan_reg.get_size()):
        #     vector_size += self.scan_reg.get_size()
        # else:
        #     vector_size += 1
        # return vector_size
        return self.scan_reg_size
    
    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.scan_reg)
    
    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.scan_reg)
    
    def get_msb_index(self) -> int:
        return self.get_all_indexes()[0]
    
    def get_lsb_index(self) -> int:
        return self.get_all_indexes()[-1]

    def get_named_msb(self) -> str:
        return self.get_item_all_named_indexes(self.scan_reg)[0]

    def get_named_lsb(self) -> str:
        return self.get_item_all_named_indexes(self.scan_reg)[1]
        
    def get_scanin_named_index(self) -> str:
        scan_in = self.get_signal_all_named_indexes(self.instance, [self.scan_in])
        assert(len(scan_in) == 1)
        return scan_in[0]

    def get_scancapture_named_index(self) -> str:
        scan_in = self.get_signal_all_named_indexes(self.instance, [self.scan_capture])
        assert(len(scan_in) == 1)
        return scan_in[0]
    
    def get_enum_reference(self) -> str:
        return self.in_ref_enum

    def check(self):

        if self.in_ref_enum:
            enumeration: IclEnum = self.instance.get_icl_item_name(self.in_ref_enum)
            assert enumeration.get_enum_size() == self.get_vector_size(),\
                f"IclScanRegister is referencing IclEnum that has size of {enumeration.get_enum_size()} but IclScanRegister has size of {self.get_vector_size()}: {self.ctx}"
            
        def enum_symbol_check(self, in_data, concat_type) -> ConcatSig:
            if isinstance(in_data, EnumRef):
                assert self.self.in_ref_enum, f"IclScanRegister uses enum symbol references without referencing concrete IclEnum: {self.ctx}"
                enumeration: IclEnum = self.instance.get_icl_item_name(self.in_ref_enum)
                enum_symbol_value = enumeration.get_enum_number(in_data)
                return ConcatSig(self.instance, [enum_symbol_value], concat_type)
            else:
                return in_data
        
        self.default_value_source = enum_symbol_check(self, self.in_default_value, "number")
        self.capture_source = enum_symbol_check(self, self.in_capture_source, "data")
        self.reset_source = enum_symbol_check(self, self.in_reset_value, "number")

        if self.default_value_source:
            self.default_value_source.check()
            self.default_value_source.check_fit(self.get_vector_size())
            if not self.default_value_source.sized_number():
                self.default_value_source.resize(self.get_vector_size())

        if self.capture_source:
            self.capture_source.check()
            self.capture_source.check_fit(self.get_vector_size())
            if not self.capture_source.sized_number():
                self.capture_source.resize(self.get_vector_size())

        if self.reset_source:
            self.reset_source.check()
            self.reset_source.check_fit(self.get_vector_size())            
            if not self.reset_source.sized_number():
                self.reset_source.resize(self.get_vector_size())


class IclLogicSignal(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            icl_name: IclSignal,
            expression: list[list:str],
            ctx: str
        ) -> None:
        super().__init__(icl_name.get_name(), instance.get_hier(), instance.get_hier(), ctx)
        self.instance: IclInstance = instance
        self.icl_name: IclSignal = icl_name
        self.expression: list = expression

        # If ICL signal name is unsized
        if self.icl_name.get_size() == 0:
            self.icl_name.ovveride_indexes([0])
        
        # Logic Signal must be width of one bit
        assert(self.icl_name.get_size() == 1)

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.icl_name)

    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.icl_name)
    
    def get_vector_size(self) -> int:
        return 1
    
    def check_ang_get_sizes(self, expr: list) -> tuple:
        size_all = 0
        size_of_unsized_number = 0
        unsized_numbers = 0
        sized_numbers = 0       
        for item in expr:
            if isinstance(item, str):    
                size_all += 1
                sized_numbers += 1
            elif isinstance(item, IclNumber):
                unsized_numbers += 1
                size_all += item.get_bit_size()                    
                size_of_unsized_number += item.get_bit_size()
            else:
                raise ValueError("???")
        assert(unsized_numbers < 2)
        return (size_all, sized_numbers, unsized_numbers > 0)
    
    def create_expr_list(self, expr:list, size:int = -1):
        new_list = []
        for item in expr:
            if isinstance(item, str):    
                new_list += [item]
            elif isinstance(item, IclNumber):
                temp_list = []
                if size > 0:                 
                    item.resize(size)
                else:
                    item.resize(item.get_bit_size())
                for idx in range(item.get_icl_size()):
                    temp_list.append("{}".format(item.get_bit(idx).get_bin_str()))                      
                temp_list.reverse()

                if item.get_negation():
                    for idx, number in enumerate(temp_list):
                        temp_list[idx] = "1" if number == "0" else "0"
                new_list += temp_list          
            else:
                raise ValueError("???")
                        
        assert(len(new_list) > 0)
        return new_list

    def do_expr_2(self, exr, lvl = 0):
        print("do_expr", exr)
        expt_type = exr[0]
        exp_instances = []
        for item in exr[1:]:
            print("ITEM", item)
            if type(item) == list:
                exp_instances.append(self.do_expr_2(item, lvl+1))
            else:
                exp_instances.append(item)
            print("exp_instances", exp_instances)

        # In situations where we compare (IclDataInPort, IclDataOutPort, IclScanRegister, IclAlias) with an enum symbol (EnumRef)
        # Transform EnumRef to Concat(IclNumber) of that enum symbol
        if expt_type == "==" and isinstance(exp_instances[1], EnumRef):
            assert len(exp_instances) == 2, "Expected exactly two expressions for comparison"

            var_1, var_2 = exp_instances
            assert isinstance(var_1, ConcatSig), f"Expected first expression to be ConcatSig, got {type(var_1)}"
            assert isinstance(var_2, EnumRef), f"Expected second expression to be EnumRef, got {type(var_2)}"

            icl_items = var_1.get_all_icl_items()
            # Check that var_1 is referencing only to one ICL item(single object)
            assert len(icl_items) == 1, "Referencing more that one icl item"
            object_item = icl_items[0]

            # Check that object_item is one of the allowed types
            valid_types = (IclDataInPort, IclDataOutPort, IclScanRegister, IclAlias)
            assert isinstance(object_item, valid_types), f"Cannot compare {type(object_item)} with {type(var_2)}, {type(object_item)} cannot be assigned with enumeration reference"

            enumeration_name = object_item.get_enum_reference()
            assert enumeration_name, f"{object_item.get_name_with_hier()} is missing enumeration reference for it to be used in LogicalSignal"

            # Try to get enumeration based on name
            enumeration_reference: IclEnum = self.instance.get_icl_item_name(enumeration_name)
            assert enumeration_reference, f"Enumeration reference {enumeration_name} not found"

            # Check that the object_item has a reference to an ICL enum and validate size
            enumeration_reference_size = enumeration_reference.get_enum_size()
            var_1.check_fit(enumeration_reference_size)

            # Get the numeric value of the enum symbol
            enum_symbol_value = enumeration_reference.get_enum_number(var_2.get_name())
            exp_instances[1] = ConcatSig(self.instance, [enum_symbol_value], "number").get_list_for_expr()

        for idx, x in enumerate(exp_instances):
            print(x, type(x))
            assert(type(x) in [ConcatSig, list, EnumRef])
            if isinstance(x, ConcatSig):
                exp_instances[idx] = x.get_list_for_expr()

        print("do_expr in progress", exr, exp_instances, lvl), 
        return_item = ["x"]

        if expt_type in ["!", "~"]:
            assert(len(exp_instances) == 1)           
            var_1 = exp_instances[0]

            if(expt_type == "!"):
                assert(len(var_1) == 1)
            else:
                assert(len(var_1) > 0)

            return_item = []
            for item in var_1:
                if isinstance(item, str):    
                    return_item += [f"(not {item})"]
                elif isinstance(item, IclNumber):
                    item.negate()
                    return_item += [item]
                else:
                    raise ValueError("???")

        elif expt_type in ["nop", "()"]:
            assert(len(exp_instances) == 1)            
            return_item = exp_instances[0]

        elif (expt_type in ["&", "|", '^']) and (len(exp_instances) == 1):
            assert(len(exp_instances) == 1)            
            var_1 = exp_instances[0]
                       
            new_list = self.create_expr_list(var_1)

            # If there is only one bit for the expression
            # It does not make sense to do any operation and just pass bit/expr along
            if len(new_list) > 1:
                expr_op = "fail"
                if expt_type in ["&"]:
                    expr_op = "and"
                elif expt_type in ["|"]:
                    expr_op = "or"
                elif expt_type in ["^"]:
                    expr_op = "xor"
                return_item = ["({} {})".format(expr_op, " ".join(new_list))]
            else:
                return_item = new_list
                
        elif expt_type in [","]:
            assert(len(exp_instances) == 2)
            return_item = exp_instances[0] + exp_instances[1]

        elif expt_type in ["&", "&&", "|", "||", '^', "=="]:
            assert(len(exp_instances) == 2)            

            var_1 = exp_instances[0]
            size_all_1, sized_size_1, unsized_1 = self.check_ang_get_sizes(var_1)
            var_1_exprs = []

            var_2 = exp_instances[1]
            size_all_2, sized_size_2, unsized_2 = self.check_ang_get_sizes(var_2)
            var_2_exprs = []
            
            # Only one variable can be unsized
            assert((not unsized_1) | (not unsized_2))

            if unsized_1:
                var_2_exprs = var_2
                var_1_exprs = self.create_expr_list(var_1, size_all_2-sized_size_1)
                size_all_1 = size_all_2
            elif unsized_2:
                var_1_exprs = var_1
                var_2_exprs = self.create_expr_list(var_2, size_all_1-sized_size_2)
                size_all_2 = size_all_1
            else:
                var_1_exprs = var_1
                var_2_exprs = var_2

            # Sanity check
            assert(len(var_1_exprs) == len(var_2_exprs))
            assert(size_all_1 == size_all_2)
            
            print(var_1_exprs)
            print(var_2_exprs)

            expr_op = ""
            if expt_type in ["&", "&&"]:
                expr_op = "and"
                # Check that boolean operation has only expr. on each side
                if expt_type in ["&&"]:
                    assert((size_all_1 == 1) and (size_all_2 == 1))
            elif expt_type in ["|", "||"]:
                expr_op = "or"
                # Check that boolean operation has only expr. on each side
                if expt_type in ["||"]:
                    assert((size_all_1 == 1) and (size_all_2 == 1))
            elif expt_type in ["^"]:
                expr_op = "xor"
            elif expt_type in ["=="]:
                expr_op = "and"
            else:
               raise ValueError(f"Error {expt_type}")
            
            return_item = []
            if expt_type in ["=="]:
                for expr_idx, _ in enumerate(var_1_exprs):
                    val = var_2_exprs[expr_idx]
                    assert(val in ["0", "1"])
                    new_exp = f"{var_1_exprs[expr_idx]}" if val == "1" else f"(not {var_1_exprs[expr_idx]})"
                    return_item.append(new_exp)
                return_item = " ".join(return_item)
                return_item = [f"(and {return_item})"]
            else:
                for expr_idx, _ in enumerate(var_1_exprs):
                    return_item.append(f"({expr_op} {var_1_exprs[expr_idx]} {var_2_exprs[expr_idx]})")
        else:
            raise ValueError(f"Error {expt_type}")
                          
        # Entire expression, must be reduced to one bit
        if lvl == 0:    
            assert(isinstance(return_item, list))
            if not (len(return_item) == 1):
                raise RuntimeError(f"Expression {self.ctx} does return {len(return_item)} bit output, insted of one bit output, conv. expr.: {return_item}")
                                                        
        return return_item

    def check(self):
        print('\n\nEXP EXP EXP EXP EXP EXP EXP ')
        print(self.ctx)
        print(self.instance)
        print(self.icl_name)
        print(self.expression)
        print('do expression')

        a = self.do_expr_2(self.expression)

        print(self.ctx)
        print(a)

        #input()

class IclDataRegister(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            icl_name: IclSignal,
            ctx: str
        ) -> None:
        super().__init__(icl_name.get_name(), instance.get_hier(), instance.get_hier(), ctx)
        self.instance: IclInstance = instance
        self.icl_name: IclSignal = icl_name

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.icl_name)

    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.icl_name)
    
    def check(self):
        pass

class IclScanMux(IclItem):
    
    def __init__(self, instance: IclInstance, ctx, scan_mux: IclSignal, scan_select: ConcatSig, mux_selects: list[tuple[list[IclNumber],ConcatSig]]) -> None:
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
    
    def get_vector_size(self) -> int:
        return len(self.get_all_indexes())
        
    def check(self):
        self.scan_select.check()
        scan_sel_size = self.scan_select.get_vector_min_size()
        scan_sel_names = self.scan_select.get_all_named_indexes(scan_sel_size)

        scan_mux_names = self.get_all_named_indexes()
        scan_mux_size = 1 if self.scan_mux.get_size() == 0 else self.scan_mux.get_size()

        for selectee_list, tos in self.mux_selects:
            selectee_size = selectee_list[0].get_icl_size()
            for selectee_expr_smt in selectee_list:
                assert(type(selectee_expr_smt) == IclNumber)
                assert(selectee_list[0].get_icl_size() == selectee_size)
            assert(selectee_size == scan_sel_size)

            tos.check()      
            to_size = tos.get_vector_min_size()
            assert(scan_mux_size == to_size)

            tos_names = tos.get_all_named_indexes(scan_mux_size)

            selectee_list_expr_smt = []
            selectee_list_expr_py = []
            for selectee in selectee_list:
                selectee_expr_smt = []
                selectee_expr_py = []
                for idx, scan_sel_bit in enumerate(scan_sel_names):
                    pass
                    scan_sel_bit = scan_sel_bit.replace('.', '_')
                    print(selectee.get_bit(idx).get_number())
                    if(selectee.get_bit(idx).get_number()):
                        selectee_expr_smt.append(scan_sel_bit)
                        selectee_expr_py.append(scan_sel_bit)
                    else:
                        selectee_expr_smt.append("(not {})".format(scan_sel_bit))
                        selectee_expr_py.append("Not({})".format(scan_sel_bit))
                selectee_expr_smt = "(and {})".format(" ".join(selectee_expr_smt))
                selectee_expr_py = "And({})".format(",".join(selectee_expr_py))

                selectee_list_expr_smt.append(selectee_expr_smt)
                selectee_list_expr_py.append(selectee_expr_py)
            selectee_list_expr_smt = "(or {})".format(" ".join(selectee_list_expr_smt))
            selectee_list_expr_py = "Or({})".format(",".join(selectee_list_expr_py))

            self.connections += (list(zip(tos_names, scan_mux_names, [selectee_list_expr_smt], [selectee_list_expr_py])))


class IclPort(IclItem):

    def __init__(self, instance: IclInstance, ctx, port: IclSignal, attributes: list[IclAttribute] = None) -> None:
        super().__init__(port.get_name(), instance.get_hier(), instance.get_module_scope(), ctx)
        self.ports: list[IclSignal] = [port]
        self.attributes: dict[IclSignal:list[IclAttribute]] = {port:attributes}
        self.instace: IclInstance = instance
        
    def get_attributes(self, index: int = None)-> list[IclAttribute]:
        if index is not None:
            for port, attribute_list in self.attributes.items():
                if index in self.get_item_all_indexes([port]):
                    return attribute_list
            return []
        else:
            all_atttributes: list[IclAttribute] = []
            for port, attribute_list in self.attributes.items():        
                all_atttributes.extend(attribute_list)     
            return all_atttributes

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
        assert type(self) == type(icl_port), f"Having port name: {self.get_name()} assosiated with multiple port types is currently not supported"
        for port in icl_port.ports:
            if port in self.ports:
                raise ValueError(f"Port {port} aready in {self.ports}")
            self.ports.append(port)
        for att in icl_port.attributes:
            if att in self.attributes:
                raise ValueError(f"Attribute {att} aready in {self.attributes}")           
            self.attributes.append(att)

class AddPortSource():
    def add_source(self, port: IclSignal, source: ConcatSig) -> None:
        self.sources: dict[IclSignal:ConcatSig] = {port:source}

    def source_check(self):
        for port, source in self.sources.items():
            if source is not None:
                port_size = len(self.get_item_all_indexes([port]))
                source_size =  source.get_vector_min_size()

                # Check size
                assert(port_size == source_size) 

    def get_named_sourced_indexes(self) -> list[str]:
        name_source_indexes:list[str] = []
        for port, source in self.sources.items():
            size = len(self.get_item_all_indexes([port]))
            name_source_indexes.extend(source.get_all_named_indexes(size))
        return name_source_indexes

    def source_merge(self, item_source: "AddPortSource"):
        for port, source in item_source.sources.items():
            if port in self.sources:
                raise ValueError(f"Source is already defined for {port}")
            self.sources[port] = source

class AddPortEnable():
    def add_enable(self, port: IclSignal, enable: IclSignal) -> None:
        self.enables: dict[IclSignal:IclSignal] = {port:enable}

    def enable_check(self):
        for port, enable in self.enables.items():
            if enable is not None:
                enable_size = len(self.get_item_all_indexes([enable]))
                # Check size
                assert(enable_size == 1) 
                

    def enable_merge(self, item_source: "AddPortEnable"):
        for port, source in item_source.enables.items():
            if port in self.enables:
                raise ValueError(f"Enable is already defined for {port}")
            self.enables[port] = source

class AddPortRef():
    def add_ref(self, port: IclSignal, ref: str) -> None:
        self.reference: str = ref

    def ref_check(self):
        if self.reference:
            enum_item: IclEnum = self.instance.get_icl_item_name(self.reference)
            enum_size = enum_item.get_enum_size()
            port_size = self.get_vector_size()
            port_name = self.get_name()
            assert enum_size == port_size, f"Error, Enum refernce has diffrent size: {enum_size} than port {port_name} of size {port_size}"                   

    def ref_merge(self, item_source: "AddPortRef"):
        assert not (self.reference and item_source.reference), f"Port {self.get_name()} can not have more than one enum reference, {self.reference} : {item_source.reference}"
        self.reference: str = item_source.reference

    def get_enum_reference(self) -> str:
        return self.reference

class AddPortDefValue():
    def add_def(self, port: IclSignal, default: str | IclNumber) -> None:
        self.defaults: dict[IclSignal:str | IclNumber] = {port:default}

    def def_check(self):
        for port in self.defaults.keys():
            default:str | IclNumber= self.defaults[port]
            if default is not None:
                enum_size = default.get_enum_size()
                port_size = len(self.get_item_all_indexes([port]))
                # Check size
                assert(enum_size == port_size) 

    def def_merge(self, item_source: "AddPortRef"):
        for port, value in item_source.defaults.items():
            if port in self.defaults:
                raise ValueError(f"Default is already defined for {port}")
            self.defaults[port] = value

class AddPolarity():
    def add_polarity(self, port: IclSignal, polarity: bool) -> None:
        self.polarities: dict[IclSignal:bool] = {port:polarity}

    def polarity_check(self):
        for port in self.polarities.keys():
            polarity: bool = self.polarities[port]
            if polarity is not None:
                assert(polarity is bool)
            else:
                polarity = bool(1)

    def polarity_merge(self, item_source: "AddPolarity"):
        for port, value in item_source.polarities.items():
            if port in self.polarities:
                raise ValueError(f"Polarity is already defined for {port}")
            self.polarities[port] = value

class AddClockSettings():
    def add_clock(self, port: IclSignal, clock_settings: dict) -> None:
        self.clock_settings: dict[IclSignal:dict] = {port:clock_settings}

    def clock_check(self):
        pass 

    def clock_merge(self, item_source: "AddClockSettings"):
        for port, value in item_source.clock_settings.items():
            if port in self.clock_settings:
                raise ValueError(f"Clock setting is already defined for {port}")
            self.clock_settings[port] = value

class IclScanInPort(IclPort):
    pass

class IclScanOutPort(IclPort, AddPortSource, AddPortEnable):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig,
            enable: IclSignal
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_source(port, source)
        self.add_enable(port, enable)

    def check(self) -> int:
        super().check()
        self.source_check()
        self.enable_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.source_merge(icl_port)
        self.enable_merge(icl_port)

class IclDataInPort(IclPort, AddPortRef, AddPortDefValue):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            default: str | IclNumber,
            ref: str            
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_def(port, default)
        self.add_ref(port, ref)

    def check(self) -> int:
        super().check()
        self.def_check()
        self.ref_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.def_merge(icl_port)
        self.ref_merge(icl_port)

class IclDataOutPort(IclPort, AddPortSource, AddPortEnable, AddPortRef):

    def __init__(
            self,
            instance: IclInstance,
            ctx,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig,
            enable: IclSignal,
            ref: str            
        ) -> None:
        
        super().__init__(instance, ctx, port, attributes)
        self.add_source(port, source)
        self.add_enable(port, enable)
        self.add_ref(port, ref)

    def check(self) -> int:
        super().check()
        self.source_check()
        self.enable_check()
        self.ref_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.source_merge(icl_port)
        self.enable_merge(icl_port)
        self.ref_merge(icl_port)

class IclShiftEnable(IclPort):
    pass

class IclUpdateEnable(IclPort):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute]
        ) -> None:
        super().__init__(instance, ctx, port, attributes)

class IclCaptureEnable(IclPort):
    pass


class IclToShiftEnable(IclPort, AddPortSource):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_source(port, source)

    def check(self) -> int:
        super().check()
        self.source_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.source_merge(icl_port)

class IclToUpdateEnable(IclPort, AddPortSource):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_source(port, source)

    def check(self) -> int:
        super().check()
        self.source_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.source_merge(icl_port)

class IclToCaptureEnable(IclPort, AddPortSource):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_source(port, source)

    def check(self) -> int:
        super().check()
        self.source_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.source_merge(icl_port)     

class IclSelectPort(IclPort):
    pass

class IclToSelectPort(IclPort, AddPortSource):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_source(port, source)

    def check(self) -> int:
        super().check()
        self.source_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.source_merge(icl_port)

class IclResetPort(IclPort, AddPolarity):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            polarity: bool
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_polarity(port, polarity)

    def check(self) -> int:
        super().check()
        self.polarity_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.polarity_merge(icl_port)

class IclToResetPort(IclPort, AddPolarity, AddPortSource):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig,
            polarity: bool
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_polarity(port, polarity)
        self.add_source(port, source)

    def check(self) -> int:
        super().check()
        self.polarity_check()
        self.source_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.polarity_merge(icl_port)                     
        self.source_merge(icl_port)


class IclTmsPort(IclPort):
    pass

class IclToTmsPort(IclPort, AddPortSource):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_source(port, source)

    def check(self) -> int:
        super().check()
        self.source_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.source_merge(icl_port)

class IclTckPort(IclPort):
    pass

class IclToTckPort(IclPort):
    pass


class IclClockPort(IclPort, AddClockSettings):
    
    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            clock_settings: dict
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_clock(clock_settings)

    def check(self) -> int:
        super().check()
        self.clock_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.clock_merge(icl_port)

class IclToClockPort(IclPort, AddClockSettings, AddPortSource):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig,
            clock_settings: dict
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_source(port, source)
        self.add_clock(clock_settings)

    def check(self) -> int:
        super().check()
        self.source_check()
        self.clock_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.source_merge(icl_port)
        self.clock_merge(icl_port)

class IclTrstPort(IclPort):
    pass

class IclToTrstPort(IclPort, AddPortSource):

    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            source: ConcatSig
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_source(port, source)

    def check(self) -> int:
        super().check()
        self.source_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.source_merge(icl_port)

class IclIrSelectPort(IclPort):
    pass

class IclAddressPort(IclPort):
    pass

class IclWriteEnPort(IclPort):
    pass

class IclReadEnPort(IclPort):
    pass
