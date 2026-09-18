from .icl_common import *
import warnings

class IclSignal:

    def __init__(self, name: str,  index_left=None, index_right = None):
        self.name:str = name
        self.negation: bool = 0
        self.dir_right_to_left: bool = 1
        self.hier:list[str] = []

        if((index_right is not None) and (index_left is not None)):
            if index_left <= index_right:
                self.indexes =  list(range(index_left, index_right + 1))
                self.dir_right_to_left = 0
            else:
                self.indexes =  list(range(index_left, index_right - 1, -1))            
                self.dir_right_to_left = 1                
        elif((index_right is None) and (index_left is not None)):
            self.indexes = [index_left]
        elif((index_right is not None) and (index_left is None)):            
            raise ValueError("index_right defined but index_left is not defined")
        else:
            self.indexes = []

    # 1 - right to left ([13:00]), 13 MSB index, 00 LSB index
    # 0 - right to left ([00:13]), 00 MSB index, 13 LSB index
    def get_direction(self) -> bool:
        return self.dir_right_to_left

    def get_right_index(self) -> int:
        return self.get_direction() if self.get_indexes()[0] else self.get_indexes()[-1]

    def get_left_index(self) -> int:
        return self.get_direction() if self.get_indexes()[-1] else self.get_indexes()[0]
            
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
        if(value_type in ["dec", "bin"]):
            for remove_char in "_' DdHhBb":
                source = source.replace(remove_char, "")
        else: # hex
            for remove_char in "_' Hh":
                source = source.replace(remove_char, "")

        # Allowed symbols
        allowed_symbols = "-Xx0123456789AaBbCcDdEeFf"
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
            raise ValueError("Object of class {0} can not be concated with object of class {1}".format(type(self).__name__ , type(icl_number).__name__))
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
    
    def bit_reversal(self):
        assert(self.sized_number())
        x = IclNumber(self.get_bin_str()[::-1], "bin", self.get_icl_size())        
        self.r_number = x.r_number
        self.x_number = x.x_number
        self.icl_size = x.icl_size
        self.bit_size = x.bit_size

    def set_value(self, value: int):
        self.x_number = 0
        self.r_number = value
        if self.sized_number():
            self.r_number = self.r_number & ((1 << self.icl_size)-1)

    def set_to_unknown(self):
            self.r_number = 0
            if(self.icl_size != -1):
                self.x_number = (1 << self.icl_size) - 1
            else:
                self.x_number = (1 << self.bit_size) - 1

    def set_bit(self, value: int, index: int):
        if((index >= self.icl_size) and (self.icl_size != -1)):
            raise ValueError("Index {} is bigger than size {}".format(index, self.icl_size))
        else:
            if(isinstance(value, str)):
                if(value in ["x", "X"]):
                    value = -1
                elif(value in ["1", "0"]):
                    value = int(value)
                else:
                    raise ValueError(f"Unexpected value -> {value}, only expected string values are ['X', 'x', '1', '0']")

            if value not in (0, 1, -1):
                raise ValueError("The bit value must be 0, 1 or -1")

            mask = ~(1 << index)
            self.r_number &= mask
            self.x_number &= mask

            if(value != -1):
                self.r_number = self.r_number | (value << index)
            else:
                self.x_number = self.x_number | (1 << index)

    def get_bit(self, index) -> "IclNumber":
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
            raise ValueError("Numbers with x(UNKNOWN) cannot be substracted")
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
        return self.__truediv__(obj_2)
    
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
    def __init__(self, instance: "IclInstance", concat_sigs: list[IclSignal | IclNumber], concat_type) -> None:
        self.type: str = concat_type
        self.instance: "IclInstance" = instance
        self.concat_sigs: list[IclSignal | IclNumber] = concat_sigs

        assert(len(concat_sigs) > 0)
        assert(concat_sigs[0] != None)

        # Unsized check can be done immediately
        self.check_unsized_numbers()
        


    def check(self) -> None:
        valid_types = {
            CONCAT_SCAN_T : [IclScanInPort, IclScanRegister, IclScanMux, IclScanOutPort, IclAlias],
            CONCAT_DATA_T : [IclDataInPort, IclDataOutPort, IclSelectPort, IclScanRegister,  IclLogicSignal, IclAlias, IclDataRegister, IclToIrSelectPort, IclToSelectPort, IclOneHotDataGroup, IclOneHotScanGroup, IclDataMux],
            CONCAT_ALIAS_T: [IclDataInPort, IclDataOutPort, IclScanRegister, IclDataRegister],
            CONCAT_RESET_T: [IclResetPort, IclToResetPort, IclScanRegister, IclDataInPort, IclDataOutPort],
            CONCAT_CE_T: [IclCaptureEnable, IclToCaptureEnable],
            CONCAT_SE_T: [IclShiftEnable, IclToShiftEnable],
            CONCAT_UE_T: [IclUpdateEnable, IclToUpdateEnable],
            CONCAT_TRST_T: [IclTrstPort, IclToTrstPort],
            CONCAT_TMS_T: [IclTmsPort, IclToTmsPort],
            CONCAT_CLOCK_T: [IclClockPort, IclToClockPort, IclTckPort, IclTckPort],
            CONCAT_TCK_T: [IclTckPort, IclTckPort],
            CONCAT_NUMBER_T: [IclNumber],
            CONCAT_UNKNOWN_T: []
        }

        for sig in self.concat_sigs:
            if isinstance(sig, IclNumber):
                continue
            checkSigExistance(self.instance, sig)
            icl_item = self.instance.get_icl_item_name(sig.get_relative_name())
            if(self.type != CONCAT_UNKNOWN_T):
                assert type(icl_item) in valid_types[self.type], f"invalid type {type(icl_item)} for {self.type} in ConcatSig {self.concat_sigs}" 

    def set_type(self, type:str):
        self.type = type

    def check_unsized_numbers(self) -> int:
        unsized_numbers = sum(1 for sig in self.concat_sigs if isinstance(sig, IclNumber) and not sig.sized_number())
        if not (unsized_numbers in {0, 1}):
            raise ValueError(f"ConcatSig {self.get_all_sigs()} has {unsized_numbers} unsized numbers max 1") 
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
    
    def get_all_sigs(self) -> list[IclSignal | IclNumber]:
        return self.concat_sigs

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
                    if(isinstance(sel_item, IclInstance)):
                        raise ValueError(f"{sig.get_relative_name()} -> {sel_item.get_hier()} is an instance")
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
            if min_size != source_size:
                raise ValueError(f"{self.concat_sigs}({min_size}) does not fit to size of {source_size}, instace: {self.instance.get_name_with_hier()}")
        else:
            difference = source_size - min_size
            if not (difference >= 0):
                raise ValueError(f"{self.concat_sigs}({min_size}) does not fit to size of {source_size}, instace: {self.instance.get_name_with_hier()}")

def checkSigExistance(instance: "IclInstance", signal:IclSignal):
    # print(singal.get_relative_name())
    icl_item = instance.get_icl_item_name(signal.get_relative_name())

    item_indexes = icl_item.get_all_indexes()
    signal_indexes = signal.get_indexes()
    missing_signal_indexes = []
    for sig_idx in signal_indexes:
        if not sig_idx in item_indexes:
            missing_signal_indexes.append(sig_idx)

    if missing_signal_indexes:
        raise ValueError(f"{icl_item.get_name_with_hier()}{missing_signal_indexes} not present in {icl_item.get_name_with_hier()}{item_indexes}")

class IclItem:

    def __init__(
            self,
            instance: "IclInstance",
            icl_name: str,
            icl_hier: str,
            module_scope: str,
            ctx: str
        ) -> None:

        self.instance: IclInstance = instance            
        self.ctx = ctx
        self.name = icl_name
        self.hier = icl_hier
        self.module_scope = module_scope
        self.icl_items = []   

    def get_instance(self) -> "IclInstance":
        return self.instance

    def get_name(self):
        return self.name

    def get_hier(self) -> str:    
        return self.hier
    
    def get_module_scope(self):
        return self.module_scope
       
    def get_name_with_hier(self):
        return "{}.{}".format(self.hier, self.name) if self.hier else self.name 

    def get_item_all_indexes(self, icl_sig: IclSignal) -> list[int]:
        if(type(icl_sig) == list):
            indexes = [port.get_indexes() for port in self.ports]
            all_numbers = [num if num else 0 for sublist in indexes for num in sublist]    
            return all_numbers
        else:
            all_numbers = icl_sig.get_indexes()
            if(not all_numbers):
                all_numbers = [0]
            return all_numbers
    
    def get_item_all_named_indexes(self, icl_sig: IclSignal) -> list[str]:
        named_indexes = []
        for index in self.get_item_all_indexes(icl_sig):
            named_indexes.append(add_last_number(self.get_name_with_hier(), index))
        return named_indexes

    def get_signal_indexes(self, instance, signal: IclSignal) -> list[int]:
        assert(isinstance(signal, IclSignal))
        
        signal_name = signal.get_relative_name()
        icl_item = instance.get_icl_item_name(signal_name)  
        
        indexes = []
        if(signal.get_size()):
            indexes = signal.get_indexes()
        else:
            for index in range(icl_item.get_vector_size()):
                indexes.append(index)
            indexes.reverse()
        return indexes
            
    def get_signal_all_named_indexes(self, instance, all_sigs: list[IclSignal]) -> list[str]:
        assert(all_sigs)
        
        named_indexes = []
        for signal in all_sigs:
            signal_full_name = instance.get_icl_item_name(signal.get_relative_name()).get_name_with_hier()  

            for index in self.get_signal_indexes(instance, signal):
                named_indexes.append(add_last_number(signal_full_name, index))
        
        return named_indexes


class IclInstance(IclItem):

    def __init__(self, icl_name: str, icl_hier: str, module_scope: str, ctx) -> None:
        super().__init__(self, icl_name, icl_hier, module_scope, ctx)
        self.attributes = {}
        self.connections: list[{IclSignal,ConcatSig}] = []
        self.parameters_override = {}
        self.parameters = {}
        self.port_seq: dict = {}
        icl_graph = None

        # Populated by check()
        self.connection_routing: dict[str:str] = {}
        
    def im_top_instace(self):
        return self.get_hier() == ""

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
                        if(not isinstance(icl_item, IclInstance)):
                            raise ValueError(f"ICL name: {name} is separated into hier path of a IclInstance {item_to_search} and name {name_seq}, but {item_to_search} is a {type(icl_item)}" )
                        return icl_item.get_icl_item_name(".".join(name_seq))
            raise ValueError("Item {} not found in instace of {} module {}".format(name,self.get_hier(), self.get_module_scope()))
    
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

        # Check all instances under this instance
        for item in instances:
            print(f"{self.get_name_with_hier()} -> Check on {item} {item.get_name()}")
            item.check()

        # IEEE 1687: A module_def having at least one ScanRegister with a specified ResetValue
        # shall have at most a single reset_signal so that the source of the reset signal for
        # the ScanRegister is unambiguous. Additionally, that reset signal must be scalar (1-bit),
        # because a multi-bit reset port leaves it ambiguous which bit drives the register reset.
        scan_regs_with_reset = [
            item for item in self.get_icl_item_type(IclScanRegister)
            if item.in_reset_value is not None
        ]
        reset_ports = self.get_icl_item_type(IclResetPort)

        if scan_regs_with_reset:
            reg_names = [r.get_name() for r in scan_regs_with_reset]

            if len(reset_ports) > 1:
                port_names = [p.get_name() for p in reset_ports]
                raise ValueError(
                    f"Module '{self.get_name()}': {len(reset_ports)} reset signals declared "
                    f"({port_names}), but ScanRegisters with ResetValue require at most one "
                    f"reset signal. Affected registers: {reg_names}. [{self.ctx}]"
                )

            if len(reset_ports) == 1 and reset_ports[0].get_vector_size() > 1:
                raise ValueError(
                    f"Module '{self.get_name()}': reset signal '{reset_ports[0].get_name()}' "
                    f"is {reset_ports[0].get_vector_size()} bits wide; ScanRegisters with "
                    f"ResetValue require a scalar (1-bit) reset signal. "
                    f"Affected registers: {reg_names}. [{self.ctx}]"
                )

        # Check all items (icl items) which are not instances
        print(non_instaces)
        for item in non_instaces:
            print("Check", item, item.get_name())
            item.check()

        # Module checks
        #######################             

        # Scan interface checks
        #######################
        # 6.4.16 - a) A handoff module with more than one port of function ScanInPort or more than one port of function
        # ScanOutPort shall define as many ScanInterface statements as there are scan interfaces in the
        # module. ScanInterface statements shall remain optional for internal modules.
        if(self.instance.im_top_instace()):
            all_ports: list[str] = []
            scan_in_ports: list[IclScanInPort] = self.instance.get_icl_item_type(IclScanInPort)
            scan_out_ports: list[IclScanOutPort] = self.instance.get_icl_item_type(IclScanOutPort)
            # Bug fix: each port.get_all_named_indexes() returns a list; must flatten
            for port in scan_in_ports:
                all_ports.extend(port.get_all_named_indexes())
            for port in scan_out_ports:
                all_ports.extend(port.get_all_named_indexes())
            num_of_scan_in_ports:  int = sum([port.get_vector_size() for port in scan_in_ports])
            num_of_scan_out_ports: int = sum([port.get_vector_size() for port in scan_out_ports])
            scan_interfaces: list[IclScanInterface] = self.instance.get_icl_item_type(IclScanInterface)

            if((num_of_scan_in_ports > 1) or (num_of_scan_out_ports > 1)):
                for interface in scan_interfaces:
                    for chain in interface.chains:
                        for port in chain["ports"]:
                            # chain["ports"] stores IclSignal objects; get_icl_item_name expects a string
                            icl_port = self.instance.get_icl_item_name(port.get_name())
                            if(not isinstance(icl_port, (IclScanInPort, IclScanOutPort))):
                                continue
                            icl_sigs = self.instance.get_signal_all_named_indexes(self.instance, [port])
                            for port_idx in icl_sigs:
                                assert(port_idx in all_ports)
                                all_ports.remove(port_idx)
                assert(len(all_ports) == 0)

            # If handoff module does not have a scan interface, try to create it
            # Only try to create it if there is only one pair of ScanInPort and ScanOutPort and it is a client interface, not 
            # a host interface, because if a top module with scan chain does not have a client interface, the module
            # cannot be driven
            if((num_of_scan_in_ports == 1) and (num_of_scan_out_ports == 1) and (len(scan_interfaces) == 0)):
                interface_name = "default_interface"     
                interface_attributes: list[IclAttribute] = []
                interface_ports: list[IclSignal] = []
                chains: list[dict] = [
                    {
                    "name": "!default-chain!",
                    "attr": [],
                    "ports": [IclSignal(scan_in_ports[0].get_name()), IclSignal(scan_out_ports[0].get_name())],
                    "default": None,
                    }
                ]
                sel_ports: list[IclSelectPort] = self.instance.get_icl_item_type(IclSelectPort)
                tms_ports: list[IclTmsPort] = self.instance.get_icl_item_type(IclTmsPort)
                shiften_ports: list[IclShiftEnable] = self.instance.get_icl_item_type(IclShiftEnable)
                assert(not self.instance.get_icl_item_type(IclToSelectPort))
                assert(not self.instance.get_icl_item_type(IclToTmsPort))
                # 6.4.6.11- a)A selectPort_name shall be associated with a ScanInterface -----,
                # or when there is a single undeclared scan client interface and a single selectPort_name.
                if((len(sel_ports) == 1) and (len(tms_ports) == 0)):
                    assert(sel_ports[0].get_vector_size() == 1)
                    interface_ports.append(IclSignal(sel_ports[0].get_name()))
                elif((len(shiften_ports) == 1) and (len(tms_ports) == 0)):
                    assert(shiften_ports[0].get_vector_size() == 1)
                    interface_ports.append(IclSignal(shiften_ports[0].get_name()))
                elif((len(shiften_ports) == 0) and (len(sel_ports) == 0) and (len(tms_ports) == 1)):
                    assert(tms_ports[0].get_vector_size() == 1)
                    interface_ports.append(IclSignal(tms_ports[0].get_name()))
                else:
                    raise ValueError( f"Top Module '{self.get_module_scope()}': failed to create default scan interface from avaliable ports" )
                scan_interface = IclScanInterface(self.instance, interface_name, interface_attributes, interface_ports, chains, "generated")
                self.add_icl_item(scan_interface)
                scan_interface.check()

        # 3. Correct type of input connection into instance this instance
        # (icl_process is not able to tell what kind of type is source:ConcatSig )
        for connection in self.connections:
            in_signal: IclSignal = list(connection.keys())[0]
            source: ConcatSig = list(connection.values())[0]
            in_port = self.get_icl_item_name(in_signal.get_name())

            if(isinstance(in_port, IclResetPort)):
                source.set_type(CONCAT_RESET_T)
            elif(isinstance(in_port, IclScanInPort)):
                source.set_type(CONCAT_SCAN_T)
                for idx, item in enumerate(source.get_all_icl_items()):
                    if(isinstance(item, IclInstance)):
                        scan_items = item.get_icl_item_type(IclScanOutPort)
                        if(len(scan_items) == 1):
                            new_source = IclSignal(scan_items[0].get_name())
                            new_source.add_hiearachy(source.concat_sigs[idx].get_relative_name()) 
                            source.concat_sigs[idx] = new_source
                            print(f"Warning: Input connection to instance {self.get_hier()} is instance and that is not allowed," +
                                    f"but because instance has only one scan input it is assumed this is the input connection")

            elif(isinstance(in_port, (IclDataInPort, IclAddressPort, IclReadEnPort, IclWriteEnPort, IclSelectPort))):
                source.set_type(CONCAT_DATA_T)
            elif(isinstance(in_port, IclClockPort)):
                source.set_type(CONCAT_CLOCK_T)
            elif(isinstance(in_port, IclClockPort)):
                source.set_type(CONCAT_TCK_T)
            elif(isinstance(in_port, IclTckPort)):
                source.set_type(CONCAT_TCK_T)
            elif(isinstance(in_port, IclShiftEnable)):
                source.set_type(CONCAT_SE_T)
            elif(isinstance(in_port, IclCaptureEnable)):
                source.set_type(CONCAT_CE_T)
            elif(isinstance(in_port, IclUpdateEnable)):
                source.set_type(CONCAT_UE_T)
            elif(isinstance(in_port, IclTmsPort)):
                source.set_type(CONCAT_TMS_T)
            elif(isinstance(in_port, IclTrstPort)):
                source.set_type(CONCAT_TRST_T)
            else:
                raise ValueError(f"Unexpected instance input to port {in_port}, ({type(in_port)}) {in_signal.get_name()} to {self.instance.get_name_with_hier()}")
            
            # IclInstance is not allowed to source a port without specifing which port is used
            for item in source.get_all_icl_items():
                if(isinstance(item, IclInstance)):
                    raise ValueError(f"IclInstance must specify port which will be passed as input connection, {self.get_hier()} - {in_port.get_name()}")

        # Solve connection between this instance and child instances
        child_instance: IclInstance
        for child_instance in instances:
            all_indexed_destiations: list[str] = [] 
            all_indexed_scan_in_destiations: list[str] = []
            all_indexed_data_in_destiations: list[str] = []
            all_indexed_scan_in_ports: list[str] = [indexed_port for port in child_instance.get_icl_item_type(IclScanInPort) for indexed_port in port.get_all_named_indexes()]
            all_indexed_data_in_ports: list[str] = [indexed_port for port in child_instance.get_icl_item_type(IclDataInPort) for indexed_port in port.get_all_named_indexes()]
            
            print(f"{self.get_name_with_hier()} -> Solving connections for instance: {child_instance}, {child_instance.get_name_with_hier()}")

            for connection in child_instance.connections:
                destination: IclSignal = list(connection.keys())[0]
                source: ConcatSig = list(connection.values())[0]
                in_port = child_instance.get_icl_item_name(destination.get_name())
                
                unsized_destination = (destination.get_size() == 0)
                if unsized_destination:
                    destination_size = len(child_instance.get_signal_indexes(child_instance, destination))
                    destination_named_indexes = child_instance.get_signal_all_named_indexes(child_instance, [destination])
                else:
                    destination_size = destination.get_size()
                    destination_named_indexes = child_instance.get_signal_all_named_indexes(child_instance, [destination])

                # Connection between source and destination must match in size, requried by standard 
                try:
                    source.check_fit(destination_size)
                except Exception as e:
                    raise ValueError(f"Connection {destination} = {source.get_all_sigs()}, size mistmach, instance: {child_instance.get_name_with_hier()}") from e

                for indexed_name in destination_named_indexes:
                    if isinstance(in_port, IclScanInPort):
                        all_indexed_scan_in_destiations.append(indexed_name) 
                    
                    if isinstance(in_port, IclDataInPort):
                        all_indexed_data_in_destiations.append(indexed_name) 
                    
                    if indexed_name in all_indexed_destiations:
                        raise ValueError(f"Input port: {indexed_name} of module instance: {child_instance.get_name_with_hier()} already once defined in connections")
                    else:
                        all_indexed_destiations.append(indexed_name)

                init_pol = 0
                if((type(in_port) == IclResetPort) or (type(in_port) == IclToResetPort)):
                    init_pol = 1 
                
                all_indexed_source = source.get_all_named_indexes_with_prefix(max_size=destination_size, neg_on=init_pol)
                for idx, _ in enumerate(destination_named_indexes):
                    child_instance.connection_routing[destination_named_indexes[idx]] = all_indexed_source[idx]
            
            # Check that every bit of scan in port or data in port has a connection
            scan_in_missing = list(set(all_indexed_scan_in_ports) - set(all_indexed_scan_in_destiations))
            if scan_in_missing:
                raise ValueError(f"Missing ScanInPort connections: {scan_in_missing}, instance: {child_instance.get_name_with_hier()}")
            data_in_missing = list(set(all_indexed_data_in_ports) - set(all_indexed_data_in_destiations))
            if data_in_missing:
                raise ValueError(f"Missing DataInPort connections: {data_in_missing}, instance: {child_instance.get_name_with_hier()}")
                
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

    # For keeping track sequence of ports from top to bottom in ICL module
    def add_port_to_sequence(self, port_type:str, port: IclSignal):
        if(port_type in self.port_seq):
            #self.port_seq[port_type].append(port)
            self.port_seq[port_type].insert(0, port)
        else:             
            self.port_seq[port_type] = [port]

    def get_port_type_sequence(self, port_type: str) -> ConcatSig | None:
        if(port_type in self.port_seq):
            return ConcatSig(self.instance,  self.port_seq[port_type], CONCAT_UNKNOWN_T)
        else:
            return None
    
class IclEnum(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            enum_name: str,
            enum_items: list[tuple[str,IclNumber]],
            ctx: str
        ) -> None:
        super().__init__(instance, enum_name, instance.get_hier(), instance.get_hier(), ctx)

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
        super().__init__(instance, alias_name.get_name(), instance.get_hier(), instance.get_hier(), ctx)

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
        #print(side_1, side_2)
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
        super().__init__(instance, att_name, instance.get_hier(), instance.get_module_scope(), ctx)
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
        
        super().__init__(instance, scan_reg.get_name(), instance.get_hier(), instance.get_hier(), ctx)

        # Inital values
        self.icl_name = scan_reg
        self.in_attributes: list[IclAttribute] = in_attributes
        self.scan_in_source: IclSignal = in_scan_in_source
        self.in_default_value: ConcatSig | EnumRef = in_default_value
        self.in_capture_source: ConcatSig | EnumRef = in_capture_source
        self.in_reset_value: ConcatSig | EnumRef = in_reset_value
        self.in_ref_enum: str = in_ref_enum

        # Assigned by function check (transforming EnumRef to ConcatSig + size checks)
        self.checked_scan_in_source_name: str
        self.capture_source: ConcatSig = None
        self.reset_source: ConcatSig = None
        self.default_value_source: ConcatSig = None

        # Register values
        self.scan_reg_size = len(self.get_all_named_indexes())
        self.default_value = IclNumber("x", "bin", self.scan_reg_size)
        self.current_value = IclNumber("x", "bin", self.scan_reg_size)
        self.next_value    = IclNumber("x", "bin", self.scan_reg_size)
        self.expected_data = IclNumber("x", "bin", self.scan_reg_size)
        self.bits_to_read  = IclNumber("0", "bin", self.scan_reg_size)
        
        self.activate = 0
        self.select_clause = ""

        # For retargeting, false by default, if register has valid selectin it will be updated
        self.scan_selection_smt: str = "false"

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

    def set_next_iapply(self):
        self.activate = 1

    def get_bits_to_read(self):
        return self.bits_to_read
    
    def set_read_bits(self, value: int):
        self.bits_to_read.set_value(value)

    def set_expected_bits(self, value: int):
        self.expected_data.set_value(value)

    def get_expected_bits(self):
        return self.expected_data

    def disable_next_iapply(self):
        self.activate = 0
            
    def is_in_next_iapply(self):
        return self.activate
    
    def reset(self):

        self.disable_next_iapply()
        self.bits_to_read.set_value(0)

        # Resets only register which has reset
        # Values of register with reset will switch to reset values
        # Values of register without reset will stay the same
        if(self.reset_source):
            self.current_value = self.reset_source.get_icl_number().copy()
            self.next_value = self.reset_source.get_icl_number().copy()
        else:
            self.current_value = self.current_value.copy()
            self.next_value = self.current_value.copy()
            
    def get_vector_size(self) -> int:
        # vector_size = 0
        # if(self.scan_reg.get_size()):
        #     vector_size += self.scan_reg.get_size()
        # else:
        #     vector_size += 1
        # return vector_size
        return self.scan_reg_size
    
    def get_capture_source(self) ->  ConcatSig | EnumRef:
        return self.capture_source
    
    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.icl_name)
    
    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.icl_name)
    
    def get_msb_index(self) -> int:
        return self.get_all_indexes()[0]
    
    def get_lsb_index(self) -> int:
        return self.get_all_indexes()[-1]

    def get_named_msb(self) -> str:
        return self.get_item_all_named_indexes(self.icl_name)[0]

    def get_named_lsb(self) -> str:
        return self.get_item_all_named_indexes(self.icl_name)[-1]
        
    def get_scanin_named_index(self) -> str:
        return self.checked_scan_in_source_name
    
    def get_enum_reference(self) -> str:
        return self.in_ref_enum

    def check(self):

        if self.in_ref_enum:
            enumeration: IclEnum = self.instance.get_icl_item_name(self.in_ref_enum)
            assert enumeration.get_enum_size() == self.get_vector_size(),\
                f"IclScanRegister is referencing IclEnum that has size of {enumeration.get_enum_size()} but IclScanRegister has size of {self.get_vector_size()}: {self.ctx}"
            
        def enum_symbol_check(self, in_data, concat_type) -> ConcatSig:
            if isinstance(in_data, EnumRef):
                assert self.in_ref_enum, f"IclScanRegister uses enum symbol references without referencing concrete IclEnum: {self.ctx}"
                enumeration: IclEnum = self.instance.get_icl_item_name(self.in_ref_enum)
                enum_symbol_value = enumeration.get_enum_number(in_data)
                return ConcatSig(self.instance, [enum_symbol_value], concat_type)
            else:
                return in_data
        
        self.default_value_source = enum_symbol_check(self, self.in_default_value, CONCAT_NUMBER_T)
        self.capture_source = enum_symbol_check(self, self.in_capture_source, CONCAT_DATA_T)
        self.reset_source = enum_symbol_check(self, self.in_reset_value, CONCAT_NUMBER_T)

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

        if self.default_value_source:
            self.default_value_source.check()
            self.default_value_source.check_fit(self.get_vector_size())
            if not self.default_value_source.sized_number():
                self.default_value_source.resize(self.get_vector_size())


        # Check, scan in source,
        # 1. Make sure it exits
        # 2. Make sure it maps to one bit source
        # 3. If source points to scan register, make sure it points to the rightmost index
        if not self.scan_in_source:
            raise ValueError(f"Scan in source is not defined: {self.get_name_with_hier()} -> {self.ctx}")
        else:
            checkSigExistance(self.get_instance(), self.scan_in_source);
            icl_item = self.instance.get_icl_item_name(self.scan_in_source.get_relative_name())           
            signal_full_name = icl_item.get_name_with_hier()  
            source = self.get_signal_all_named_indexes(self.instance, [self.scan_in_source])
            assert(len(source) > 0)    

            if self.scan_in_source.get_size() == 0:
                if len(source) == 1:
                    self.checked_scan_in_source_name = source[0]
                elif len(source) > 1:
                    if isinstance(icl_item, IclScanRegister):
                        self.checked_scan_in_source_name = add_last_number(signal_full_name, icl_item.get_lsb_index())
                    else:                   
                        raise ValueError(f"Scan in source {self.scan_in_source} points to multibit source, define which bit: {self.get_name_with_hier()} -> {self.ctx}")                    
            elif self.scan_in_source.get_size() == 1:
                    if isinstance(icl_item, IclScanRegister):
                        if self.scan_in_source.get_indexes()[0] == self.scan_in_source.get_right_index():
                            self.checked_scan_in_source_name = source[0]
                        else:
                            raise ValueError(f"Scan in source {self.scan_in_source} points to ScanRegister source, but not to rightmost index : {self.get_name_with_hier()} -> {self.ctx}")                    
                    else:
                        self.checked_scan_in_source_name = source[0]
            else:
                raise ValueError(f"Scan in source {self.scan_in_source} is defined as range, only one bit input is allowed: {self.get_name_with_hier()} -> {self.ctx}")

        
        # Calculate default value
        #   Default is zero
        #   Reset value can overwrite Default
        #   Default value can overwrite Reset value
        
        if self.reset_source and self.default_value_source:
            self.default_value = IclNumber("x", "bin", self.scan_reg_size)

            a = self.reset_source.get_icl_number().copy()
            b = self.default_value_source.get_icl_number().copy()
            assert(a.get_icl_size() == b.get_icl_size())

            for idx in range(a.get_icl_size()):
                # When both scanRegister_defaultLoadValue and scanRegister_resetValue exist, the values in the
                # bits of scanRegister_defaultLoadValue shall match the non-X values in the corresponding bits of
                # scanRegister_resetValue.        
                a_char =  a.get_bit(idx).get_bin_str()
                b_char =  b.get_bit(idx).get_bin_str()

                if((b_char in ["0","1"]) and (a_char not in ["x"])):
                    if(b_char != a_char):
                        raise ValueError(f"{a} - {b} Both values must match in the non-X values {self.ctx}")

                if(b_char == "x"):
                    self.default_value.set_bit(a_char, idx)
                else:
                    self.default_value.set_bit(b_char, idx)

        elif self.reset_source:
            self.default_value = self.reset_source.get_icl_number().copy()
            
        elif self.default_value_source:
            self.default_value = self.default_value_source.get_icl_number().copy()
            
        else:
            self.default_value = IclNumber("0", "bin", self.scan_reg_size)

        # If there is a x in a ICL number, convert it to 0            
        for idx in range(self.default_value.get_icl_size()):
            if(self.default_value.get_bit(idx).get_bin_str() == "x"):
                self.default_value.set_bit("0", idx)

        assert(self.default_value.get_number() > -1)

                    
class IclLogicSignal(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            icl_name: IclSignal,
            expression: list[list:str],
            ctx: str
        ) -> None:
        super().__init__(instance, icl_name.get_name(), instance.get_hier(), instance.get_hier(), ctx)
        self.icl_name: IclSignal = icl_name
        self.expression: list = expression
        self.sympy_expression = None
        self.smt2_expression = None

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

    def get_sympy_expression(self) -> str:
        return self.sympy_expression

    def get_smt2_expression(self) -> str:
        return self.smt2_expression
    
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

    def create_simpy_expression(self, exr, lvl = 0):
        #print("do_expr", exr)
        expt_type = exr[0]
        exp_instances = []
        for item in exr[1:]:
            #print("ITEM", item)
            if type(item) == list:
                exp_instances.append(self.create_simpy_expression(item, lvl+1))
            else:
                exp_instances.append(item)
            #print("exp_instances", exp_instances)

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
            exp_instances[1] = ConcatSig(self.instance, [enum_symbol_value], CONCAT_NUMBER_T).get_list_for_expr()

        for idx, x in enumerate(exp_instances):
            #print(x, type(x))
            assert(type(x) in [ConcatSig, list, EnumRef])
            if isinstance(x, ConcatSig):
                exp_instances[idx] = x.get_list_for_expr()

        #print("do_expr in progress", exr, exp_instances, lvl), 
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
                    return_item += [f"Not({item})"]
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
                expr_op = "Fail"
                if expt_type in ["&"]:
                    expr_op = "And"
                elif expt_type in ["|"]:
                    expr_op = "Or"
                elif expt_type in ["^"]:
                    expr_op = "Xor"
                return_item = ["{}({})".format(expr_op, ",".join(new_list))]
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
            
            #print(var_1_exprs)
            #print(var_2_exprs)

            expr_op = ""
            if expt_type in ["&", "&&"]:
                expr_op = "And"
                # Check that boolean operation has only expr. on each side
                if expt_type in ["&&"]:
                    assert((size_all_1 == 1) and (size_all_2 == 1))
            elif expt_type in ["|", "||"]:
                expr_op = "Or"
                # Check that boolean operation has only expr. on each side
                if expt_type in ["||"]:
                    assert((size_all_1 == 1) and (size_all_2 == 1))
            elif expt_type in ["^"]:
                expr_op = "Xor"
            elif expt_type in ["=="]:
                expr_op = "And"
            else:
               raise ValueError(f"Error {expt_type}")
            
            return_item = []
            if expt_type in ["=="]:
                for expr_idx, _ in enumerate(var_1_exprs):
                    val = var_2_exprs[expr_idx]
                    assert(val in ["0", "1"])
                    new_exp = f"{var_1_exprs[expr_idx]}" if val == "1" else f"Not({var_1_exprs[expr_idx]})"
                    return_item.append(new_exp)
                return_item = ",".join(return_item)
                return_item = [f"And({return_item})"]
            else:
                for expr_idx, _ in enumerate(var_1_exprs):
                    return_item.append(f"{expr_op}({var_1_exprs[expr_idx]}, {var_2_exprs[expr_idx]})")
        else:
            raise ValueError(f"Error {expt_type}")

        # Entire expression, must be reduced to one bit
        if lvl == 0:    
            assert(isinstance(return_item, list))
            if not (len(return_item) == 1):
                raise RuntimeError(f"Expression {self.ctx} does return {len(return_item)} bit output, insted of one bit output, conv. expr.: {return_item}")
            if isinstance(return_item[0], IclNumber):
                item: IclNumber = return_item[0]
                assert(item.get_bit_size() == 1)
                if item.get_bin_bit_str(0) == "1":
                    return_item = ["True"]
                elif item.get_bin_bit_str(0) == "0":
                    return_item = ["False"]
                else:
                    raise RuntimeError(f"Expression {self.ctx} returns a X")
                               
        return return_item
    
    def check(self):
        self.sympy_expression = self.create_simpy_expression(self.expression)[0]
        self.smt2_expression = sympy_to_smt2(self.sympy_expression) 

        #print(self.ctx)
        #print(self.sympy_expression)
        #print(self.smt2_expression)

class IclDataRegister(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            icl_name: IclSignal,
            reg_type: str,
            source: ConcatSig,
            write_en: IclSignal,
            address: int,
            ctx: str
        ) -> None:
        super().__init__(instance, icl_name.get_name(), instance.get_hier(), instance.get_hier(), ctx)
        self.icl_name: IclSignal = icl_name

        # Type of data register: selectable, addressable or callback
        self.type_of_data_reg:str = reg_type
        self.one_hot: IclOneHotDataGroup = None
        self.reg_address: int = address
        self.write_source: ConcatSig = source
        self.write_en: IclSignal = write_en

        # Is is able to read/write
        self._is_readable: bool = None
        self._is_writable: bool = None


        # Register values
        self.data_reg_size = len(self.get_all_named_indexes())
        self.current_value = IclNumber("x", "bin", self.data_reg_size)
        self.bits_to_read  = IclNumber("0", "bin", self.data_reg_size)
        self.expected_data = IclNumber("x", "bin", self.data_reg_size)
        self.next_value    = IclNumber("x", "bin", self.data_reg_size)
        self.write_activate = 0
        self.read_activate = 0

    def set_current_bit(self, value: int, index:int):
        self.current_value.set_bit(value, index)

    def set_current_value(self, value: int):
        self.current_value.set_value(value)
    
    def set_next_bit(self, value: int, index:int):
        self.next_value.set_bit(value, index)

    def set_expected_bits(self, value: int):
        self.expected_data.set_value(value)

    def get_expected_bits(self):
        return self.expected_data

    def get_bits_to_read(self):
        return self.bits_to_read
    
    def set_read_bits(self, value: int):
        self.bits_to_read.set_value(value)

    def set_next_value(self, value: int):
        self.next_value.set_value(value)

    def set_next_value_to_current(self):
        self.current_value = self.next_value.copy()

    def set_next_write_iapply(self):
        self.write_activate = 1

    def disable_next_write_iapply(self):
        self.write_activate = 0
            
    def is_in_next_write_iapply(self):
        return self.write_activate

    def set_next_read_iapply(self):
        self.read_activate = 1

    def disable_next_read_iapply(self):
        self.read_activate = 0
            
    def is_in_next_read_iapply(self):
        return self.read_activate

    def reset(self):

        self.disable_next_write_iapply()
        self.disable_next_read_iapply()
        self.set_read_bits(0)

        # Temp solution
        self.current_value.set_value(0)
        self.next_value.set_value(0)
        self.bits_to_read.set_value(0)

    def set_mux(self, one_hot: "IclOneHotDataGroup"):
        self.one_hot = one_hot

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.icl_name)

    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.icl_name)

    def get_vector_size(self) -> int:
        return len(self.get_all_indexes())

    def is_readable(self) -> bool:
        return self._is_readable

    def is_writable(self) -> bool:
        return self._is_writable

    def get_reg_address(self) -> int:
        return self.reg_address

    def get_reg_type(self) -> str:
        return self.type_of_data_reg

    def get_data_out(self) -> ConcatSig:
        return self.instance.get_port_type_sequence((IclDataOutPort))

    def get_data_in(self) -> ConcatSig:
        return self.instance.get_port_type_sequence((IclDataInPort))

    def get_write_en(self) -> ConcatSig:
        return self.instance.get_port_type_sequence((IclWriteEnPort))

    def get_read_en(self) -> ConcatSig:
        return self.instance.get_port_type_sequence((IclReadEnPort))

    def get_reg_select(self) -> str:
        if(self.type_of_data_reg == "addressable"):
            addres_port: ConcatSig = self.instance.get_port_type_sequence((IclAddressPort))
            address_size: int = self.reg_address.bit_length()
            address_size = 1 if (address_size == 0) else address_size

            address_port_bits: list[str] = addres_port.get_all_named_indexes_with_prefix(max_size=addres_port.get_sized_bits_size(), neg_on=0)

            return_item = []
            for i in range(address_size):
                bit_val = (self.reg_address >> i) & 1
                new_exp = f"{address_port_bits[i]}" if bit_val == 1 else f"(not {address_port_bits[i]})"
                return_item.append(new_exp)
            return_item = " ".join(return_item)
            return_item = f"(and {return_item})"
            return return_item
        else:
            raise ValueError(f"Error {self.type_of_data_reg}")

    def check(self):
        
        if(self.type_of_data_reg == "addressable"):
            reg_size: int = self.get_vector_size()
            address_size: int = self.reg_address.bit_length()
            address_size = 1 if (address_size == 0) else address_size
            
            addres_port: ConcatSig = self.instance.get_port_type_sequence((IclAddressPort))
            data_in_port: ConcatSig = self.instance.get_port_type_sequence((IclDataInPort))
            data_out_port: ConcatSig = self.instance.get_port_type_sequence((IclDataOutPort))           
            write_en_port: ConcatSig = self.instance.get_port_type_sequence((IclWriteEnPort))
            read_en_port: ConcatSig = self.instance.get_port_type_sequence((IclReadEnPort))

            if(self.one_hot == None):
                raise ValueError(f"Addressable data register is not under one hot data group, {self.ctx}")
                        
            if(addres_port == None):
                raise ValueError(f"No Address port in current module for addressable register, {self.ctx}")
            else:
                assert(addres_port.sized_number())

                address_port_size = addres_port.get_sized_bits_size()
                if(not (address_size <= address_port_size)):
                    raise ValueError(f"Address port size({address_port_size}) is smaller thatn register address value ({address_size}), {self.ctx}")
           
            if((write_en_port != None) and (data_in_port!= None)):
                assert(write_en_port.sized_number())
                assert(data_in_port.sized_number())

                write_en_port_size = write_en_port.get_sized_bits_size()
                data_in_port_size = data_in_port.get_sized_bits_size()

                if(write_en_port_size != 1):
                    raise ValueError(f"Write EN has more than one bit, {self.ctx}" )

                if(not (reg_size <= data_in_port_size)):
                    raise ValueError(f"Data in port size({data_in_port_size}) is smaller thatn register that is supposed to write to ({reg_size}), {self.ctx}")

                self._is_writable = True

            if((read_en_port != None) and (data_out_port != None)):
                assert(read_en_port.sized_number())
                assert(data_out_port.sized_number())

                read_en_port_size = read_en_port.get_sized_bits_size()
                data_out_port_size = data_out_port.get_sized_bits_size()


                if(read_en_port_size != 1):
                    raise ValueError(f"Read EN has more than one bit")

                if(not (reg_size <= data_out_port_size)):
                    raise ValueError(f"Data out port size({data_out_port_size}) is smaller thatn register that is supposed to read from ({reg_size}), {self.ctx}")

                if(not (reg_size <= self.one_hot.get_vector_size())):
                    raise ValueError(f"One hot data group with size ({self.one_hot.get_vector_size()}) is smaller that register that is supposed to get data ({reg_size}), {self.ctx}")

                self._is_readable = True

        print(f"{self.ctx}")
        print(f"Write able-{self._is_writable}")
        print(f"Read able-{self._is_readable}")
        

class IclOneHotScanGroup(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            icl_name: IclSignal,
            selectee: list[ConcatSig],
            ctx: str
        ) -> None:
        super().__init__(instance, icl_name.get_name(), instance.get_hier(), instance.get_hier(), ctx)
        self.icl_name: IclSignal = icl_name
        self.selectee:  list[ConcatSig] = selectee

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.icl_name)

    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.icl_name)

    def get_vector_size(self) -> int:
        return len(self.get_all_indexes())
        
    def check(self):
        pass

class IclOneHotDataGroup(IclItem):
    def __init__(
            self,
            instance: IclInstance,
            icl_name: IclSignal,
            ctx: str
        ) -> None:
        super().__init__(instance, icl_name.get_name(), instance.get_hier(), instance.get_hier(), ctx)
        self.icl_name: IclSignal = icl_name
        self.selectee: list = []

    def add_selectee(self, item):
        self.selectee.append(item)

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.icl_name)

    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.icl_name)

    def get_vector_size(self) -> int:
        return len(self.get_all_indexes())
        
    def check(self):
        pass


class IclScanMux(IclItem):
    
    def __init__(self, instance: IclInstance, ctx, mux: IclSignal, mux_control: ConcatSig, mux_selects: list[tuple[list[IclNumber],ConcatSig]]) -> None:
        super().__init__(instance, mux.get_name(), instance.get_hier(), instance.get_module_scope(), ctx)
        self.mux = mux
        self.mux_control = mux_control
        self.mux_selects = mux_selects
        self.connections = []

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.mux)

    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.mux)
    
    def get_all_connections(self) -> list[tuple[str]]:
        return self.connections
    
    def get_vector_size(self) -> int:
        return len(self.get_all_indexes())
        
    def check(self):
        self.mux_control.check()
        mux_control_size = self.mux_control.get_vector_min_size()
        mux_control_names = self.mux_control.get_all_named_indexes(mux_control_size)
        mux_control_names.reverse()

        mux_names = self.get_all_named_indexes()
        mux_size = 1 if self.mux.get_size() == 0 else self.mux.get_size()

        # If mux selection value has unsized value, try to size it
        # to mux control size, if it fits, it is ok, otherwise it is not ok
        # Also check that all sized values match with mux control size
        for selectee_list, tos in self.mux_selects:
            for mux_selection_value in selectee_list:
                print(mux_selection_value)               
                if(not mux_selection_value.sized_number()):
                    mux_selection_value.resize(mux_control_size)
                if(mux_selection_value.get_icl_size() != mux_control_size):
                    raise ValueError(f"In {self.ctx} - mux select size and mux control size does not match, {mux_selection_value.get_icl_size()} - {mux_control_size}")

        for selectee_list, tos in self.mux_selects:
            tos.check()      
            to_size = tos.get_vector_min_size()
            assert(mux_size == to_size)

            tos_names = tos.get_all_named_indexes(mux_size)

            selectee_list_expr_smt = []
            selectee_list_expr_py = []
            for selectee in selectee_list:
                selectee_expr_smt = []
                selectee_expr_py = []
                for idx, scan_sel_bit in enumerate(mux_control_names):
                    #print(selectee.get_bit(idx).get_number())
                    
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

            self.connections += (list(zip(tos_names, mux_names, [selectee_list_expr_smt], [selectee_list_expr_py])))

class IclDataMux(IclItem):
    
    def __init__(self, instance: IclInstance, ctx, mux: IclSignal, mux_control: ConcatSig, mux_selects: list[tuple[list[IclNumber],ConcatSig]]) -> None:
        super().__init__(instance, mux.get_name(), instance.get_hier(), instance.get_module_scope(), ctx)
        self.mux = mux
        self.mux_control = mux_control
        self.mux_selects = mux_selects
        self.connections = []

    def get_all_named_indexes(self) -> list[str]:
        return self.get_item_all_named_indexes(self.mux)

    def get_all_indexes(self) -> list[int]:
        return self.get_item_all_indexes(self.mux)
    
    def get_all_connections(self) -> list[tuple[str]]:
        return self.connections
    
    def get_vector_size(self) -> int:
        return len(self.get_all_indexes())
        
    def check(self):
        self.mux_control.check()
        mux_control_size = self.mux_control.get_vector_min_size()
        mux_control_names = self.mux_control.get_all_named_indexes(mux_control_size)
        mux_control_names.reverse()

        mux_names = self.get_all_named_indexes()
        mux_size = 1 if self.mux.get_size() == 0 else self.mux.get_size()

        # If mux selection value has unsized value, try to size it
        # to mux control size, if it fits, it is ok, otherwise it is not ok
        # Also check that all sized values match with mux control size
        for selectee_list, tos in self.mux_selects:
            for mux_selection_value in selectee_list:
                #print(mux_selection_value)               
                if(not mux_selection_value.sized_number()):
                    mux_selection_value.resize(mux_control_size)
                if(mux_selection_value.get_icl_size() != mux_control_size):
                    raise ValueError(f"In {self.ctx} - mux select size and mux control size does not match, {mux_selection_value.get_icl_size()} - {mux_control_size}")


        for selectee_list, tos in self.mux_selects:
            tos.check()      
            to_size = tos.get_vector_min_size()
            assert(mux_size == to_size)

            tos_names = tos.get_all_named_indexes(mux_size)

            selectee_list_expr_smt = []
            selectee_list_expr_py = []
            for selectee in selectee_list:
                selectee_expr_smt = []
                selectee_expr_py = []
                for idx, scan_sel_bit in enumerate(mux_control_names):
                    #print(selectee.get_bit(idx).get_number())
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

            self.connections += (list(zip(tos_names, mux_names, [selectee_list_expr_smt], [selectee_list_expr_py])))

class IclScanInterface(IclItem):

    def __init__(
            self,
            instance: IclInstance,
            icl_name: str,
            icl_attributes: list[IclAttribute],
            interface_ports: list[IclSignal],
            scan_chains: list[dict],
            ctx: str
        ) -> None:

        super().__init__(instance, icl_name, instance.get_hier(), instance.get_hier(), ctx)
        self.icl_name: str = icl_name
    
        self.attributes: list[IclAttribute] = icl_attributes
        self.interface_ports_ref: list[IclSignal] = interface_ports
        self.chains: list[dict] = scan_chains

        # Types: host_tap, client_tap, host_scan_interface, client_scan_interface
        self.interface_type = None 

    def get_interface_type(self) -> str:
        return self.interface_type

    def check(self):
        # Filter out ports that are not Scan In or Scan out from !default-chain!
        # (Default chain inherits all interface_ports including control ports; keep only SI/SO)
        tmp = []
        for idx, chain in enumerate(self.chains):
            if ("!default-chain!" == chain["name"]):
                for port_ref in chain["ports"]:
                    if isinstance(self.instance.get_icl_item_name(port_ref.get_name()), (IclScanInPort,IclScanOutPort)):
                        tmp.append(port_ref)
                self.chains[idx]["ports"] = tmp

        # If there is a default chain, remove ports from normal interface ports
        # Otherwise they would be duplicated in chain and interface_ports
        for chain in self.chains:
            if ("!default-chain!" == chain["name"]):
                new_interface_ports_ref = []
                for port in self.interface_ports_ref:
                    if port not in chain["ports"]:
                        new_interface_ports_ref.append(port)
                self.interface_ports_ref = new_interface_ports_ref
                break

        # Determine which type this scan interface is
        # 6.4.16 - d)
        for port_ref in self.interface_ports_ref:
            icl_port = self.instance.get_icl_item_name(port_ref.get_name())
            if(isinstance(icl_port, (IclTmsPort))):
                self.interface_type = CLIENT_TAP
                break
            elif(isinstance(icl_port, (IclToTmsPort))):
                self.interface_type = HOST_TAP
                break
            elif(isinstance(icl_port, (IclShiftEnable, IclSelectPort))):
                self.interface_type = CLIENT_SCAN_INTERFACE
                break
            elif(isinstance(icl_port, (IclToShiftEnable, IclToSelectPort))):
                self.interface_type = HOST_SCAN_INTERFACE
                break

        # Check if we found a type
        if self.interface_type is None:
            raise ValueError(f"ScanInterface '{self.icl_name}': cannot determine type — interface must contain a TMSPort/ToTMSPort, ShiftEnPort/SelectPort, or ToShiftEnPort/ToSelectPort (rule d)")
        
        # Check if scan interface does not have duplicate ports.
        port_keys: list[str] = self.get_signal_all_named_indexes(self.instance, self.interface_ports_ref)
        for chain in self.chains:
            port_keys.extend(self.get_signal_all_named_indexes(self.instance, chain["ports"]))
        if len(port_keys) != len(set(port_keys)):
            raise ValueError(f"ScanInterface '{self.icl_name}': duplicate port in ScanInterface: {port_keys}")

        # Make sure ports in interface are the right type, and righ count
        # Count each port occurence
        # 6.4.16 - e) f) g) h)
        type_counter: dict = {
            IclTckPort: 0,
            IclToTckPort: 0,
            IclScanInPort: 0,
            IclScanOutPort: 0,
            IclShiftEnable: 0,
            IclUpdateEnable: 0,
            IclCaptureEnable: 0,
            IclResetPort: 0,
            IclSelectPort: 0,
            IclToShiftEnable: 0,
            IclToUpdateEnable: 0,
            IclToCaptureEnable: 0,
            IclToResetPort: 0,
            IclToSelectPort: 0,            
            IclTmsPort: 0,
            IclTrstPort: 0,
            IclToTmsPort: 0,
            IclToTrstPort: 0
        }
        for port_ref in self.interface_ports_ref:
            icl_port = self.instance.get_icl_item_name(port_ref.get_name())
            icl_port_ref_size = len(self.get_signal_all_named_indexes(self.instance, [port_ref]))
            icl_type = type(self.instance.get_icl_item_name(port_ref.get_name()))
            if(icl_type in type_counter.keys()):
                type_counter[icl_type] += icl_port_ref_size
            else:
                type_counter[icl_type] = icl_port_ref_size

            if(self.interface_type == CLIENT_SCAN_INTERFACE):
                if not isinstance(icl_port, (IclScanInPort, IclScanOutPort, IclShiftEnable, IclSelectPort, IclCaptureEnable, IclUpdateEnable, IclResetPort, IclTckPort)):
                    raise ValueError(f"ScanInterface '{self.icl_name}': port '{port_ref.get_name()}' ({type(icl_port).__name__}) not allowed in client scan interface")
            elif(self.interface_type == HOST_SCAN_INTERFACE):
                if not isinstance(icl_port, (IclScanInPort, IclScanOutPort, IclToShiftEnable, IclToSelectPort, IclToCaptureEnable, IclToUpdateEnable, IclToResetPort, IclToTckPort)):
                    raise ValueError(f"ScanInterface '{self.icl_name}': port '{port_ref.get_name()}' ({type(icl_port).__name__}) not allowed in host scan interface")
            elif(self.interface_type == CLIENT_TAP):
                if not isinstance(icl_port, (IclScanInPort, IclScanOutPort, IclTmsPort, IclTrstPort, IclTckPort)):
                    raise ValueError(f"ScanInterface '{self.icl_name}': port '{port_ref.get_name()}' ({type(icl_port).__name__}) not allowed in client TAP interface")
            elif(self.interface_type == HOST_TAP):
                if not isinstance(icl_port, (IclScanInPort, IclScanOutPort, IclToTmsPort, IclToTrstPort, IclToTckPort)):
                    raise ValueError(f"ScanInterface '{self.icl_name}': port '{port_ref.get_name()}' ({type(icl_port).__name__}) not allowed in host TAP interface")
        for chain in self.chains:
            for port_ref in chain["ports"]:
                icl_port = self.instance.get_icl_item_name(port_ref.get_name())
                if not isinstance(icl_port, (IclScanInPort, IclScanOutPort)):
                    raise ValueError(f"ScanInterface '{self.icl_name}': chain '{chain['name']}' port '{port_ref.get_name()}' must be ScanInPort or ScanOutPort, got {type(icl_port).__name__}")
                icl_type = type(icl_port)
                if(icl_type in type_counter.keys()):
                    type_counter[icl_type] += icl_port_ref_size
                else:
                    type_counter[icl_type] = icl_port_ref_size

        # 6.4.16 - i)
        # When there is a single port of function ShiftEnPort, CaptureEnPort, or UpdateEnPort, it shall be
        # implicitly associated with every client scan interface that does not already have a port of that
        # particular port function among its members.
        if(self.interface_type == CLIENT_SCAN_INTERFACE):
            if(type_counter[IclCaptureEnable] == 0):
                tmp: list[IclCaptureEnable] = self.instance.get_icl_item_type(IclCaptureEnable)
                num_of_ports: int = sum([port.get_vector_size() for port in tmp])
                if(num_of_ports == 1):
                    self.interface_ports_ref.append(IclSignal(tmp[0].get_name()))
                    type_counter[IclCaptureEnable] += 1
            if(type_counter[IclUpdateEnable] == 0):
                tmp: list[IclUpdateEnable] = self.instance.get_icl_item_type(IclUpdateEnable)
                num_of_ports: int = sum([port.get_vector_size() for port in tmp])
                if(num_of_ports == 1):
                    self.interface_ports_ref.append(IclSignal(tmp[0].get_name()))
                    type_counter[IclUpdateEnable] += 1
            if(type_counter[IclShiftEnable] == 0):
                tmp: list[IclShiftEnable] = self.instance.get_icl_item_type(IclShiftEnable)
                num_of_ports: int = sum([port.get_vector_size() for port in tmp])
                if(num_of_ports == 1):
                    self.interface_ports_ref.append(IclSignal(tmp[0].get_name()))
                    type_counter[IclShiftEnable] += 1
            # Not in standard
            if(self.instance.im_top_instace()):
                if(type_counter[IclTckPort] == 0):
                    tmp: list[IclTckPort] = self.instance.get_icl_item_type(IclTckPort)
                    num_of_ports: int = sum([port.get_vector_size() for port in tmp])
                    if(num_of_ports == 1):
                        self.interface_ports_ref.append(IclSignal(tmp[0].get_name()))
                        type_counter[IclTckPort] += 1

        # Not in standard
        elif(self.interface_type == HOST_TAP):
            if(self.instance.im_top_instace()):
                if(type_counter[IclTckPort] == 0):
                    tmp: list[IclTckPort] = self.instance.get_icl_item_type(IclTckPort)
                    num_of_ports: int = sum([port.get_vector_size() for port in tmp])
                    if(num_of_ports == 1):
                        self.interface_ports_ref.append(IclSignal(tmp[0].get_name()))
                        type_counter[IclTckPort] += 1

        # 6.4.16 - j)
        elif(self.interface_type == HOST_SCAN_INTERFACE):
            if(type_counter[IclToCaptureEnable] == 0):
                tmp: list[IclToCaptureEnable] = self.instance.get_icl_item_type(IclToCaptureEnable)
                num_of_ports: int = sum([port.get_vector_size() for port in tmp])
                if(num_of_ports == 1):
                    self.interface_ports_ref.append(IclSignal(tmp[0].get_name()))
                    type_counter[IclToCaptureEnable] += 1
            if(type_counter[IclToUpdateEnable] == 0):
                tmp: list[IclToUpdateEnable] = self.instance.get_icl_item_type(IclToUpdateEnable)
                num_of_ports: int = sum([port.get_vector_size() for port in tmp])
                if(num_of_ports == 1):
                    self.interface_ports_ref.append(IclSignal(tmp[0].get_name()))
                    type_counter[IclToUpdateEnable] += 1
            if(type_counter[IclToShiftEnable] == 0):
                tmp: list[IclToShiftEnable] = self.instance.get_icl_item_type(IclToShiftEnable)
                num_of_ports: int = sum([port.get_vector_size() for port in tmp])
                if(num_of_ports == 1):
                    self.interface_ports_ref.append(IclSignal(tmp[0].get_name()))
                    type_counter[IclToShiftEnable] += 1

        def _check(cond, msg):
            if not cond:
                raise ValueError(f"ScanInterface '{self.icl_name}' ({self.interface_type}): {msg}")

        if(self.interface_type == CLIENT_SCAN_INTERFACE):
            # 6.4.16 e3) zero or one CaptureEnPort
            _check(type_counter[IclCaptureEnable] in [0,1], "zero or one CaptureEnPort allowed (rule e3)")
            # 6.4.16 e4) zero or one UpdateEnPort
            _check(type_counter[IclUpdateEnable] in [0,1], "zero or one UpdateEnPort allowed (rule e4)")
            # 6.4.16 e5) zero or one ResetPort
            _check(type_counter[IclResetPort] in [0,1], "zero or one ResetPort allowed (rule e5)")
            # 6.4.16 e6) zero or one TCKPort
            _check(type_counter[IclTckPort] in [0,1], "zero or one TCKPort allowed (rule e6)")
            # 6.4.16 e2) one ShiftEnPort and/or one-or-many SelectPort — at least one required
            _check(type_counter[IclShiftEnable] in [0,1], "at most one ShiftEnPort allowed (rule e2)")
            _check(type_counter[IclShiftEnable] > 0 or type_counter[IclSelectPort] > 0,
                   "one ShiftEnPort and/or one-or-many SelectPort required (rule e2)")
            # 6.4.16 e1) one or many SI/SO pairs
            _check(type_counter[IclScanInPort] > 0, "one or many ScanInPort required (rule e1)")
            _check(type_counter[IclScanOutPort] > 0, "one or many ScanOutPort required (rule e1)")
            _check(type_counter[IclScanInPort] == type_counter[IclScanOutPort],
                   "ScanInPort and ScanOutPort counts must match (rule e1)")

        elif(self.interface_type == HOST_SCAN_INTERFACE):
            # 6.4.16 f3) zero or one ToCaptureEnPort
            _check(type_counter[IclToCaptureEnable] in [0,1], "zero or one ToCaptureEnPort allowed (rule f3)")
            # 6.4.16 f4) zero or one ToUpdateEnPort
            _check(type_counter[IclToUpdateEnable] in [0,1], "zero or one ToUpdateEnPort allowed (rule f4)")
            # 6.4.16 f5) zero or one ToResetPort
            _check(type_counter[IclToResetPort] in [0,1], "zero or one ToResetPort allowed (rule f5)")
            # 6.4.16 f6) zero or one ToTCKPort
            _check(type_counter[IclToTckPort] in [0,1], "zero or one ToTCKPort allowed (rule f6)")
            # 6.4.16 f2) one ToShiftEnPort and/or one-or-many ToSelectPort — at least one required
            _check(type_counter[IclToShiftEnable] in [0,1], "at most one ToShiftEnPort allowed (rule f2)")
            _check(type_counter[IclToShiftEnable] > 0 or type_counter[IclToSelectPort] > 0,
                   "one ToShiftEnPort and/or one-or-many ToSelectPort required (rule f2)")
            # 6.4.16 f1) one ScanInPort and/or one ScanOutPort; ScanOutPort mandatory
            _check(type_counter[IclScanInPort] in [0,1], "at most one ScanInPort allowed (rule f1)")
            _check(type_counter[IclScanOutPort] == 1, "exactly one ScanOutPort required (rule f1)")
            _check(type_counter[IclScanInPort] <= type_counter[IclScanOutPort],
                   "ScanInPort count must not exceed ScanOutPort count (rule f1)")

        elif(self.interface_type == CLIENT_TAP):
            # 6.4.16 g2) one TMSPort
            _check(type_counter[IclTmsPort] == 1, "exactly one TMSPort required (rule g2)")
            # 6.4.16 g3) zero or one TRSTPort
            _check(type_counter[IclTrstPort] in [0,1], "zero or one TRSTPort allowed (rule g3)")
            # 6.4.16 g4) zero or one TCKPort
            _check(type_counter[IclTckPort] in [0,1], "zero or one TCKPort allowed (rule g4)")
            # 6.4.16 g1) one or many SI/SO pairs
            _check(type_counter[IclScanInPort] > 0, "one or many ScanInPort required (rule g1)")
            _check(type_counter[IclScanOutPort] > 0, "one or many ScanOutPort required (rule g1)")
            _check(type_counter[IclScanInPort] == type_counter[IclScanOutPort],
                   "ScanInPort and ScanOutPort counts must match (rule g1)")

        elif(self.interface_type == HOST_TAP):
            # 6.4.16 h2) one ToTMSPort
            _check(type_counter[IclToTmsPort] == 1, "exactly one ToTMSPort required (rule h2)")
            # 6.4.16 h3) zero or one ToTRSTPort
            _check(type_counter[IclToTrstPort] in [0,1], "zero or one ToTRSTPort allowed (rule h3)")
            # 6.4.16 h4) zero or one ToTCKPort
            _check(type_counter[IclToTckPort] in [0,1], "zero or one ToTCKPort allowed (rule h4)")
            # 6.4.16 h1) one ScanInPort and/or one ScanOutPort; ScanOutPort mandatory
            _check(type_counter[IclScanInPort] in [0,1], "at most one ScanInPort allowed (rule h1)")
            _check(type_counter[IclScanOutPort] == 1, "exactly one ScanOutPort required (rule h1)")
            _check(type_counter[IclScanInPort] <= type_counter[IclScanOutPort],
                   "ScanInPort count must not exceed ScanOutPort count (rule h1)")

        # 6.4.16 - k) If a scan client interface has more than one ScanInPort/ScanOutPort pair, then each pair shall be
        # declared in a scanInterfaceChain_def element.
        if(self.interface_type == CLIENT_SCAN_INTERFACE):
            if((type_counter[IclScanInPort] + type_counter[IclScanOutPort]) > 2):
                for chain in self.chains:
                    num_of_scan_ins = 0
                    num_of_scan_outs = 0
                    for port_ref in chain["ports"]:
                        port_item = self.instance.get_icl_item_name(port_ref.get_name())
                        port_ref_size = len(self.get_signal_all_named_indexes(self.instance, [port_ref]))
                        if (isinstance(port_item, (IclScanInPort))):
                            num_of_scan_ins += port_ref_size
                        if (isinstance(port_item, (IclScanOutPort))):
                            num_of_scan_outs += port_ref_size
                    if not ((num_of_scan_ins == 1) and (num_of_scan_outs == 1)):
                        raise ValueError(f"ScanInterface '{self.icl_name}': chain '{chain['name']}' must have exactly one ScanInPort and one ScanOutPort (rule k)")

        # 6.4.16 - l) If a scanInterfaceChain_def element is present, there shall be neither scanInterfacePort_def (with
        # function ScanInPort or ScanOutPort) nor defaultLoad_def statements outside the
        # scanInterfaceChain_def
        for chain_1 in self.chains:
            if ("!default-chain!" != chain_1["name"]):
                for port in self.interface_ports_ref:
                    icl_port = self.instance.get_icl_item_name(port.get_name())
                    if isinstance(icl_port, (IclScanInPort, IclScanOutPort)):
                        raise ValueError(f"ScanInterface '{self.icl_name}': ScanInPort/ScanOutPort '{port.get_name()}' must not appear outside scanInterfaceChain_def when chains are present (rule l)")
                for chain_2 in self.chains:
                    if ("!default-chain!" == chain_2["name"]):
                        if chain_2["default"] is not None:
                            raise ValueError(f"ScanInterface '{self.icl_name}': DefaultLoadValue must not appear outside scanInterfaceChain_def when chains are present (rule l)")
                break
        # 6.4.16 - m) Each scan interface of a module shall be uniquely selectable (with all other scan interfaces of that
        # module disabled).
        pass

        # 6.4.16 - n) The scanInterfaceChain_name shall be unique within a scanInterface_def.
        chain_names = [chain["name"] for chain in self.chains]
        if len(chain_names) != len(set(chain_names)):
            raise ValueError(f"ScanInterface '{self.icl_name}': duplicate chain names: {chain_names} (rule n)")

        # 6.4.16 - o) The scanInterfacePort_def inside a scanInterfaceChain_def shall only include ports with function
        # ScanInPort and ScanOutPort.
        for chain in self.chains:
            for port in chain["ports"]:
                icl_port = self.instance.get_icl_item_name(port.get_name())
                if not isinstance(icl_port, (IclScanInPort, IclScanOutPort)):
                    raise ValueError(f"ScanInterface '{self.icl_name}': chain '{chain['name']}' port '{port.get_name()}' must be ScanInPort or ScanOutPort (rule o)")

        # 6.4.16 - p) The scanInterfaceChain_def is only allowed in scanInterface_def of type client or client-TAP.
        for chain in self.chains:
            if ("!default-chain!" != chain["name"]):
                if self.interface_type not in [CLIENT_SCAN_INTERFACE, CLIENT_TAP]:
                    raise ValueError(f"ScanInterface '{self.icl_name}': scanInterfaceChain_def only allowed in client or client-TAP interface, not '{self.interface_type}' (rule p)")

        # 6.4.16 - q) A scanInterfaceChain_def element shall include one scanInterfacePort_def with function
        # ScanInPort and one with function ScanOutPort and each port shall only be referenced by a
        # single scanInterfaceChain_def element.

        # Top/handoff module checks — not part of the standard, custom enforcement
        # For CLIENT_SCAN_INTERFACE (custom):
        #   Requires TCKPort in the module — without it scan registers cannot be clocked
        #   Requires ShiftEnPort — without it scan data cannot be shifted through scan registers
                # 6.4.5 - j)A handoff module with at least one scanInPort_def shall have at least one shiftEnPort_def.
        #   Warns if UpdateEnPort is missing — scan registers with update stage won't update
        #   Warns if CaptureEnPort is missing — scan registers with capture won't capture
        #   Warns if ResetPort is missing — resettable scan registers won't reset
        # For CLIENT_TAP (custom):
        #   Requires TCKPort in the module — without it scan registers cannot be clocked
        if(self.instance.im_top_instace()):

            if((self.interface_type == CLIENT_SCAN_INTERFACE) or (self.interface_type == CLIENT_TAP)):
                num_of_tck_ports: int = sum([port.get_vector_size() for port in self.instance.get_icl_item_type(IclTckPort)])
                if(num_of_tck_ports  == 0):
                    raise ValueError(f"Scan interface:{self.get_name()} in Top/handoff instance {self.instance.get_name()} is missing TckPort port")

            if(self.interface_type == CLIENT_SCAN_INTERFACE):
                if(type_counter[IclShiftEnable] == 0):
                    raise ValueError(f"Scan interface:{self.get_name()} in Top/handoff instance {self.instance.get_name()} is missing IclShiftEnable port")
                if(type_counter[IclUpdateEnable] == 0):
                    warnings.warn(f"Scan interface:{self.get_name()} in Top/handoff instance {self.instance.get_name()} is missing UpdateEnable port")
                if(type_counter[IclCaptureEnable] == 0):
                    warnings.warn(f"Scan interface:{self.get_name()} in Top/handoff instance {self.instance.get_name()} is missing CaptureEnable port")
                if(type_counter[IclResetPort] == 0):
                    warnings.warn(f"Scan interface:{self.get_name()} in Top/handoff instance {self.instance.get_name()} is missing ResetPort port")

        # DefaultLoadValue syntax is validated above; actual use is not yet implemented
        for chain in self.chains:
            if(chain["default"]):
                raise ValueError(f"DefaultLoadValue is not yet supported in: {self.ctx}/scan interface:{self.get_name_with_hier()}")
            
class IclPort(IclItem):

    def __init__(self, instance: IclInstance, ctx, port: IclSignal, attributes: list[IclAttribute] = None) -> None:
        super().__init__(instance, port.get_name(), instance.get_hier(), instance.get_module_scope(), ctx)
        self.ports: list[IclSignal] = [port]
        self.attributes: dict[IclSignal:list[IclAttribute]] = {port:attributes}
        
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
    
    def get_ports(self) -> list[IclSignal]:
        return self.ports
    
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

    def has_port_source(self) -> bool: 
        return 0

class AddPortSource():
    def add_source(self, port: IclSignal, source: ConcatSig) -> None:
        self.sources: dict[IclSignal:ConcatSig] = {port:source}

    def source_check(self):

        # Special case for IclScanOutPort
        # Example ScanRegister X[9:0],  ScanRegister Y[0:9]
        # Allowed: Source X; -> transforms it to X[0]
        # Allowed: Source Y; -> transforms it to Y[9]       
        # Allowed: Source X[0];
        # Allowed: Source Y[9];
        # Not allowed: Source X[9];
        # Not allowed: Source Y[0];
        # Not allowed: Source X[1:0];
        for port, source in self.sources.items():
            if isinstance(self, IclScanOutPort):
                for concat_item in source.concat_sigs:
                    print(type(concat_item))
                    if isinstance(concat_item, IclSignal):
                        cocnat_icl_item = self.instance.get_icl_item_name(concat_item.get_relative_name())
                        if isinstance(cocnat_icl_item, IclScanRegister):
                            size = len(concat_item.get_indexes())
                            if size == 0:
                                concat_item.ovveride_indexes([cocnat_icl_item.get_lsb_index()])
                            elif size == 1:
                                if cocnat_icl_item.get_lsb_index() != concat_item.get_indexes()[0]:
                                    raise ValueError(f"ScanOutPort source points to ScanRegister index that does not point to the scan register output: {self.get_name_with_hier()} -> {self.ctx}")
                            else:
                                raise ValueError(f"ScanOutPort source points to ScanRegister as a range, must select only one bit: {self.get_name_with_hier()} -> {self.ctx}")
       
        for port, source in self.sources.items():
            if source is not None:
                port_size = len(self.get_item_all_indexes([port]))
                source_size =  source.get_vector_min_size()

                # Check size
                assert(port_size == source_size) 

    def get_named_sourced_indexes(self) -> list[str]:
        name_source_indexes:list[str] = []
        
        for port, source in self.sources.items():
            if(not source):
                continue
            size = len(self.get_item_all_indexes([port]))
            name_source_indexes.extend(source.get_all_named_indexes(size))

        return name_source_indexes

    def source_merge(self, item_source: "AddPortSource"):
        for port, source in item_source.sources.items():
            if port in self.sources:
                raise ValueError(f"Source is already defined for {port}")
            self.sources[port] = source
            
    def has_port_source(self) -> bool: 
        return len(self.get_named_sourced_indexes()) > 0

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
                assert(type(polarity) is bool)
            else:
                self.polarities[port] = bool(1)

    def polarity_merge(self, item_source: "AddPolarity"):
        for port, value in item_source.polarities.items():
            if port in self.polarities:
                raise ValueError(f"Polarity is already defined for {port}")
            self.polarities[port] = value
    
    def get_polarites(self):
        return self.polarities
    
    def get_index_polarity(self, index: int) -> bool:
        assert (index in self.get_all_indexes())
        for icl_sig, polarity in self.polarities.items():
            icl_sig : IclSignal
            if len(icl_sig.get_indexes()) > 0:
                if index in icl_sig.get_indexes():
                    return polarity
            else:
                assert(len(self.polarities.keys()) == 1)
                return polarity
        raise RuntimeError(f"This code should have been unreachable")

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

class IclScanOutPort(AddPortSource, AddPortEnable, IclPort):

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

class IclDataInPort(AddPortRef, AddPortDefValue, IclPort):

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

class IclDataOutPort(AddPortSource, AddPortEnable, AddPortRef, IclPort):

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


class IclToShiftEnable(AddPortSource, IclPort):

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

class IclToUpdateEnable(AddPortSource, IclPort):

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

class IclToCaptureEnable(AddPortSource, IclPort):

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

class IclToSelectPort(AddPortSource, IclPort):

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

class IclResetPort(AddPolarity, IclPort):

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

class IclToResetPort(AddPolarity, AddPortSource, IclPort):

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

class IclToTmsPort(AddPortSource, IclPort):

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


class IclClockPort(AddClockSettings, IclPort):
    
    def __init__(
            self,
            instance: IclInstance,
            ctx: str,
            port: IclSignal,
            attributes: list[IclAttribute],
            clock_settings: dict
        ) -> None:

        super().__init__(instance, ctx, port, attributes)
        self.add_clock(port, clock_settings)

    def check(self) -> int:
        super().check()
        self.clock_check()

    def merge(self, icl_port: IclPort):
        super().merge(icl_port)
        self.clock_merge(icl_port)

class IclToClockPort(AddClockSettings, AddPortSource, IclPort):

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
        self.add_clock(port, clock_settings)

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

class IclToTrstPort(AddPortSource, IclPort):

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

class IclToIrSelectPort(IclPort):
    pass

class IclAddressPort(IclPort):
    pass

class IclWriteEnPort(IclPort):
    pass

class IclReadEnPort(IclPort):
    pass
