#main.py

import sys
import time

from typing import Any

from antlr4 import *
from parser.iclLexer import iclLexer
from parser.iclParser import iclParser

from icl_pre_process import *
from icl_process import *
from icl_register_model import *

from cProfile import Profile
from pstats import SortKey, Stats

def pre_process_icl_files(icl_files: list[str]) -> dict[str, dict]:
    all_icl_modules = {"root":{}}
    
    for icl_file in icl_files:

        icl_pre_process = IclPreProcess()
        icl_pre_process.modules = all_icl_modules
                
        loaded_file = FileStream(icl_file, encoding='utf-8')
        
        lexer = iclLexer(loaded_file)
        stream = CommonTokenStream(lexer)
        parser = iclParser(stream)
        tree = parser.icl_source()
        walker = ParseTreeWalker()
        walker.walk(icl_pre_process, tree)

        all_icl_modules = icl_pre_process.modules

        #print(tree.toStringTree(recog=parser))

    return all_icl_modules

def process_icl_module(all_icl_modules: dict[str, dict], module_name: str) -> IclInstance:
    instance_name = "top" 
    scope = "root"

    icl_process = IclProcess(instance_name, module_name, scope)
    icl_process.all_icl_modules = all_icl_modules
    icl_process.start_icl_module = all_icl_modules[scope][module_name]

    module_to_process = all_icl_modules[scope][module_name]["data"]

    lexer = iclLexer(InputStream(module_to_process))
    stream = CommonTokenStream(lexer)
    parser = iclParser(stream)
    tree = parser.module_def()
    walker = ParseTreeWalker()
    walker.walk(icl_process, tree)

    icl_process.icl_instance.check()
    
    #print(tree.toStringTree(recog=parser))

    return icl_process.icl_instance

def test_0(argv):

    print("Args.: ", argv)
    if len(argv) > 2:
        
        print("ICL File:", argv[1])
        print("ICL Module parse:", argv[2])
        file_name = argv[1]
        module_name = argv[2]
    else:
        sys.exit('Error: Expected a valid file and ICL module name to parse')

    icl_files = [file_name]
    
    all_icl_modules = pre_process_icl_files(icl_files)
    icl_instance = process_icl_module(all_icl_modules, module_name)
    
    icl_instance.plotGraph()

def icl_number_test():
    x = IclNumber("xx", "bin", -1)
    print(x)
    assert("xx" == x.get_bin_str())
    x.resize(4)
    print(x)
    assert("xxxx" == x.get_bin_str())
    try:
        x.resize(3,1)
    except:
        pass
    else:
        raise ValueError("Function did not fail")
    x.resize(3, 0)
    print(x)
    assert("xxx" == x.get_bin_str())
    
    x = IclNumber("0", "bin", -1)
    print(x)
    assert("0" == x.get_bin_str())
    x.resize(5)
    print(x)
    assert("00000" == x.get_bin_str())

    x = IclNumber("'b11_00", "bin", -1)
    print(x)
    assert("1100" == x.get_bin_str())
    x.resize(6)
    print(x)
    assert("001100" == x.get_bin_str())
    try:
        x.resize(3,1)
    except:
        pass
    else:
        raise ValueError("Function did not fail")
    x.resize(3,0)
    print(x)
    assert("100" == x.get_bin_str())

    x = IclNumber("'B11", "bin", 10)
    print(x)
    assert("0000000011" == x.get_bin_str())

    x = IclNumber("xx01_x11", "bin", 10)
    print(x)
    assert("xxxxx01x11" == x.get_bin_str())

    x = IclNumber("'d13", "dec", -1)
    print(x)
    assert("1101" == x.get_bin_str())
    x.resize(6)
    print(x)
    assert("001101" == x.get_bin_str())

    x = IclNumber("'HE", "hex", -1)
    print(x)
    assert("1110" == x.get_bin_str())

    x = IclNumber("1_2_3", "dec", -1)
    print(x)
    assert("1111011" == x.get_bin_str())
            
    x = IclNumber("0235", "dec", -1)
    print(x)
    assert("11101011" == x.get_bin_str())
            
    x = IclNumber("'d 134", "dec", -1)
    print(x)
    assert("10000110" == x.get_bin_str())

    x = IclNumber("'h 23ff", "hex", -1)
    print(x)
    assert("10001111111111" == x.get_bin_str())

    try:
        x = IclNumber("3fa", "dec", -1)
    except:
        pass
    else:
        raise ValueError("Function did not fail")

    try:
        x = IclNumber("0xa", "dec", -1)
    except:
        pass
    else:
        raise ValueError("Function did not fail")
    
    x = IclNumber("'b0101", "bin", 4)
    print(x)
    assert("0101" == x.get_bin_str())    

    x = IclNumber("'D 3", "dec", 5)
    print(x)
    assert("00011" == x.get_bin_str())    

    x = IclNumber("'b0_1x", "bin", 3)
    print(x)
    assert("01x" == x.get_bin_str())

    x = IclNumber("'hx", "hex", 7)
    print(x)
    assert("xxxxxxx" == x.get_bin_str())
                                
    x = IclNumber("'h3", "hex", 2)
    print(x)
    assert("11" == x.get_bin_str())

    try:
        x = IclNumber("'hF", "hex", 2)
    except:
        pass
    else:
        raise ValueError("Function did not fail")

    #try:
    #    x = IclNumber("' hx", "hex", 7)
    #except:
    #    pass
    #else:
    #    raise ValueError("Function did not fail")

    try:
        x = IclNumber("'b", "bin", 0)
    except:
        pass
    else:
        raise ValueError("Function did not fail")

    try:
        x = IclNumber("'30", "hex", 5)
    except:
        pass
    else:
        raise ValueError("Function did not fail")

    x = IclNumber("' x", "hex", -1)
    print(x)
    assert("xxxx" == x.get_bin_str())
    x.resize(9)
    print(x)
    assert("xxxxxxxxx" == x.get_bin_str())

    x = IclNumber("' 3x", "hex", -1)
    print(x)
    assert("11xxxx" == x.get_bin_str())
    x.resize(9)
    print(x)
    assert("00011xxxx" == x.get_bin_str())

    x = IclNumber("'x3", "hex", -1)
    print(x)
    assert("xxxx0011" == x.get_bin_str())
    x.resize(9)
    print(x)
    assert("xxxxx0011" == x.get_bin_str())

    a = IclNumber("'b00101", "bin", 5)
    b = IclNumber("'b1111", "bin", 4)
    print(a, b)
    x = a.concat(b)
    print(x)
    assert("001011111" == x.get_bin_str())

    a = IclNumber("'b00101", "bin", 5)
    b = IclNumber("'b111x", "bin", 4)
    print(a, b)
    x = a.concat(b)
    print(x)
    assert("00101111x" == x.get_bin_str())

    x = IclNumber("'b111x", "bin", 4)
    x.resize(1,0)
    x.resize(4,0)
    print(x)                      
    assert("xxxx" == x.get_bin_str())

    x = IclNumber("'bx100", "bin", 4)
    x.resize(1,0)
    x.resize(4,0)
    print(x)                      
    assert("0000" == x.get_bin_str())

    x = IclNumber("'bx100", "bin", 4)
    y = x.copy()
    assert(x.get_bin_str() == y.get_bin_str())
    
    x = IclNumber("x100", "hex", -1)
    y = x.copy()
    assert(x.get_bin_str() == y.get_bin_str())
        
    x = IclNumber("x101", "bin", -1)
    print(x)
    assert(x.get_bin_bit_str(0) == "1")
    assert(x.get_bin_bit_str(1) == "0")
    assert(x.get_bin_bit_str(2) == "1")
    assert(x.get_bin_bit_str(3) == "x")

    x.set_bit(0,0)
    x.set_bit(0,1)
    print(x)

    assert(x.get_bin_bit_str(0) == "0")
    assert(x.get_bin_bit_str(1) == "0")

    x.set_bit(1,0)
    print(x)

    assert(x.get_bin_bit_str(0) == "1")
    assert(x.get_bin_bit_str(1) == "0")

    x.set_bit(1,1)
    print(x)
    assert(x.get_bin_bit_str(0) == "1")
    assert(x.get_bin_bit_str(1) == "1")

def test_1():
    pass

icl_blocks =  [ "test_icls/benchmarks/ICL/EmptyModule.icl", "test_icls/benchmarks/ICL/Instruments.icl", "test_icls/benchmarks/ICL/NetworkStructs.icl"]
icl_tests = ["test_icls/benchmarks/ICL/Basic/TreeFlat/TreeFlat.icl"]
icl_all = icl_blocks + icl_tests
def test_2():
    icl_files = ["test_icls/scan_mux_001.icl", "test_icls/scan_mux_002.icl", "test_icls/scan_mux_003.icl"] + icl_blocks
    module_name = "scan_mux_002"
    
    all_icl_modules = pre_process_icl_files(icl_files)
    icl_instance = process_icl_module(all_icl_modules, module_name)
    
    #import pickle
    #with open('icl_instance.pkl', 'wb') as file:
    #    pickle.dump(icl_instance, file)
    #input()


    # UnSized_0 - 6
    reg: IclScanRegister =  icl_instance.get_icl_item_name("UnSized_0")
    concat: ConcatSig = reg.capture_source
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes(reg_size)
    exp = ['reg8.SR_0001', 'D_0001', 'D_0000', '0', '0']
    print(sigs, exp)
    assert(sigs == exp)

    reg: IclScanRegister =  icl_instance.get_icl_item_name("UnSized_1")
    concat: ConcatSig = reg.capture_source
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes(reg_size)
    exp = ['reg8.SR_0001', '0', '0', 'D_0001', 'D_0000']
    print(sigs, exp)
    assert(sigs == exp)

    reg: IclScanRegister =  icl_instance.get_icl_item_name("UnSized_2")
    concat: ConcatSig = reg.capture_source
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes(reg_size)
    exp = ['0', '0', 'reg8.SR_0001', 'D_0001', 'D_0000']
    print(sigs, exp)
    assert(sigs == exp)

    reg: IclScanRegister =  icl_instance.get_icl_item_name("UnSized_3")
    concat: ConcatSig = reg.capture_source
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes(reg_size)
    exp = ['reg8.SR_0001', 'D_0001', 'D_0000', '1', '1']
    print(sigs, exp)
    assert(sigs == exp)

    reg: IclScanRegister =  icl_instance.get_icl_item_name("UnSized_4")
    concat: ConcatSig = reg.capture_source
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes(reg_size)
    exp = ['reg8.SR_0001', '1', '1', 'D_0001', 'D_0000']
    print(sigs, exp)
    assert(sigs == exp)

    reg: IclScanRegister =  icl_instance.get_icl_item_name("UnSized_5")
    concat: ConcatSig = reg.capture_source
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes(reg_size)
    exp = [ '1', '1', 'reg8.SR_0001', 'D_0001', 'D_0000']
    print(sigs, exp)
    assert(sigs == exp)
    
    reg: IclScanRegister =  icl_instance.get_icl_item_name("UnSized_6")
    concat: ConcatSig = reg.capture_source
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes(reg_size)
    exp = ['reg8.SR_0001', '1', '0', 'D_0001', 'D_0000']
    print(sigs, exp)
    assert(sigs == exp)    

    reg: IclScanRegister =  icl_instance.get_icl_item_name("Sized_0")
    concat: ConcatSig = reg.capture_source
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes(reg_size)
    exp = ['reg8.SR_0001', '1', '0', 'D_0001', 'D_0000']
    print(sigs, exp)
    assert(sigs == exp)
    
    reg: IclScanRegister =  icl_instance.get_icl_item_name("Sized_1")
    concat: ConcatSig = reg.capture_source
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes(reg_size)
    exp = ['reg8.SR_0001', '1', '0', '0', 'D_0000']
    print(sigs, exp)
    assert(sigs == exp)

    reg: IclScanRegister =  icl_instance.get_icl_item_name("Sized_2")
    reg_size = reg.get_vector_size()
    concat: ConcatSig = reg.capture_source
    sigs = concat.get_all_named_indexes(reg_size)
    exp = ['C_0001', 'C_0000', '1', '0', '0']
    print(sigs, exp)
    assert(sigs == exp)
    
    concat: ConcatSig = ConcatSig(reg.instance, [IclSignal("C", 1, 0),  IclNumber("4", "dec")], "data")     
    assert(concat.sized_number() == 0)
    concat.resize(5)
    assert(concat.sized_number() == 1)
    
    concat.negate()
    reg_size = reg.get_vector_size()
    sigs = concat.get_all_named_indexes_with_prefix(reg_size, 1)
    exp = ['(not C_0001)', '(not C_0000)', '0', '1', '1']
    print(sigs, exp)
    assert(sigs == exp)
    
    # input()
    
    ijtag_reg_model = IclRegisterModel(icl_instance)
    for i in range(1):
        ijtag_reg_model.iReset()
        ijtag_reg_model.iWrite("A", 1)
        ijtag_reg_model.iWrite("B", 0)
        ijtag_reg_model.iWrite("C", 1)
        vectors = ijtag_reg_model.iApply()

        ijtag_reg_model.iWrite("C", 2)
        ijtag_reg_model.iWrite("D", 3)
        vectors = ijtag_reg_model.iApply()

        ijtag_reg_model.iWrite("D", 6)
        vectors = ijtag_reg_model.iApply()

        ijtag_reg_model.iWrite("A", 3)
        ijtag_reg_model.iWrite("D", 7)
        ijtag_reg_model.iWrite("reg8.SR", 6)

        vectors = ijtag_reg_model.iApply()

def test_3():
    icl_files = icl_all
    module_name = "TreeFlat"
    
    all_icl_modules = pre_process_icl_files(icl_files)
    icl_instance = process_icl_module(all_icl_modules, module_name)
    ijtag_reg_model = IclRegisterModel(icl_instance)
    
    #ijtag_reg_model.plotGraph()

    
if __name__ == '__main__':
    #print(sys.argv)
    #main(sys.argv)

    icl_number_test()


    test_1()
    #test_2()    

    with Profile() as profile:
        test_2()    
        #test_3()

    # Now processing the stats
    stats = Stats(profile)
    stats.strip_dirs()
    stats.sort_stats(SortKey.CUMULATIVE)
    stats.print_stats(20)  # This limits the output to the top 20 lines
        
        