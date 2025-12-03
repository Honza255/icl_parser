
import os
import unittest

from tests.config import COMMON_ICL_BLOCKS
from src.ijtag import *

# Get the directory containing the current file
current_dir = os.path.dirname(os.path.abspath(__file__))

class TestIclSyntax1(unittest.TestCase):

    def test_all(self):
        icl_files = ["test_icls/scan_mux_001.icl", "test_icls/scan_mux_002.icl", "test_icls/scan_mux_003.icl"] + COMMON_ICL_BLOCKS
        module_name = "scan_mux_002"

        ijtag = Ijtag(module_name, icl_files, [current_dir])
        icl_instance = ijtag.icl_instance

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

    def test_3(self):
        icl_files = COMMON_ICL_BLOCKS + ["test_icls/benchmarks/ICL/Basic/TreeFlat/TreeFlat.icl"]
        module_name = "TreeFlat"
        
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        # ijtag.create_network_graph()


if __name__ == '__main__':
    unittest.main()