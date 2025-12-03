import os
import unittest

from tests.config import ICL_BENCHMARKS
from src.ijtag import *

# Get the directory containing the current file
current_dir = os.path.dirname(os.path.abspath(__file__))

# Check all ICL benchmarks can be opened and processed or at least most of them
class TestIclSyntax4(unittest.TestCase):

    ##########
    # Basic
    ##########

    # OK 
    def test_process_icl_BasicSCB(self):
        module_name = "BasicSCB"
        icl_files = ICL_BENCHMARKS[module_name]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
    
    # OK
    def test_process_icl_Mingle(self):
        module_name = "Mingle"
        icl_files = ICL_BENCHMARKS[module_name]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
    
        
    #def test_process_icl_TreeBalanced(self):
    #    module_name = "TreeBalanced"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(module_name, icl_files, [current_dir])

    # OK
    def test_process_icl_TreeFlat(self):
        module_name = "TreeFlat"
        icl_files = ICL_BENCHMARKS[module_name]
        ijtag = Ijtag(module_name, icl_files, [current_dir])

    #def test_process_icl_TreeFlat_Ex(self):
    #    module_name = "TreeFlat_Ex"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(module_name, icl_files, [current_dir])

    #def test_process_icl_TreeUnbalanced(self):
    #    module_name = "TreeFlat"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(module_name, icl_files, [current_dir])


    ##########
    # Classic
    ##########

    # OK - slow
    #def test_process_icl_a586710(self):
    #    module_name = "a586710"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag("a586710::M0", icl_files, [current_dir])

    # OK
    def test_process_icl_p22810(self):
        module_name = "p22810"
        icl_files = ICL_BENCHMARKS[module_name]
        ijtag = Ijtag(f"{module_name}::M0", icl_files, [current_dir])

    #def test_process_icl_p34392(self):
    #    module_name = "p34392"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}::M0", icl_files, [current_dir])

    #def test_process_icl_p93791(self):
    #    module_name = "p93791"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}::M0", icl_files, [current_dir])

    #def test_process_icl_q12710(self):
    #    module_name = "q12710"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}::M0", icl_files, [current_dir])

    #def test_process_icl_t512505(self):
    #    module_name = "t512505"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}::M0", icl_files, [current_dir])

    ##########
    # Advanced
    ##########

    # OK - slow   
    #def test_process_icl_FlexScan(self):
    #     module_name = "FlexScan"
    #     icl_files = ICL_BENCHMARKS[module_name]
    #     #ijtag = Ijtag("ScanCell", icl_files, [current_dir])
    #     ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    # OK - fast       
    def test_process_icl_N17D3(self):
        module_name = "N17D3"
        icl_files = ICL_BENCHMARKS[module_name]
        ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    # Too slow       
    #def test_process_icl_N32D6(self):
    #    module_name = "N32D6"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    # Too slow       
    # def test_process_icl_N73D14(self):
    #    module_name = "N73D14"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    # Ok
    # def test_process_icl_N132D4(self):
    #     module_name = "N132D4"
    #     icl_files = ICL_BENCHMARKS[module_name]
    #     ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    # ??? Too slow
    # def test_process_icl_NE600P150(self):
    #    module_name = "NE600P150"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])       

    # ??? Too slow
    #def test_process_icl_NE1200P430(self):
    #    module_name = "NE1200P430"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    # Ok
    def test_process_icl_TrapOrFlap(self):
        module_name = "TrapOrFlap"
        icl_files = ICL_BENCHMARKS[module_name]
        ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    ##########
    # Standard    
    ##########

    # Error -> Instance not supported in onehot group with an address
    #def test_process_icl_SOC_DAP_3D(self):
    #    module_name = "SOC_DAP_3D"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    # Error -> AccessLink not supported
    #def test_process_icl_Kernel(self):
    #    module_name = "Kernel"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    # Error -> AccessLink not supported
    #def test_process_icl_MultiCoreAccessLink(self):
    #    module_name = "MultiCoreAccessLink"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

    # Error -> Too slow/ too much resourses
    #def test_process_icl_MultiTap(self):
    #    module_name = "MultiTap"
    #    icl_files = ICL_BENCHMARKS[module_name]
    #    ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])
