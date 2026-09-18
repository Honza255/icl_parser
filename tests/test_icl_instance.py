import os
import unittest

from src.ijtag import *
import logging

# Get the directory containing the current file
current_dir = os.path.dirname(os.path.abspath(__file__))

# Check all ICL benchmarks can be opened and processed or at least most of them
class TestIclInstance(unittest.TestCase):

    def test_process_icl_ok_0(self):
        module_name = "ok_icl_instace_0"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        ijtag.draw_scan_graph_pydot()
        assert(ijtag.ijtag_reg_model.get_element_driver("A.SI_0000") == ["tdi_0000"])
        assert(ijtag.ijtag_reg_model.get_element_driver("A.SI_0001") == ["0"])

    def test_process_icl_ok_1(self):
        module_name = "ok_icl_instace_1"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        ijtag.draw_scan_graph_pydot()
        assert(ijtag.ijtag_reg_model.get_element_driver("A.SI_0000") == ["tdi_0000"])
        assert(ijtag.ijtag_reg_model.get_element_driver("A.SI_0001") == ["0"])

    def test_process_icl_ok_2(self):
        module_name = "ok_icl_instace_2"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        ijtag.draw_scan_graph_pydot()
        assert(ijtag.ijtag_reg_model.get_element_driver("A.SI_0000") == ["tdi_0000"])
        assert(ijtag.ijtag_reg_model.get_element_driver("A.SI_0001") == ["0"])
        
    def test_process_icl_ok_3(self):
        module_name = "ok_icl_instace_2"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        ijtag.draw_scan_graph_pydot()
        
    def test_process_icl_not_ok_0(self):
        module_name = "not_ok_icl_instace_0"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("Error during IJTAG initialization")

    def test_process_icl_not_ok_1(self):
        module_name = "not_ok_icl_instace_1"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("Error during IJTAG initialization")

    def test_process_icl_not_ok_2(self):
        module_name = "not_ok_icl_instace_2"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("Error during IJTAG initialization")


    def test_process_icl_not_ok_3(self):
        module_name = "not_ok_icl_instace_3"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("Error during IJTAG initialization")

    def test_process_icl_not_ok_4(self):
        module_name = "not_ok_icl_instace_4"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("Error during IJTAG initialization")


    def test_process_icl_not_ok_5(self):
        module_name = "not_ok_icl_instace_5"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("Error during IJTAG initialization")


    def test_process_icl_not_ok_6(self):
        module_name = "not_ok_icl_instace_6"
        icl_files = [current_dir + "/test_icls/test_icl_instance.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("Error during IJTAG initialization")

