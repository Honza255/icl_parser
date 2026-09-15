import os
import unittest

from src.ijtag import *
import logging

# Get the directory containing the current file
current_dir = os.path.dirname(os.path.abspath(__file__))

# Check all ICL benchmarks can be opened and processed or at least most of them
class TestIclScanRegister(unittest.TestCase):


    def test_process_icl_ok_1(self):
        module_name = "ok_1"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        ijtag.draw_scan_graph_pydot()

    def test_process_icl_ok_2(self):
        module_name = "ok_2"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        ijtag.draw_scan_graph_pydot()

    def test_process_icl_ok_3(self):
        module_name = "ok_3"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        ijtag.draw_scan_graph_pydot()

    def test_process_icl_ok_4(self):
        module_name = "ok_4"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        ijtag.draw_scan_graph_pydot()

    def test_process_icl_ok_5(self):
        module_name = "ok_5"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        ijtag = Ijtag(module_name, icl_files, [current_dir])
        ijtag.draw_scan_graph_pydot()

    def test_process_icl_not_ok_1(self):
        module_name = "not_ok_1"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("test_process_icl_not_ok_1 did not fail")

    def test_process_icl_not_ok_2(self):
        module_name = "not_ok_2"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("test_process_icl_not_ok_2 did not fail")              

    def test_process_icl_not_ok_3(self):
        module_name = "not_ok_3"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("test_process_icl_not_ok_3 did not fail")

    def test_process_icl_not_ok_4(self):
        module_name = "not_ok_4"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("test_process_icl_not_ok_4 did not fail")
        
    def test_process_icl_not_ok_5(self):
        module_name = "not_ok_5"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("test_process_icl_not_ok_5 did not fail")

    def test_process_icl_not_ok_6(self):
        module_name = "not_ok_6"
        icl_files = [current_dir + "/test_icls/test_icl_scan_register.icl"]
        try:
            ijtag = Ijtag(module_name, icl_files, [current_dir])
        except:
            pass
        else:
            raise ValueError("test_process_icl_not_ok_6 did not fail")