
# Test loads ICL with simple network which has registers with various reset/default values.
# Test scan register default/reset values during retargeting.
# Test retargeting before and after reset.

import os
import unittest
import inspect

from tests.config import COMMON_ICL_BLOCKS, COMMON_VHDL_BLOCKS, IjtagSimulationDriver
from src.ijtag import *

import cocotb
from cocotb_tools.runner import get_runner, get_results
from cocotb.clock import Clock

# Get the directory containing the current file
current_dir = os.path.dirname(os.path.abspath(__file__))
    
class TestIclSyntax6(unittest.TestCase):

    def test_bad_reset_and_load_defaul_value(self):
        icl_files = ["test_icls/benchmarks_conv/ICL/test_icl_syntax_6.icl"]
        module_name = "test_icl_syntax_6_bad"
        
        with self.assertRaises(Exception):
            Ijtag(f"{module_name}", icl_files, [current_dir])

    def test_defaul_value_0(self):
        icl_files = ["test_icls/benchmarks_conv/ICL/test_icl_syntax_6.icl"]
        module_name = "test_icl_syntax_6"       

        ijtag = Ijtag(f"{module_name}", icl_files, [current_dir])

        scan_reg_0: IclScanRegister = ijtag.icl_instance.get_icl_item_name("SR_0")
        scan_reg_1: IclScanRegister = ijtag.icl_instance.get_icl_item_name("SR_1")

        self.assertEqual(scan_reg_0.default_value.get_number(), 0b10001010)
        self.assertEqual(scan_reg_1.default_value.get_number(), 0b00100101)
        
    def test_defaul_value_1(self):
        verilog_files = [current_dir + "/test_icls/benchmarks_conv/HDL/Verilog/test_icl_syntax_6.sv"]
        module_name = "test_icl_syntax_6"

        hdl_simulator = os.getenv("SIM", "icarus")       
        
        runner = get_runner(hdl_simulator)
        runner.build(
            sources=verilog_files,
            hdl_toplevel=module_name,
            always=True,
            waves=True
        )

        result = runner.test(
            hdl_toplevel=module_name,
            test_module=["tests.test_icl_syntax_6"],
            testcase=["test_icl_syntax_6_1_test"],
            waves=1
        )
        if get_results(result)[1]:
            self.fail("Cocotb simulation failed")

    def test_defaul_value_2(self):
        verilog_files = [current_dir + "/test_icls/benchmarks_conv/HDL/Verilog/test_icl_syntax_6.sv"]
        module_name = "test_icl_syntax_6"

        hdl_simulator = os.getenv("SIM", "icarus")       
        
        runner = get_runner(hdl_simulator)
        runner.build(
            sources=verilog_files,
            hdl_toplevel=module_name,
            always=True,
            waves=True
        )

        result = runner.test(
            hdl_toplevel=module_name,
            test_module=["tests.test_icl_syntax_6"],
            testcase=["test_icl_syntax_6_2_test"],
            waves=1
        )
        if get_results(result)[1]:
            self.fail("Cocotb simulation failed")

@cocotb.test()
async def test_icl_syntax_6_1_test(dut):
    icl_files = ["test_icls/benchmarks_conv/ICL/test_icl_syntax_6.icl"]
    module_name = "test_icl_syntax_6"
    test_func_name = inspect.getframeinfo(inspect.currentframe()).function

    # IJTAG model network creation from ICL files + IJTAG driver
    ijtag = IjtagSimulationDriver(dut, 30, module_name, icl_files, [current_dir])
    ijtag.set_observable_elements(
        [
            "SR_0.u_reg",
            "SR_1.u_reg"
        ]
    )

    print(f"-----------------------------------------------------------------------------------")
    print(f"Starting test simulation: {test_func_name}, ICL: {icl_files}, Module: {module_name}")
    print(f"-----------------------------------------------------------------------------------")

    ijtag.iWrite("SR_0")
    await ijtag.iApply()

    ijtag.iRead( "SR_0[7:0]", "0b1000_1010")
    ijtag.iRead( "SR_1[0:7]", "0b0010_0101")    
    await ijtag.iApply()
    
    ijtag.iWrite("SR_0[7]", "0b0")
    ijtag.iWrite("SR_1[7]", "0b0")
    ijtag.iRead( "SR_0[7:0]", "0b1000_1010")
    ijtag.iRead( "SR_1[0:7]", "0b0010_0101")    
    await ijtag.iApply()

    ijtag.iRead( "SR_0[7:0]", "0b0000_1010")
    ijtag.iRead( "SR_1[0:7]", "0b0010_0100")
    await ijtag.iApply()

@cocotb.test()
async def test_icl_syntax_6_2_test(dut):
    icl_files = ["test_icls/benchmarks_conv/ICL/test_icl_syntax_6.icl"]
    module_name = "test_icl_syntax_6"
    test_func_name = inspect.getframeinfo(inspect.currentframe()).function

    # IJTAG model network creation from ICL files + IJTAG driver
    ijtag = IjtagSimulationDriver(dut, 30, module_name, icl_files, [current_dir])
    ijtag.set_observable_elements(
        [
            "SR_0.u_reg",
            "SR_1.u_reg"
        ]
    )

    print(f"-----------------------------------------------------------------------------------")
    print(f"Starting test simulation: {test_func_name}, ICL: {icl_files}, Module: {module_name}")
    print(f"-----------------------------------------------------------------------------------")

    ijtag.iWrite("SR_0[0]", "0b1")
    ijtag.iWrite("SR_1[0]", "0b1")
    await ijtag.iApply()

    ijtag.iRead( "SR_0[7:0]", "0b1000_1011")
    ijtag.iRead( "SR_1[0:7]", "0b1010_0101")    
    await ijtag.iApply()

if __name__ == '__main__':
    unittest.main()