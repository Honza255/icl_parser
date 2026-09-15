
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
    
class TestIclSyntax5(unittest.TestCase):

    def test_trap_or_flap(self):
        verilog_files = [current_dir + "/test_icls/benchmarks_conv/HDL/Verilog/test_icl_syntax_5.sv"]
        module_name = "test_icl_syntax_5"

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
            test_module=["tests.test_icl_syntax_5"],
            testcase=["test_icl_syntax_5_test"],
            waves=1
        )
        if get_results(result)[1]:
            self.fail("Cocotb simulation failed")

@cocotb.test()
async def test_icl_syntax_5_test(dut):
    icl_files = ["test_icls/benchmarks_conv/ICL/test_icl_syntax_5.icl"]
    module_name = "test_icl_syntax_5"
    test_func_name = inspect.getframeinfo(inspect.currentframe()).function

    # IJTAG model network creation from ICL files + IJTAG driver
    ijtag = IjtagSimulationDriver(dut, 30, module_name, icl_files, [current_dir])

    print(f"-----------------------------------------------------------------------------------")
    print(f"Starting test simulation: {test_func_name}, ICL: {icl_files}, Module: {module_name}")
    print(f"-----------------------------------------------------------------------------------")

    ijtag.draw_scan_graph_pydot()

    # Reset DUT
    ###########
    await ijtag.iReset()

    # Test - number is bigger that reg. or port
    #################################
    try:
        ijtag.iWrite("SR_0", "0b1_0000_1010")
    except:
        pass
    else:
        raise ValueError("Fail - iWrite must fail when number is bigger that reg. or port")

    try:
        ijtag.iRead("SR_0", "0b1_0000_1010")
    except:
        pass
    else:
        raise ValueError("Fail - iRead must fail when number is bigger that reg. or port")
    
    try:
        ijtag.iWrite("SR_0", "555555555555")
    except:
        pass
    else:
        raise ValueError("Fail - iWrite must fail when number is bigger that reg. or port")

    try:
        ijtag.iRead("SR_0", "555555555555")
    except:
        pass
    else:
        raise ValueError("Fail - iRead must fail when number is bigger that reg. or port")

    try:
        ijtag.iWrite("SR_0", "0xeeeeeeeeeeee")
    except:
        pass
    else:
        raise ValueError("Fail - iWrite must fail when number is bigger that reg. or port")

    try:
        ijtag.iRead("SR_0", "0xeeeeeeeeeeee")
    except:
        pass
    else:
        raise ValueError("Fail - iRead must fail when number is bigger that reg. or port")
            
    # Write and read to scan register
    #################################

    # Normal scan register order
    # SR_0 is defined as SR_1[7:0] in ICL, the data shifts from SR_1[7] -> SR_1[0]     
    ijtag.iWrite("SR_0", "3")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0000_0011)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0", "0xAa")
    ijtag.iRead( "SR_0",  "3")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b1010_1010)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0", "0xBb")
    ijtag.iRead( "SR_0", "0xAa")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b1011_1011)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0", "0b00111x01")
    ijtag.iRead( "SR_0", "0xBb")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0011_1001)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0", "0bx0111")
    ijtag.iRead( "SR_0", "0b00111x01")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0011_0111)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0", "0bx1")
    ijtag.iRead( "SR_0", "0bx0111")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0011_0111)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0[0]", "0")
    ijtag.iRead( "SR_0", "0bx0111")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0011_0110)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0[0]", "1")
    ijtag.iRead( "SR_0[0]", "0")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0011_0111)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0[4:0]", "0b0011")
    ijtag.iRead( "SR_0[0]", "1")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0010_0011)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0[4:0]", "0b1101")
    ijtag.iRead( "SR_0[4:0]", "0b0011")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0010_1101)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0[7:6]", "01")
    ijtag.iRead( "SR_0[4:0]", "0b1101")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0110_1101)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iRead( "SR_0[7:6]", "01")
    ijtag.iRead( "SR_0[4:0]", "0b1101")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0110_1101)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0")
    ijtag.iRead( "SR_0")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0110_1101)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iWrite("SR_0[0:4]", "0b11100")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0110_0111)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    ijtag.iRead("SR_0[0:4]", "0b11100")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0110_0111)
    assert(dut.SR_1.u_reg.value == 0b0000_0000)

    # Reversed scan register order
    # SR_1 is defined as SR_1[0:7] in ICL, the data shifts from SR_1[0] -> SR_1[7] 
    ijtag.iWrite("SR_1[7]", "1")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b01100111)
    assert(dut.SR_1.u_reg.value == 0b10000000)

    ijtag.iWrite("SR_1[0]", "1")
    ijtag.iRead("SR_1[7]",  "1")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b01100111)
    assert(dut.SR_1.u_reg.value == 0b10000001)

    ijtag.iWrite("SR_1[7:5]", "0b011")
    ijtag.iRead("SR_1[7]",  "1")
    ijtag.iRead("SR_1[0]",  "1")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b01100111)
    assert(dut.SR_1.u_reg.value == 0b01100001)

    ijtag.iWrite("SR_1[5:7]", "0b011")
    ijtag.iRead( "SR_1[7:0]", "0b0110_0001")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b01100111)
    assert(dut.SR_1.u_reg.value == 0b11000001)

    # if iWrite does not have a range defined, it shoud be treateated as SR_1[0:7]
    # 7.8.a - Omission of the bit range for a register or port or alias in PDL shall imply that the full width and
    #   index order of that element shall be used as defined in the ICL description
    ijtag.iWrite("SR_1",      "0b0000_1010")
    ijtag.iRead( "SR_1[7:0]", "0b1100_0001")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0110_0111)
    assert(dut.SR_1.u_reg.value == 0b0101_0000)

    ijtag.iRead( "SR_1[7:0]", "0b0101_0000")
    await ijtag.iApply()
    assert(dut.SR_0.u_reg.value == 0b0110_0111)
    assert(dut.SR_1.u_reg.value == 0b0101_0000)
    
if __name__ == '__main__':
    unittest.main()