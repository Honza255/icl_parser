
import os
import unittest
import inspect

from tests.config import COMMON_ICL_BLOCKS, COMMON_VHDL_BLOCKS, IjtagSimulationDriver
from src.ijtag import *

import cocotb
from cocotb_tools.runner import get_runner
from cocotb.clock import Clock

# Get the directory containing the current file
current_dir = os.path.dirname(os.path.abspath(__file__))
    
class TestIclSyntax3(unittest.TestCase):

    def test_trap_or_flap(self):
        vhdl_files = COMMON_VHDL_BLOCKS + ["test_icls/benchmarks/HDL/VHDL/Advanced/TrapOrFlap/TrapOrFlap.vhd"]
        verilog_files = [current_dir + "/test_icls/benchmarks_conv/TrapOrFlap.sv"]
        module_name = "TrapOrFlap"

        hdl_simulator = os.getenv("SIM", "icarus")       
        
        runner = get_runner(hdl_simulator)
        runner.build(
            sources=verilog_files,
            hdl_toplevel=module_name,
            always=True,
            waves=True
        )

        runner.test(
            hdl_toplevel=module_name,
            test_module=["tests.test_icl_syntax_3"],
            testcase=["TrapOrFlap_simple_test"],
            waves=1
        )

@cocotb.test()
async def TrapOrFlap_simple_test(dut):
    icl_files = COMMON_ICL_BLOCKS + ["test_icls/benchmarks/ICL/Advanced/TrapOrFlap/TrapOrFlap.icl"]
    module_name = "TrapOrFlap"
    test_func_name = inspect.getframeinfo(inspect.currentframe()).function

    # IJTAG model network creation from ICL files + IJTAG driver
    ijtag = IjtagSimulationDriver(dut, 30, module_name, icl_files, [current_dir])

    print(f"-----------------------------------------------------------------------------------")
    print(f"Starting test simulation: {test_func_name}, ICL: {icl_files}, Module: {module_name}")
    print(f"-----------------------------------------------------------------------------------")


    clock = Clock(dut.INSTR_CLK, 10, "ns")
    cocotb.start_soon(clock.start())

    # Reset DUT
    ###########
    await ijtag.iReset()

    # Write and read to scan register
    #################################
    ijtag.iWrite("SREG1.SR", "3")
    await ijtag.iApply()

    ijtag.iRead("SREG1.SR", "0") # Capture of SREG1.SR is always zero
    ijtag.iRead("SIB_24.SR", "1") # SIB must be set to reach SREG1.SR
    ijtag.iRead("SIB_11.SR", "1") # SIB must be set to reach SREG1.SR
    ijtag.iWrite("WI_4.reg8.SR", "133")
    ijtag.iWrite("WI_3.reg8.SR", "191")
    await ijtag.iApply()

    ijtag.iRead("SREG0.SR", "3") # Capture of SREG0.SR is always 3
    ijtag.iRead("WI_4.reg8.SR", "133")
    ijtag.iRead("WI_3.reg8.SR", "191")    
    await ijtag.iApply()

    ijtag.iWrite("CONF1.SR", "16")
    ijtag.iRead("WI_4.reg8.SR", "133")
    ijtag.iRead("WI_3.reg8.SR", "191")    
    await ijtag.iApply()

    ijtag.iWrite("CONF2.SR", "7")
    ijtag.iRead("WI_4.reg8.SR", "133")
    ijtag.iRead("WI_3.reg8.SR", "191")
    await ijtag.iApply()

    ijtag.iWrite("WI_4.reg8.SR", "5")
    ijtag.iWrite("WI_3.reg8.SR", "63")
    ijtag.iRead("WI_4.reg8.SR", "133")
    ijtag.iRead("WI_3.reg8.SR", "191")
    await ijtag.iApply()

    ijtag.iRead("WI_4.reg8.SR", "133")
    ijtag.iRead("WI_3.reg8.SR", "191")
    await ijtag.iApply()
    
    #ijtag.plot_network_graph()

if __name__ == '__main__':
    unittest.main()