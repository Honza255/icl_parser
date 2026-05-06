# Test loads ICL with simple TAP network.
# Test generates vectors for reading and wrting ICL registers via retargeter.
# Test drives vectors to DUT in simulation and checks actual and expected values.

import os
import unittest
import inspect

from tests.config import  IjtagSimulationDriver
from src.ijtag import *

import cocotb
from cocotb_tools.runner import get_runner

current_dir = os.path.dirname(os.path.abspath(__file__))

class TestIclSyntax7(unittest.TestCase):

    def test_icl_syntax_7(self):
        verilog_files = [current_dir + "/test_icls/benchmarks_conv/HDL/Verilog/test_icl_syntax_7.sv"]
        module_name = "test_icl_syntax_7"

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
            test_module=["tests.test_icl_syntax_7"],
            testcase=["test_icl_syntax_7_test"],
            waves=1
        )

@cocotb.test()
async def test_icl_syntax_7_test(dut):
    icl_files = ["test_icls/benchmarks_conv/ICL/test_icl_syntax_7.icl"]
    module_name = "test_icl_syntax_7"
    test_func_name = inspect.getframeinfo(inspect.currentframe()).function

    ijtag = IjtagSimulationDriver(dut, 30, module_name, icl_files, [current_dir])
    ijtag.icl_retargeter.set_max_steps(8)

    print(f"-----------------------------------------------------------------------------------")
    print(f"Starting test simulation: {test_func_name}, ICL: {icl_files}, Module: {module_name}")
    print(f"-----------------------------------------------------------------------------------")

    ijtag.draw_scan_graph_pydot()

    await ijtag.iReset(sync=0)
    
    # Verify DUT reset values
    assert dut.conf_a_q.value   == 0xA5
    assert dut.conf_b_q.value   == 0xDEAD
    assert dut.status_q.value   == 0xABC
    assert dut.ctrl_q.value     == 0xCAFEBABE
    assert dut.jtag_ir_q.value  == 0x01

    ijtag.iRead("IDCODE", "0x00000001")
    await ijtag.iApply()

    ijtag.iWrite("CONF_A", "0x12")
    await ijtag.iApply()
    assert dut.conf_a_q.value == 0x12

    ijtag.iRead("CONF_A", "0x12")
    await ijtag.iApply()
    assert dut.conf_a_q.value == 0x12

    ijtag.iWrite("CONF_B", "0x1234")
    await ijtag.iApply()
    assert dut.conf_b_q.value == 0x1234

    ijtag.iRead("CONF_B", "0x1234")
    await ijtag.iApply()

    ijtag.iWrite("STATUS_REG", "0x789")
    await ijtag.iApply()
    assert dut.status_q.value == 0x789

    ijtag.iRead("STATUS_REG", "0x789")
    await ijtag.iApply()
    assert dut.status_q.value == 0x789

    ijtag.iWrite("CTRL", "0xDEADBEEF")
    await ijtag.iApply()
    assert dut.ctrl_q.value == 0xDEADBEEF

    ijtag.iRead("CTRL", "0xDEADBEEF")
    await ijtag.iApply()
    assert dut.ctrl_q.value == 0xDEADBEEF
    
    ijtag.iWrite("CONF_A", "0xFF")
    await ijtag.iApply()
    assert dut.conf_a_q.value == 0xFF

    ijtag.iWrite("CONF_B", "0xABCD")
    await ijtag.iApply()
    assert dut.conf_b_q.value == 0xABCD

    ijtag.iRead("CONF_A", "0xFF")
    await ijtag.iApply()
    assert dut.conf_a_q.value == 0xFF
    
    ijtag.iRead("CONF_B", "0xABCD")
    await ijtag.iApply()
    assert dut.conf_b_q.value == 0xABCD
    
    # Sync reset with TMS
    await ijtag.iReset(sync=1)
    
    # Read reset registers
    ijtag.iRead("CONF_A", "0xA5")
    ijtag.iRead("CONF_B", "0xDEAD")
    ijtag.iRead("STATUS_REG", "0xABC")
    ijtag.iRead("CTRL", "0xCAFEBABE")    
    await ijtag.iApply()

    assert dut.conf_a_q.value   == 0xA5
    assert dut.conf_b_q.value   == 0xDEAD
    assert dut.status_q.value   == 0xABC
    assert dut.ctrl_q.value     == 0xCAFEBABE

if __name__ == '__main__':
    unittest.main()
