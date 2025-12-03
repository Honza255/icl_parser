from src.ijtag import *

import cocotb
from cocotb.triggers import *
from cocotb.clock import Clock

from cocotb_bus.drivers import BusDriver

COMMON_ICL_BLOCKS =  [ "test_icls/benchmarks/ICL/EmptyModule.icl",
                       "test_icls/benchmarks/ICL/Instruments.icl",
                       "test_icls/benchmarks/ICL/NetworkStructs.icl"]

COMMON_VHDL_BLOCKS = ["test_icls/benchmarks/HDL/VHDL/Instruments.vhd",
                      "test_icls/benchmarks/HDL/VHDL/NetworkStructs.vhd",
                      "test_icls/benchmarks/HDL/VHDL/Primitives.vhd"]

ICL_BENCHMARKS = {        
    "BasicSCB":             COMMON_ICL_BLOCKS +
                            ["test_icls/benchmarks/ICL/Basic/BasicSCB/BasicSCB.icl"],
    "Mingle":               COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Basic/Mingle/Mingle.icl"],
    "TreeBalanced":         COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Basic/TreeBalanced/H953.icl",
                             "test_icls/benchmarks/ICL/Basic/TreeBalanced/TreeBalanced.icl" ],
    "TreeFlat":             COMMON_ICL_BLOCKS +
                            ["test_icls/benchmarks/ICL/Basic/TreeFlat/TreeFlat.icl"],
    "TreeFlat_Ex":          COMMON_ICL_BLOCKS +
                            ["test_icls/benchmarks/ICL/Basic/TreeFlat_Ex/G1023.icl",
                             "test_icls/benchmarks/ICL/Basic/TreeFlat_Ex/TreeFlat_Ex.icl"],
    "TreeUnbalanced":       COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Basic/TreeUnbalanced/A586710.icl",
                             "test_icls/benchmarks/ICL/Basic/TreeUnbalanced/TreeUnbalanced.icl"],

    "a586710":              COMMON_ICL_BLOCKS +
                            ["test_icls/benchmarks/ICL/Classic/a586710/a586710.icl"],
    "p22810":               COMMON_ICL_BLOCKS +
                            ["test_icls/benchmarks/ICL/Classic/p22810/p22810.icl"],
    "p34392":               COMMON_ICL_BLOCKS +
                            ["test_icls/benchmarks/ICL/Classic/p34392/p34392.icl"],
    "p93791":               COMMON_ICL_BLOCKS +
                            ["test_icls/benchmarks/ICL/Classic/p93791/p93791.icl"],
    "q12710":               COMMON_ICL_BLOCKS +
                            ["test_icls/benchmarks/ICL/Classic/q12710/q12710.icl"],
    "t512505":              COMMON_ICL_BLOCKS +
                            ["test_icls/benchmarks/ICL/Classic/t512505/t512505.icl"],

    "SOC_DAP_3D":           ["test_icls/benchmarks/ICL/Standard/CAD.icl",
                             "test_icls/benchmarks/ICL/Standard/SOC_DAP.icl"],                    
    "Kernel":               COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Standard/E30.icl",
                             "test_icls/benchmarks/ICL/Standard/A586710.icl",
                             "test_icls/benchmarks/ICL/Standard/Kernel/Kernel.icl"],
    "MultiCoreAccessLink":  COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Standard/E30.icl",
                             "test_icls/benchmarks/ICL/Standard/MultiCoreAccessLink.icl"],
    "MultiTap":             COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Standard/A586710.icl",
                             "test_icls/benchmarks/ICL/Standard/MultiTAP.icl"],

    "FlexScan":             COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Advanced/FlexScan/ScanCell.icl",
                            "test_icls/benchmarks/ICL/Advanced/FlexScan/FlexScan.icl"],
    "N17D3":                COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Advanced/N17D3/N17D3.icl"],    
    "N32D6":                COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Advanced/N32D6/N32D6.icl"],
    "N73D14":               COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Advanced/N73D14/N73D14.icl"],
    "N132D4":               COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Advanced/N132D4/N132D4.icl"],    
    "NE600P150":            COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Advanced/NE600P150/NE600P150.icl"],
    "NE1200P430":           COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Advanced/NE1200P430/NE1200P430.icl"],
    "TrapOrFlap":           COMMON_ICL_BLOCKS + 
                            ["test_icls/benchmarks/ICL/Advanced/TrapOrFlap/TrapOrFlap.icl"]

}


class IJTAGInternalDriver(BusDriver):
    # Mandatory abstract names for the internal interface
    _needed_signals = ["tck", "ce", "se", "ue", "si", "so", "sel"]

    def __init__(self, entity, clock, signals, optional_signals=None):
        missing = [s for s in self._needed_signals if s not in signals]
        if missing:
             raise ValueError(f"IJTAGInternalDriver Error: Map missing {missing}")

        self._signals = signals
        self._optional_signals = optional_signals if optional_signals else {}
        super().__init__(entity, name=None, clock=clock)

        # Initialize defaults
        self.bus.ce.value = 0
        self.bus.se.value = 0
        self.bus.ue.value = 0
        self.bus.sel.value = 0
        self.bus.si.value = 0

        # Handle Optional Reset Default
        if hasattr(self.bus, "rst"):
            self.bus.rst.value = 0 # Assume Active Low (inactive)

    async def reset_instrument(self):
        if hasattr(self.bus, "rst"):
            await Timer(5, "ns")
            self.bus.rst.value = 1
            await Timer(5, "ns")
            self.bus.rst.value = 0
            await Timer(5, "ns")
        else:
            raise ValueError("Requested instrument reset, but 'rst' signal is not mapped.")

    async def apply_ijtag_steps(self, ijtag_steps: list[jtagStep]):
        for step in ijtag_steps:
            act_out_data = await self.write_read_register(step.in_data)
            print("SREG1.SR", self.entity.SREG1.SR.u_reg.value )
            print("SIB_10.SR", self.entity.SIB_10.SR.u_reg.value )
            print("SIB_23.SR", self.entity.SIB_23.SR.u_reg.value )
            print("SIB_24.SR", self.entity.SIB_24.SR.u_reg.value )
            print("SIB_11.SR", self.entity.SIB_11.SR.u_reg.value )
            print("SIB_12.SR", self.entity.SIB_12.SR.u_reg.value )
            print("SCB1.SR", self.entity.SCB1.SR.u_reg.value )
            print("WI_3.reg8.SR", self.entity.WI_3.reg8.SR.u_reg.value )
            print("WI_4.reg8.SR", self.entity.WI_4.reg8.SR.u_reg.value )

            print(step, "length", len(step.in_data))
            print(step, "act", act_out_data)
            print(step, "exp", step.exp_data)
            assert(len(step.in_data) == len(act_out_data))
            
            modified_act_out_data = ""
            for idx, bit in enumerate(step.exp_data):
                if(bit == "X"):
                    modified_act_out_data = f"{modified_act_out_data}X"
                else:
                    modified_act_out_data = f"{modified_act_out_data}{act_out_data[idx]}"
            print(step, "acc", modified_act_out_data)
            assert(modified_act_out_data == step.exp_data)

    async def write_read_register(self, in_vector: str) -> str:

        clock = Clock(self.clock, 10, "ns")
        cocotb.start_soon(clock.start())
        await  RisingEdge(self.clock)
        await  RisingEdge(self.clock)
        await  RisingEdge(self.clock)

        # --- 1. CAPTURE PHASE (CE) ---
        self.bus.ce.value = 1
        self.bus.sel.value = 1
        await FallingEdge(self.clock)
        await RisingEdge(self.clock)
        self.bus.ce.value = 0
        await FallingEdge(self.clock)
        
        # --- 2. SHIFT PHASE (SE) ---
        self.bus.se.value  = 1
        read_val = ""
        for i in reversed(in_vector):
            assert(i in ["1", "0"])
            self.bus.si.value = 1 if i == "1" else 0
            print(type(self.bus.si.value), self.bus.si.value,  i)
            await RisingEdge(self.clock)
            read_val = f"{self.bus.so.value}{read_val}"
            await FallingEdge(self.clock)
        self.bus.se.value = 0

        # --- 3. UPDATE PHASE (UE) ---
        await RisingEdge(self.clock)
        self.bus.ue.value = 1
        await FallingEdge(self.clock)
        self.bus.ue.value = 0
        self.bus.sel.value = 0

        await  RisingEdge(self.clock)
        await  RisingEdge(self.clock)
        await  RisingEdge(self.clock)
        clock.stop()

        return read_val