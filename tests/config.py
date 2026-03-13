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
    _needed_signals: list[str] = ["tck", "ce", "se", "ue", "si", "so", "sel"]

    def __init__(self, entity, clock, signals, optional_signals=None):
        missing = [s for s in self._needed_signals if s not in signals]
        if missing:
             raise ValueError(f"IJTAGInternalDriver Error: Map missing {missing}")

        self._observables: list[str] = []

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

    # Set elements (variables/signals/register ) to be observed in simulation after each step
    # Example:          
    #    driver.set_observable_elements(["SR_0.u_reg", "SR_1.u_reg"])
    def set_observable_elements(self, observables: list[str]):
        self._observables = observables
    
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
        print(f"--------------------------------------------------------------------")
        for step in ijtag_steps:
            out_data = await self.write_read_register(step.in_data)

            # If expected data has bit with x, mask this bit in actual data from DUT
            # In order to compare expected data and data from DUT
            masked_out_data = ""
            for idx, bit in enumerate(step.exp_data):
                if(bit == "X"):
                    masked_out_data = f"{masked_out_data}X"
                else:
                    masked_out_data = f"{masked_out_data}{out_data[idx]}"

            length = len(step.in_data)
            print(f"Sim. - Step: {step.step},       DUT act. data in  ({step.tdi_port}) ({step.type_of_chain}): {length}b'{step.in_data}")
            print(f"Sim. - Step: {step.step},       DUT act. data out ({step.tdo_port}) ({step.type_of_chain}): {length}b'{out_data}")
            print(f"Sim. - Step: {step.step}, solver    exp. data on  ({step.tdo_port}) ({step.type_of_chain}): {length}b'{step.exp_data}")
            print(f"Sim. - Step: {step.step}, mask. DUT act. data on  ({step.tdo_port}) ({step.type_of_chain}): {length}b'{masked_out_data}")

            # Prints DUT values of observable variables/signals/register/... in each step            
            for observable in self._observables:
                obj = getattr(self.entity, observable)
                print(f"Sim. - Step: {step.step}, Simulator spy on: {observable} -> DUT value: {obj.value}")

            # Check actual vs expected scan chain data
            assert(len(step.in_data) == len(out_data))
            if(masked_out_data != step.exp_data):

                class bcolors:
                    OKGREEN = '\033[92m'
                    FAIL = '\033[91m'
                    ENDC = '\033[0m'

                for idx, _ in enumerate(step.in_data_names):
                    tmp = f"Bit [{step.in_data_names[idx]}/{step.read_data_bit_names[idx]}] - act. {masked_out_data[idx]} vs exp. {step.exp_data[idx]}"
                    if(masked_out_data[idx] ==  step.exp_data[idx]):
                        print(f"{bcolors.OKGREEN}{tmp}{bcolors.ENDC}")
                    else:
                        print(f"{bcolors.FAIL}{tmp}{bcolors.ENDC}")
                        
                raise ValueError(f"Mismatch -> Expected data ({step.exp_data}), actual data ({masked_out_data}), step: {step.step}")
            
            print(f"--------------------------------------------------------------------")

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
            #print(type(self.bus.si.value), self.bus.si.value,  i)
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