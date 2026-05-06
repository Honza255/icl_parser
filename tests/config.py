from src.ijtag import *

import cocotb
from cocotb.triggers import *
from cocotb.clock import Clock

from cocotb.handle import LogicObject, LogicArrayObject       
from cocotb.triggers import Combine

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

class DummyPort:
    def __init__(self):
        self.value: int = 0

class ClientInterface():
    def __init__(self):
        self.tck: LogicObject | DummyPort = None
        self.selects: list[LogicObject | DummyPort] = None
        self.shift: LogicObject | DummyPort = None
        self.update: LogicObject | DummyPort = None
        self.capture: LogicObject | DummyPort = None
        self.reset: LogicObject | DummyPort = None
        self.reset_polarity: int = 1
        self.scan_in_ports: dict[str, LogicObject | DummyPort] = None
        self.scan_out_ports: dict[str, LogicObject | DummyPort] = None
        
class ClientTapInterface():
    def __init__(self):
        self.tck: LogicObject | DummyPort = None
        self.trst: LogicObject | DummyPort = None
        self.tms: LogicObject | DummyPort = None
        self.scan_in_ports: dict[str, LogicObject | DummyPort] = None
        self.scan_out_ports: dict[str, LogicObject | DummyPort] = None

class IjtagSimulationDriver(Ijtag):
    ALL_ONES = -1
    ALL_ZEROES = 0  

    # Crete IJAG model from ICL files
    # sim:            Simulation object
    # tck_period_ns   TCK period in ns
    # top_name :      Top ICL module name
    # icl_files:      ICL files
    # iclude_folders: Where to look for ICL files without absolute path
    def __init__(self, sim, tck_period_ns: int, top_module_name: str, icl_files: list[str], iclude_folders: list[str] = []):
        super().__init__(top_module_name, icl_files, iclude_folders)
        self.sim_dut = sim

        self.client_interfaces: dict[str, ClientInterface] = {}
        self.client_interface_resets: tuple[LogicObject, int] = None

        self.tap_client_interfaces: dict[str, ClientTapInterface] = {}

        self.tck_period_ns = tck_period_ns
        self.other = None

        self._observables: list[str] = []

        self.one_hot_scan_interfaces: dict[str,list[str]] = {}

        # Check that handoff ports also exists in simulation                       
        ports: list[IclPort] = self.icl_instance.get_icl_item_type(IclPort)
        for port in ports:
            self.check_existence(port.get_name(), port.get_all_indexes())

        def get_port(port_type: type, ports: list[IclSignal], exp_size: int) -> list[tuple[str, int, bool]]:
            tmp = [] 
            for port_ref in ports:
                icl_item: IclPort = self.icl_instance.get_icl_item_name(port_ref.get_name())
                if isinstance(icl_item, port_type):
                    name: str = port_ref.get_name()
                    indexes: list[int] = self.icl_instance.get_signal_indexes(self.icl_instance, port_ref)
                    if isinstance(icl_item, AddPolarity):
                        tmp += [(name, idx, icl_item.get_index_polarity(idx)) for idx in indexes]
                    else:
                        polarity = False if isinstance(icl_item, (IclTrstPort, IclToTrstPort)) else True
                        tmp += [(name, idx, polarity) for idx in indexes]

            if tmp:
                if exp_size > 0:
                    assert(len(tmp) == exp_size)
                return tmp
            else:
                return [None]

        interfaces: list[IclScanInterface] = self.icl_instance.get_icl_item_type(IclScanInterface)                   
        for interface in interfaces:
            #reset = [isinstance(port, IclResetPort) for port in interface.interface_ports_ref]
            #if reset:
                
            if interface.get_interface_type() == CLIENT_SCAN_INTERFACE:
                self.add_clien_interface(
                    interface_name = interface.get_name(),
                    scan_in_ports  = {chain["name"]: get_port(IclScanInPort, chain["ports"], 1)[0] for chain in interface.chains},
                    scan_out_ports = {chain["name"]: get_port(IclScanOutPort, chain["ports"], 1)[0] for chain in interface.chains},
                    tck            = get_port(IclTckPort, interface.interface_ports_ref, 1)[0],
                    shift          = get_port(IclShiftEnable, interface.interface_ports_ref, 1)[0],
                    update         = get_port(IclUpdateEnable, interface.interface_ports_ref, 1)[0],
                    capture        = get_port(IclCaptureEnable, interface.interface_ports_ref, 1)[0],
                    reset          = get_port(IclResetPort, interface.interface_ports_ref, 1)[0],
                    select         = get_port(IclSelectPort, interface.interface_ports_ref, -1)
                )
            elif interface.get_interface_type() == CLIENT_TAP:
                self.add_tap_client_interface(
                    interface_name = interface.get_name(),
                    scan_in_ports  = {chain["name"]: get_port(IclScanInPort, chain["ports"], 1)[0] for chain in interface.chains},
                    scan_out_ports = {chain["name"]: get_port(IclScanOutPort, chain["ports"], 1)[0] for chain in interface.chains},
                    tck            = get_port(IclTckPort, interface.interface_ports_ref, 1)[0],
                    tms            = get_port(IclTmsPort, interface.interface_ports_ref, 1)[0],
                    trst           = get_port(IclTrstPort, interface.interface_ports_ref, 1)[0]
                )

        for reset_port in self.icl_instance.get_icl_item_type(IclResetPort):
            name = reset_port.get_name()
            indexes = reset_port.get_all_indexes()
            self.client_interface_resets = [(self.get_one_bit_port((name, index, 1)), reset_port.get_index_polarity(index)) for index in indexes]

    async def iApply(self):
        super().iApply()
        await self.apply_ijtag_steps(self.getiApplyVectors())

    async def iReset(self, sync: bool = 0):
        super().iReset(sync)

        # ---  De-assert all interface signals ---
        await Timer(self.tck_period_ns, "ns")
        
        for interface_name, interface in self.client_interfaces.items():
            for chain_name, scan_in_port in interface.scan_in_ports.items():
                scan_in_port.value = 0
            for sel in interface.selects:
                sel.value = 0
            interface.capture.value = 0
            interface.update.value = 0
            interface.shift.value = 0
            interface.tck.value = 0
            interface.reset.value = not interface.reset_polarity
            
        for interface_name, interface in self.tap_client_interfaces.items():
            for chain_name, scan_in_port in interface.scan_in_ports.items():
                scan_in_port.value = 0
            interface.tck.value = 0
            if isinstance(interface.trst, DummyPort):
                interface.tms.value = 1
                interface.trst.value = 1          
            elif sync:
                interface.tms.value = 1
                interface.trst.value = 1           
            else:
                interface.tms.value = 0
                interface.trst.value = 1


        await Timer(self.tck_period_ns * 0.75, "ns")
        for interface_name, interface in self.tap_client_interfaces.items():
            interface.tck.value = 1
        await Timer(self.tck_period_ns * 0.25, "ns")

        # --- Assert resets and de-assert resets ---

        if self.client_interface_resets:
            for dut_port, reset_polarity in self.client_interface_resets:
                dut_port.value = reset_polarity

        for interface_name, interface in self.tap_client_interfaces.items():
            if isinstance(interface.trst, DummyPort):
                interface.tms.value = 1
                interface.trst.value = 1
            elif sync:
                interface.tms.value = 1
                interface.trst.value = 1
            else:
                interface.tms.value = 0
                interface.trst.value = 0

        await Timer(self.tck_period_ns * 0.25, "ns")
        for interface_name, interface in self.tap_client_interfaces.items():
            interface.tck.value = 0
        await Timer(self.tck_period_ns * 0.5, "ns")
        for interface_name, interface in self.tap_client_interfaces.items():
            interface.tck.value = 1
        await Timer(self.tck_period_ns * 0.25, "ns")

        if self.client_interface_resets:
            for dut_port, reset_polarity in self.client_interface_resets:
                dut_port.value = not reset_polarity

        for _ in range(3):
            for interface_name, interface in self.tap_client_interfaces.items():
                if isinstance(interface.trst, DummyPort):
                    interface.tms.value = 1
                    interface.trst.value = 1
                elif sync:
                    interface.tms.value = 1
                    interface.trst.value = 1
                else:
                    interface.tms.value = 0
                    interface.trst.value = 1

            await Timer(self.tck_period_ns * 0.25, "ns")
            for interface_name, interface in self.tap_client_interfaces.items():
                interface.tck.value = 0
            await Timer(self.tck_period_ns * 0.5, "ns")
            for interface_name, interface in self.tap_client_interfaces.items():
                interface.tck.value = 1
            await Timer(self.tck_period_ns * 0.25, "ns")

        for interface_name, interface in self.tap_client_interfaces.items():
            if isinstance(interface.trst, DummyPort):
                interface.tms.value = 0
                interface.trst.value = 1
            elif sync:
                interface.tms.value = 0
                interface.trst.value = 1
            else:
                interface.tms.value = 0
                interface.trst.value = 1

        # Last pulse
        await Timer(self.tck_period_ns * 0.25, "ns")
        for interface_name, interface in self.tap_client_interfaces.items():
            interface.tck.value = 0
        await Timer(self.tck_period_ns * 0.5, "ns")
        for interface_name, interface in self.tap_client_interfaces.items():
            interface.tck.value = 1
        await Timer(self.tck_period_ns * 0.25, "ns")

        # Finish last pulse period
        await Timer(self.tck_period_ns * 0.25, "ns")
        for interface_name, interface in self.tap_client_interfaces.items():
            interface.tck.value = 0
        await Timer(self.tck_period_ns * 0.5, "ns")
        

    def check_existence(self, port_name: str, indexes: list[int]) -> bool:

        assert((port_name != "") and (len(indexes) > 0))

        dut_object = None
        try:
            dut_object = getattr(self.sim_dut, port_name)
        except (AttributeError) as e:
            return False

        if not isinstance(dut_object, (LogicObject, LogicArrayObject)):
            raise ValueError(f" DUT port {port_name} is not a LogicObject or LogicArrayObject but {type(dut_object)}, ICL port is limited to X or X[1:0]")

        if isinstance(dut_object, LogicObject):
            # There is no way to get index from LogicObject, so we use work around
            # _handle.get_range() is a private API — may break on cocotb updates            
            left, right, direction = dut_object._handle.get_range()
            for index in indexes:
                if not (min(left, right) <= index <= max(left, right)):
                    return False
            return True           
        else:
            for index in indexes:
                if index not in dut_object.range:
                    return False
            return True

    def get_one_bit_port(self, port: tuple[str, int]) -> LogicObject | DummyPort:
        if not port:
            return DummyPort()
        port_name, index, polarity = port

        try:
            dut_object = getattr(self.sim_dut, port_name)
        except (AttributeError) as e:
            raise ValueError(f"DUT port: {port_name} not found in simulation")

        if isinstance(dut_object, LogicObject):
            # There is no way to get index from LogicObject, so we use work around
            # _handle.get_range() is a private API — may break on cocotb updates            
            left, right, direction = dut_object._handle.get_range()
            if (min(left, right) <= index <= max(left, right)):
                return dut_object
            else:
                raise ValueError(f"DUT port: {port_name} does not have an index: {index}")
        elif isinstance(dut_object, LogicArrayObject):
            if index in dut_object.range:
                return dut_object[index]
            else:
                raise ValueError(f"DUT port: {port_name} does not have an index: {index}")
        else:
            raise ValueError(f" DUT port {port_name} is not a LogicObject or LogicArrayObject but {type(dut_object)}")
        
        
    def add_clien_interface(self,
            interface_name: str,
            scan_in_ports:  dict[str,tuple[str, int, bool]],
            scan_out_ports: dict[str,tuple[str, int, bool]],
            tck:            tuple[str, int, bool],
            shift:          tuple[str, int, bool],
            update:         tuple[str, int, bool],
            capture:        tuple[str, int, bool] = None,
            reset:          tuple[str, int, bool] = None,
            select:         list[tuple[str, int, bool]] = None
        ):
        interface = ClientInterface()
        interface.scan_in_ports = {key: self.get_one_bit_port(port) for key, port in scan_in_ports.items()}
        interface.scan_out_ports = {key: self.get_one_bit_port(port) for key, port in scan_out_ports.items()}        
        interface.tck = self.get_one_bit_port(tck)
        interface.shift = self.get_one_bit_port(shift)
        interface.update = self.get_one_bit_port(update)
        interface.capture = self.get_one_bit_port(capture)
        interface.reset = self.get_one_bit_port(reset)
        interface.reset_polarity = reset[2] if reset else 1
        assert(interface.reset_polarity in [1,0])
        interface.selects = [self.get_one_bit_port(x) for x in select]  

        self.client_interfaces[interface_name] = interface
        
    def add_tap_client_interface(self,
            interface_name: str,
            scan_in_ports:  dict[str,tuple[str, int, bool]],
            scan_out_ports: dict[str,tuple[str, int, bool]],
            tck:            tuple[str, int, bool],
            tms:            tuple[str, int, bool],
            trst:           tuple[str, int, bool] = None
        ):
        interface = ClientTapInterface()
        interface.scan_in_ports = {key: self.get_one_bit_port(port) for key, port in scan_in_ports.items()}
        interface.scan_out_ports = {key: self.get_one_bit_port(port) for key, port in scan_out_ports.items()}        
        interface.tck = self.get_one_bit_port(tck)
        interface.tms = self.get_one_bit_port(tms)
        interface.trst = self.get_one_bit_port(trst)

        self.tap_client_interfaces[interface_name] = interface

    async def apply_ijtag_steps(self, ijtag_steps: list[stepScanData]):
        assert(len(ijtag_steps) > 0)

        if ijtag_steps[0].scan_interface_name in self.client_interfaces:
            interface = self.client_interfaces[ijtag_steps[0].scan_interface_name]
            drive_one_step = self.drive_client_interface          
        elif ijtag_steps[0].scan_interface_name in self.tap_client_interfaces:
            interface = self.tap_client_interfaces[ijtag_steps[0].scan_interface_name]
            drive_one_step = self.drive_tap_interface
        else:
            raise ValueError(f"Unknown scan interface: {ijtag_steps[0].scan_interface_name}")
        
        for step in ijtag_steps:
            print(f"--------------------------------------------------------------------")      
            chains_data_out: list[tuple[str, str]] = await drive_one_step(interface, step)

            # Prints DUT values of observable variables/signals/register/... in each step of iApply         
            for observable in self._observables:
                obj = getattr(self.sim_dut, observable)
                print(f"Sim. - Step: {step.step}, Simulator spy on: {observable} -> DUT value: {obj.value}")
                            
            print(f"--------------------------------------------------------------------")
            self.check_chains(step, chains_data_out)

        print(f"--------------------------------------------------------------------")

    # Set elements (variables/signals/register ) to be observed in simulation after each step
    # Example:          
    #    driver.set_observable_elements(["SR_0.u_reg", "SR_1.u_reg"])
    def set_observable_elements(self, observables: list[str]):
        self._observables = observables

    def check_chains(self, step: stepScanData, chains_data_out: list[tuple[str, str]]):
        errors: list[str] = []
        for chain_data in chains_data_out:
            name, chain_data_out = chain_data
            
            # If expected data has bit with x, mask this bit in actual data from DUT
            # In order to compare expected data and data from DUT
            masked_out_data = ""
            for idx, bit in enumerate(step.chain[name].exp_data):
                if(bit == "X"):
                    masked_out_data = f"{masked_out_data}X"
                else:
                    masked_out_data = f"{masked_out_data}{chain_data_out[idx]}"

            length = len(step.chain[name].in_data)
            print(f"Interface name: {step.scan_interface_name}")
            print(f"Sim. - Step: {step.step},       DUT act. data in  ({step.chain[name].tdi_port}) ({step.type_of_chain}): {length}b'{step.chain[name].in_data}")
            print(f"Sim. - Step: {step.step},       DUT act. data out ({step.chain[name].tdo_port}) ({step.type_of_chain}): {length}b'{chain_data_out}")
            print(f"Sim. - Step: {step.step}, solver    exp. data on  ({step.chain[name].tdo_port}) ({step.type_of_chain}): {length}b'{step.chain[name].exp_data}")
            print(f"Sim. - Step: {step.step}, mask. DUT act. data on  ({step.chain[name].tdo_port}) ({step.type_of_chain}): {length}b'{masked_out_data}")

            # Check actual vs expected scan chain data
            assert(len(step.chain[name].in_data) == len(chain_data_out))
            if(masked_out_data != step.chain[name].exp_data):

                class bcolors:
                    OKGREEN = '\033[92m'
                    FAIL = '\033[91m'
                    ENDC = '\033[0m'

                for idx, _ in enumerate(step.chain[name].in_data_names):
                    tmp = f"Bit [{step.chain[name].in_data_names[idx]}/{step.chain[name].read_data_bit_names[idx]}] - act. {masked_out_data[idx]} vs exp. {step.chain[name].exp_data[idx]}"
                    if(masked_out_data[idx] ==  step.chain[name].exp_data[idx]):
                        print(f"{bcolors.OKGREEN}{tmp}{bcolors.ENDC}")
                    else:
                        print(f"{bcolors.FAIL}{tmp}{bcolors.ENDC}")
                
                errors.append(f"Mismatch [{step.chain[name].tdi_port}->{step.chain[name].tdo_port}]: Expected data ({step.chain[name].exp_data}), actual data ({masked_out_data}), step: {step.step}")        

        if errors:
            raise ValueError(errors)
    
        
    # When drive_client_interface_chain is called, it is assumed that this function can immediately drive ScanIn port,
    # without any timing vioalation
    async def drive_client_interface_chain(self, name: str, chain: chainScanData, interface: ClientInterface) -> str:
        assert(isinstance(interface, ClientInterface))

        data_out = ""
        scan_in = interface.scan_in_ports[name]
        scan_out = interface.scan_out_ports[name]

        for i in reversed(chain.in_data):
            assert(i in ["1", "0"])
            scan_in.value = 1 if i == "1" else 0
            interface.shift.value  = 1
        
            #print(type(scan_in.value), scan_in.value,  i)
            await FallingEdge(interface.tck)
            await Timer(self.tck_period_ns * 0.25, "ns")
            data_out = f"{scan_out.value}{data_out}"
            
            await RisingEdge(interface.tck)
            await Timer(self.tck_period_ns * 0.25, "ns")

        return (name, data_out)
        
    async def drive_client_interface(self, interface: ClientInterface, ijtag_step: stepScanData) -> list[tuple[str, str]]: 
        read_data: list[tuple[str, str]] = {}

        clock = Clock(interface.tck, self.tck_period_ns, "ns")
        cocotb.start_soon(clock.start())

        await  RisingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")
        
        interface.reset = ~interface.reset_polarity
        interface.update.value = 0
        interface.shift.value = 0      
        interface.capture.value = 0
        for sel in interface.selects:
            sel.value = 0
            
        # --- 1. CAPTURE PHASE (CE) ---
        
        interface.capture.value = 1
 
        for sel in interface.selects:
            sel.value = 1
            
        await RisingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")
        interface.capture.value = 0
        
        # --- 2. SHIFT PHASE (SE) ---
        # Launch all chains concurrently as cocotb tasks
        tasks = [ cocotb.start_soon( self.drive_client_interface_chain(chain_name, ijtag_step.chain[chain_name], interface))
            for chain_name in ijtag_step.chain.keys()
        ]            
        await Combine(*tasks)        
        read_data = [t.result() for t in tasks]

        interface.shift.value = 0

        # --- 3. UPDATE PHASE (UE) ---
        
        await FallingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")
       
        interface.update.value = 1

        await FallingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")       

        interface.update.value = 0

        await RisingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")       

        for sel in interface.selects:
            sel.value = 0

        await FallingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")       
        clock.stop()
        await Timer(self.tck_period_ns * 0.25, "ns")       

        return read_data

    # When drive_tap_interface_chain is called, it is assumed that posedge clock moved FSM to shift phase
    # before calling this function
    async def drive_tap_interface_chain(self, name: str, chain: chainScanData, interface: ClientTapInterface) -> str:
        assert(isinstance(interface, ClientTapInterface))

        data_out = ""
        scan_in = interface.scan_in_ports[name]
        scan_out = interface.scan_out_ports[name]

        # Get all chain bits exept the last one, bits will be driven with TMS == 0
        chain_0_tms = chain.in_data[1:]
        
        # Get last chain bit, bit will be driven with TMS == 1
        chain_1_tms = chain.in_data[0]

        if(chain_0_tms):
            await Timer(self.tck_period_ns* 0.25, "ns")

        for i in reversed(chain_0_tms):
            assert(i in ["1", "0"])
            
            scan_in.value = 1 if i == "1" else 0
            interface.tms.value = 0
            #print(type(scan_in.value), scan_in.value,  i)
            
            await FallingEdge(interface.tck)
            await RisingEdge(interface.tck)

            await Timer(self.tck_period_ns * 0.25, "ns")
            data_out = f"{scan_out.value}{data_out}"


        if(not chain_0_tms):
            await Timer(self.tck_period_ns * 0.25, "ns")       

        for i in reversed(chain_1_tms):
            assert(i in ["1", "0"])
            
            scan_in.value = 1 if i == "1" else 0
            #print(type(scan_in.value), scan_in.value,  i)
            interface.tms.value = 1

            await FallingEdge(interface.tck)
            await RisingEdge(interface.tck)

            await Timer(self.tck_period_ns * 0.25, "ns")
            data_out = f"{scan_out.value}{data_out}"

        return (name, data_out)
    
    async def drive_tap_interface(self, interface: ClientTapInterface, ijtag_step: stepScanData) -> list[tuple[str, str]]:
        read_data: list[tuple[str, str]] = {}
        is_ir = (ijtag_step.type_of_chain == "IR")

        clock = Clock(interface.tck, self.tck_period_ns, "ns")
        cocotb.start_soon(clock.start())

        # Sync in Run-Test/Idle FSM state
        await RisingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")
        interface.tms.value = 0
        await RisingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")
        
        # ---  WALING FSM TO SHIFT PHASE ---

        # Navigate from Run-Test/Idle FSM state to SHIFT-DR or SHIFT-IR state
        # On Rising edge move to SELECT-DR state
        interface.tms.value = 1
        await RisingEdge(interface.tck)   
        await Timer(self.tck_period_ns * 0.25, "ns")

        # For IR chain - On Rising edge move to SELECT-IR state
        if is_ir:
            interface.tms.value = 1
            await RisingEdge(interface.tck)
            await Timer(self.tck_period_ns * 0.25, "ns")

        # On Rising edge move to CAPTURE state
        interface.tms.value = 0
        await RisingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")

        # On Rising edge move to SHIFT state
        interface.tms.value = 0
        await RisingEdge(interface.tck)

        # ---  SHIFT PHASE ---
        # Launch all chains concurrently as cocotb tasks
        tasks = [ cocotb.start_soon( self.drive_tap_interface_chain(chain_name, ijtag_step.chain[chain_name], interface))
            for chain_name in ijtag_step.chain.keys()
        ]            
        await Combine(*tasks)        
        read_data = [t.result() for t in tasks]        

        # ---  WALING FSM TO Run-Test/Idle PHASE ---

        # On Rising edge move to UPDATE state
        interface.tms.value = 1
        await RisingEdge(interface.tck)
        await Timer(self.tck_period_ns * 0.25, "ns")

        # On Rising edge move to Run-Test/Idle state
        interface.tms.value = 0
        await RisingEdge(interface.tck)
        await FallingEdge(interface.tck)
        
        clock.stop()
        await Timer(self.tck_period_ns * 0.5, "ns")


        return read_data