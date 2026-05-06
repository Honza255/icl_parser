import re

CONCAT_RESET_T = "reset"
CONCAT_SCAN_T = "scan"
CONCAT_DATA_T = "data"
CONCAT_CLOCK_T = "clock"
CONCAT_TCK_T = "tck"
CONCAT_SE_T = "shiften"
CONCAT_CE_T = "to_capture_en"
CONCAT_UE_T = "updateen"
CONCAT_TMS_T = "tms"
CONCAT_TRST_T = "trst"

CONCAT_ALIAS_T = "alias"
CONCAT_NUMBER_T = "number"
CONCAT_UNKNOWN_T = "unknown"

# Interface Types
CLIENT_TAP = "client_tap"
HOST_TAP = "host_tap"
CLIENT_SCAN_INTERFACE = "client_scan_interface"
HOST_SCAN_INTERFACE = "host_scan_interface"
        
# Example:
# full_name: u_rosc_cut_lvt.CTRL
# write_en: u_regs_rosc_cut_lvt.ctrl_0001
# write_en_sel: sel_u_regs_rosc_cut_lvt.ctrl_0000
# sel_en: (and (not u_rosc_cut_lvt.addr_0000))
# data_reg: u_rosc_cut_lvt.CTRL_0000, u_rosc_cut_lvt.CTRL_0001
# data_in_reg: (u_regs_rosc_cut_lvt.u_tdr_data.tdr_0000, u_rosc_cut_lvt.CTRL_0000), (u_regs_rosc_cut_lvt.u_tdr_data.tdr_0000, u_rosc_cut_lvt.CTRL_0001)
# read_path_ready: Determines if register can read out by checking read out TDR is selected and also by checking that path from data register to TDR is enabled
#                  [(data_reg, (sel_sink_tdr_reg, read_path_expression))]
class smtDataReg():
    def __init__(self):
        self.full_name: str = ""
        self.write_en: str = ""
        self.write_en_sel: str = ""
        self.read_en: str = ""
        self.read_en_sel: str = ""
        self.sel_en: str = ""
        self.data_reg: list[str] = []
        self.data_in_reg: list[tuple[str:str]] = []
        self.read_path_ready: list[tuple[str, list[tuple[str:str]]]] = []
        
        # [(data_reg_bit, (sel_sink_tdr_reg, read_path_expression))]
        # self.read_path_ready_2: list[tuple[str:str:str]] = []


class smtScanReg():
    def __init__(self):
        self.full_name: str = ""
        self.write_en: str = ""
        self.read_en: str = ""
        self.sel_en: str = ""
        self.scan_reg: list[str] = []

class smtOneHotGroup():
    def __init__(self):
        self.one_hot_bits: list[str]


class chainScanData():

    def __init__(self):
        self.tdi_port: str
        self.tdo_port: str
        self.in_data: str
        self.in_data_names: list[str]
        self.exp_data: str
        self.read_data_bit_names: list[str]

# Example:
#   step: 1
#   type_of_chain: "'DR'/'IR'"
#   scan_chain: {"default_chain":
#       tdi_port_name:       "TDI_0"
#       tdo_port_name:       "TDO_0"
#       in_data:             "10010"
#       exp_data:            "XX001"
#       in_data_names:       ["TDR_A_1", "TDR_A_0",      "TDR_B_2", "TDR_B_1", "TDR_B_0"]
#       read_data_bit_names: ["None",    "DATA_BIT_R_0", "None",    "None",    "None"]
#   }
#   paraell_in:          [("P_DATA_0", "1"), ("P_DATA_1", "0")]
#   paraell_exp:         [("P_DATA_0", "X"), ("P_DATA_1", "1")]
#   scan_interface_name: "default_scan_interface"
class stepScanData():

    def __init__(self):
        self.step: int
        self.type_of_chain: str

        # Scan data about pairs of scan in and scan out ports
        self.chain: dict[str, chainScanData] = {}
        
        # Paraell in/out data, not associated with scan interface
        self.paraell_in:  list[tuple[str, str]]    # Parallel data for data input ports
        self.paraell_exp: list[tuple[str, str]]    # Parallel expected data for data on output ports
        
        # Information for JTAG/IJTAG Driver
        self.scan_interface_name: str = ""      # Scan interface name which is being driven 

# Converts sympy string expression into SMT2 string expression
# Example: And(A, B) -> (and A B)
def sympy_to_smt2(expr: str) -> str:
    assert(isinstance(expr, str))                                                                                                                                                                                                                                                                                 
    expr = expr.strip()                                                                                                                                                                                                                                                                                                     
    op_map = {"And": "and", "Or": "or", "Not": "not", "Xor": "xor"}                                                                                                                                                                                                                                                         
    for sympy_op, smt2_op in op_map.items():                                                                                                                                                                                                                                                                                
        if expr.startswith(sympy_op + "(") and expr.endswith(")"):
            inner = expr[len(sympy_op) + 1:-1]                                                                                                                                                                                                                                                                              

            args, depth, start = [], 0, 0                                                                                                                                                                                                                                                                                           
            for i, c in enumerate(inner):
                if c == "(":   depth += 1
                elif c == ")": depth -= 1                                                                                                                                                                                                                                                                                           
                elif c == "," and depth == 0:
                    args.append(inner[start:i].strip())                                                                                                                                                                                                                                                                                 
                    start = i + 1
            args.append(inner[start:].strip())
            
            converted = " ".join(sympy_to_smt2(a) for a in args)                                                                                                                                                                                                                                                      
            return f"({smt2_op} {converted})"                                                                                                                                                                                                                                                                               
    if expr in ("true", "True"):
        return "true"                                                                                                                                                                                                                                                                                                       
    if expr in ("false", "False"):
        return "false"
    return expr

# Extracts last number from string
# Last number must have this prefix "_"
# Example:
#   str(ABC_0004) -> int(4)
def get_last_number(input: str) -> int:
    return int(re.sub(r'([\w.]+)_(\d+)', r'\2', input))

# Strips last number from string
# Last number must have this prefix "_"
# Example:
#   str(ABC_0004) -> str(ABC)
def strip_last_number(input: str) -> str:
    return re.sub(r'([\w.]+)(_\d+)', r'\1', input)

# Add number to an end of a string
# Example:
#   str(ABC), int(4) -> str(ABC_0004)
def add_last_number(input: str, index: int):
    return "{}_{:04}".format(input, index)
