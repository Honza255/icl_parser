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

# Example:
#   step: 1
#   tdi_port_name: "TDI_0"
#   tdo_port_name: "TDO_0"
#   type_of_chain: "'DR'/'IR'"
#   in_data:  "10010"
#   exp_data: "XX001"
#   self.in_data_names:  [TDR_A_1, TDR_A_0,      TDR_B_2, TDR_B_1, TDR_B_0]
#   read_data_bit_names: [None,    DATA_BIT_R_0, None,    None,    None]
class jtagStep():
    def __init__(self):
        self.step: int
        self.tdi_port: str
        self.tdo_port: str
        self.type_of_chain: str
        self.in_data: str
        self.in_data_names: list[str]
        self.exp_data: str
        self.read_data_bit_names: list[str]


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
def strip_last_number(self, input: str) -> str:
    return re.sub(r'([\w.]+)(_\d+)', r'\1', input)
