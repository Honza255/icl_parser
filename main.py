from src.ijtag import *

# Usage example: IJTAG model network creation + retargeting
if __name__ == '__main__':

        # Get the directory containing the current file
        current_dir = os.path.dirname(os.path.abspath(__file__)) + "/tests"

        # Inputs
        from tests.config import COMMON_ICL_BLOCKS
        icl_files = ["test_icls/benchmarks/ICL/Advanced/TrapOrFlap/TrapOrFlap.icl"] + COMMON_ICL_BLOCKS
        module_name = "TrapOrFlap"

        # IJTAG model network creation
        ijtag = Ijtag(module_name, icl_files, [current_dir])

        # Rest
        ijtag.iReset()

        # Write to scan register
        ijtag.iWrite("SREG1.SR", "3")
        ijtag.iApply()
        print(ijtag.getiApplyVectors())
        
        # Read from scan register
        ijtag.iRead("SREG1.SR", "1")
        ijtag.iApply()
        print(ijtag.getiApplyVectors()) 
        
        # Write to scan register
        ijtag.iWrite("WI_2.reg8.SR", "2")
        ijtag.iApply()
        print(ijtag.getiApplyVectors()) 

        # Write to scan register
        ijtag.iWrite("CONF1.SR", "16")
        ijtag.iApply()
        print(ijtag.getiApplyVectors()) 

        # Write to scan register
        ijtag.iWrite("CONF2.SR", "7")
        ijtag.iApply()
        print(ijtag.getiApplyVectors()) 

        ## Open a window wih simplified graph of IJTAG network
        ijtag.plot_network_graph()