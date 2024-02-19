# Shitty IJTAG ICL parser to scan graph

Tries to create scan graph from ICL file.
(work maybe in progress)

# May work with these ICL statments:
- useNameSpace_def
- instance_def
- parameter_def
- localParameter_def
- port_def :
  - scanInPort_def
  - scanOutPort_def
  - dataInPort_def
  - dataOutPort_def
- scanRegister_def
- scanMux_def

# Run
python3 main.py ICL file                     ICL module to parse
python3 main.py ./test_icls/scan_mux_001.icl "scan_mux_001"

