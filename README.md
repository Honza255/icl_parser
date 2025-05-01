# Poor IJTAG ICL Parser to Scan Graph

This tool attempts to create a scan graph from an ICL file. 
(Note: Work may still be in progress)

## Supported ICL Statements
- useNameSpace_def
- instance_def
- parameter_def
- localParameter_def
- port_def:
  - scanInPort_def
  - scanOutPort_def
  - dataInPort_def
  - dataOutPort_def
- scanRegister_def
- scanMux_def

## How to Run
- python3 main.py ICL file ICL module to parse
- python3 main.py ./test_icls/scan_mux_001.icl "scan_mux_001"


## Useful Paper Links
- [IJTAG Standard (IEEE 1687-2014)](https://ieeexplore.ieee.org/document/6974961)
- [Reconfigurable Scan Networks: Formal Verification, Access Optimization, and Protection](http://dx.doi.org/10.18419/opus-3246)
- [Analysis and Design of an On-Chip Retargeting Engine for IEEE 1687 Networks](https://ieeexplore.ieee.org/document/7519301)
- [Structured Scan Patterns Retargeting for Dynamic Instruments Access](https://ieeexplore.ieee.org/document/7928955)
- [Analysis and Design of a Dependability Manager for Self-Aware System-on-Chips](https://essay.utwente.nl/76229/1/Geerlings_MA_CAES-TDT.pdf)
- [A Suite of IEEE 1687 Benchmark Networks](https://ieeexplore.ieee.org/document/7805840)

## Repositories associated with IJTAG
- [Library of Reconfigurable Scan Network Designs shared by the IJTAG community](https://gitlab.com/IJTAG/)
- [Origen Interface/Driver for the IEEE 1687 (IJTAG) Standard](https://github.com/Origen-SDK/ijtag)
- [P2654 Simulations](https://github.com/bradfordvt/P2654Simulations)
- [Structured Retargeting](https://github.com/abraralaa92/structured_retargeting)
- [Adaptive Retargeting](https://github.com/abraralaa92/adaptive_retargeting)
- [Structural SAT Retargeting](https://github.com/abraralaa92/Structural_SAT_Retargeting)
- [mast-opensource](https://gricad-gitlab.univ-grenoble-alpes.fr/portolam/mast-opensource)
