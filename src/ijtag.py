import os
import threading

from .icl_parser.iclLexer import iclLexer
from .icl_parser.iclParser import iclParser

from .icl_common import *
from .icl_pre_process import *
from .icl_process import *
from .icl_register_model import *

class Ijtag:

    top_module = "top" 
    top_module_scope = "root"
    icl_instance: IclInstance = None
    icl_retargeter:IclRetargeting = None
    ijtag_reg_model: IclRegisterModel = None

    # Crete IJAG model from ICL files
    # top_name :      Top ICL module name
    # icl_files:      ICL files
    # iclude_folders: Where to look for ICL files without absolute path
    def __init__(self, top_module_name: str,  icl_files: list[str], iclude_folders: list[str] = []):

        assert(type(icl_files) == list)
        assert(type(iclude_folders) == list)

        # Check if ICL files exist
        # If file is relative, check inside include folder
        abb_path_icl_files: list[str] = []
        for path in icl_files:
            candidate_paths = []

            if os.path.isabs(path):
                candidate_paths.append(path)
            else:
                # Try each search folder for relative paths
                for folder in iclude_folders:
                    candidate_paths.append(os.path.join(folder, path))

            # Try to find the first existing file
            found_path = next((os.path.abspath(p) for p in candidate_paths if os.path.exists(p)), None)

            if found_path:
                abb_path_icl_files.append(found_path)
            else:
                raise ValueError(f"File not found in any search folder: {path}")


        all_icl_modules = self.__pre_process_icl_files(abb_path_icl_files)
        self.icl_instance = self.__process_icl_module(all_icl_modules, top_module_name)
        self.ijtag_reg_model = IclRegisterModel(self.icl_instance)
        self.icl_retargeter = self.ijtag_reg_model.retargeter
 
    def iWrite(self, reg_or_port: str, value: str):
        pattern = r'^([A-Za-z]{1}[.A-Za-z0-9_]*)(?:[\[(](\d+)(?::(\d+))?[\])])*'
        match =  re.search(pattern, reg_or_port)
        if (not match):
            raise ValueError(f"Bad name: {reg_or_port} passed tp iWrite ")

        only_name = match.group(1)        
        left_idx = match.group(2)
        right_idx = match.group(3)

        print(only_name, left_idx, right_idx)
        if(left_idx or right_idx):
            raise NotImplementedError(f"Indexing iWrite value ({value}) is not implemented")

        icl_item = self.icl_instance.get_icl_item_name(only_name)  
        if(not (type(icl_item) in [IclDataRegister, IclScanRegister])):
            raise NotImplementedError(f"iWrite is not supported for {reg_or_port} of type {type(icl_item)} in current script")

        if(value):
            if(value[:2] == "0x"):
                raise NotImplementedError(f"iWrite with hex value ({value}) is not implemented")
            elif(value[:2] == "0b"):
                raise NotImplementedError(f"iWrite with binary value ({value}) is not implemented")
            elif(all(char in "0123456789" for char in value)):
                self.ijtag_reg_model.iWrite(only_name, int(value))
            else:
                raise NotImplementedError(f"{value} is probably an enum, enum is not currently supported")
        else:
            raise NotImplementedError(f"iWrite without value is not implemented")
        

    def iRead(self, reg_or_port: str, value: str = ""):
        pattern = r'^([A-Za-z]{1}[.A-Za-z0-9_]*)(?:[\[(](\d+)(?::(\d+))?[\])])*'
        match =  re.search(pattern, reg_or_port)
        if (not match):
            raise ValueError(f"Bad name: {reg_or_port} passed tp iWrite ")

        only_name = match.group(1)        
        left_idx = match.group(2)
        right_idx = match.group(3)

        if(left_idx or right_idx):
            raise NotImplementedError(f"Indexing iRead value ({value}) is not implemented")

        icl_item = self.icl_instance.get_icl_item_name(only_name)  
        if(not (type(icl_item) in [IclDataRegister, IclScanRegister])):
            raise NotImplementedError(f"iRead is not supported for {reg_or_port} of type {type(icl_item)} in current script")
        
        if(value):
            if(value[:2] == "0x"):
                raise NotImplementedError(f"iRead with hex value ({value}) is not implemented")
            elif(value[:2] == "0b"):
                raise NotImplementedError(f"iRead with binary value ({value}) is not implemented")
            elif(all(char in "0123456789" for char in value)):
                self.ijtag_reg_model.iRead(only_name, int(value))
            else:
                raise NotImplementedError(f"{value} is probably an enum, enum is not currently supported")
        else:
            raise NotImplementedError(f"iRead without value is not implemented")      

    def iApply(self):
        self.ijtag_reg_model.iApply()

    def iReset(self, sync: bool = 0):
        if(sync):
            raise NotImplementedError(f"sync option in iReset is not currently supported")
        self.ijtag_reg_model.iReset()

    # Get vectors that iApply calculated
    def getiApplyVectors(self) -> list[jtagStep]:
        return self.ijtag_reg_model.getiApplyVectors()

    # Draws IJTAG scan network into a svg image
    def draw_scan_graph_pydot(self, filename=""):

        if (not filename):
            if (self.top_module):
                filename = self.top_module
            else:
                filename = self.top_module_scope + "_" + self.top_module
        
        # Initialize pydot digraph
        import pydot       
        dot = pydot.Dot(graph_type='digraph', label=filename, labelloc="t")

        # Convert ICL graph nodes into pydot
        icl_graph = self.ijtag_reg_model.create_scan_graph(squish_registers=True)
        for node, data in icl_graph.nodes(data=True):
            node_label = str(node)
            
            # Get attributes from node
            fill_color = data.get("color", "lightgray")
            shape = data.get("node_shape", "rect")

            # Quotes inside label ensure text displays correctly
            p_node = pydot.Node(
                f'"{str(node)}"', 
                shape=shape, 
                style="filled", 
                fillcolor=fill_color,
                label=f'"{node_label}"', 
                fontname="Arial",
                fontsize="10"
            )
            
            dot.add_node(p_node)

        # Convert ICL graph edges into pydot
        for u, v, data in icl_graph.edges(data=True):
            # Quotes inside label ensure text displays correctly       
            p_edge = pydot.Edge(
                f'"{str(u)}"', 
                f'"{str(v)}"',
            )
            dot.add_edge(p_edge)

        # Add legend
        # Create a separate subgraph cluster just for the legend
        legend_cluster = pydot.Subgraph(graph_name="cluster_key")
        legend_cluster.set_label("Legend:")

        # Define the legend items: (InternalName, DisplayLabel, Shape, Color)
        legend_items = [
            ("leg_port", "Scan Port", "oval", "lightgreen"),
            ("leg_reg",  "Register",    "rect", "red"), 
            ("leg_mux",  "Multiplexer", "invtrapezium", "grey")
        ]

        previous_node_id = None

        for leg_id, leg_label, leg_shape, leg_color in legend_items:
            # Create the visual node
            leg_node = pydot.Node(
                leg_id,
                label=leg_label,
                shape=leg_shape,
                style="filled",
                fillcolor=leg_color
            )
            legend_cluster.add_node(leg_node)

            # Stack them vertically using invisible edges
            if previous_node_id:
                edge_invis = pydot.Edge(previous_node_id, leg_id, style="invis")
                legend_cluster.add_edge(edge_invis)
            
            previous_node_id = leg_id

        dot.add_subgraph(legend_cluster)

        print(f"Generating IJTAG scan network into a svg image: {filename}")
        dot.write_svg(filename + ".svg")

    # Displays IJTAG network graphis into a window
    def display_scan_graph_mathplot(self):
        import matplotlib.pyplot as plt        

        icl_graph = self.ijtag_reg_model.create_scan_graph(squish_registers=True)      
        pos = nx.kamada_kawai_layout(icl_graph)

        # Exctract color attribute for each node
        node_colors = [data['color'] if "color" in data else "gray" for node, data in icl_graph.nodes(data=True)]

        nx.draw(icl_graph, pos, with_labels=True, node_size=1500, node_color=node_colors, font_size=10, font_weight="bold")
        plt.show()


    # Inner functions
    def __pre_process_icl_files(self, icl_files: list[str]) -> dict[str, dict]:

        def __pre_process_file(icl_file, results, index):
            print(f"Pre processing file: {icl_file}")

            pre = IclPreProcess()
            pre.modules = {"root": {}}
            stream = CommonTokenStream(iclLexer(FileStream(icl_file, encoding='utf-8')))
            parser_tree = iclParser(stream).icl_source()
            walker = ParseTreeWalker()
            walker.walk(pre, parser_tree)
            results[index] = pre.modules

        results = [None] * len(icl_files)
        threads = [threading.Thread(target=__pre_process_file, args=(f, results, i)) for i, f in enumerate(icl_files)]

        for t in threads: t.start()
        for t in threads: t.join()

        # Merge in order
        all_icl_modules = {"root": {}}
        for r in results:
            for k, v in r.items():
                all_icl_modules.setdefault(k, {}).update(v if isinstance(v, dict) else {})

        for x,b  in all_icl_modules.items():
            print(x, b.keys())
            
        return all_icl_modules 

    def __process_icl_module(self, all_icl_modules: dict[str, dict], module_name: str) -> IclInstance:
        pattern = re.compile(r'(?:([\w]+)::)?([\w]+)')
        m = pattern.match(module_name)
        if m:
            self.top_module_scope = m.group(1) if m.group(1) is not None else "root"
            module_name = m.group(2)
            #print(module_name, self.top_module_scope)
        self.top_module = module_name

        print(f"Starting to process: {self.top_module_scope}::{self.top_module}")
        
        icl_process = IclProcess(self.top_module, self.top_module, self.top_module_scope)           
        icl_process.all_icl_modules = all_icl_modules
        icl_process.start_icl_module = all_icl_modules[self.top_module_scope][module_name]

        parser_tree = all_icl_modules[self.top_module_scope][module_name]["module_parser_tree"]
        walker = ParseTreeWalker()
        walker.walk(icl_process, parser_tree)

        icl_process.icl_instance.check()       

        return icl_process.icl_instance
