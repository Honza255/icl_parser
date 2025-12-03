from graphviz import Digraph

# Initialize a directed graph
dot = Digraph(comment='Block Diagram of IC')

# Define nodes for Ports
ports = ["SI", "CE", "SE", "UE", "SEL", "RST", "TCK", "SO"]
for port in ports:
    dot.node(port, port, shape='ellipse', style='filled', fillcolor='lightgrey')

# Define nodes for Instances with their ports
instances = {
    "SIB_main": {"inputs": ["SI", "SIB10.SO", "sel_SIB_MAIN"], "outputs": ["SO"]},
    "SCB1": {"inputs": ["sMuxSO", "SEL"], "outputs": ["SO", "DO"]},
    "WI_0": {"inputs": ["sMux0", "sel_WI0"], "outputs": ["SO"]},
    "WI_1": {"inputs": ["sMux1", "sel_WI1"], "outputs": ["SO"]},
    "WI_2": {"inputs": ["sMux2", "sel_WI2"], "outputs": ["SO"]},
    "WI_3": {"inputs": ["sMux3", "sel_WI3"], "outputs": ["SO"]},
    "WI_4": {"inputs": ["sMux4", "sel_WI4"], "outputs": ["SO"]},
    "WI_5": {"inputs": ["sMux5", "sel_WI5"], "outputs": ["SO"]},
    "WI_6": {"inputs": ["sMux6", "sel_WI6"], "outputs": ["SO"]},
    "WI_7": {"inputs": ["sMux7", "sel_WI7"], "outputs": ["SO"]},
    "WI_8": {"inputs": ["sMux8", "sel_WI8"], "outputs": ["SO"]},
    "WI_9": {"inputs": ["sMux9", "sel_WI9"], "outputs": ["SO"]},
    "WI_10": {"inputs": ["sMux10", "sel_WI10"], "outputs": ["SO"]},
    "SIB0": {"inputs": ["SIB_main.toSI", "WI_0.SO"], "outputs": []},
    "SIB1": {"inputs": ["SIB0.SO", "WI_1.SO"], "outputs": []},
    "SIB2": {"inputs": ["SIB1.SO", "WI_2.SO"], "outputs": []},
    "SIB3": {"inputs": ["SIB2.SO", "WI_3.SO"], "outputs": []},
    "SIB4": {"inputs": ["SIB3.SO", "WI_4.SO"], "outputs": []},
    "SIB5": {"inputs": ["SIB4.SO", "WI_5.SO"], "outputs": []},
    "SIB6": {"inputs": ["SIB5.SO", "WI_6.SO"], "outputs": []},
    "SIB7": {"inputs": ["SIB6.SO", "WI_7.SO"], "outputs": []},
    "SIB8": {"inputs": ["SIB7.SO", "WI_8.SO"], "outputs": []},
    "SIB9": {"inputs": ["SIB8.SO", "WI_9.SO"], "outputs": []},
    "SIB10": {"inputs": ["SIB9.SO", "WI_10.SO"], "outputs": []},
}

# Add instance nodes to the graph
for instance, ports in instances.items():
    label = f'{instance}\n{" ".join(ports["inputs"])}\n{" ".join(ports["outputs"])}'
    dot.node(instance, label, shape='box', style='filled', fillcolor='lightblue')

# Define edges based on the provided code
edges = [
    ("SI", "SIB_main"), 
    ("SIB10.SO", "SIB_main"),
    ("sel_SIB_MAIN", "SIB_main"),
    ("SIB_main.SO", "SCB1"),
    ("SEL", "SCB1"),
    ("SCB1.SO", "SO"),
    ("SCB1.DO", "sMuxSO"),
    ("SCB1.DO", "sMux0"),
    ("SCB1.DO", "sMux1"),
    ("SCB1.DO", "sMux2"),
    ("SCB1.DO", "sMux3"),
    ("SCB1.DO", "sMux4"),
    ("SCB1.DO", "sMux5"),
    ("SCB1.DO", "sMux6"),
    ("SCB1.DO", "sMux7"),
    ("SCB1.DO", "sMux8"),
    ("SCB1.DO", "sMux9"),
    ("SCB1.DO", "sMux10"),
    ("sMuxSO", "SCB1"),
    ("sMux0", "WI_0"),
    ("sel_WI0", "WI_0"),
    ("WI_0.SO", "sMux1"),
    ("sMux1", "WI_1"),
    ("sel_WI1", "WI_1"),
    ("WI_1.SO", "sMux2"),
    ("sMux2", "WI_2"),
    ("sel_WI2", "WI_2"),
    ("WI_2.SO", "sMux3"),
    ("sMux3", "WI_3"),
    ("sel_WI3", "WI_3"),
    ("WI_3.SO", "sMux4"),
    ("sMux4", "WI_4"),
    ("sel_WI4", "WI_4"),
    ("WI_4.SO", "sMux5"),
    ("sMux5", "WI_5"),
    ("sel_WI5", "WI_5"),
    ("WI_5.SO", "sMux6"),
    ("sMux6", "WI_6"),
    ("sel_WI6", "WI_6"),
    ("WI_6.SO", "sMux7"),
    ("sMux7", "WI_7"),
    ("sel_WI7", "WI_7"),
    ("WI_7.SO", "sMux8"),
    ("sMux8", "WI_8"),
    ("sel_WI8", "WI_8"),
    ("WI_8.SO", "sMux9"),
    ("sMux9", "WI_9"),
    ("sel_WI9", "WI_9"),
    ("WI_9.SO", "sMux10"),
    ("sMux10", "WI_10"),
    ("sel_WI10", "WI_10"),
    ("WI_10.SO", "SIB10"),
    ("SIB9.SO", "SIB10"),
    ("SIB10.SO", "SIB_main"),
    ("SIB0.SO", "SIB1"),
    ("SIB1.SO", "SIB2"),
    ("SIB2.SO", "SIB3"),
    ("SIB3.SO", "SIB4"),
    ("SIB4.SO", "SIB5"),
    ("SIB5.SO", "SIB6"),
    ("SIB6.SO", "SIB7"),
    ("SIB7.SO", "SIB8"),
    ("SIB8.SO", "SIB9")
]

# Add edges to the graph
for edge in edges:
    dot.edge(*edge)

# Render the graph to a file and display it
dot.render('block_diagram', format='png', view=True)
