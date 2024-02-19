#main.py

from typing import Any
from antlr4 import *
import sys


from icl_pre_process import *
from icl_process import *

#yourGrammarNameParser.py
from parser.iclLexer import iclLexer
from parser.iclParser import iclParser


def main(argv):
    import sys
    import json

    if len(sys.argv) > 2:
        print("ICL File:", argv[1])
        print("ICL Module parse:", argv[2])
        input = FileStream(argv[1], encoding='utf-8')
        module_name = argv[2]
    else:
        sys.exit('Error: Expected a valid file and ICL module name to parse')

    lexer = iclLexer(input)
    stream = CommonTokenStream(lexer)
    parser = iclParser(stream)
    tree = parser.icl_source()
    print(tree.toStringTree(recog=parser))

    my_listener = IclPreProcess()
    walker = ParseTreeWalker()
    walker.walk(my_listener, tree)

    init_data = my_listener.modules

    print(json.dumps(init_data, sort_keys=True, indent=4))

    instance_name = "top" 
    scope_name = "root"
    #module_name = "x"
    #module_name = "scan_mux_001"

    module_to_parse = init_data[scope_name][module_name]["data"]

    lexer = iclLexer(InputStream(module_to_parse))
    stream = CommonTokenStream(lexer)
    parser = iclParser(stream)
    tree = parser.module_def()
    print(tree.toStringTree(recog=parser))

    my_listener = IclProcess(instance_name, module_name, scope_name)
    
    my_listener.all_module_data = init_data
    my_listener.current_init_data = init_data[scope_name][module_name]
    walker = ParseTreeWalker()
    walker.walk(my_listener, tree)

    icl_instance = my_listener.new_inst
    print(icl_instance)
    icl_instance.check()
    icl_instance.create_tree_diagram()


if __name__ == '__main__':
    print(sys.argv)
    main(sys.argv)
