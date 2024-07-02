from typing import Any
from antlr4 import *
import antlr4

from parser.iclLexer import iclLexer
from parser.iclListener import iclListener
from parser.iclParser import iclParser

from icl_items import *


class IclProcess(iclListener):
    def __init__(self, instance_name, module_name, scope_name="root", hier=""):
        self.all_icl_modules = {}
        self.start_icl_module = {}
        self.icl_instance = IclInstance(instance_name, hier, module_name, None)
        # Tree helper
        self.record  = {}
        self.result = {}

        # Data
        self.parameters = {}

    def print_tree(self, node, indent=""):
        # Check if the node is a terminal node (i.e., has no children)
        if not isinstance(node, antlr4.tree.Tree.TerminalNode):
            print(f"{indent}{type(node).__name__} -> {node.getText()}")

            # Indent for children
            child_indent = indent + "    "
            for i in range(node.getChildCount()):
                child = node.getChild(i)
                self.print_tree(child, child_indent)


    # alias_def : 'Alias' alias_name '=' concat_hier_data_signal (';' | ('{' alias_item+ '}' ) ) ;
    # alias_name : reg_port_signal_id;
    # alias_item : attribute_def |
    #             'AccessTogether' ';' |
    #             alias_iApplyEndState |
    #             alias_refEnum ;
    # alias_iApplyEndState : 'iApplyEndState' concat_number ';' ;    
    # alias_refEnum : 'RefEnum' enum_name ';' ;
    def exitAlias_def(self, ctx:iclParser.Alias_defContext):
        alias_name: IclSignal = self.result[ctx.alias_name().reg_port_signal_id()]
        concat_sig: ConcatSig = self.result[ctx.concat_hier_data_signal()]
        items = {
            "att": [],
            "ace": 0,
            "end": None,
            "ref": None ,
        }
        
        for item in ctx.alias_item():
            if (item.attribute_def()):
                items["att"].append(self.result[item.attribute_def()])

            elif (item.getChild(0).getText() == 'AccessTogether'):
               items["ace"] = 1

            elif (item.alias_iApplyEndState()):
                new_end_state = self.result[item.alias_iApplyEndState().concat_number()] 
                if(items["end"] != None):
                    raise ValueError("Alias {} already has one end state {} and can not have an another {}".format(alias_name, items["end"], new_end_state))                
                items["end"] = new_end_state

            elif (item.alias_refEnum()):
                new_ref_enum = self.result[item.alias_refEnum().enum_name()]
                if(items["ref"] != None):
                    raise ValueError("Alias {} already has one end enum reference {} and can not have an another  {}".format(alias_name, items["ref"], new_ref_enum))
                items["ref"] = new_ref_enum

        alias = IclAlias(self.icl_instance, alias_name, concat_sig, items, ctx.getText())
        self.icl_instance.add_icl_item(alias)
        
        self.result[ctx] = (alias_name, concat_sig, items)
        print("exitAlias_def-X", ctx.getText(), "->", self.result[ctx])

    # concat_hier_data_signal : '~'? hier_data_signal (',' '~'? hier_data_signal)* ;    
    def exitConcat_hier_data_signal(self, ctx:iclParser.Concat_hier_data_signalContext):
        data = []
        operator = ""
        for index in range(ctx.getChildCount()):
            if(ctx.getChild(index).getText() == "~"):
                operator = "~"
            elif(ctx.getChild(index).getText() == ","):
                operator = ""
            else:
                item = self.result[ctx.getChild(index)]
                if type(item) == IclSignal:
                    if(operator == "~"):
                        item = ~item
                    operator = ""
                    data.append(item)
                else:
                    raise ValueError("Unknown type{}".format(type(item)))                    
        self.result[ctx] = ConcatSig(self.icl_instance, data, "alias")

    # hier_data_signal : (instance_name '.')* reg_port_signal_id ;    
    def exitHier_data_signal(self, ctx:iclParser.Hier_data_signalContext):
        item: IclSignal = self.result[ctx.reg_port_signal_id()]
        for index in range(ctx.getChildCount()):
            if (ctx.instance_name(index)):
                item.add_hiearachy(ctx.instance_name(index).getText())
        self.result[ctx] = item


    # enum_def : 'Enum' enum_name '{' enum_item+ '}' ;
    def exitEnum_def(self, ctx:iclParser.Enum_defContext):
        enum_name = self.result[ctx.enum_name()]
        enum_items = []
        for index in range(ctx.getChildCount()):
            if (ctx.enum_item(index)):
                enum_items.append(self.result[ctx.enum_item(index)])
        icl_enum = IclEnum(self.icl_instance, enum_name, enum_items, ctx.getText())
        self.icl_instance.add_icl_item(icl_enum)

        self.result[ctx] = (enum_name, enum_items)
        print("exitEnum_def-X", ctx.getText(), "->", self.result[ctx])

    # enum_name : SCALAR_ID ;
    def exitEnum_name(self, ctx:iclParser.Enum_nameContext):
        self.result[ctx] = ctx.getChild(0).getText()

    # enum_item : enum_symbol '=' enum_value ';' ;
    def exitEnum_item(self, ctx:iclParser.Enum_itemContext):
        name = self.result[ctx.enum_symbol()]
        value = self.result[ctx.enum_value()]
        self.result[ctx] = (name,value)
        
    # enum_symbol : SCALAR_ID;
    def exitEnum_symbol(self, ctx:iclParser.Enum_symbolContext):
        self.result[ctx] = ctx.SCALAR_ID().getText()

    # enum_value : concat_number;   
    def exitEnum_value(self, ctx:iclParser.Enum_valueContext):
        self.result[ctx] = self.result[ctx.concat_number()]



    # logicSignal_def : 'LogicSignal' logicSignal_name '{' logic_expr ';' '}' ;
    def exitLogicSignal_def(self, ctx:iclParser.LogicSignal_defContext):
        logicSignal_name: IclSignal = self.result[ctx.logicSignal_name()] 
        logic_expr: list[list:str] = self.result[ctx.logic_expr()]
        
        icl_logic_signal = IclLogicSignal(self.icl_instance, logicSignal_name, logic_expr, ctx.getText())
        self.icl_instance.add_icl_item(icl_logic_signal)

        ## Start printing from the current node
        #self.print_tree(ctx, "")

        self.result[ctx] =  (logicSignal_name, logic_expr)       
        print("exitLogicSignal_def-X", ctx.getText(), "->", self.result[ctx])   

    # logicSignal_name : reg_port_signal_id;
    def exitLogicSignal_name(self, ctx:iclParser.LogicSignal_nameContext):
        self.result[ctx] = self.result[ctx.reg_port_signal_id()]

    # logic_expr : logic_expr_lvl1 ;
    def exitLogic_expr(self, ctx:iclParser.Logic_exprContext):
        tmp =  self.result[ctx.logic_expr_lvl1()]
        # In case, where no operation is performed, inticate it by 'nop'
        if not isinstance(tmp, list):
            self.result[ctx] =  [ "nop", self.result[ctx.logic_expr_lvl1()]]
        else:
            self.result[ctx] =  self.result[ctx.logic_expr_lvl1()]

    # logic_expr_lvl1 : logic_expr_lvl2 ( ('&&' | '||') logic_expr_lvl1 )? ;
    def exitLogic_expr_lvl1(self, ctx:iclParser.Logic_expr_lvl1Context):
        if(ctx.logic_expr_lvl1()):
            operator = ctx.getChild(1).getText()
            self.result[ctx] = [operator, self.result[ctx.logic_expr_lvl2()],  self.result[ctx.logic_expr_lvl1()]]
        else:
            self.result[ctx] = self.result[ctx.logic_expr_lvl2()]
        # print("exitLogic_expr_lvl1-X", ctx.getText(), "->", self.result[ctx])   
        
    # logic_expr_lvl2 : logic_expr_lvl3 ( ('&' | '|' | '^') logic_expr_lvl2 )? |
    #                                   ( ('&' | '|' | '^') logic_expr_lvl2 );    
    def exitLogic_expr_lvl2(self, ctx:iclParser.Logic_expr_lvl2Context):
        if(ctx.logic_expr_lvl3()):
            if(ctx.logic_expr_lvl2()):
                operator = ctx.getChild(1).getText()
                self.result[ctx] = [operator, self.result[ctx.logic_expr_lvl3()],  self.result[ctx.logic_expr_lvl2()]]
            else:
                self.result[ctx] = self.result[ctx.logic_expr_lvl3()]
        else:
            operator = ctx.getChild(0).getText()
            self.result[ctx] = [operator, self.result[ctx.logic_expr_lvl2()]]
        # print("exitLogic_expr_lvl2-X", ctx.getText(), "->", self.result[ctx])        

    # logic_expr_lvl3 : logic_expr_lvl4 ( ('==' | '!=') logic_expr_num_arg )?;
    def exitLogic_expr_lvl3(self, ctx:iclParser.Logic_expr_lvl3Context):
        if(ctx.logic_expr_num_arg()):
            operator = ctx.getChild(1).getText()           
            self.result[ctx] = [operator, self.result[ctx.logic_expr_lvl4()],  self.result[ctx.logic_expr_num_arg()]]
        else:
            self.result[ctx] = self.result[ctx.logic_expr_lvl4()]
        # print("exitLogic_expr_lvl3-X", ctx.getText(), "->", self.result[ctx])

    # logic_expr_lvl4 : logic_expr_arg (',' logic_expr_lvl4 )?;
    def exitLogic_expr_lvl4(self, ctx:iclParser.Logic_expr_lvl4Context):
        if(ctx.logic_expr_lvl4()):
            operator = ctx.getChild(1).getText()                      
            self.result[ctx] = [operator, self.result[ctx.logic_expr_arg()],  self.result[ctx.logic_expr_lvl4()]]
        else:
            self.result[ctx] = self.result[ctx.logic_expr_arg()]

    # logic_unary_expr : ('~'|'!') logic_expr_arg;              
    def exitLogic_unary_expr(self, ctx:iclParser.Logic_unary_exprContext):
        operator = ctx.getChild(0).getText()
        self.result[ctx] = [operator, self.result[ctx.logic_expr_arg()]]
    
    # '(' logic_expr ')';
    def exitLogic_expr_paren(self, ctx:iclParser.Logic_expr_parenContext):
        self.result[ctx] = ["()", self.result[ctx.logic_expr()]]

    # logic_expr_arg : logic_expr_paren | logic_unary_expr | concat_data_signal ;
    def exitLogic_expr_arg(self, ctx:iclParser.Logic_expr_argContext):
        self.result[ctx] = self.result[ctx.getChild(0)]

    # logic_expr_num_arg : concat_number |  enum_name | '(' logic_expr_num_arg ')' ;            
    def exitLogic_expr_num_arg(self, ctx:iclParser.Logic_expr_num_argContext):
        if(ctx.concat_number()):
                self.result[ctx] = ConcatSig(self.icl_instance, [self.result[ctx.concat_number()]], IclNumber)
        if(ctx.enum_name()):
                ##self.result[ctx] = self.result[ctx.enum_name()]
                self.result[ctx] = EnumRef(self.icl_instance, self.result[ctx.enum_name()])
        if(ctx.logic_expr_num_arg()):
                self.result[ctx] = self.result[ctx.logic_expr_num_arg()]



    def parse_port_name(self, ctx:iclParser.Port_nameContext, declaration: bool):
        sig = None
        if(ctx.SCALAR_ID()):
            name = ctx.SCALAR_ID().getText()
            sig = IclSignal(name, 0) if declaration else IclSignal(name)
        elif(ctx.vector_id()):
            name = ctx.vector_id().SCALAR_ID().getText()           
            if(ctx.vector_id().index()):
                number =  self.result[ctx.vector_id().index().integer_expr()].get_number()
                sig = IclSignal(name, number)
            else:
                index_l = self.result[ctx.vector_id().rangex().index(0).integer_expr()].get_number()
                index_h = self.result[ctx.vector_id().rangex().index(1).integer_expr()].get_number()
                sig = IclSignal(name, index_l, index_h)

        self.result[ctx] = sig
        print(ctx.getText(), "->", self.result[ctx])
    
    def exitPort_name(self, ctx:iclParser.Port_nameContext):                    self.parse_port_name(ctx, 0)
    def exitRegister_name(self, ctx: iclParser.Register_nameContext):           self.parse_port_name(ctx, 1)
    def exitReg_port_signal_id(self, ctx:iclParser.Reg_port_signal_idContext):  self.parse_port_name(ctx, 0)
    
    def exitHier_port(self, ctx:iclParser.Hier_portContext):
        item = self.result[ctx.port_name()]
        for index in range(ctx.getChildCount()):
            if (ctx.instance_name(index)):
                item.add_hiearachy(ctx.instance_name(index).getText())
        self.result[ctx] = item
        print("exitHier_port-X", ctx.getText(), "->", self.result[ctx])

    def exitSignal(self, ctx:iclParser.SignalContext):
        self.result[ctx] = self.result[ctx.getChild(0)]
        print("exitSignal-X", ctx.getText(), "->", self.result[ctx])

    def exitData_signal(self, ctx:iclParser.Data_signalContext):
        operator = ctx.getChild(0).getText()  
        if(operator == "~"):
            self.result[ctx] = [~item for item in self.result[ctx.signal()]]
        else:
            self.result[ctx] = self.result[ctx.signal()]
        print("exitData_signal-X", ctx.getText(), "->", self.result[ctx])

    def exitReset_signal(self, ctx): self.exitData_signal(ctx)
    def exitScan_signal(self, ctx): self.exitData_signal(ctx)
    def exitClock_signal(self, ctx): self.exitData_signal(ctx)   
    def exitTck_signal(self, ctx): self.result[ctx] = self.result[ctx.signal()]
    def exitTms_signal(self, ctx): self.result[ctx] = self.result[ctx.signal()]
    def exitTrst_signal(self, ctx): self.result[ctx] = self.result[ctx.signal()]
    def exitShiftEn_signal(self, ctx): self.result[ctx] = self.result[ctx.signal()]
    def exitCaptureEn_signal(self, ctx): self.result[ctx] = self.result[ctx.signal()]
    def exitUpdateEn_signal(self, ctx): self.result[ctx] = self.result[ctx.signal()]

    def exitConcat_data_signal(self, ctx:iclParser.Concat_data_signalContext, type: str ="data"):
        concat = []
        for child in ctx.getChildren():
            if (child.getText() != ","):
                concat.append(self.result[child])
        self.result[ctx] = concat
        self.result[ctx] = ConcatSig(self.icl_instance, concat, type)
        print("exitConcat_data_signal-X", ctx.getText(), "->", self.result[ctx])

    def exitConcat_reset_signal(self, ctx): self.exitConcat_data_signal(ctx, "reset")        
    def exitConcat_scan_signal(self, ctx): self.exitConcat_data_signal(ctx, "scan")        
    def exitConcat_clock_signal(self, ctx): self.exitConcat_data_signal(ctx, "clock")        
    def exitConcat_tck_signal(self, ctx): self.exitConcat_data_signal(ctx, "tck")        
    def exitConcat_shiftEn_signal(self, ctx): self.exitConcat_data_signal(ctx, "shiften")        
    def exitConcat_captureEn_signal(self, ctx): self.exitConcat_data_signal(ctx, "captureen")        
    def exitConcat_updateEn_signal(self, ctx): self.exitConcat_data_signal(ctx, "updateen")        
    def exitConcat_tms_signal(self, ctx): self.exitConcat_data_signal(ctx, "tms")        
    def exitConcat_trst_signal(self, ctx): self.exitConcat_data_signal(ctx, "trst")        


    def exitSize(self, ctx:iclParser.SizeContext):
        if(ctx.pos_int()):
            self.result[ctx] = int(ctx.pos_int().getText())
        if(ctx.SCALAR_ID()):
            self.result[ctx] = int(ctx.SCALAR_ID().strip("\""))
        print("exitSize-X", self.result[ctx] ,"-X")

    def exitSized_dec_num(self, ctx:iclParser.Sized_dec_numContext):
        self.result[ctx] = IclNumber(ctx.UNSIZED_DEC_NUM().getText(), "dec", self.result[ctx.size()])
        print("exitSized_dec_num-X", ctx.getText(), "->", self.result[ctx])

    def exitSized_hex_num(self, ctx:iclParser.Sized_hex_numContext):
        self.result[ctx] = IclNumber(ctx.UNSIZED_HEX_NUM().getText(), "hex", self.result[ctx.size()])
        print("exitSized_hex_num-X", ctx.getText(), "->", self.result[ctx])

    def exitSized_bin_num(self, ctx:iclParser.Sized_bin_numContext):
        self.result[ctx] = IclNumber(ctx.UNSIZED_BIN_NUM().getText(), "bin", self.result[ctx.size()])
        print("exitSized_bin_num-X", ctx.getText(), "->", self.result[ctx])


    def exitSized_number(self, ctx:iclParser.Sized_numberContext):
        self.result[ctx] = self.result[ctx.getChild(0)]

    def exitUnsized_number(self, ctx:iclParser.Unsized_numberContext):
        if(ctx.pos_int()):
            self.result[ctx] =  IclNumber(ctx.pos_int().getText(), "dec")
        if(ctx.UNSIZED_DEC_NUM()):
            self.result[ctx] =  IclNumber(ctx.UNSIZED_DEC_NUM().getText(), "dec")
        if(ctx.UNSIZED_HEX_NUM()):
            self.result[ctx] =  IclNumber(ctx.UNSIZED_HEX_NUM().getText(), "hex")
        if(ctx.UNSIZED_BIN_NUM()):
            self.result[ctx] =  IclNumber(ctx.UNSIZED_BIN_NUM().getText(), "bin")            
        print("exitUnsized_number-", ctx.getText(), "->", self.result[ctx])

    def exitInteger_expr(self, ctx:iclParser.Integer_exprContext):
        self.result[ctx] = self.result[ctx.integer_expr_lvl1()]
        print("exitInteger_expr-", ctx.getText(), "->", self.result[ctx])

    def exitInteger_expr_lvl1(self, ctx:iclParser.Integer_expr_lvl1Context):
        if(ctx.integer_expr_lvl1()):
            operator = ctx.getChild(1).getText()  
            if(operator == "+"):
                self.result[ctx] = self.result[ctx.integer_expr_lvl2()] + self.result[ctx.integer_expr_lvl1()]
            if(operator == "-"):
                self.result[ctx] = self.result[ctx.integer_expr_lvl2()] - self.result[ctx.integer_expr_lvl1()]
        else:
            self.result[ctx] = self.result[ctx.integer_expr_lvl2()]

    def exitInteger_expr_lvl2(self, ctx:iclParser.Integer_expr_lvl2Context):
        if(ctx.integer_expr_lvl2()):
            operator = ctx.getChild(1).getText()
            if(operator == "*"):
                self.result[ctx] = self.result[ctx.integer_expr_arg()] * self.result[ctx.integer_expr_lvl2()]
            if(operator == "/"):
                self.result[ctx] = self.result[ctx.integer_expr_arg()] / self.result[ctx.integer_expr_lvl2()]
            if(operator == "%"):
                self.result[ctx] = self.result[ctx.integer_expr_arg()] % self.result[ctx.integer_expr_lvl2()]
        else:
            self.result[ctx] = self.result[ctx.integer_expr_arg()]
        print("exitInteger_expr_lvl2-", ctx.getText(), "->", self.result[ctx])


    def exitInteger_expr_arg(self, ctx:iclParser.Integer_expr_argContext):
        if(ctx.pos_int()):
            self.result[ctx] =  IclNumber(ctx.pos_int().getText(), "dec")
        if(ctx.integer_expr_paren()):
            self.result[ctx] = self.result[ctx.integer_expr_paren().integer_expr()]
        if(ctx.parameter_ref()):
            self.result[ctx] = self.record[ctx.parameter_ref()]
        print("exitInteger_expr_arg-", ctx.getText(), "->", self.result[ctx])

    def exitNumber(self, ctx:iclParser.NumberContext):
        self.result[ctx] = self.result[ctx.getChild(0)]
        print("exitNumber-X", ctx.getText(), "->", self.result[ctx])

    def exitConcat_number(self, ctx:iclParser.Concat_numberContext):
        # First value
        if(ctx.getChild(0).getText() == "~"):
            concat_number = ~self.result[ctx.getChild(1)]
            start = 2
        else:
            concat_number = self.result[ctx.getChild(0)]
            start = 1
        inv = 0

        # Concat values to first value
        for i in range(start, ctx.getChildCount()):
            if(ctx.getChild(i).getText() == ","):
                continue
            if(ctx.getChild(i).getText() == "~"):
                inv = 1
                continue
            if (ctx.getChild(i)):
                temp = self.result[ctx.getChild(i)]
                if(inv):
                    temp = ~temp
                concat_number = concat_number.concat(temp)
            inv = 0

        self.result[ctx] = concat_number
        print("exitConcat_number-X", ctx.getText(), "->", self.result[ctx])

    # Exit a parse tree produced by iclParser#concat_number_list.
    def exitConcat_number_list(self, ctx:iclParser.Concat_number_listContext):
        self.result[ctx] = []
        for index in range(ctx.getChildCount()):
            if (ctx.concat_number(index)):
                self.result[ctx].append(self.result[ctx.concat_number(index)])

        print("exitConcat_number_list-X", ctx.getText(), "->", self.result[ctx])

    def exitConcat_string(self, ctx:iclParser.Concat_stringContext):
        self.result[ctx] = ""
        for index in range(ctx.getChildCount()):
            if (ctx.STRING(index)):
                if(index == 0):
                    self.result[ctx] = ""
                self.result[ctx] += ctx.getToken(iclParser.STRING,index).getText()
                self.result[ctx] = self.result[ctx].replace("\"", "")

            if (ctx.parameter_ref(index)):
                if(index == 0):
                    self.result[ctx] = self.record[ctx.parameter_ref(index)]
                else:
                    self.result[ctx] += self.record[ctx.parameter_ref(index)]

        print("exitConcat_string-X", ctx.getText(), "->", self.result[ctx])

    def exitParameter_value(self, ctx:iclParser.Parameter_valueContext):
        self.result[ctx] = self.result[ctx.getChild(0)]
        print("exitParameter_value-X", ctx.getText(), "->", self.result[ctx])
        self.result["END"] = self.result[ctx]


    def exitParameter_def(self, ctx:iclParser.Parameter_defContext):
        parameter_name = ctx.parameter_name().SCALAR_ID().getText()
        parameter_data = self.result[ctx.parameter_value()]
        self.result[ctx] = {parameter_name: parameter_data}

        if(ctx.parentCtx.getRuleIndex() != iclParser.RULE_parameter_override):
            self.icl_instance.add_parameter(parameter_name, parameter_data)

        print("exitParameter_def-X", ctx.getText(), "->", self.result[ctx])

    def exitParameter_override(self, ctx:iclParser.Parameter_overrideContext):
        self.result[ctx] = self.result[ctx.getChild(0)]
        print("exitParameter_override-X", ctx.getText(), "->", self.result[ctx])

    def exitLocalParameter_def(self, ctx:iclParser.LocalParameter_defContext):
        parameter_name = ctx.parameter_name().SCALAR_ID().getText()
        parameter_data = self.result[ctx.parameter_value()]
        self.result[ctx] = {parameter_name: parameter_data}

        self.icl_instance.add_parameter(parameter_name, parameter_data)

        print("exitLocalParameter_def-X", ctx.getText(), "->", parameter_data)


    def enterParameter_ref(self, ctx:iclParser.Parameter_refContext):
        parameter_name = ctx.SCALAR_ID().getText()
        print(self.start_icl_module["parameters"][parameter_name])
        if(self.icl_instance.get_parameter_override(parameter_name)):
            self.record[ctx] = self.icl_instance.get_parameter_override(parameter_name)
        elif(self.icl_instance.get_parameter(parameter_name)):
            self.record[ctx] = self.icl_instance.get_parameter(parameter_name)
        else:
            lexer = iclLexer(InputStream(self.start_icl_module["parameters"][parameter_name]))
            stream = CommonTokenStream(lexer)
            parser = iclParser(stream)
            tree = parser.module_item()
            my_listener = IclProcess("dummy", "dummy", "dummy")
            my_listener.start_icl_module = self.start_icl_module;
            walker = ParseTreeWalker()
            #print("enterParameter_ref X0", variable, self.params[variable])
            walker.walk(my_listener, tree)
            self.record[ctx] = my_listener.result["END"]
        print("enterParameter_ref-X", ctx.getText(), "->", self.record[ctx])




    # dataRegister_def : 'DataRegister' dataRegister_name (';' | ( '{' dataRegister_item+ '}' ) ) ;   
    def exitDataRegister_def(self, ctx:iclParser.DataRegister_defContext):
        icl_name: IclSignal = self.result[ctx.dataRegister_name()]
        icl_data_register = IclDataRegister(self.icl_instance, icl_name, ctx.getText())
        self.icl_instance.add_icl_item(icl_data_register)
        print("exitDataRegister_def-X", ctx.getText(), "->", icl_data_register)

    # dataRegister_name : register_name ;
    def exitDataRegister_name(self, ctx:iclParser.DataRegister_nameContext):
        self.result[ctx] = self.result[ctx.register_name()]

    # dataRegister_item : dataRegister_type |
    #                     dataRegister_common ;
    # dataRegister_type : dataRegister_selectable |
    #                     dataRegister_addressable |
    #                     dataRegister_readCallBack |
    #                     dataRegister_writeCallBack ;
    # // Common to all types:
    # dataRegister_common : dataRegister_resetValue |
    #                     dataRegister_defaultLoadValue |
    #                     dataRegister_refEnum |
    #                     attribute_def ;
    # dataRegister_resetValue : 'ResetValue' (concat_number | enum_symbol) ';';
    # dataRegister_defaultLoadValue : 'DefaultLoadValue' (concat_number | enum_symbol)';' ;
    # dataRegister_refEnum : 'RefEnum' enum_name ';' ;
    # //For Selectable Data Register:
    # dataRegister_selectable : dataRegister_writeEnSource |
    # dataRegister_writeDataSource;
    # dataRegister_writeEnSource : 'WriteEnSource' '~'? data_signal ';' ;
    # dataRegister_writeDataSource : 'WriteDataSource' concat_data_signal ';' ;
    # // Addressable Data Register:
    # dataRegister_addressable : dataRegister_addressValue;
    # dataRegister_addressValue : 'AddressValue' number ';' ;
    # // CallBack Data Register:
    # dataRegister_readCallBack : dataRegister_readCallBack_proc |
    # dataRegister_readDataSource ;
    # dataRegister_readCallBack_proc : 'ReadCallBack' iProc_namespace iProc_name iProc_args* ';';
    # dataRegister_readDataSource : 'ReadDataSource' concat_data_signal ';' ;
    # dataRegister_writeCallBack : 'WriteCallBack' iProc_namespace iProc_name iProc_args* ';' ;
    # iProc_namespace : (namespace_name? '::')? ref_module_name ( '::' sub_namespace )? ;
    # iProc_name : SCALAR_ID | parameter_ref ;
    # iProc_args : '<D>' |
    #            '<R>' |
    #             number |
    #             STRING |
    #             parameter_ref ;
        



    # scanRegister_def : 'ScanRegister' scanRegister_name (';' |
    #                 '{' scanRegister_item* '}') ;
    # scanRegister_name : register_name ;
    # scanRegister_item : attribute_def |
    #                     scanRegister_scanInSource |
    #                     scanRegister_defaultLoadValue |
    #                     scanRegister_captureSource |
    #                     scanRegister_resetValue |
    #                     scanRegister_refEnum ;
    # scanRegister_scanInSource : 'ScanInSource' scan_signal ';' ;
    # scanRegister_defaultLoadValue : 'DefaultLoadValue' (concat_number | enum_symbol) ';' ;
    # scanRegister_captureSource : 'CaptureSource' (concat_data_signal | enum_symbol) ';';
    # scanRegister_resetValue : 'ResetValue' (concat_number | enum_symbol)';' ;
    # scanRegister_refEnum : 'RefEnum' enum_name ';' ;
    def exitScanRegister_def(self, ctx:iclParser.ScanRegister_defContext):

        scan_reg = self.result[ctx.scanRegister_name().register_name()]       
        attributes: list[IclAttribute] = []
        scan_in_source: IclSignal = None
        default_value: ConcatSig | EnumRef = None
        capture_source: ConcatSig | EnumRef = None
        reset_value: ConcatSig | EnumRef = None
        ref_enum:  str = None
        
        for item in ctx.scanRegister_item():
            if(item.attribute_def()):
                attribute_def = self.result[item.attribute_def()]
                attributes.append(attribute_def)  
                                  
            elif(item.scanRegister_scanInSource()):
                if scan_in_source is not None:
                    raise ValueError(f"ScanRegister has multiple scan in sources {ctx.getText()}")
                else:
                    scan_in_source = self.result[item.scanRegister_scanInSource().scan_signal()]
                                
            elif(item.scanRegister_defaultLoadValue()):
                if default_value is not None:
                    raise ValueError(f"ScanRegister has multiple default values {ctx.getText()}")
                else:
                    if item.scanRegister_defaultLoadValue().enum_symbol():
                        default_value = EnumRef(self.icl_instance, item.scanRegister_defaultLoadValue().enum_symbol().enum_value().getText())
                    elif item.scanRegister_defaultLoadValue().concat_number():
                        default_value = self.result[item.scanRegister_defaultLoadValue().concat_number()]
                        default_value: ConcatSig = ConcatSig(self.icl_instance,[default_value], "number")
                    else:
                        raise ValueError(f"Unexpected {ctx.getText()}")
                    
            elif(item.scanRegister_captureSource()):
                if capture_source is not None:
                    raise ValueError(f"ScanRegister has multiple capture sources {ctx.getText()}")
                else:
                    if item.scanRegister_captureSource().enum_symbol():
                        capture_source = EnumRef(self.icl_instance, item.scanRegister_captureSource().enum_symbol().enum_value().getText())
                    elif item.scanRegister_captureSource().concat_data_signal():
                        capture_source = self.result[item.scanRegister_captureSource().concat_data_signal()]
                    else:
                        raise ValueError(f"Unexpected {ctx.getText()}")
                
            elif(item.scanRegister_resetValue()):
                if reset_value is not None:
                    raise ValueError(f"ScanRegister has multiple reset values {ctx.getText()}")
                else:
                    if item.scanRegister_resetValue().enum_symbol():
                        reset_value = EnumRef(self.icl_instance, item.scanRegister_resetValue().enum_symbol().enum_value().getText())
                    elif item.scanRegister_resetValue().concat_number():
                        reset_value: IclNumber = self.result[item.scanRegister_resetValue().concat_number()]
                        reset_value: ConcatSig = ConcatSig(self.icl_instance,[reset_value], "number")
                    else:
                        raise ValueError(f"Unexpected {ctx.getText()}")
                
            elif(item.scanRegister_refEnum()):
                if ref_enum is not None:
                    raise ValueError(f"ScanRegister has multiple RefEnum {ctx.getText()}")
                else:
                    ref_enum = item.scanRegister_refEnum().enum_name().getText()

        new_icl_item = IclScanRegister(self.icl_instance, scan_reg, attributes, scan_in_source, default_value, capture_source, reset_value, ref_enum, ctx.getText())
        self.icl_instance.add_icl_item(new_icl_item)
        print("exitScanRegister_def-X", ctx.getText(), "->", new_icl_item)

    # scanMux_def : 'ScanMux' scanMux_name 'SelectedBy' scanMux_select '{' scanMux_selection+ '}' ;
    # scanMux_name : reg_port_signal_id ;
    # scanMux_select : concat_data_signal ;
    # scanMux_selection : concat_number_list':' concat_scan_signal ';' ;
    def exitScanMux_def(self, ctx:iclParser.ScanMux_defContext):       
        scan_mux = self.result[ctx.scanMux_name().reg_port_signal_id()]
        scan_select = self.result[ctx.scanMux_select().concat_data_signal()] 
        
        mux_selects = []
        for item in ctx.scanMux_selection():
            selector_list = self.result[item.concat_number_list()]
            selectee = self.result[item.concat_scan_signal()]
            mux_selects.append(tuple((selector_list, selectee)))
                   
        new_icl_item = IclScanMux(self.icl_instance, ctx.getText(), scan_mux,scan_select, mux_selects)
        self.icl_instance.add_icl_item(new_icl_item)

        print("exitScanMux_def-X", ctx.getText(), "->", new_icl_item)



    # instance_def : 'Instance' instance_name 'Of' (namespace_name? '::')?
    #                 module_name (';' | ( '{' instance_item* '}' ) ) ;
    # instance_item : inputPort_connection |
    #                 allowBroadcast_def |
    #                 attribute_def |
    #                 parameter_override |
    #                 instance_addressValue ;
    # inputPort_connection : 'InputPort' inputPort_name '=' inputPort_source ';' ;
    # allowBroadcast_def : 'AllowBroadcastOnScanInterface' scanInterface_name ';' ;
    # inputPort_name : port_name ;
    # inputPort_source : concat_reset_signal |
    #                 concat_scan_signal |
    #                 concat_data_signal |
    #                 concat_clock_signal |
    #                 concat_tck_signal |
    #                 concat_shiftEn_signal |
    #                 concat_captureEn_signal |
    #                 concat_updateEn_signal |
    #                 concat_tms_signal |
    #                 concat_trst_signal ;
    # parameter_override : parameter_def;
    # instance_addressValue : 'AddressValue' number ';' ;
    def exitInstance_def(self, ctx:iclParser.Instance_defContext):
        instance_name = ctx.instance_name().SCALAR_ID().getText()
        instances_names_in_module = self.start_icl_module["instances"].keys()

        if(instance_name not in instances_names_in_module):
            print(instance_name)
            print(instances_names_in_module)            
            raise Exception("Instance in not in all modules data")

        module_scope = self.start_icl_module["instances"][instance_name][0]
        module_name = self.start_icl_module["instances"][instance_name][1]            
        module_to_parse = self.all_icl_modules[module_scope][module_name]["data"]
        if(self.icl_instance.get_hier() == ""):
            instance_hier = instance_name
        else:
            instance_hier = ".".join([self.icl_instance.get_hier()] + [instance_name])

        icl_eval_lis = IclProcess(instance_name, module_name, module_scope, instance_hier)
        icl_eval_lis.all_icl_modules = self.all_icl_modules
        icl_eval_lis.start_icl_module = self.all_icl_modules[module_scope][module_name]

        input_ports = []
        attributes = []
        parameters = []
        for child in ctx.getChildren():
            if isinstance(child, iclParser.Instance_itemContext):

                if(child.inputPort_connection()):
                    port_name  = self.result[child.inputPort_connection().inputPort_name().port_name()]
                    port_paths = self.result[child.inputPort_connection().inputPort_source().getChild(0)]                  
                    connection = {port_name: port_paths}
                    icl_eval_lis.icl_instance.add_connection(connection)                  
                    input_ports.append((port_name, port_paths))
                elif(child.allowBroadcast_def()):
                    pass
                elif(child.attribute_def()):
                    name, attribure = self.result[child.getChild(0)].popitem()
                    icl_eval_lis.icl_instance.add_attribute(name, attribure)
                    input_ports.append((name, attribure))
                elif(child.parameter_override()):
                    name, parameter = self.result[child.getChild(0)].popitem()                  
                    icl_eval_lis.icl_instance.add_parameter_override(name, parameter)
                    parameters.append((name, parameter))
                else:
                    raise Exception("Unknown instance item")
                
        lexer = iclLexer(InputStream(module_to_parse))           
        stream = CommonTokenStream(lexer)
        parser = iclParser(stream)
        tree = parser.module_def()

        walker = ParseTreeWalker()
        walker.walk(icl_eval_lis, tree)


        self.icl_instance.add_icl_item(icl_eval_lis.icl_instance)

    #module_item :   useNameSpace_def |
    #                port_def |
    #                instance_def |
    #                scanRegister_def |
    #                dataRegister_def |
    #                logicSignal_def |
    #                scanMux_def |
    #                dataMux_def |
    #                clockMux_def |
    #                oneHotDataGroup_def |
    #                oneHotScanGroup_def |
    #                scanInterface_def |
    #                accessLink_def |
    #                alias_def |
    #                enum_def |
    #                parameter_def |
    #                localParameter_def |
    #                attribute_def ;
    def enterModule_item(self, ctx:iclParser.Module_itemContext):
        self.module_item_attributes: list = []

    #port_def :  scanInPort_def |
    #            scanOutPort_def |
    #            shiftEnPort_def |
    #            captureEnPort_def |
    #            updateEnPort_def |
    #            dataInPort_def |
    #            dataOutPort_def |
    #            toShiftEnPort_def |
    #            toUpdateEnPort_def |
    #            toCaptureEnPort_def |
    #            selectPort_def |
    #            toSelectPort_def |
    #            resetPort_def |
    #            toResetPort_def |
    #            tmsPort_def |
    #            toTmsPort_def |
    #            tckPort_def |
    #            toTckPort_def |
    #            clockPort_def |
    #            toClockPort_def |
    #            trstPort_def |
    #            toTrstPort_def |
    #            toIRSelectPort_def |
    #            addressPort_def |
    #            writeEnPort_def |
    #            readEnPort_def ;
    def exitPort_def(self, ctx:iclParser.Port_defContext):
        icl_item: IclItem = None
        attributes = self.module_item_attributes

        # scanInPort_def : 'ScanInPort' scanInPort_name (';' | ( '{' attribute_def* '}' ) ) ;
        # scanInPort_name : port_name ;
        if   ctx.scanInPort_def():
            new_ctx: iclParser.ScanInPort_defContext = ctx.scanInPort_def()
            port = self.result[new_ctx.scanInPort_name().port_name()]
            icl_item = IclScanInPort(self.icl_instance, ctx.getText(), port, attributes)

        # scanOutPort_def : 'ScanOutPort' scanOutPort_name ( ';' | ( '{' scanOutPort_item* '}' ) ) ;
        # scanOutPort_name : port_name;
        # scanOutPort_item : attribute_def |
        #                 scanOutPort_source |
        #                 scanOutPort_enable ;
        # scanOutPort_source : 'Source' concat_scan_signal ';';
        # scanOutPort_enable : 'Enable' data_signal ';';        
        elif ctx.scanOutPort_def():   
            new_ctx: iclParser.ScanOutPort_defContext = ctx.scanOutPort_def()
            port = self.result[new_ctx.scanOutPort_name().port_name()]
            source: ConcatSig = None
            enable: IclSignal = None

            for item in new_ctx.scanOutPort_item():
                if (item.scanOutPort_source()):
                    if not source:
                        source = self.result[item.scanOutPort_source().concat_scan_signal()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")                     
                    
                elif (item.scanOutPort_enable()):
                    if not enable:
                        enable = self.result[item.scanOutPort_enable().data_signal()]
                    else:
                        raise ValueError(f"More than one enable' {ctx.getText()}")        
                    
            icl_item = IclScanOutPort(self.icl_instance, ctx.getText(), port, attributes, source, enable)

        #shiftEnPort_def : 'ShiftEnPort' shiftEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
        #shiftEnPort_name : port_name ;        
        elif ctx.shiftEnPort_def():   
            new_ctx: iclParser.ShiftEnPort_defContext = ctx.shiftEnPort_def()
            port = self.result[new_ctx.shiftEnPort_name().port_name()]
            icl_item = IclShiftEnable(self.icl_instance, ctx.getText(), port, attributes)

        # captureEnPort_def : 'CaptureEnPort' captureEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
        # captureEnPort_name : port_name ;            
        elif ctx.captureEnPort_def():   
            new_ctx: iclParser.CaptureEnPort_defContext = ctx.captureEnPort_def()
            port = self.result[new_ctx.captureEnPort_name().port_name()]
            icl_item = IclCaptureEnable(self.icl_instance, ctx.getText(), port, attributes)

        # updateEnPort_def : 'UpdateEnPort' updateEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
        # updateEnPort_name : port_name ;            
        elif ctx.updateEnPort_def():   
            new_ctx: iclParser.UpdateEnPort_defContext = ctx.updateEnPort_def()
            port = self.result[new_ctx.updateEnPort_name().port_name()]
            icl_item = IclUpdateEnable(self.icl_instance, ctx.getText(), port, attributes)

        # dataInPort_def : 'DataInPort' dataInPort_name ( ';' | ( '{' dataInPort_item* '}' ) ) ;
        # dataInPort_name : port_name ;
        # dataInPort_item : attribute_def |
        #                 dataInPort_refEnum |
        #                 dataInPort_defaultLoadValue ;
        # dataInPort_refEnum : 'RefEnum' enum_name ';' ;
        # dataInPort_defaultLoadValue : 'DefaultLoadValue' (concat_number | enum_symbol) ';' ;            
        elif ctx.dataInPort_def():   
            new_ctx: iclParser.DataInPort_defContext = ctx.dataInPort_def()
            port = self.result[new_ctx.dataInPort_name().port_name()]
            default_value: IclNumber | str = None
            ref_enum: str = None

            for item in new_ctx.dataInPort_item():
                if (item.dataInPort_defaultLoadValue()):
                    if not default_value:
                        if item.dataInPort_defaultLoadValue().concat_number():
                            default_value = self.result[item.dataInPort_defaultLoadValue().concat_data_signal()]
                        else:
                            default_value = self.result[item.dataInPort_defaultLoadValue().enum_symbol()]                           
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")                                        
                elif (item.dataInPort_refEnum()):
                    if not ref_enum:
                        ref_enum = self.result[item.dataInPort_refEnum().enum_name()]
                    else:
                        raise ValueError(f"More than one reference' {ctx.getText()}")    
                                        
            icl_item = IclDataInPort(self.icl_instance, ctx.getText(), port, attributes, default_value, ref_enum)

        # dataOutPort_def : 'DataOutPort' dataOutPort_name (';' | ( '{' dataOutPort_item* '}' ) ) ;
        # dataOutPort_name : port_name ;
        # dataOutPort_item : attribute_def |
        #                   dataOutPort_source |
        #                   dataOutPort_enable |
        #                   dataOutPort_refEnum ;
        # dataOutPort_source : 'Source' concat_data_signal ';' ;
        # dataOutPort_enable : 'Enable' data_signal ';' ;
        # dataOutPort_refEnum : 'RefEnum' enum_name ';' ;        
        elif ctx.dataOutPort_def():   
            new_ctx: iclParser.DataInPort_defContext = ctx.dataOutPort_def()
            port = self.result[new_ctx.dataOutPort_name().port_name()]
            source: ConcatSig = None
            enable: IclSignal = None
            ref_enum: str = None

            for item in new_ctx.dataOutPort_item():
                if (item.dataOutPort_source()):
                    if not source:
                        source = self.result[item.dataOutPort_source().concat_data_signal()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")                     
                    
                elif (item.dataOutPort_enable()):
                    if not enable:
                        enable = self.result[item.dataOutPort_enable().data_signal()]
                    else:
                        raise ValueError(f"More than one enable' {ctx.getText()}")        

                elif (item.dataOutPort_refEnum()):
                    if not ref_enum:
                        ref_enum = self.result[item.dataOutPort_refEnum().enum_name()]
                    else:
                        raise ValueError(f"More than one reference' {ctx.getText()}")    
                                        
            icl_item = IclDataOutPort(self.icl_instance, ctx.getText(), port, attributes, source, enable, ref_enum)
                        
        # toShiftEnPort_def : 'ToShiftEnPort' toShiftEnPort_name (';' | ( '{' toShiftEnPort_items* '}' ) ) ;
        # toShiftEnPort_name : port_name ;
        # toShiftEnPort_items : attribute_def | toShiftEnPort_source ;  
        # toShiftEnPort_source : 'Source' concat_shiftEn_signal ';' ;        
        elif ctx.toShiftEnPort_def():   
            new_ctx: iclParser.ToShiftEnPort_defContext = ctx.toShiftEnPort_def()
            port = self.result[new_ctx.toShiftEnPort_name().port_name()]
            source: ConcatSig =None

            for item in new_ctx.toShiftEnPort_items():
                if (item.toShiftEnPort_source()):
                    if not source:
                        source = self.result[item.toShiftEnPort_source().concat_shiftEn_signal()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")
                    
            icl_item = IclToShiftEnable(self.icl_instance, ctx.getText(), port, attributes, source)

        # toUpdateEnPort_def : 'ToUpdateEnPort' toUpdateEnPort_name (';' |( '{' toUpdateEnPort_items* '}' ) ) ;
        # toUpdateEnPort_name : port_name ;
        # toUpdateEnPort_items : attribute_def | toUpdateEnPort_source ;
        # toUpdateEnPort_source : 'Source' updateEn_signal ';' ;            
        elif ctx.toUpdateEnPort_def():   
            new_ctx: iclParser.ToUpdateEnPort_defContext = ctx.toUpdateEnPort_def()
            port = self.result[new_ctx.toUpdateEnPort_name().port_name()]
            source: ConcatSig =None

            for item in new_ctx.toUpdateEnPort_items():
                if (item.toUpdateEnPort_source()):
                    if not source:
                        source = self.result[item.toUpdateEnPort_source().updateEn_signal()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")
                    
            icl_item = IclToUpdateEnable(self.icl_instance, ctx.getText(), port, attributes, source)

        # toCaptureEnPort_def : 'ToCaptureEnPort' toCaptureEnPort_name (';' | ( '{' toCaptureEnPort_items* '}' ) ) ;
        # toCaptureEnPort_name : port_name ;
        # toCaptureEnPort_items : attribute_def | toCaptureEnPort_source ;
        # toCaptureEnPort_source : 'Source' captureEn_signal ';' ;            
        elif ctx.toCaptureEnPort_def():   
            new_ctx: iclParser.ToCaptureEnPort_defContext = ctx.toCaptureEnPort_def()
            port = self.result[new_ctx.toCaptureEnPort_name().port_name()]
            source: ConcatSig = None

            for item in new_ctx.toCaptureEnPort_items():
                if item.toCaptureEnPort_source():
                    if not source:
                        source = self.result[item.toCaptureEnPort_source().captureEn_signal()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")      
                    
            icl_item = IclToCaptureEnable(self.icl_instance, ctx.getText(), port, attributes, source)

        # selectPort_def : 'SelectPort' selectPort_name (';' |( '{' attribute_def* '}' ) ) ;
        # selectPort_name : port_name ;
        elif ctx.selectPort_def():   
            new_ctx: iclParser.SelectPort_defContext = ctx.selectPort_def()
            port = self.result[new_ctx.selectPort_name().port_name()]

            icl_item = IclSelectPort(self.icl_instance, ctx.getText(), port, attributes)

        # toSelectPort_def : 'ToSelectPort' toSelectPort_name (';' | ( '{' toSelectPort_item+ '}' ) ) ;
        # toSelectPort_name : port_name ;
        # toSelectPort_item : attribute_def | toSelectPort_source ;
        # toSelectPort_source : 'Source' concat_data_signal ';' ;        
        elif ctx.toSelectPort_def():   
            new_ctx: iclParser.ToSelectPort_defContext = ctx.toSelectPort_def()
            port = self.result[new_ctx.toSelectPort_name().port_name()]
            source: ConcatSig = None

            for item in new_ctx.toSelectPort_item():
                if item.toSelectPort_source():
                    if not source:
                        source = self.result[item.toSelectPort_source().concat_data_signal()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")
                    
            icl_item = IclToSelectPort(self.icl_instance, ctx.getText(), port, attributes, source)  

        # resetPort_def : 'ResetPort' resetPort_name (';' | ( '{' resetPort_item* '}' ) ) ;
        # resetPort_name : port_name ;
        # resetPort_item : attribute_def | resetPort_polarity ;
        # resetPort_polarity : 'ActivePolarity' ('0'| '1') ';' ;                    
        elif ctx.resetPort_def():   
            new_ctx: iclParser.ResetPort_defContext = ctx.resetPort_def()
            port = self.result[new_ctx.resetPort_name().port_name()]
            polarity: bool = None

            for item in new_ctx.resetPort_item():
                if item.resetPort_polarity():
                    if not default_value:
                        polarity = bool(int(item.resetPort_polarity().getChild(1)))
                    else:
                        raise ValueError(f"More than one polarity' {ctx.getText()}")
                    
            icl_item = IclResetPort(self.icl_instance, ctx.getText(), port, attributes, polarity)

        # toResetPort_def : 'ToResetPort' toResetPort_name (';' | ( '{' toResetPort_item+ '}' ) ) ;
        # toResetPort_name : port_name ;
        # toResetPort_item : attribute_def | toResetPort_source | toResetPort_polarity;
        # toResetPort_source : 'Source' concat_reset_signal ';' ;
        # toResetPort_polarity : 'ActivePolarity' ('0'| '1') ';' ;        
        elif ctx.toResetPort_def():   
            new_ctx: iclParser.ToResetPort_defContext = ctx.toResetPort_def()
            port = self.result[new_ctx.toResetPort_name().port_name()]
            source: ConcatSig = None
            polarity: bool = None

            for item in new_ctx.toResetPort_item():
                if item.toResetPort_polarity():
                    if not default_value:
                        polarity = bool(int(item.toResetPort_polarity().getChild(1)))
                    else:
                        raise ValueError(f"More than one polarity' {ctx.getText()}")
                elif item.toResetPort_source():
                    if not source:
                        source = self.result[item.toResetPort_source()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")
                    
            icl_item = IclToResetPort(self.icl_instance, ctx.getText(), port, attributes, source, polarity)                                        

        # tmsPort_def : 'TMSPort' tmsPort_name (';' | ( '{' attribute_def*'}' ) ) ;
        # tmsPort_name : port_name ;
        elif ctx.tmsPort_def():   
            new_ctx: iclParser.TmsPort_defContext = ctx.tmsPort_def()
            port = self.result[new_ctx.tmsPort_name().port_name()]
            icl_item = IclTmsPort(self.icl_instance, ctx.getText(), port, attributes)                                        

        # toTmsPort_def : 'ToTMSPort' toTmsPort_name (';' | ( '{' toTmsPort_item* '}' ) ) ;
        # toTmsPort_name : port_name ;
        # toTmsPort_item : attribute_def | toTmsPort_source ;
        # toTmsPort_source : 'Source' concat_tms_signal ';' ;
        elif ctx.toTmsPort_def():   
            new_ctx: iclParser.ToTmsPort_defContext = ctx.toTmsPort_def()
            port = self.result[new_ctx.toTmsPort_name().port_name()]
            source: ConcatSig = None

            for item in new_ctx.toTmsPort_item():
                if item.toTmsPort_source():
                    if not source:
                        source = self.result[item.toTmsPort_source().concat_tms_signal()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")
                    
            icl_item = IclToTmsPort(self.icl_instance, ctx.getText(), port, attributes, source)                                                            

        # tckPort_def : 'TCKPort' tckPort_name (';' | ( '{' attribute_def* '}' ) ) ;
        # tckPort_name : port_name ;
        elif ctx.tckPort_def():   
            new_ctx: iclParser.TckPort_defContext = ctx.tckPort_def()
            port = self.result[new_ctx.tckPort_name().port_name()]
            icl_item = IclTckPort(self.icl_instance, ctx.getText(), port, attributes)                                        

        # toTckPort_def : 'ToTCKPort' toTckPort_name (';' | ( '{' attribute_def* '}' ) ) ;
        # toTckPort_name : port_name ;                 
        elif ctx.toTckPort_def():   
            new_ctx: iclParser.ToTckPort_defContext = ctx.toTckPort_def()
            port = self.result[new_ctx.toTckPort_name().port_name()]
            icl_item = IclToTckPort(self.icl_instance, ctx.getText(), port, attributes)                                        

        # clockPort_def : 'ClockPort' clockPort_name (';' | ( '{' clockPort_item* '}' ));
        # clockPort_name : port_name ;
        # clockPort_item : attribute_def | clockPort_diffPort ;
        # clockPort_diffPort : 'DifferentialInvOf' concat_clock_signal ';' ;           
        elif ctx.clockPort_def():   
            new_ctx: iclParser.ClockPort_defContext = ctx.clockPort_def()
            port = self.result[new_ctx.clockPort_name().port_name()]
            diff_port: ConcatSig = None

            for item in new_ctx.clockPort_item():
                if item.clockPort_diffPort():
                    if not diff_port:
                        diff_port = self.result[item.clockPort_diffPort().concat_clock_signal()]
                    else:
                        raise ValueError(f"More than diff port' {ctx.getText()}")
                    
            clock_settings: dict = {
                "diff": diff_port,
                "direction": "in",
            }

            icl_item = IclClockPort(self.icl_instance, ctx.getText(), port, attributes, clock_settings)

        # toClockPort_def : 'ToClockPort' toClockPort_name (';' | ( '{' toClockPort_item+ '}' ) ) ;
        # toClockPort_name : port_name ;
        # toClockPort_item :  attribute_def |
        #                     toClockPort_source |
        #                     freqMultiplier_def |
        #                     freqDivider_def |
        #                     differentialInvOf_def |
        #                     period_def ;
        # toClockPort_source : 'Source' concat_clock_signal ';' ;
        # 
        # freqMultiplier_def : 'FreqMultiplier' pos_int ';' ;
        # freqDivider_def : 'FreqDivider' pos_int ';' ;
        # differentialInvOf_def : 'DifferentialInvOf' concat_clock_signal ';' ;
        # 
        # period_def : 'Period' pos_int ('s' | 'ms' | 'us' | 'ns' | 'ps' | 'fs' | 'as')? ';' ;          
        elif ctx.toClockPort_def():   
            new_ctx: iclParser.ToClockPort_defContext = ctx.toClockPort_def()
            port = self.result[new_ctx.toClockPort_name().port_name()]
            source: ConcatSig = None
            freq_mult: int = None
            freq_div: int = None
            diff_port: ConcatSig = None
            period: int = None

            for item in new_ctx.toClockPort_item():
                if item.toClockPort_source():
                    if not source:
                        source = self.result[item.toClockPort_source()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")
                elif item.freqMultiplier_def():
                    if not freq_mult:
                        freq_mult = int(item.freqMultiplier_def().pos_int().getText())
                    else:
                        raise ValueError(f"More than one freq. mult.' {ctx.getText()}")
                elif item.freqDivider_def():
                    if not freq_div:
                        freq_div = int(item.freqDivider_def().pos_int().getText())
                    else:
                        raise ValueError(f"More than one freq. div.' {ctx.getText()}")
                if item.differentialInvOf_def():
                    if not diff_port:
                        diff_port = self.result[item.differentialInvOf_def().concat_clock_signal()]
                    else:
                        raise ValueError(f"More than diff port' {ctx.getText()}")                    
                elif item.period_def():
                    if not period:
                        period = int(item.period_def().pos_int().getText())
                        if(item.period_def().getChild(2)):
                            period_unit = item.period_def().getChild(2).getText()
                            if   (period_unit == 's'): period *= 1 
                            elif (period_unit == 'ms'): period *= 10**(-3)
                            elif (period_unit == 'us'): period *= 10**(-6) 
                            elif (period_unit == 'ns'): period *= 10**(-9) 
                            elif (period_unit == 'ps'): period *= 10**(-12) 
                            elif (period_unit == 'fs'): period *= 10**(-15) 
                            elif (period_unit == 'as'): period *= 10**(-18)                             
                            else: period *= 10**(-9)
                    else:
                        raise ValueError(f"More than one period' {ctx.getText()}")
                    
            clock_settings: dict = {
                "diff": diff_port,
                "period": period,
                "freq_div": freq_div,
                "freq_mul": freq_mult,
                "source": source,
                "direction": "out",
            }

            icl_item = IclToClockPort(self.icl_instance, ctx.getText(), port, attributes, source, clock_settings)

        # trstPort_def : 'TRSTPort' trstPort_name (';' | ( '{' attribute_def* '}' ) ) ;
        # trstPort_name : port_name ;
        elif ctx.trstPort_def():
            new_ctx: iclParser.TrstPort_defContext = ctx.trstPort_def()
            port = self.result[new_ctx.trstPort_name().port_name()]
            icl_item = IclTrstPort(self.icl_instance, ctx.getText(), port, attributes)

        # toTrstPort_def : 'ToTRSTPort' toTrstPort_name (';' | ( '{' toTrstPort_item+ '}' ) ) ;
        # toTrstPort_name : port_name ;
        # toTrstPort_item : attribute_def | toTrstPort_source ;
        # toTrstPort_source : 'Source' concat_trst_signal ';' ;     
        elif ctx.toTrstPort_def():   
            new_ctx: iclParser.ToTrstPort_defContext = ctx.toTrstPort_def()
            port = self.result[new_ctx.toTrstPort_name().port_name()]
            source: ConcatSig = None

            for item in new_ctx.toTrstPort_item():
                if item.toTrstPort_source():
                    if not source:
                        source = self.result[item.toTrstPort_source().concat_trst_signal()]
                    else:
                        raise ValueError(f"More than one source' {ctx.getText()}")
                    
            icl_item = IclToTrstPort(self.icl_instance, ctx.getText(), port, attributes, source)

        # toIRSelectPort_def : 'ToIRSelectPort' toIRSelectPort_name (';' |
        #             ( '{' attribute_def* '}' )) ;
        # toIRSelectPort_name : port_name ;
        elif ctx.toIRSelectPort_def():   
            new_ctx: iclParser.ToIRSelectPort_defContext = ctx.toIRSelectPort_def()
            port = self.result[new_ctx.ToIRSelectPort().port_name()]
            icl_item = IclIrSelectPort(self.icl_instance, ctx.getText(), port, attributes)

        # addressPort_def : 'AddressPort' addressPort_name (';' | ( '{' attribute_def*'}' ) ) ;
        # addressPort_name : port_name ;
        elif ctx.addressPort_def():   
            new_ctx: iclParser.AddressPort_defContext = ctx.addressPort_def()
            port = self.result[new_ctx.addressPort_name().port_name()]
            icl_item = IclAddressPort(self.icl_instance, ctx.getText(), port, attributes)

        # writeEnPort_def : 'WriteEnPort' writeEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
        # writeEnPort_name : port_name ;
        elif ctx.writeEnPort_def():   
            new_ctx: iclParser.WriteEnPort_defContext = ctx.writeEnPort_def()
            port = self.result[new_ctx.writeEnPort_name().port_name()]
            icl_item = IclWriteEnPort(self.icl_instance, ctx.getText(), port, attributes)                                        

        # readEnPort_def : 'ReadEnPort' readEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
        # readEnPort_name : port_name ;        
        elif ctx.readEnPort_def():   
            new_ctx: iclParser.ReadEnPort_defContext = ctx.readEnPort_def()
            port = self.result[new_ctx.readEnPort_name().port_name()]
            icl_item = IclReadEnPort(self.icl_instance, ctx.getText(), port, attributes)                                        
        else:   
            raise ValueError(f"Unknown port definition {ctx.getText()}")

        self.result[ctx] = icl_item
        if icl_item:
            port = icl_item.ports[0]
            port_name: str = port.get_name()              
            try:
                port_item = self.icl_instance.get_icl_item_name(port_name).merge(icl_item)
            except:
                port_item = None

            if port_item:  
                port_item.merge(icl_item)
            else:
                self.icl_instance.add_icl_item(icl_item)

            print(f"exit port {ctx.getChild(0).getText()} -> {icl_item, port_name, attributes}")      

    # attribute_def : 'Attribute' attribute_name ('=' attribute_value )? ';' ;
    # attribute_name : SCALAR_ID;
    # attribute_value : (concat_string | concat_number) ;
    def exitAttribute_def(self, ctx:iclParser.Attribute_defContext):
        attribute_name = ctx.attribute_name().SCALAR_ID().getText()
        attribute_data = self.result[ctx.attribute_value().getChild(0)]
        self.result[ctx] = IclAttribute(self.icl_instance, ctx.getText(), attribute_name, attribute_data)

        # For exitPort_def
        self.module_item_attributes.append(self.result[ctx])

        print("attribute_def-X", ctx.getText(), "->", self.result[ctx])
