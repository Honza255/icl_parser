from typing import Any
from antlr4 import *
import sys

from parser.iclLexer import iclLexer
from parser.iclListener import iclListener
from parser.iclParser import iclParser

from icl_number import *
from icl_signal import *
from icl_item import *

class IclProcess(iclListener):
    def __init__(self, instance_name, module_name, scope_name="root", hier=""):
        self.all_module_data = {}
        self.current_init_data = {}
        self.new_inst = IclInstance(instance_name,hier, module_name, self)
        # Tree helper
        self.record  = {}
        self.result = {}

        # Data
        self.parameters = {}

    def exitPort_name(self, ctx:iclParser.Port_nameContext):
        sig = None
        if(ctx.SCALAR_ID()):
            name = ctx.SCALAR_ID().getText()
            sig = IclSignal(name)
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
        print("exitPort_name-X", ctx.getText(), "->", self.result[ctx])

    def exitReg_port_signal_id(self, ctx:iclParser.Reg_port_signal_idContext): self.exitPort_name(ctx)
    def exitRegister_name(self, ctx: iclParser.Register_nameContext): self.exitPort_name(ctx)
    
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

    def exitConcat_data_signal(self, ctx:iclParser.Concat_data_signalContext):
        concat = []
        for child in ctx.getChildren():
            if (child.getText() != ","):
                concat.append(self.result[child])
        self.result[ctx] = concat
        print("exitConcat_data_signal-X", ctx.getText(), "->", self.result[ctx])

    def exitConcat_reset_signal(self, ctx): self.exitConcat_data_signal(ctx)        
    def exitConcat_scan_signal(self, ctx): self.exitConcat_data_signal(ctx)        
    def exitConcat_clock_signal(self, ctx): self.exitConcat_data_signal(ctx)        
    def exitConcat_tck_signal(self, ctx): self.exitConcat_data_signal(ctx)        
    def exitConcat_shiftEn_signal(self, ctx): self.exitConcat_data_signal(ctx)        
    def exitConcat_captureEn_signal(self, ctx): self.exitConcat_data_signal(ctx)        
    def exitConcat_updateEn_signal(self, ctx): self.exitConcat_data_signal(ctx)        
    def exitConcat_tms_signal(self, ctx): self.exitConcat_data_signal(ctx)        
    def exitConcat_trst_signal(self, ctx): self.exitConcat_data_signal(ctx)        


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

    def exitAttribute_def(self, ctx:iclParser.Attribute_defContext):
        attribute_name = ctx.attribute_name().SCALAR_ID().getText()
        attribute_data = self.result[ctx.attribute_value().getChild(0)]
        att = IclAttribute(self.new_inst, ctx, attribute_name, attribute_data)
        self.result[ctx] = att
        #self.result[ctx] = {attribute_name: attribute_data}

        #if(ctx.parentCtx.getRuleIndex() == iclParser.RULE_module_item):
        #    self.instance.add_attribute(attribute_name, attribute_data)
                    
        print("attribute_def-X", ctx.getText(), "->", self.result[ctx])

    def exitParameter_def(self, ctx:iclParser.Parameter_defContext):
        parameter_name = ctx.parameter_name().SCALAR_ID().getText()
        parameter_data = self.result[ctx.parameter_value()]
        self.result[ctx] = {parameter_name: parameter_data}

        if(ctx.parentCtx.getRuleIndex() != iclParser.RULE_parameter_override):
            self.new_inst.add_parameter(parameter_name, parameter_data)

        print("exitParameter_def-X", ctx.getText(), "->", self.result[ctx])

    def exitParameter_override(self, ctx:iclParser.Parameter_overrideContext):
        self.result[ctx] = self.result[ctx.getChild(0)]
        print("exitParameter_override-X", ctx.getText(), "->", self.result[ctx])

    def exitLocalParameter_def(self, ctx:iclParser.LocalParameter_defContext):
        parameter_name = ctx.parameter_name().SCALAR_ID().getText()
        parameter_data = self.result[ctx.parameter_value()]
        self.result[ctx] = {parameter_name: parameter_data}

        self.new_inst.add_parameter(parameter_name, parameter_data)

        print("exitLocalParameter_def-X", ctx.getText(), "->", parameter_data)


    def enterParameter_ref(self, ctx:iclParser.Parameter_refContext):
        parameter_name = ctx.SCALAR_ID().getText()
        print(self.current_init_data["parameters"][parameter_name])
        if(self.new_inst.get_parameter_override(parameter_name)):
            self.record[ctx] = self.new_inst.get_parameter_override(parameter_name)
        elif(self.new_inst.get_parameter(parameter_name)):
            self.record[ctx] = self.new_inst.get_parameter(parameter_name)
        else:
            lexer = iclLexer(InputStream(self.current_init_data["parameters"][parameter_name]))
            stream = CommonTokenStream(lexer)
            parser = iclParser(stream)
            tree = parser.module_item()
            my_listener = IclProcess("dummy", "dummy", "dummy")
            my_listener.current_init_data = self.current_init_data;
            walker = ParseTreeWalker()
            #print("enterParameter_ref X0", variable, self.params[variable])
            walker.walk(my_listener, tree)
            self.record[ctx] = my_listener.result["END"]
        print("enterParameter_ref-X", ctx.getText(), "->", self.record[ctx])


    def exitScanInPort_def(self, ctx:iclParser.ScanInPort_defContext):
        port_sig = self.result[ctx.scanInPort_name().port_name()]
        port_name = port_sig.get_name()
        icl_item = IclScanInPort(self.new_inst, ctx, port_sig)

        for index in range(ctx.getChildCount()):
            if (ctx.attribute_def(index)):
                attribute_def = self.result[ctx.attribute_def(index)]
                icl_item.add_attribute(port_sig, attribute_def)
                

        try:
            self.new_inst.get_icl_item_name(port_name).merge(icl_item)
        except:
            self.new_inst.add_icl_item(icl_item)
        print("exitScanInPort_def-X", ctx.getText(), "->", icl_item)
    

    def exitScanOutPort_def(self, ctx:iclParser.ScanOutPort_defContext):
        port_sig = self.result[ctx.scanOutPort_name().port_name()]
        port_name = port_sig.get_name()
        new_icl_item = IclScanOutPort(self.new_inst, ctx, port_sig)

        for index in range(ctx.getChildCount()):
            item = ctx.scanOutPort_item(index)
            if(not item):
                continue
            elif (item.attribute_def()):
                attribute_def = self.result[item.attribute_def()]
                new_icl_item.add_attribute(port_sig, attribute_def)

            elif (item.scanOutPort_source()):
                source_data = self.result[item.scanOutPort_source().concat_scan_signal()]
                new_icl_item.add_source(port_sig, source_data)
                
            elif (item.scanOutPort_enable()):
                enable_data = self.result[item.scanOutPort_enable().concat_scan_signal()]

        try:
            self.new_inst.get_icl_item_name(port_name).merge(new_icl_item)
        except:
            self.new_inst.add_icl_item(new_icl_item)

        print("exitScanOutPort_def-X", ctx.getText(), "->", new_icl_item)

    def exitScanRegister_def(self, ctx:iclParser.ScanRegister_defContext):
        scan_sig = self.result[ctx.scanRegister_name().register_name()]
        scan_name = scan_sig.get_name()
        new_icl_item = IclScanRegister(self.new_inst, ctx, scan_sig)
        for index in range(ctx.getChildCount()):
            item = ctx.scanRegister_item(index)

            if(not item):
                continue
            
            elif(item.attribute_def()):
                attribute_def = self.result[item.attribute_def()]
                new_icl_item.add_attribure(attribute_def)  
                  
            elif(item.scanRegister_scanInSource()):
                scan_in = self.result[item.scanRegister_scanInSource().scan_signal()]
                new_icl_item.add_scan_in(scan_in)
                
            elif(item.scanRegister_defaultLoadValue()):
                default_value = self.result[item.scanRegister_defaultLoadValue().getChild(1)]
                new_icl_item.add_default_value(default_value)
                
            elif(item.scanRegister_captureSource()):
                capture_source = self.result[item.scanRegister_captureSource().getChild(1)]
                new_icl_item.add_scan_capture(capture_source)
                
            elif(item.scanRegister_resetValue()):
                reset_value = self.result[item.scanRegister_resetValue().getChild(1)]
                new_icl_item.add_reset_value(reset_value)
                
            elif(item.scanRegister_refEnum()):
                pass

        self.new_inst.add_icl_item(new_icl_item)
        print("exitScanRegister_def-X", ctx.getText(), "->", new_icl_item)

    def exitDataInPort_def(self, ctx:iclParser.DataInPort_defContext):
        icl_port = self.result[ctx.dataInPort_name().port_name()]
        icl_item_name = icl_port.get_name()
        new_icl_item = IclDataInPort(self.new_inst, ctx, icl_port)

        for index in range(ctx.getChildCount()):
            item = ctx.dataInPort_item(index)

            if(not item):
                continue
            elif(item.attribute_def()):
                attribute_def = self.result[item.attribute_def()]
                #icl_item.add_addon({"attribute": attribute_def}) 
                new_icl_item.add_attribute(icl_port, attribute_def)         
            elif(item.dataInPort_refEnum()):
                pass
            elif(item.dataInPort_defaultLoadValue()):
                pass

        try:
            self.new_inst.get_icl_item_name(icl_item_name).merge(new_icl_item)
        except:
            self.new_inst.add_icl_item(new_icl_item)

        print("exitDataInPort_def_def-X", ctx.getText(), "->", icl_item_name)

    def exitDataOutPort_def(self, ctx:iclParser.DataOutPort_defContext):
        icl_port = self.result[ctx.dataOutPort_name().port_name()]
        icl_item_name = icl_port.get_name()
        new_icl_item = IclDataOutPort(self.new_inst, ctx, icl_port)

        for index in range(ctx.getChildCount()):
            item = ctx.dataOutPort_item(index)

            if(not item):
                continue
            elif(item.attribute_def()):
                attribute_def = self.result[item.attribute_def()]
                new_icl_item.add_attribute(icl_port,attribute_def)        
                
            elif(item.dataOutPort_source()):
                new_icl_item.add_source(icl_port, self.result[item.dataOutPort_source().concat_data_signal()])
                
            elif(item.dataOutPort_enable()):
                pass
            
            elif(item.dataOutPort_refEnum()):
                pass

        try:
            self.new_inst.get_icl_item_name(icl_item_name).merge(new_icl_item)
        except:
            self.new_inst.add_icl_item(new_icl_item)
            
        print("exitDataOutPort_def-X", ctx.getText(), "->", icl_item_name)

    def exitScanMux_def(self, ctx:iclParser.ScanMux_defContext):       
        scan_mux = self.result[ctx.scanMux_name().reg_port_signal_id()]
        scan_select = ConcatSig(self.new_inst, self.result[ctx.scanMux_select().concat_data_signal()], "data")       
        
        mux_selects = []
        for index in range(ctx.getChildCount()):           
            if(ctx.scanMux_selection(index)):
                selector_list = self.result[ctx.scanMux_selection(index).concat_number_list()]
                selectee = ConcatSig(self.new_inst, self.result[ctx.scanMux_selection(index).concat_scan_signal()], "scan")
                for sel_num in selector_list:
                    mux_selects.append(tuple((sel_num, selectee)))
                   
        new_icl_item = IclScanMux(self.new_inst, ctx, scan_mux,scan_select, mux_selects)
        self.new_inst.add_icl_item(new_icl_item)

        print("exitScanMux_def-X", ctx.getText(), "->", new_icl_item)
    
    
    def exitInstance_def(self, ctx:iclParser.Instance_defContext):
        instance_name = ctx.instance_name().SCALAR_ID().getText()
        instances_names_in_module = self.current_init_data["instances"].keys()

        if(instance_name not in instances_names_in_module):
            print(instance_name)
            print(instances_names_in_module)            
            raise Exception("Instance in not in all modules data")

        module_scope = self.current_init_data["instances"][instance_name][0]
        module_name = self.current_init_data["instances"][instance_name][1]            
        module_to_parse = self.all_module_data[module_scope][module_name]["data"]
        if(self.new_inst.get_hier() == ""):
            instance_hier = instance_name
        else:
            instance_hier = ".".join([self.new_inst.get_hier()] + [instance_name])

        icl_eval_lis = IclProcess(instance_name, module_name, module_scope, instance_hier)
        icl_eval_lis.all_module_data = self.all_module_data
        icl_eval_lis.current_init_data = self.all_module_data[module_scope][module_name]

        input_ports = []
        attributes = []
        parameters = []
        for child in ctx.getChildren():
            if isinstance(child, iclParser.Instance_itemContext):

                if(child.inputPort_connection()):
                    port_name  = self.result[child.inputPort_connection().inputPort_name().port_name()]
                    port_paths = self.result[child.inputPort_connection().inputPort_source().getChild(0)]                  
                    connection = {port_name: port_paths}
                    icl_eval_lis.new_inst.add_connection(connection)                  
                    input_ports.append((port_name, port_paths))
                elif(child.allowBroadcast_def()):
                    pass
                elif(child.attribute_def()):
                    name, attribure = self.result[child.getChild(0)].popitem()
                    icl_eval_lis.new_inst.add_attribute(name, attribure)
                    input_ports.append((name, attribure))
                elif(child.parameter_override()):
                    name, parameter = self.result[child.getChild(0)].popitem()                  
                    icl_eval_lis.new_inst.add_parameter_override(name, parameter)
                    parameters.append((name, parameter))
                else:
                    raise Exception("Unknown instance item")
                
        lexer = iclLexer(InputStream(module_to_parse))           
        stream = CommonTokenStream(lexer)
        parser = iclParser(stream)
        tree = parser.module_def()

        walker = ParseTreeWalker()
        walker.walk(icl_eval_lis, tree)


        self.new_inst.add_icl_item(icl_eval_lis.new_inst)
