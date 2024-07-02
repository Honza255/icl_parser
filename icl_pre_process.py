from typing import Any

from antlr4 import *
from parser.iclLexer import iclLexer
from parser.iclListener import iclListener
from parser.iclParser import iclParser

from icl_items import *

class IclPreProcess(iclListener):

    currnet_moddef_scope = "root"

    current_namespace_outside = "root"
    current_namespace = "root"

    current_module_name  = ""
    current_module_data  = ""
    modules = {"root":{}}


    def enterModule_def(self, ctx:iclParser.Module_defContext):
        self.current_module_name = ctx.module_name().SCALAR_ID().getText()
        self.current_module_data =  ctx.getText()
        
        if(self.currnet_moddef_scope not in self.modules):
            self.modules[self.currnet_moddef_scope] = {}

        self.modules[self.currnet_moddef_scope][self.current_module_name] = {}
        self.modules[self.currnet_moddef_scope][self.current_module_name]["data"] = self.extract_original_text(ctx) 
        self.modules[self.currnet_moddef_scope][self.current_module_name]["parameters"] = {}
        self.modules[self.currnet_moddef_scope][self.current_module_name]["local_parameters"] = {}
        self.modules[self.currnet_moddef_scope][self.current_module_name]["instances"] = {}


    def exitModule_def(self, ctx:iclParser.Module_defContext):
        self.current_namespace = self.current_namespace_outside;
                    
    def enterNameSpace_def(self, ctx:iclParser.NameSpace_defContext):
        if(ctx.namespace_name()):
            self.currnet_moddef_scope = ctx.namespace_name().SCALAR_ID().getText()
        else:
            self.currnet_moddef_scope = "root"
        self.current_namespace = self.currnet_moddef_scope

        if(ctx.parentCtx.getRuleIndex() != iclParser.RULE_module_item):
            self.current_namespace_outside = self.currnet_moddef_scope


    def enterUseNameSpace_def(self, ctx:iclParser.UseNameSpace_defContext):
        if(ctx.namespace_name()):
            self.current_namespace = ctx.namespace_name().SCALAR_ID().getText()
        else:
            self.current_namespace = "root"

    def extract_original_text(self, ctx):
        token_source = ctx.start.getTokenSource()
        input_stream = token_source.inputStream
        #print(token_source)
        #print(ctx.start)
        #print(ctx.stop)


        start, stop  = ctx.start.start, ctx.stop.stop
        return input_stream.getText(start, stop)

    def enterParameter_def(self, ctx:iclParser.Parameter_defContext):
        if(ctx.parentCtx.getRuleIndex() != iclParser.RULE_parameter_override):
            parameter_name = ctx.parameter_name().SCALAR_ID().getText()
            parameter_data = self.extract_original_text(ctx.parameter_value())
            parameter_data = str(self.extract_original_text(ctx)) + " XXX"
            #parameter_data = ctx.getText()


            if(parameter_name in self.modules[self.currnet_moddef_scope][self.current_module_name]["parameters"]):
                raise Exception("Parameter already defined in module before")
            self.modules[self.currnet_moddef_scope][self.current_module_name]["parameters"][parameter_name] = parameter_data

    def enterLocalParameter_def(self, ctx:iclParser.LocalParameter_defContext):
        if(ctx.parentCtx.getRuleIndex() != iclParser.RULE_parameter_override):
            parameter_name = ctx.parameter_name().SCALAR_ID().getText()
            parameter_data = self.extract_original_text(ctx.parameter_value())
            parameter_data = self.extract_original_text(ctx)

            if(parameter_name in self.modules[self.currnet_moddef_scope][self.current_module_name]["local_parameters"]):
                raise Exception("Local_parameters already defined in module before")
            self.modules[self.currnet_moddef_scope][self.current_module_name]["local_parameters"][parameter_name] = parameter_data

    def enterInstance_def(self, ctx:iclParser.Instance_defContext):
        name = ctx.instance_name().SCALAR_ID().getText()
        data = self.extract_original_text(ctx)

        module_name = ctx.module_name().SCALAR_ID().getText()
        if(ctx.namespace_name()):
           namespace = ctx.namespace_name().SCALAR_ID().getText()
        else:
           namespace = self.current_namespace


        if(name in self.modules[self.currnet_moddef_scope][self.current_module_name]["instances"]):
            raise Exception("instances already defined in module before")
        self.modules[self.currnet_moddef_scope][self.current_module_name]["instances"][name] = [namespace,module_name,data]
