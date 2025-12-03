from .icl_parser.iclListener import iclListener
from .icl_parser.iclParser import iclParser

class IclPreProcess(iclListener):

    module_definition_name_space = "root"

    instance_namespace_out = "root"
    instance_namespace = "root"

    current_module_name  = ""
    modules = {"root":{}}

    # icl_source : iclSource_items+ ;
    # iclSource_items : nameSpace_def | useNameSpace_def | module_def;
    #
    # nameSpace_def : 'NameSpace' namespace_name? ';' ;
    # namespace_name : SCALAR_ID;
    def enterNameSpace_def(self, ctx:iclParser.NameSpace_defContext):
        if(ctx.namespace_name()):
            self.module_definition_name_space = ctx.namespace_name().SCALAR_ID().getText()
        else:
            self.module_definition_name_space = "root"

    # useNameSpace_def : 'UseNameSpace' namespace_name? ';' ;
    # namespace_name : SCALAR_ID;
    def enterUseNameSpace_def(self, ctx:iclParser.UseNameSpace_defContext):
        if(ctx.namespace_name()):
            self.instance_namespace = ctx.namespace_name().SCALAR_ID().getText()
        else:
            self.instance_namespace = "root"

        # If useNameSpace_def is outside of module
        if(ctx.parentCtx.getRuleIndex() != iclParser.RULE_module_item):
            self.instance_namespace_out = self.instance_namespace

    # A UseNameSpace directive found inside a module shall 
    # only have effect until the end of the module statement.
    def exitModule_def(self, ctx:iclParser.Module_defContext):
        self.instance_namespace = self.instance_namespace_out

    #                                                               Things IclPreProcess gathers in module:
    # module_def : 'Module' module_name '{' module_item* '}' ;      <----
    # module_item :   useNameSpace_def |                            <----
    #                 port_def |
    #                 instance_def |                                <----
    #                 scanRegister_def |
    #                 dataRegister_def |
    #                 logicSignal_def |
    #                 scanMux_def |
    #                 dataMux_def |
    #                 clockMux_def |
    #                 oneHotDataGroup_def |
    #                 oneHotScanGroup_def |
    #                 scanInterface_def |
    #                 accessLink_def |
    #                 alias_def |
    #                 enum_def |
    #                 parameter_def |                               <----
    #                 localParameter_def |                          <----
    #                 attribute_def ;    
    def enterModule_def(self, ctx:iclParser.Module_defContext):
        self.current_module_name = ctx.module_name().SCALAR_ID().getText()
        
        if(self.module_definition_name_space not in self.modules):
            self.modules[self.module_definition_name_space] = {}

        self.modules[self.module_definition_name_space][self.current_module_name] = {}
        self.modules[self.module_definition_name_space][self.current_module_name]["module_parser_tree"] = ctx
        self.modules[self.module_definition_name_space][self.current_module_name]["parameters_parser_tree"] = {}
        self.modules[self.module_definition_name_space][self.current_module_name]["local_parameters_parser_tree"] = {}        
        self.modules[self.module_definition_name_space][self.current_module_name]["instances"] = {}

    # parameter_def : 'Parameter' parameter_name '=' parameter_value ';' ;
    # parameter_name : SCALAR_ID;
    def enterParameter_def(self, ctx:iclParser.Parameter_defContext):
        if(ctx.parentCtx.getRuleIndex() != iclParser.RULE_parameter_override):
            parameter_name = ctx.parameter_name().SCALAR_ID().getText()

            if(parameter_name in self.modules[self.module_definition_name_space][self.current_module_name]["parameters_parser_tree"]):
                raise Exception("parameters_parser_tree already defined in module before")
            self.modules[self.module_definition_name_space][self.current_module_name]["parameters_parser_tree"][parameter_name] = ctx

    # localParameter_def : 'LocalParameter' parameter_name '=' parameter_value ';' ;
    # parameter_name : SCALAR_ID;
    def enterLocalParameter_def(self, ctx:iclParser.LocalParameter_defContext):
        if(ctx.parentCtx.getRuleIndex() != iclParser.RULE_parameter_override):
            local_parameter_name = ctx.parameter_name().SCALAR_ID().getText()

            if(local_parameter_name in self.modules[self.module_definition_name_space][self.current_module_name]["local_parameters_parser_tree"]):
                raise Exception("local_parameters_parser_tree already defined in module before")
            self.modules[self.module_definition_name_space][self.current_module_name]["local_parameters_parser_tree"][local_parameter_name] = ctx

    # instance_def : 'Instance' instance_name 'Of' (namespace_name? '::')?
    #                module_name (';' | ( '{' instance_item* '}' ) ) ;
    def enterInstance_def(self, ctx:iclParser.Instance_defContext):
        isntace_name = ctx.instance_name().SCALAR_ID().getText()
        module_name = ctx.module_name().SCALAR_ID().getText()
        
        if(ctx.namespace_name()):
           namespace = ctx.namespace_name().SCALAR_ID().getText()
        else:
           namespace = self.instance_namespace

        if(isntace_name in self.modules[self.module_definition_name_space][self.current_module_name]["instances"]):
            raise Exception("instances already defined in module before")
        self.modules[self.module_definition_name_space][self.current_module_name]["instances"][isntace_name] = [namespace, module_name]