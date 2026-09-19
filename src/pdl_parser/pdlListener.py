# Generated from pdl.g4 by ANTLR 4.7.2
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .pdlParser import pdlParser
else:
    from pdlParser import pdlParser

# This class defines a complete listener for a parse tree produced by pdlParser.
class pdlListener(ParseTreeListener):

    # Enter a parse tree produced by pdlParser#pdl_source.
    def enterPdl_source(self, ctx:pdlParser.Pdl_sourceContext):
        pass

    # Exit a parse tree produced by pdlParser#pdl_source.
    def exitPdl_source(self, ctx:pdlParser.Pdl_sourceContext):
        pass


    # Enter a parse tree produced by pdlParser#flat_commands.
    def enterFlat_commands(self, ctx:pdlParser.Flat_commandsContext):
        pass

    # Exit a parse tree produced by pdlParser#flat_commands.
    def exitFlat_commands(self, ctx:pdlParser.Flat_commandsContext):
        pass


    # Enter a parse tree produced by pdlParser#dot_id.
    def enterDot_id(self, ctx:pdlParser.Dot_idContext):
        pass

    # Exit a parse tree produced by pdlParser#dot_id.
    def exitDot_id(self, ctx:pdlParser.Dot_idContext):
        pass


    # Enter a parse tree produced by pdlParser#scalar_id.
    def enterScalar_id(self, ctx:pdlParser.Scalar_idContext):
        pass

    # Exit a parse tree produced by pdlParser#scalar_id.
    def exitScalar_id(self, ctx:pdlParser.Scalar_idContext):
        pass


    # Enter a parse tree produced by pdlParser#keyword.
    def enterKeyword(self, ctx:pdlParser.KeywordContext):
        pass

    # Exit a parse tree produced by pdlParser#keyword.
    def exitKeyword(self, ctx:pdlParser.KeywordContext):
        pass


    # Enter a parse tree produced by pdlParser#instancePath.
    def enterInstancePath(self, ctx:pdlParser.InstancePathContext):
        pass

    # Exit a parse tree produced by pdlParser#instancePath.
    def exitInstancePath(self, ctx:pdlParser.InstancePathContext):
        pass


    # Enter a parse tree produced by pdlParser#scanInterface_name.
    def enterScanInterface_name(self, ctx:pdlParser.ScanInterface_nameContext):
        pass

    # Exit a parse tree produced by pdlParser#scanInterface_name.
    def exitScanInterface_name(self, ctx:pdlParser.ScanInterface_nameContext):
        pass


    # Enter a parse tree produced by pdlParser#port.
    def enterPort(self, ctx:pdlParser.PortContext):
        pass

    # Exit a parse tree produced by pdlParser#port.
    def exitPort(self, ctx:pdlParser.PortContext):
        pass


    # Enter a parse tree produced by pdlParser#reg_or_port.
    def enterReg_or_port(self, ctx:pdlParser.Reg_or_portContext):
        pass

    # Exit a parse tree produced by pdlParser#reg_or_port.
    def exitReg_or_port(self, ctx:pdlParser.Reg_or_portContext):
        pass


    # Enter a parse tree produced by pdlParser#reg_port_or_instance.
    def enterReg_port_or_instance(self, ctx:pdlParser.Reg_port_or_instanceContext):
        pass

    # Exit a parse tree produced by pdlParser#reg_port_or_instance.
    def exitReg_port_or_instance(self, ctx:pdlParser.Reg_port_or_instanceContext):
        pass


    # Enter a parse tree produced by pdlParser#hier_signal.
    def enterHier_signal(self, ctx:pdlParser.Hier_signalContext):
        pass

    # Exit a parse tree produced by pdlParser#hier_signal.
    def exitHier_signal(self, ctx:pdlParser.Hier_signalContext):
        pass


    # Enter a parse tree produced by pdlParser#reg_port_signal_id.
    def enterReg_port_signal_id(self, ctx:pdlParser.Reg_port_signal_idContext):
        pass

    # Exit a parse tree produced by pdlParser#reg_port_signal_id.
    def exitReg_port_signal_id(self, ctx:pdlParser.Reg_port_signal_idContext):
        pass


    # Enter a parse tree produced by pdlParser#vector_id.
    def enterVector_id(self, ctx:pdlParser.Vector_idContext):
        pass

    # Exit a parse tree produced by pdlParser#vector_id.
    def exitVector_id(self, ctx:pdlParser.Vector_idContext):
        pass


    # Enter a parse tree produced by pdlParser#index.
    def enterIndex(self, ctx:pdlParser.IndexContext):
        pass

    # Exit a parse tree produced by pdlParser#index.
    def exitIndex(self, ctx:pdlParser.IndexContext):
        pass


    # Enter a parse tree produced by pdlParser#pdl_range.
    def enterPdl_range(self, ctx:pdlParser.Pdl_rangeContext):
        pass

    # Exit a parse tree produced by pdlParser#pdl_range.
    def exitPdl_range(self, ctx:pdlParser.Pdl_rangeContext):
        pass


    # Enter a parse tree produced by pdlParser#enum_name.
    def enterEnum_name(self, ctx:pdlParser.Enum_nameContext):
        pass

    # Exit a parse tree produced by pdlParser#enum_name.
    def exitEnum_name(self, ctx:pdlParser.Enum_nameContext):
        pass


    # Enter a parse tree produced by pdlParser#instance_name.
    def enterInstance_name(self, ctx:pdlParser.Instance_nameContext):
        pass

    # Exit a parse tree produced by pdlParser#instance_name.
    def exitInstance_name(self, ctx:pdlParser.Instance_nameContext):
        pass


    # Enter a parse tree produced by pdlParser#cycleCount.
    def enterCycleCount(self, ctx:pdlParser.CycleCountContext):
        pass

    # Exit a parse tree produced by pdlParser#cycleCount.
    def exitCycleCount(self, ctx:pdlParser.CycleCountContext):
        pass


    # Enter a parse tree produced by pdlParser#sysClock.
    def enterSysClock(self, ctx:pdlParser.SysClockContext):
        pass

    # Exit a parse tree produced by pdlParser#sysClock.
    def exitSysClock(self, ctx:pdlParser.SysClockContext):
        pass


    # Enter a parse tree produced by pdlParser#sourceClock.
    def enterSourceClock(self, ctx:pdlParser.SourceClockContext):
        pass

    # Exit a parse tree produced by pdlParser#sourceClock.
    def exitSourceClock(self, ctx:pdlParser.SourceClockContext):
        pass


    # Enter a parse tree produced by pdlParser#chain_id.
    def enterChain_id(self, ctx:pdlParser.Chain_idContext):
        pass

    # Exit a parse tree produced by pdlParser#chain_id.
    def exitChain_id(self, ctx:pdlParser.Chain_idContext):
        pass


    # Enter a parse tree produced by pdlParser#length.
    def enterLength(self, ctx:pdlParser.LengthContext):
        pass

    # Exit a parse tree produced by pdlParser#length.
    def exitLength(self, ctx:pdlParser.LengthContext):
        pass


    # Enter a parse tree produced by pdlParser#procName.
    def enterProcName(self, ctx:pdlParser.ProcNameContext):
        pass

    # Exit a parse tree produced by pdlParser#procName.
    def exitProcName(self, ctx:pdlParser.ProcNameContext):
        pass


    # Enter a parse tree produced by pdlParser#pdl_number.
    def enterPdl_number(self, ctx:pdlParser.Pdl_numberContext):
        pass

    # Exit a parse tree produced by pdlParser#pdl_number.
    def exitPdl_number(self, ctx:pdlParser.Pdl_numberContext):
        pass


    # Enter a parse tree produced by pdlParser#tvalue.
    def enterTvalue(self, ctx:pdlParser.TvalueContext):
        pass

    # Exit a parse tree produced by pdlParser#tvalue.
    def exitTvalue(self, ctx:pdlParser.TvalueContext):
        pass


    # Enter a parse tree produced by pdlParser#eoc.
    def enterEoc(self, ctx:pdlParser.EocContext):
        pass

    # Exit a parse tree produced by pdlParser#eoc.
    def exitEoc(self, ctx:pdlParser.EocContext):
        pass


    # Enter a parse tree produced by pdlParser#pdl_level_def.
    def enterPdl_level_def(self, ctx:pdlParser.Pdl_level_defContext):
        pass

    # Exit a parse tree produced by pdlParser#pdl_level_def.
    def exitPdl_level_def(self, ctx:pdlParser.Pdl_level_defContext):
        pass


    # Enter a parse tree produced by pdlParser#pdl_level.
    def enterPdl_level(self, ctx:pdlParser.Pdl_levelContext):
        pass

    # Exit a parse tree produced by pdlParser#pdl_level.
    def exitPdl_level(self, ctx:pdlParser.Pdl_levelContext):
        pass


    # Enter a parse tree produced by pdlParser#versionString.
    def enterVersionString(self, ctx:pdlParser.VersionStringContext):
        pass

    # Exit a parse tree produced by pdlParser#versionString.
    def exitVersionString(self, ctx:pdlParser.VersionStringContext):
        pass


    # Enter a parse tree produced by pdlParser#iprocsformodule_def.
    def enterIprocsformodule_def(self, ctx:pdlParser.Iprocsformodule_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iprocsformodule_def.
    def exitIprocsformodule_def(self, ctx:pdlParser.Iprocsformodule_defContext):
        pass


    # Enter a parse tree produced by pdlParser#module_name.
    def enterModule_name(self, ctx:pdlParser.Module_nameContext):
        pass

    # Exit a parse tree produced by pdlParser#module_name.
    def exitModule_name(self, ctx:pdlParser.Module_nameContext):
        pass


    # Enter a parse tree produced by pdlParser#icl_namespace_name.
    def enterIcl_namespace_name(self, ctx:pdlParser.Icl_namespace_nameContext):
        pass

    # Exit a parse tree produced by pdlParser#icl_namespace_name.
    def exitIcl_namespace_name(self, ctx:pdlParser.Icl_namespace_nameContext):
        pass


    # Enter a parse tree produced by pdlParser#pdl_namespace_name.
    def enterPdl_namespace_name(self, ctx:pdlParser.Pdl_namespace_nameContext):
        pass

    # Exit a parse tree produced by pdlParser#pdl_namespace_name.
    def exitPdl_namespace_name(self, ctx:pdlParser.Pdl_namespace_nameContext):
        pass


    # Enter a parse tree produced by pdlParser#iuseprocnamespace_def.
    def enterIuseprocnamespace_def(self, ctx:pdlParser.Iuseprocnamespace_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iuseprocnamespace_def.
    def exitIuseprocnamespace_def(self, ctx:pdlParser.Iuseprocnamespace_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iproc_def.
    def enterIproc_def(self, ctx:pdlParser.Iproc_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iproc_def.
    def exitIproc_def(self, ctx:pdlParser.Iproc_defContext):
        pass


    # Enter a parse tree produced by pdlParser#commands.
    def enterCommands(self, ctx:pdlParser.CommandsContext):
        pass

    # Exit a parse tree produced by pdlParser#commands.
    def exitCommands(self, ctx:pdlParser.CommandsContext):
        pass


    # Enter a parse tree produced by pdlParser#argument.
    def enterArgument(self, ctx:pdlParser.ArgumentContext):
        pass

    # Exit a parse tree produced by pdlParser#argument.
    def exitArgument(self, ctx:pdlParser.ArgumentContext):
        pass


    # Enter a parse tree produced by pdlParser#argWithDefault.
    def enterArgWithDefault(self, ctx:pdlParser.ArgWithDefaultContext):
        pass

    # Exit a parse tree produced by pdlParser#argWithDefault.
    def exitArgWithDefault(self, ctx:pdlParser.ArgWithDefaultContext):
        pass


    # Enter a parse tree produced by pdlParser#args.
    def enterArgs(self, ctx:pdlParser.ArgsContext):
        pass

    # Exit a parse tree produced by pdlParser#args.
    def exitArgs(self, ctx:pdlParser.ArgsContext):
        pass


    # Enter a parse tree produced by pdlParser#command.
    def enterCommand(self, ctx:pdlParser.CommandContext):
        pass

    # Exit a parse tree produced by pdlParser#command.
    def exitCommand(self, ctx:pdlParser.CommandContext):
        pass


    # Enter a parse tree produced by pdlParser#iprefix_def.
    def enterIprefix_def(self, ctx:pdlParser.Iprefix_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iprefix_def.
    def exitIprefix_def(self, ctx:pdlParser.Iprefix_defContext):
        pass


    # Enter a parse tree produced by pdlParser#icall_def.
    def enterIcall_def(self, ctx:pdlParser.Icall_defContext):
        pass

    # Exit a parse tree produced by pdlParser#icall_def.
    def exitIcall_def(self, ctx:pdlParser.Icall_defContext):
        pass


    # Enter a parse tree produced by pdlParser#ireset_def.
    def enterIreset_def(self, ctx:pdlParser.Ireset_defContext):
        pass

    # Exit a parse tree produced by pdlParser#ireset_def.
    def exitIreset_def(self, ctx:pdlParser.Ireset_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iread_def.
    def enterIread_def(self, ctx:pdlParser.Iread_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iread_def.
    def exitIread_def(self, ctx:pdlParser.Iread_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iwrite_def.
    def enterIwrite_def(self, ctx:pdlParser.Iwrite_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iwrite_def.
    def exitIwrite_def(self, ctx:pdlParser.Iwrite_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iscan_def.
    def enterIscan_def(self, ctx:pdlParser.Iscan_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iscan_def.
    def exitIscan_def(self, ctx:pdlParser.Iscan_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iscan_data.
    def enterIscan_data(self, ctx:pdlParser.Iscan_dataContext):
        pass

    # Exit a parse tree produced by pdlParser#iscan_data.
    def exitIscan_data(self, ctx:pdlParser.Iscan_dataContext):
        pass


    # Enter a parse tree produced by pdlParser#ioverridescaninterface_def.
    def enterIoverridescaninterface_def(self, ctx:pdlParser.Ioverridescaninterface_defContext):
        pass

    # Exit a parse tree produced by pdlParser#ioverridescaninterface_def.
    def exitIoverridescaninterface_def(self, ctx:pdlParser.Ioverridescaninterface_defContext):
        pass


    # Enter a parse tree produced by pdlParser#scanInterfaceRef_list.
    def enterScanInterfaceRef_list(self, ctx:pdlParser.ScanInterfaceRef_listContext):
        pass

    # Exit a parse tree produced by pdlParser#scanInterfaceRef_list.
    def exitScanInterfaceRef_list(self, ctx:pdlParser.ScanInterfaceRef_listContext):
        pass


    # Enter a parse tree produced by pdlParser#scanInterfaceRef.
    def enterScanInterfaceRef(self, ctx:pdlParser.ScanInterfaceRefContext):
        pass

    # Exit a parse tree produced by pdlParser#scanInterfaceRef.
    def exitScanInterfaceRef(self, ctx:pdlParser.ScanInterfaceRefContext):
        pass


    # Enter a parse tree produced by pdlParser#iapply_def.
    def enterIapply_def(self, ctx:pdlParser.Iapply_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iapply_def.
    def exitIapply_def(self, ctx:pdlParser.Iapply_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iclock_def.
    def enterIclock_def(self, ctx:pdlParser.Iclock_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iclock_def.
    def exitIclock_def(self, ctx:pdlParser.Iclock_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iclock_override_def.
    def enterIclock_override_def(self, ctx:pdlParser.Iclock_override_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iclock_override_def.
    def exitIclock_override_def(self, ctx:pdlParser.Iclock_override_defContext):
        pass


    # Enter a parse tree produced by pdlParser#irunloop_def.
    def enterIrunloop_def(self, ctx:pdlParser.Irunloop_defContext):
        pass

    # Exit a parse tree produced by pdlParser#irunloop_def.
    def exitIrunloop_def(self, ctx:pdlParser.Irunloop_defContext):
        pass


    # Enter a parse tree produced by pdlParser#imerge_def.
    def enterImerge_def(self, ctx:pdlParser.Imerge_defContext):
        pass

    # Exit a parse tree produced by pdlParser#imerge_def.
    def exitImerge_def(self, ctx:pdlParser.Imerge_defContext):
        pass


    # Enter a parse tree produced by pdlParser#itake_def.
    def enterItake_def(self, ctx:pdlParser.Itake_defContext):
        pass

    # Exit a parse tree produced by pdlParser#itake_def.
    def exitItake_def(self, ctx:pdlParser.Itake_defContext):
        pass


    # Enter a parse tree produced by pdlParser#irelease_def.
    def enterIrelease_def(self, ctx:pdlParser.Irelease_defContext):
        pass

    # Exit a parse tree produced by pdlParser#irelease_def.
    def exitIrelease_def(self, ctx:pdlParser.Irelease_defContext):
        pass


    # Enter a parse tree produced by pdlParser#inote_def.
    def enterInote_def(self, ctx:pdlParser.Inote_defContext):
        pass

    # Exit a parse tree produced by pdlParser#inote_def.
    def exitInote_def(self, ctx:pdlParser.Inote_defContext):
        pass


    # Enter a parse tree produced by pdlParser#istate_def.
    def enterIstate_def(self, ctx:pdlParser.Istate_defContext):
        pass

    # Exit a parse tree produced by pdlParser#istate_def.
    def exitIstate_def(self, ctx:pdlParser.Istate_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iget_read_data_def.
    def enterIget_read_data_def(self, ctx:pdlParser.Iget_read_data_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iget_read_data_def.
    def exitIget_read_data_def(self, ctx:pdlParser.Iget_read_data_defContext):
        pass


    # Enter a parse tree produced by pdlParser#pdl_format.
    def enterPdl_format(self, ctx:pdlParser.Pdl_formatContext):
        pass

    # Exit a parse tree produced by pdlParser#pdl_format.
    def exitPdl_format(self, ctx:pdlParser.Pdl_formatContext):
        pass


    # Enter a parse tree produced by pdlParser#iget_miscompares_def.
    def enterIget_miscompares_def(self, ctx:pdlParser.Iget_miscompares_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iget_miscompares_def.
    def exitIget_miscompares_def(self, ctx:pdlParser.Iget_miscompares_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iget_status_def.
    def enterIget_status_def(self, ctx:pdlParser.Iget_status_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iget_status_def.
    def exitIget_status_def(self, ctx:pdlParser.Iget_status_defContext):
        pass


    # Enter a parse tree produced by pdlParser#iset_fail_def.
    def enterIset_fail_def(self, ctx:pdlParser.Iset_fail_defContext):
        pass

    # Exit a parse tree produced by pdlParser#iset_fail_def.
    def exitIset_fail_def(self, ctx:pdlParser.Iset_fail_defContext):
        pass


    # Enter a parse tree produced by pdlParser#text_message.
    def enterText_message(self, ctx:pdlParser.Text_messageContext):
        pass

    # Exit a parse tree produced by pdlParser#text_message.
    def exitText_message(self, ctx:pdlParser.Text_messageContext):
        pass


