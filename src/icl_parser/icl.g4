// ICL grammar v20130821
grammar icl;
//hier_port
// ICL grammar v20140303
SCALAR_ID : ('a'..'z' | 'A'..'Z')('a'..'z' | 'A'..'Z' | DEC_DIGIT | '_')* ;
// ANTLR4 has all keywords reserved. Since ICL keywords are not reserved, anadditional rule will be required to properly handle.
pos_int : '0' | '1' | POS_INT ;
POS_INT : DEC_DIGIT('_'|DEC_DIGIT)* ;

size : pos_int | '$' SCALAR_ID ;
UNKNOWN_DIGIT : 'X' | 'x';
DEC_DIGIT : '0'..'9' ;
BIN_DIGIT : '0'..'1' | UNKNOWN_DIGIT ;
HEX_DIGIT : '0'..'9' | 'A'..'F' | 'a'..'f' | UNKNOWN_DIGIT ;
DEC_BASE : '\'' ('d' | 'D') (' ' | '\t')*;
BIN_BASE : '\'' ('b' | 'B') (' ' | '\t')*;
HEX_BASE : '\'' ('h' | 'H') (' ' | '\t')*;
UNSIZED_DEC_NUM : DEC_BASE POS_INT ;
UNSIZED_BIN_NUM : BIN_BASE BIN_DIGIT('_'|BIN_DIGIT)* ;
UNSIZED_HEX_NUM : HEX_BASE HEX_DIGIT('_'|HEX_DIGIT)* ;
sized_dec_num : size UNSIZED_DEC_NUM ;
sized_bin_num : size UNSIZED_BIN_NUM ;
sized_hex_num : size UNSIZED_HEX_NUM ;
vector_id : SCALAR_ID '[' (index | rangex) ']' ;
index : integer_expr ;
rangex : index ':' index ;
number : unsized_number | sized_number | integer_expr ;
integer_expr : integer_expr_lvl1 ;
integer_expr_lvl1 : integer_expr_lvl2 ( ('+' | '-') integer_expr_lvl1 )? ;
integer_expr_lvl2 : integer_expr_arg (('*' | '/' | '%') integer_expr_lvl2 )? ;
integer_expr_paren : '(' integer_expr ')'; // Parentheses
integer_expr_arg : integer_expr_paren | pos_int | parameter_ref ;
parameter_ref : '$'(SCALAR_ID) ;
unsized_number : pos_int | UNSIZED_DEC_NUM | UNSIZED_BIN_NUM | UNSIZED_HEX_NUM ;
sized_number : sized_dec_num | sized_bin_num | sized_hex_num;
concat_number : '~'? number (',' '~'? number)* ;


//semantic rules prevents inverting unsized numbers and having more than one
//unsized number within a concat_number. See section 6.4.10.
concat_number_list : concat_number ( '|' concat_number )* ;
hier_port : (instance_name '.')+ port_name ;
port_name : SCALAR_ID | vector_id ;
register_name : SCALAR_ID | vector_id ;
instance_name : SCALAR_ID;
namespace_name : SCALAR_ID;
module_name : SCALAR_ID;
reg_port_signal_id : SCALAR_ID | vector_id;
signal : (number | reg_port_signal_id | hier_port ) ;

reset_signal : '~'? signal ;
scan_signal : '~'? signal ;
data_signal : '~'? signal ;
clock_signal : '~'? signal ;
tck_signal : signal ;
tms_signal : signal ;
trst_signal : signal ;
shiftEn_signal : signal ;
captureEn_signal : signal ;
updateEn_signal : signal ;

concat_reset_signal : (reset_signal | data_signal) ( ',' (reset_signal | data_signal) )*;
concat_scan_signal : (scan_signal | data_signal) ( ',' (scan_signal | data_signal) )*;
concat_data_signal : data_signal ( ',' data_signal)*;
concat_clock_signal : (clock_signal | data_signal)  ( ',' (clock_signal | data_signal))*;
concat_tck_signal : (tck_signal | data_signal) ( ',' (tck_signal | data_signal))*;
concat_shiftEn_signal : (shiftEn_signal | data_signal) ( ',' (shiftEn_signal | data_signal))* ;
concat_captureEn_signal : (captureEn_signal | data_signal) ( ',' (captureEn_signal | data_signal) )*;
concat_updateEn_signal : (updateEn_signal | data_signal) ( ',' (updateEn_signal | data_signal) )*;
concat_tms_signal : (tms_signal | data_signal) ( ',' (tms_signal | data_signal))*;
concat_trst_signal : (trst_signal | data_signal) ( ',' (trst_signal | data_signal) )*;

icl_source : iclSource_items+ ;
iclSource_items : nameSpace_def | useNameSpace_def | module_def;

nameSpace_def : 'NameSpace' namespace_name? ';' ;
useNameSpace_def : 'UseNameSpace' namespace_name? ';' ;

module_def : 'Module' module_name '{' module_item* '}' ;
module_item :   useNameSpace_def |
                port_def |
                instance_def |
                scanRegister_def |
                dataRegister_def |
                logicSignal_def |
                scanMux_def |
                dataMux_def |
                clockMux_def |
                oneHotDataGroup_def |
                oneHotScanGroup_def |
                scanInterface_def |
                accessLink_def |
                alias_def |
                enum_def |
                parameter_def |
                localParameter_def |
                attribute_def ;

port_def :  scanInPort_def |
            scanOutPort_def |
            shiftEnPort_def |
            captureEnPort_def |
            updateEnPort_def |
            dataInPort_def |
            dataOutPort_def |
            toShiftEnPort_def |
            toUpdateEnPort_def |
            toCaptureEnPort_def |
            selectPort_def |
            toSelectPort_def |
            resetPort_def |
            toResetPort_def |
            tmsPort_def |
            toTmsPort_def |
            tckPort_def |
            toTckPort_def |
            clockPort_def |
            toClockPort_def |
            trstPort_def |
            toTrstPort_def |
            toIRSelectPort_def |
            addressPort_def |
            writeEnPort_def |
            readEnPort_def ;

scanInPort_def : 'ScanInPort' scanInPort_name (';' | ( '{' attribute_def* '}' ) ) ;
scanInPort_name : port_name ;

scanOutPort_def : 'ScanOutPort' scanOutPort_name ( ';' | ( '{' scanOutPort_item* '}' ) ) ;
scanOutPort_name : port_name;
scanOutPort_item : attribute_def |
                   scanOutPort_source |
                   scanOutPort_enable ;
scanOutPort_source : 'Source' concat_scan_signal ';';
scanOutPort_enable : 'Enable' data_signal ';';

shiftEnPort_def : 'ShiftEnPort' shiftEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
shiftEnPort_name : port_name ;

captureEnPort_def : 'CaptureEnPort' captureEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
captureEnPort_name : port_name ;

updateEnPort_def : 'UpdateEnPort' updateEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
updateEnPort_name : port_name ;

dataInPort_def : 'DataInPort' dataInPort_name ( ';' | ( '{' dataInPort_item* '}' ) ) ;
dataInPort_name : port_name ;
dataInPort_item : attribute_def |
                  dataInPort_refEnum |
                  dataInPort_defaultLoadValue ;
dataInPort_refEnum : 'RefEnum' enum_name ';' ;
dataInPort_defaultLoadValue : 'DefaultLoadValue' (concat_number | enum_symbol) ';' ;

dataOutPort_def : 'DataOutPort' dataOutPort_name (';' | ( '{' dataOutPort_item* '}' ) ) ;
dataOutPort_name : port_name ;
dataOutPort_item : attribute_def |
                   dataOutPort_source |
                   dataOutPort_enable |
                   dataOutPort_refEnum ;
dataOutPort_source : 'Source' concat_data_signal ';' ;
dataOutPort_enable : 'Enable' data_signal ';' ;
dataOutPort_refEnum : 'RefEnum' enum_name ';' ;

toShiftEnPort_def : 'ToShiftEnPort' toShiftEnPort_name (';' | ( '{' toShiftEnPort_items* '}' ) ) ;
toShiftEnPort_name : port_name ;
toShiftEnPort_items : attribute_def |
                      toShiftEnPort_source ;  
toShiftEnPort_source : 'Source' concat_shiftEn_signal ';' ;

toCaptureEnPort_def : 'ToCaptureEnPort' toCaptureEnPort_name (';' | ( '{' toCaptureEnPort_items* '}' ) ) ;
toCaptureEnPort_name : port_name ;
toCaptureEnPort_items : attribute_def |
                        toCaptureEnPort_source ;
toCaptureEnPort_source : 'Source' captureEn_signal ';' ;

toUpdateEnPort_def : 'ToUpdateEnPort' toUpdateEnPort_name (';' |( '{' toUpdateEnPort_items* '}' ) ) ;
toUpdateEnPort_name : port_name ;
toUpdateEnPort_items : attribute_def | toUpdateEnPort_source ;
toUpdateEnPort_source : 'Source' updateEn_signal ';' ;

selectPort_def : 'SelectPort' selectPort_name (';' |( '{' attribute_def* '}' ) ) ;
selectPort_name : port_name ;

toSelectPort_def : 'ToSelectPort' toSelectPort_name (';' | ( '{' toSelectPort_item+ '}' ) ) ;
toSelectPort_name : port_name ;
toSelectPort_item : attribute_def | toSelectPort_source ;
toSelectPort_source : 'Source' concat_data_signal ';' ;

resetPort_def : 'ResetPort' resetPort_name (';' | ( '{' resetPort_item* '}' ) ) ;
resetPort_name : port_name ;
resetPort_item : attribute_def |
resetPort_polarity ;
resetPort_polarity : 'ActivePolarity' ('0'| '1') ';' ;

toResetPort_def : 'ToResetPort' toResetPort_name (';' | ( '{' toResetPort_item+ '}' ) ) ;
toResetPort_name : port_name ;
toResetPort_item : attribute_def |
                   toResetPort_source |
                   toResetPort_polarity;
toResetPort_source : 'Source' concat_reset_signal ';' ;
toResetPort_polarity : 'ActivePolarity' ('0'| '1') ';' ;

tmsPort_def : 'TMSPort' tmsPort_name (';' | ( '{' attribute_def*'}' ) ) ;
tmsPort_name : port_name ;

toTmsPort_def : 'ToTMSPort' toTmsPort_name (';' | ( '{' toTmsPort_item* '}' ) ) ;
toTmsPort_name : port_name ;
toTmsPort_item : attribute_def |
toTmsPort_source ;
toTmsPort_source : 'Source' concat_tms_signal ';' ;

toIRSelectPort_def : 'ToIRSelectPort' toIRSelectPort_name (';' |
            ( '{' attribute_def* '}' )) ;
toIRSelectPort_name : port_name ;

tckPort_def : 'TCKPort' tckPort_name (';' | ( '{' attribute_def* '}' ) ) ;
tckPort_name : port_name ;
toTckPort_def : 'ToTCKPort' toTckPort_name (';' | ( '{' attribute_def* '}' ) ) ;
toTckPort_name : port_name ;

clockPort_def : 'ClockPort' clockPort_name (';' | ( '{' clockPort_item* '}' ));
clockPort_name : port_name ;
clockPort_item : attribute_def | clockPort_diffPort ;
clockPort_diffPort : 'DifferentialInvOf' concat_clock_signal ';' ;
toClockPort_def : 'ToClockPort' toClockPort_name (';' | ( '{' toClockPort_item+ '}' ) ) ;
toClockPort_name : port_name ;
toClockPort_item :  attribute_def |
                    toClockPort_source |
                    freqMultiplier_def |
                    freqDivider_def |
                    differentialInvOf_def |
                    period_def ;
toClockPort_source : 'Source' concat_clock_signal ';' ;

freqMultiplier_def : 'FreqMultiplier' pos_int ';' ;
freqDivider_def : 'FreqDivider' pos_int ';' ;
differentialInvOf_def : 'DifferentialInvOf' concat_clock_signal ';' ;

period_def : 'Period' pos_int ('s' | 'ms' | 'us' | 'ns' | 'ps' | 'fs' | 'as')? ';' ;
trstPort_def : 'TRSTPort' trstPort_name (';' | ( '{' attribute_def* '}' ) ) ;
trstPort_name : port_name ;

toTrstPort_def : 'ToTRSTPort' toTrstPort_name (';' | ( '{' toTrstPort_item+ '}' ) ) ;
toTrstPort_name : port_name ;
toTrstPort_item : attribute_def |
                  toTrstPort_source ;
toTrstPort_source : 'Source' concat_trst_signal ';' ;

addressPort_def : 'AddressPort' addressPort_name (';' | ( '{' attribute_def*'}' ) ) ;
addressPort_name : port_name ;

writeEnPort_def : 'WriteEnPort' writeEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
writeEnPort_name : port_name ;

readEnPort_def : 'ReadEnPort' readEnPort_name (';' | ( '{' attribute_def* '}' ) ) ;
readEnPort_name : port_name ;

instance_def : 'Instance' instance_name 'Of' (namespace_name? '::')?
                module_name (';' | ( '{' instance_item* '}' ) ) ;
instance_item : inputPort_connection |
                allowBroadcast_def |
                attribute_def |
                parameter_override |
                instance_addressValue ;
inputPort_connection : 'InputPort' inputPort_name '=' inputPort_source ';' ;
allowBroadcast_def : 'AllowBroadcastOnScanInterface' scanInterface_name ';' ;
inputPort_name : port_name ;
inputPort_source : concat_reset_signal |
                concat_scan_signal |
                concat_data_signal |
                concat_clock_signal |
                concat_tck_signal |
                concat_shiftEn_signal |
                concat_captureEn_signal |
                concat_updateEn_signal |
                concat_tms_signal |
                concat_trst_signal ;
parameter_override : parameter_def;
instance_addressValue : 'AddressValue' number ';' ;

scanRegister_def : 'ScanRegister' scanRegister_name (';' |
                '{' scanRegister_item* '}') ;
scanRegister_name : register_name ;
scanRegister_item : attribute_def |
                    scanRegister_scanInSource |
                    scanRegister_defaultLoadValue |
                    scanRegister_captureSource |
                    scanRegister_resetValue |
                    scanRegister_refEnum ;
scanRegister_scanInSource : 'ScanInSource' scan_signal ';' ;
scanRegister_defaultLoadValue : 'DefaultLoadValue' (concat_number | enum_symbol) ';' ;
scanRegister_captureSource : 'CaptureSource' (concat_data_signal | enum_symbol) ';';
scanRegister_resetValue : 'ResetValue' (concat_number | enum_symbol)';' ;
scanRegister_refEnum : 'RefEnum' enum_name ';' ;

dataRegister_def : 'DataRegister' dataRegister_name (';' | ( '{' dataRegister_item+ '}' ) ) ;
dataRegister_name : register_name ;
dataRegister_item : dataRegister_type |
                    dataRegister_common ;
dataRegister_type : dataRegister_selectable |
                    dataRegister_addressable |
                    dataRegister_readCallBack |
                    dataRegister_writeCallBack ;
// Common to all types:
dataRegister_common : dataRegister_resetValue |
                      dataRegister_defaultLoadValue |
                      dataRegister_refEnum |
                      attribute_def ;
dataRegister_resetValue : 'ResetValue' (concat_number | enum_symbol) ';';
dataRegister_defaultLoadValue : 'DefaultLoadValue' (concat_number | enum_symbol)';' ;
dataRegister_refEnum : 'RefEnum' enum_name ';' ;
//For Selectable Data Register:
dataRegister_selectable : dataRegister_writeEnSource |
dataRegister_writeDataSource;
dataRegister_writeEnSource : 'WriteEnSource' '~'? data_signal ';' ;
dataRegister_writeDataSource : 'WriteDataSource' concat_data_signal ';' ;
// Addressable Data Register:
dataRegister_addressable : dataRegister_addressValue;
dataRegister_addressValue : 'AddressValue' number ';' ;
// CallBack Data Register:
dataRegister_readCallBack : dataRegister_readCallBack_proc |
dataRegister_readDataSource ;
dataRegister_readCallBack_proc : 'ReadCallBack' iProc_namespace iProc_name iProc_args* ';';
dataRegister_readDataSource : 'ReadDataSource' concat_data_signal ';' ;
dataRegister_writeCallBack : 'WriteCallBack' iProc_namespace iProc_name iProc_args* ';' ;
iProc_namespace : (namespace_name? '::')? ref_module_name ( '::' sub_namespace )? ;
iProc_name : SCALAR_ID | parameter_ref ;
iProc_args : '<D>' |
             '<R>' |
             number |
             STRING |
             parameter_ref ;
sub_namespace : SCALAR_ID |
                parameter_ref ;
ref_module_name : SCALAR_ID |
                  parameter_ref ;
logicSignal_def : 'LogicSignal' logicSignal_name '{' logic_expr ';' '}' ;
logicSignal_name : reg_port_signal_id;
logic_expr : logic_expr_lvl1 ;
logic_expr_lvl1 : logic_expr_lvl2 ( ('&&' | '||') logic_expr_lvl1 )? ;
logic_expr_lvl2 : logic_expr_lvl3 ( ('&' | '|' | '^') logic_expr_lvl2 )? |
                  ( ('&' | '|' | '^') logic_expr_lvl2 );
logic_expr_lvl3 : logic_expr_lvl4 ( ('==' | '!=') logic_expr_num_arg )?;
logic_expr_lvl4 : logic_expr_arg (',' logic_expr_lvl4 )?;
logic_unary_expr : ('~'|'!') logic_expr_arg;
logic_expr_paren : '(' logic_expr ')';
logic_expr_arg : logic_expr_paren |
                 logic_unary_expr |
                 concat_data_signal ;
logic_expr_num_arg : concat_number |
                     enum_name |
                     '(' logic_expr_num_arg ')' ;

scanMux_def : 'ScanMux' scanMux_name 'SelectedBy' scanMux_select '{' scanMux_selection+ '}' ;
scanMux_name : reg_port_signal_id ;
scanMux_select : concat_data_signal ;
scanMux_selection : concat_number_list':' concat_scan_signal ';' ;
dataMux_def : 'DataMux' dataMux_name 'SelectedBy' dataMux_select '{' dataMux_selection+ '}' ;
dataMux_name : reg_port_signal_id ;
dataMux_select : concat_data_signal ;
dataMux_selection : concat_number_list':' concat_data_signal ';' ;

clockMux_def : 'ClockMux' clockMux_name 'SelectedBy' clockMux_select '{' clockMux_selection+ '}' ;
clockMux_name : reg_port_signal_id ;
clockMux_select : concat_data_signal ;
clockMux_selection : concat_number_list':' concat_clock_signal ';' ;

oneHotScanGroup_def : 'OneHotScanGroup' oneHotScanGroup_name '{' oneHotScanGroup_item+ '}' ;
oneHotScanGroup_name : reg_port_signal_id ;
oneHotScanGroup_item : 'Port' concat_scan_signal ';' ;
oneHotDataGroup_def : 'OneHotDataGroup' oneHotDataGroup_name '{' oneHotDataGroup_item+ '}' ;
oneHotDataGroup_name : reg_port_signal_id ;
oneHotDataGroup_item : instance_def |
                       dataRegister_def |
                       oneHotDataGroup_portSource ;
oneHotDataGroup_portSource : 'Port' concat_data_signal ';' ;

scanInterface_def : 'ScanInterface' scanInterface_name '{' scanInterface_item+ '}' ;
scanInterface_name : SCALAR_ID;
scanInterface_item : attribute_def |
                     scanInterfacePort_def |
                     defaultLoad_def |
                     scanInterfaceChain_def ;
scanInterfacePort_def : 'Port' reg_port_signal_id ';';
scanInterfaceChain_def : 'Chain' scanInterfaceChain_name '{' scanInterfaceChain_item+ '}' ;
scanInterfaceChain_name : SCALAR_ID;
scanInterfaceChain_item : attribute_def |
                          scanInterfacePort_def |
                          defaultLoad_def ;
defaultLoad_def : 'DefaultLoadValue' concat_number ';' ;
accessLink_def : accessLink1149_def | AccessLinkGeneric_def ;

// Actual parser will need to add gated semantic predicate here or rule will
// match 1149 definition as well
AccessLinkGeneric_def : 'AccessLink' SPACE SCALAR_ID SPACE 'Of' SPACE
SCALAR_ID SPACE? ;
fragment AccessLinkGeneric_block :'{' ( AccessLinkGeneric_block |
AccessLinkGeneric_text | SPACE | STRING )* '}' ;
fragment AccessLinkGeneric_text : [^{}"\t\n\r ]+; // Not used in ANTLR parser,
accessLink_genericID : SCALAR_ID;
accessLink1149_def : 'AccessLink'
accessLink_name 'Of' ('STD_1149_1_2001' | 'STD_1149_1_2013')'{' 'BSDLEntity' bsdlEntity_name ';'bsdl_instr_ref+ '}' ;
accessLink_name : SCALAR_ID;
bsdlEntity_name : SCALAR_ID ;
bsdl_instr_ref : bsdl_instr_name '{' bsdl_instr_selected_item+ '}' ;
bsdl_instr_name : SCALAR_ID ;
bsdl_instr_selected_item : 'ScanInterface''{' (accessLink1149_ScanInterface_name ';')+ '}' |
                            ('ActiveSignals''{'(accessLink1149_ActiveSignal_name ';')+ '}' ) ;
accessLink1149_ActiveSignal_name : reg_port_signal_id ;
accessLink1149_ScanInterface_name : instance_name('.' scanInterface_name)? ;

alias_def : 'Alias' alias_name '=' concat_hier_data_signal (';' | ('{' alias_item+ '}' ) ) ;
alias_name : reg_port_signal_id;
alias_item : attribute_def |
            'AccessTogether' ';' |
            alias_iApplyEndState |
            alias_refEnum ;
alias_iApplyEndState : 'iApplyEndState' concat_number ';' ;
alias_refEnum : 'RefEnum' enum_name ';' ;
concat_hier_data_signal : '~'? hier_data_signal (',' '~'? hier_data_signal)* ;
hier_data_signal : (instance_name '.')* reg_port_signal_id ;

enum_def : 'Enum' enum_name '{' enum_item+ '}' ;
enum_name : SCALAR_ID ;
enum_item : enum_symbol '=' enum_value ';' ;
enum_symbol : SCALAR_ID;
enum_value : concat_number;

parameter_def : 'Parameter' parameter_name '=' parameter_value ';' ;
localParameter_def : 'LocalParameter' parameter_name '=' parameter_value ';' ;
parameter_name : SCALAR_ID;
parameter_value : concat_string | concat_number;
concat_string : (STRING | parameter_ref) (',' (STRING | parameter_ref) )* ;

attribute_def : 'Attribute' attribute_name ('=' attribute_value )? ';' ;
attribute_name : SCALAR_ID;
attribute_value : (concat_string | concat_number) ;

STRING : '"' (~('"'|'\\')|'\\\\'|'\\"')* '"' ;
SPACE : ( ' ' | '\t' | ('\r'? '\n') )+ -> skip ;

// Multi-line Comments
ML_COMMENT : '/*' .*? '*/' -> skip ;

// Single-line Comments
SL_COMMENT : '//' (~('\r'|'\n')*) '\r'? '\n' -> skip ;

