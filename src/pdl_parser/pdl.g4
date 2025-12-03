// PDL0 grammar v20130806
grammar PDL;

pdl_source : (WS | eoc | pdl_level_def | iprocsformodule_def | iuseprocnamespace_def | iproc_def | SL_COMMENT)+ ;

// ===========
// Identifiers
// ===========
dot_id : scalar_id ( '.' scalar_id )*;
scalar_id : SCALAR_ID | keyword; // keywords are not reserved
keyword : 'iPDLLevel' |
          'iProcsForModule' |
          'iProc' |
          'iPrefix' |
          'iCall' |
          'iReset' |
          'iUseProcNameSpace' |
          'iRead' |
          'iWrite' |
          'iScan' |
          'iApply' |
          'iNote' |
          'iTake' |
          'iRelease' |
          'iMerge' |
          'iClock' |
          'iClockOverride' |
          'iRunLoop'|
          'iOverrideScanInterface' |
          'iState' |
          'iGetReadData' |
          'iGetMiscompares' |
          'iGetStatus' |
          'iSetFail' |
          'on' |
          'off'; // Keywords in ANTLR4 are reserved,
// non-reserved keywords must be listed explicitly.
// The list here may be incomplete for ANTLR4.

// *******************
// Generic Identifiers
// *******************
instancePath : dot_id;
scanInterface_name : (instancePath DOT)? scalar_id 
port: hier_signal ;
reg_or_port: hier_signal ;
reg_port_or_instance : hier_signal ;
hier_signal : (instancePath DOT)? reg_port_signal_id | ARGUMENT_REF ;

reg_port_signal_id: scalar_id | vector_id ;
vector_id:     scalar_id LBRACKET ( index | range ) RBRACKET
            |  scalar_id LPAREN   ( index | range ) RPAREN;
index : pdl_number;
range : index COLON index ;
enum_name : scalar_id ;
instance_name : scalar_id ;

// **************
// Generic Tokens
// **************
SCALAR_ID : ('a'..'z' | 'A'..'Z')('a'..'z' | 'A'..'Z' | '0'..'9' | '_')*;
ARGUMENT_REF : '$' SCALAR_ID;
LBRACKET : '[';
RBRACKET : ']';
LPAREN : '(';
RPAREN : ')';
COLON : ':';
DOT : '.';

// ==============
// Command tokens
// ==============
cycleCount : pdl_number ;
sysClock : hier_signal ;
sourceClock : hier_signal ;
chain_id: scalar_id;
length : POS_INT ;
procName : scalar_id ;

// =======
// Numbers
// =======
pdl_number : POS_INT | TCL_HEX_NUMBER | TCL_BIN_NUMBER | ARGUMENT_REF;
POS_INT: ('0'..'9')+;
TCL_HEX_NUMBER : '0x' ( '0'..'9' | 'A'..'F' | 'a'..'f' | 'x' | 'X' )+;
TCL_BIN_NUMBER : '0b' ( '0'..'1' | 'x' | 'X' )+;
ISCAN_HEX_NUMBER : '{' WS? '0x' ( '0'..'9' | 'A'..'F' | 'a'..'f' | 'x' | 'X' | WS | NL )+ '}'
                 | '"' WS? '0x' ( '0'..'9' | 'A'..'F' | 'a'..'f' | 'x' | 'X' | WS | NL )+ '"' ;
ISCAN_BIN_NUMBER :    '{' WS? '0b' ( '0'..'1' | 'x' | 'X' | WS | NL )+ '}'
                    | '"' WS? '0b' ( '0'..'1' | 'x' | 'X' | WS | NL )+ '"' ;
tvalue : (EVALUE | DVALUE)TSUFFIX ;
EVALUE : POS_INT'.'POS_INT'e-'POS_INT ;
DVALUE : POS_INT'.'POS_INT ;
TSUFFIX : 's' | 'ms' | 'us' | 'ns' | 'ps' | 'fs' | 'as' ;

// ====================
// Comments and Whitespace
// ====================
SL_COMMENT : '#' (~('\r'|'\n'))* ;
WS : ( ' ' | '\t' | '\\' '\r'? '\n' )+ ;
QUOTED : '"' (~('\"'))* '"' ; // Collapse into one token (mainly for iNote)
eoc : SEMICOLON | NL;
SEMICOLON : ';';
NL : '\r'? '\n' ;

// =======
// Commands
// =======
pdl_level_def : 'iPDLLevel' WS pdl_level WS '-version' WS versionString eoc ;
pdl_level : '0' | '1';
versionString : 'STD_1687_2014' ;
// -------
iprocsformodule_def : 'iProcsForModule' WS module_name (WS '-iProcNameSpace' WS pdl_namespace_name)? eoc ;
module_name : (icl_namespace_name '::')? scalar_id ;
icl_namespace_name : scalar_id;
pdl_namespace_name : scalar_id;
// -------
iuseprocnamespace_def : 'iUseProcNameSpace' (pdl_namespace_name|'-') ;
// -------
iproc_def : 'iProc' WS procName WS '{' (WS? argument ( WS argument )* WS? | WS?) '}' WS '{' commands '}' eoc ;
commands : command* ;
argument : scalar_id | ( '{' WS? argWithDefault WS? '}' ) ;
argWithDefault : scalar_id WS args ;
args : pdl_number | enum_name | reg_or_port;
command : WS? (icall_def |
               iuseprocnamespace_def |
               iprefix_def |
               ireset_def |
               iread_def |
               iwrite_def |
               iscan_def |
               iapply_def |
               inote_def |
               ioverridescaninterface_def |
               imerge_def |
               itake_def |
               irelease_def |
               iclock_def |
               iclock_override_def |
               istate_def |
               irunloop_def |
               SL_COMMENT) WS? eoc | WS? eoc ; //empty line acceptable
// -------
iprefix_def : 'iPrefix' WS (instancePath|'-') ;

// -------
icall_def : 'iCall' WS (instancePath DOT)? (pdl_namespace_name '::')? procName
( WS args )* ;

// -------
ireset_def : 'iReset' (WS '-sync')? ;

// -------
iread_def : 'iRead' WS reg_or_port WS (( pdl_number | enum_name ))?;

// -------
iwrite_def : 'iWrite' WS reg_or_port WS ( pdl_number | enum_name );

// -------
iscan_def : 'iScan' WS ('-ir' WS)? scanInterface_name
                (WS '–chain' chain_id)? WS length
            (WS '-si' WS iscan_data)? (WS '-so' WS iscan_data)? ('-stable')? ;
iscan_data : pdl_number | ISCAN_HEX_NUMBER | ISCAN_BIN_NUMBER;

// -------
ioverridescaninterface_def : 'iOverrideScanInterface' WS scanInterfaceRef_list
                             (WS '-capture' WS ('on'|'off'))?
                             (WS '-update' WS ('on'|'off'))?
                             (WS '-broadcast' WS ('on'|'off'))? ;
scanInterfaceRef_list : scanInterfaceRef (WS scanInterfaceRef)*;
scanInterfaceRef : (instancePath DOT)? scanInterface_name;

// -------
iapply_def : 'iApply' (WS '-together')?;

// -------
iclock_def : 'iClock' WS sysClock;

// -------
iclock_override_def : 'iClockOverride' WS sysClock
                       (WS '-source' WS sourceClock)?
                       (WS '-freqMultiplier' WS POS_INT)?
                       (WS '-freqDivider' WS POS_INT)? ;
// -------
irunloop_def : 'iRunLoop' WS ( cycleCount ( WS '-tck' | WS '-sck' port )? | '-time' WS tvalue);

// -------
imerge_def : 'iMerge' WS ( '-begin' | '-end' );

// -------
itake_def : 'iTake' WS reg_port_or_instance ;

// -------
irelease_def : 'iRelease' WS reg_port_or_instance ;

// -------
inote_def : 'iNote' WS ( '-comment' | '-status' ) WS QUOTED;

// -------
istate_def : 'iState' WS reg_or_port WS pdl_number (WS '-LastWrittenValue' | WS '-LastReadValue' | WS '-LastMiscompareValue')? ;

//PDL1 grammar 20120328
// -------
iget_read_data_def : 'iGetReadData' WS (reg_or_port | scanInterface_name (WS '–chain' WS chain_id)? ) ( WS format )? ;
format : '-dec' | '-bin' | '-hex' ;

// -------
iget_miscompares_def : 'iGetMiscompares' (reg_or_port | scanInterface_name (WS '–chain' WS chain_id)? ) ( WS format )? ;
iget_status_def : 'iGetStatus' ( '-clear' )? ;
iset_fail_def : 'iSetFail' text_message ( '-quit' )? ;
text_message : string ;