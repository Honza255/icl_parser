// ICL description of test_icl_syntax_7 — standalone JTAG TAP with 6 DR paths.
// Port names match RTL: tdi_i, tdo_o, tck_i, tms_i, trst_ni.
// IR: 5 bits.  DRs: IDCODE(32b), BYPASS(1b), CONF_A(8b), CONF_B(16b),
//                   STATUS_REG(12b), CTRL(32b).

Module TapStates {
    TMSPort tms;
    TCKPort tck;
    ToResetPort tlr;
    ToIRSelectPort IRSel;
    ToCaptureEnPort CE;
    ToShiftEnPort SE;
    ToUpdateEnPort UE;
}

Module test_icl_syntax_7 {

    ScanInPort tdi_i;
    ScanOutPort tdo_o {
        Source IRMux;
    }
    TCKPort tck_i;
    TMSPort tms_i;
    TRSTPort trst_ni;

    ScanInterface tap_client {
        Port tdi_i;
        Port tdo_o;
        Port tck_i;
        Port tms_i;
        Port trst_ni;
    }

    Instance FSM Of TapStates {
        InputPort tms = tms_i;
        InputPort tck = tck_i;
    }

    ScanRegister IR[4:0] {
        ScanInSource tdi_i;
        CaptureSource 5'b00101;
        ResetValue 5'b00001;
    }

    ScanRegister IDCODE[31:0] {
        ScanInSource tdi_i;
        CaptureSource 32'h00000001;
        ResetValue 32'h00000001;
    }

    ScanRegister BYPASS {
        ScanInSource tdi_i;
        CaptureSource 1'b0;
        ResetValue 1'b0;
    }

    ScanRegister CONF_A[7:0] {
        ScanInSource tdi_i;
        CaptureSource CONF_A;
        ResetValue 8'hA5;
    }

    ScanRegister CONF_B[15:0] {
        ScanInSource tdi_i;
        CaptureSource CONF_B;
        ResetValue 16'hDEAD;
    }

    ScanRegister STATUS_REG[11:0] {
        ScanInSource tdi_i;
        CaptureSource STATUS_REG;
        ResetValue 12'hABC;
    }

    ScanRegister CTRL[31:0] {
        ScanInSource tdi_i;
        CaptureSource CTRL;
        ResetValue 32'hCAFEBABE;
    }

    ScanMux DRmux SelectedBy IR[4:0] {
        5'h00 : BYPASS;
        5'h01 : IDCODE[0];
        5'h02 : CONF_A[0];
        5'h04 : CONF_B[0];
        5'h08 : STATUS_REG[0];
        5'h10 : CTRL[0];
    }

    ScanMux IRMux SelectedBy FSM.IRSel {
        1'b0 : DRmux;
        1'b1 : IR[0];
    }
}
