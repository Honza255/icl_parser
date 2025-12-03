//  -- Copyright Testonica Lab (C) 2016
//
//  -- History:
//  ---------------+------------+-------------------------+------------------------
//  --  Version    |  Date      | Author                  | Organization
//  ---------------+------------+-------------------------+------------------------
//  --         1.0 | 21.11.2016 | Dmitri Mihhailov        | Testonica Lab
//  ---------------+------------+-------------------------+------------------------

// -----------------------------------------------------------------------------
// Module: ScanRegister
// -----------------------------------------------------------------------------
`timescale 1ns/1ps

module ScanRegister #(
    parameter integer Size = 1,
    parameter string  BitOrder = "MSBLSB", // MSBLSB / LSBMSB
    parameter integer SOSource = 0,
    parameter [Size-1:0] ResetValue = {Size{1'b0}}
)(
    input  wire SI,
    input  wire CE,
    input  wire SE,
    input  wire UE,
    input  wire SEL,
    input  wire RST,
    input  wire TCK,
    output wire SO,
    input  wire [Size-1:0] CaptureSource,
    output wire [Size-1:0] ScanRegister_out
);

    wire and_ce, and_se, and_ue;
    wire [Size:0] internal_si;
    reg  [Size-1:0] cs_reg;
    reg  [Size-1:0] u_reg;
    wire [Size-1:0] se_mux, ce_mux, ue_mux;

    // Basic Combinational Logic
    assign and_ce = CE & SEL;
    assign and_se = SE & SEL;
    assign and_ue = UE & SEL;
    assign internal_si[Size] = SI;

    // TDR Shift Register Core
    genvar i;
    generate
        for (i = Size-1; i >= 0; i = i - 1) begin : SCAN_REGISTER_LOOP
            // Multiplexers
            assign se_mux[i] = (and_se) ? internal_si[i+1] : cs_reg[i];
            assign ce_mux[i] = (and_ce) ? CaptureSource[i] : se_mux[i];
            assign ue_mux[i] = (and_ue) ? cs_reg[i] : u_reg[i];

            // Flip-Flops
            // Capture Shift Reg (Rising Edge TCK)
            always @(posedge TCK) begin
                cs_reg[i] <= ce_mux[i];
            end

            // Update Reg (Async Reset, Falling Edge TCK)
            always @(negedge TCK or posedge RST) begin
                if (RST) begin
                    u_reg[i] <= ResetValue[Size-1-i];
                end else begin
                    u_reg[i] <= ue_mux[i];
                end
            end

            // Internal Connections
            assign internal_si[i] = cs_reg[i];
        end
    endgenerate

    // Outputs
    generate
        if (BitOrder == "MSBLSB") begin : MSBLSB_SO
            assign SO = internal_si[SOSource];
        end else if (BitOrder == "LSBMSB") begin : LSBMSB_SO
            assign SO = internal_si[Size-1-SOSource];
        end else begin : DEFAULT_SO
            assign SO = internal_si[SOSource]; // Default fallback
        end
    endgenerate

    assign ScanRegister_out = u_reg;

endmodule

// -----------------------------------------------------------------------------
// Module: ScanMux
// -----------------------------------------------------------------------------
module ScanMux #(
    parameter integer ControlSize = 3
)(
    input  wire [(1<<ControlSize)-1:0] ScanMux_in,
    input  wire [ControlSize-1:0]      SelectedBy,
    output wire                        ScanMux_out
);
    // Behavioral implementation of the Mux Tree
    assign ScanMux_out = ScanMux_in[SelectedBy];

endmodule

// -----------------------------------------------------------------------------
// Module: DataRegister
// -----------------------------------------------------------------------------
module DataRegister #(
    parameter integer Size = 8,
    parameter [Size-1:0] ResetValue = 1
)(
    input  wire RST,
    input  wire CLK,
    input  wire WriteEnableSource,
    input  wire [Size-1:0] WriteDataSource,
    output reg  [Size-1:0] DataRegister_out
);

    always @(negedge CLK or posedge RST) begin
        if (RST) begin
            DataRegister_out <= ResetValue;
        end else begin
            if (WriteEnableSource) begin
                DataRegister_out <= WriteDataSource;
            end
        end
    end

endmodule

// -----------------------------------------------------------------------------
// Module: DataMux
// -----------------------------------------------------------------------------
module DataMux #(
    parameter integer ControlSize = 2,
    parameter integer DataSize = 8
)(
    input  wire [(1<<ControlSize)*DataSize-1:0] DataMux_in,
    input  wire [ControlSize-1:0]               SelectedBy,
    output wire [DataSize-1:0]                  DataMux_out
);
    // Behavioral implementation of the Data Mux
    // Indexed Part Select
    assign DataMux_out = DataMux_in[SelectedBy*DataSize +: DataSize];

endmodule

// -----------------------------------------------------------------------------
// Module: Instrument
// -----------------------------------------------------------------------------
module Instrument #(
    parameter integer Size = 8
)(
    input  wire RST,
    input  wire CLK,
    input  wire [Size-1:0] DI, // DataInPort
    output wire [Size-1:0] DO  // DataOutPort
);

    wire [Size-1:0] dr_do;
    wire enable;
    
    localparam [Size-1:0] ResetValue = {Size{1'b0}}; // default

    assign DO = dr_do;
    assign enable = DI[Size-1];

    DataRegister #(
        .Size(Size),
        .ResetValue(ResetValue)
    ) dr (
        .RST(RST),
        .CLK(CLK),
        .WriteEnableSource(enable),
        .WriteDataSource(DI),
        .DataRegister_out(dr_do)
    );

endmodule

// -----------------------------------------------------------------------------
// Module: LoopDIDO
// -----------------------------------------------------------------------------
module LoopDIDO #(
    parameter integer LoopDIDO_width = 1
)(
    input  wire [LoopDIDO_width-1:0] DI,
    output wire [LoopDIDO_width-1:0] DO
);

    assign DO = DI;

endmodule

// -----------------------------------------------------------------------------
// Module: SReg
// -----------------------------------------------------------------------------
module SReg #(
    parameter integer Size = 7
)(
    input  wire SI,
    output wire SO,
    input  wire SEL,
    input  wire SE,
    input  wire CE,
    input  wire UE,
    input  wire RST,
    input  wire TCK,
    input  wire [Size-1:0] DI,
    output wire [Size-1:0] DO
);

    wire SR_so;
    wire [Size-1:0] SR_do;
    
    localparam [Size-1:0] ResetValue = {Size{1'b0}};

    assign SO = SR_so;
    assign DO = SR_do;

    ScanRegister #(
        .Size(Size),
        .BitOrder("MSBLSB"),
        .SOSource(0),
        .ResetValue(ResetValue)
    ) SR (
        .SI(SI),
        .CE(CE),
        .SE(SE),
        .UE(UE),
        .SEL(SEL),
        .RST(RST),
        .TCK(TCK),
        .SO(SR_so),
        .CaptureSource(DI),
        .ScanRegister_out(SR_do)
    );

endmodule

// -----------------------------------------------------------------------------
// Module: WrappedInstr
// -----------------------------------------------------------------------------
module WrappedInstr #(
    parameter integer Size = 8
)(
    input  wire SI,
    output wire SO,
    input  wire SEL,
    input  wire SE,
    input  wire CE,
    input  wire UE,
    input  wire RST,
    input  wire TCK,
    input  wire INSTR_CLK,
    input  wire INSTR_RST
);

    wire [Size-1:0] I1_do;
    wire reg8_so;
    wire [Size-1:0] reg8_do;

    assign SO = reg8_so;

    Instrument #(
        .Size(Size)
    ) I1 (
        .RST(INSTR_RST),
        .CLK(INSTR_CLK),
        .DI(reg8_do),
        .DO(I1_do)
    );

    SReg #(
        .Size(Size)
    ) reg8 (
        .SI(SI),
        .SO(reg8_so),
        .SEL(SEL),
        .SE(SE),
        .CE(CE),
        .UE(UE),
        .RST(RST),
        .TCK(TCK),
        .DI(I1_do),
        .DO(reg8_do)
    );

endmodule

// -----------------------------------------------------------------------------
// Module: WrappedScan
// -----------------------------------------------------------------------------
module WrappedScan #(
    parameter integer dataWidth = 1
)(
    input  wire SI,
    output wire SO,
    input  wire SEL,
    input  wire SE,
    input  wire CE,
    input  wire UE,
    input  wire RST,
    input  wire TCK
);

    wire [dataWidth-1:0] I1_do;
    wire reg_so;
    wire [dataWidth-1:0] reg_do;

    assign SO = reg_so;

    LoopDIDO #(
        .LoopDIDO_width(dataWidth)
    ) I1 (
        .DI(reg_do),
        .DO(I1_do)
    );

    SReg #(
        .Size(dataWidth)
    ) reg_inst (
        .SI(SI),
        .SO(reg_so),
        .SEL(SEL),
        .SE(SE),
        .CE(CE),
        .UE(UE),
        .RST(RST),
        .TCK(TCK),
        .DI(I1_do),
        .DO(reg_do)
    );

endmodule

// -----------------------------------------------------------------------------
// Module: SIB_mux_pre
// -----------------------------------------------------------------------------
module SIB_mux_pre (
    // Scan Interface client
    input  wire SI,
    input  wire CE,
    input  wire SE,
    input  wire UE,
    input  wire SEL,
    input  wire RST,
    input  wire TCK,
    output wire SO,
    // Scan Interface host
    input  wire fromSO,
    output wire toCE,
    output wire toSE,
    output wire toUE,
    output wire toSEL,
    output wire toRST,
    output wire toTCK,
    output wire toSI
);

    wire SR_so;
    wire [0:0] SR_do;
    wire SIBmux_out;

    assign SO = SR_so;
    assign toCE = CE;
    assign toSE = SE;
    assign toUE = UE;
    assign toSEL = SEL & SR_do[0];
    assign toRST = RST;
    assign toTCK = TCK;
    assign toSI = SI;

    ScanRegister #(
        .Size(1),
        .BitOrder("MSBLSB"),
        .SOSource(0),
        .ResetValue(1'b0)
    ) SR (
        .SI(SIBmux_out),
        .CE(CE),
        .SE(SE),
        .UE(UE),
        .SEL(SEL),
        .RST(RST),
        .TCK(TCK),
        .SO(SR_so),
        .CaptureSource(SR_do),
        .ScanRegister_out(SR_do)
    );

    ScanMux #(
        .ControlSize(1)
    ) SIBmux (
        .ScanMux_in({fromSO, SI}), // [1] = fromSO, [0] = SI
        .SelectedBy(SR_do),
        .ScanMux_out(SIBmux_out)
    );

endmodule

// -----------------------------------------------------------------------------
// Module: SIB_mux_post
// -----------------------------------------------------------------------------
module SIB_mux_post (
    // Scan Interface client
    input  wire SI,
    input  wire CE,
    input  wire SE,
    input  wire UE,
    input  wire SEL,
    input  wire RST,
    input  wire TCK,
    output wire SO,
    // Scan Interface host
    input  wire fromSO,
    output wire toCE,
    output wire toSE,
    output wire toUE,
    output wire toSEL,
    output wire toRST,
    output wire toTCK,
    output wire toSI
);

    wire SR_so;
    wire [0:0] SR_do;
    wire SIBmux_out;

    assign SO = SIBmux_out;
    assign toCE = CE;
    assign toSE = SE;
    assign toUE = UE;
    assign toSEL = SEL & SR_do[0];
    assign toRST = RST;
    assign toTCK = TCK;
    assign toSI = SR_so;

    ScanRegister #(
        .Size(1),
        .BitOrder("MSBLSB"),
        .SOSource(0),
        .ResetValue(1'b0)
    ) SR (
        .SI(SI),
        .CE(CE),
        .SE(SE),
        .UE(UE),
        .SEL(SEL),
        .RST(RST),
        .TCK(TCK),
        .SO(SR_so),
        .CaptureSource(SR_do),
        .ScanRegister_out(SR_do)
    );

    ScanMux #(
        .ControlSize(1)
    ) SIBmux (
        .ScanMux_in({fromSO, SR_so}), // [1]=fromSO, [0]=SR_so
        .SelectedBy(SR_do),
        .ScanMux_out(SIBmux_out)
    );

endmodule

// -----------------------------------------------------------------------------
// Module: SCB
// -----------------------------------------------------------------------------
module SCB (
    input  wire SI,
    input  wire CE,
    input  wire SE,
    input  wire UE,
    input  wire SEL,
    input  wire RST,
    input  wire TCK,
    output wire SO,
    output wire toSEL,
    output wire [0:0] DO
);

    wire SR_so;
    wire [0:0] SR_do;

    assign toSEL = SR_do[0];
    assign SO = SR_so;
    assign DO = SR_do;

    ScanRegister #(
        .Size(1),
        .BitOrder("MSBLSB"),
        .SOSource(0),
        .ResetValue(1'b0)
    ) SR (
        .SI(SI),
        .CE(CE),
        .SE(SE),
        .UE(UE),
        .SEL(SEL),
        .RST(RST),
        .TCK(TCK),
        .SO(SR_so),
        .CaptureSource(SR_do),
        .ScanRegister_out(SR_do)
    );

endmodule

// -----------------------------------------------------------------------------
// Module: SCR
// -----------------------------------------------------------------------------
module SCR #(
    parameter integer size = 2
)(
    input  wire SI,
    input  wire CE,
    input  wire SE,
    input  wire UE,
    input  wire SEL,
    input  wire RST,
    input  wire TCK,
    output wire SO,
    output wire [size-1:0] DO
);

    localparam [size-1:0] ResetValue = {size{1'b0}};
    wire SR_so;
    wire [size-1:0] SR_do;

    assign SO = SR_so;
    assign DO = SR_do;

    ScanRegister #(
        .Size(size),
        .BitOrder("MSBLSB"),
        .SOSource(0),
        .ResetValue(ResetValue)
    ) SR (
        .SI(SI),
        .CE(CE),
        .SE(SE),
        .UE(UE),
        .SEL(SEL),
        .RST(RST),
        .TCK(TCK),
        .SO(SR_so),
        .CaptureSource(SR_do),
        .ScanRegister_out(SR_do)
    );

endmodule

// -----------------------------------------------------------------------------
// Module: BypassReg
// -----------------------------------------------------------------------------
module BypassReg (
    input  wire SI,
    input  wire CE,
    input  wire SE,
    input  wire UE,
    input  wire SEL,
    input  wire RST,
    input  wire TCK,
    output wire SO
);

    wire SR_so;
    wire [0:0] SR_do;

    assign SO = SR_so;

    ScanRegister #(
        .Size(1),
        .BitOrder("MSBLSB"),
        .SOSource(0),
        .ResetValue(1'b1)
    ) SR (
        .SI(SI),
        .CE(CE),
        .SE(SE),
        .UE(UE),
        .SEL(SEL),
        .RST(RST),
        .TCK(TCK),
        .SO(SR_so),
        .CaptureSource(SR_do),
        .ScanRegister_out(SR_do)
    );

endmodule

// -----------------------------------------------------------------------------
// Module: TrapOrFlap (Top Level)
// -----------------------------------------------------------------------------
module TrapOrFlap (
    // iJTAG interface
    input  wire SI,
    input  wire CE,
    input  wire SE,
    input  wire UE,
    input  wire SEL,
    input  wire RST,
    input  wire TCK,
    output wire SO,
    // Instruments interface
    input  wire INSTR_CLK,
    input  wire INSTR_RST
);
    parameter integer regSize = 8;
    parameter integer conf1Size = 16;
    parameter integer conf2Size = 32;

    // Internal Signal Declarations
    wire SIB_10_so, SIB_11_so, SIB_12_so, SIB_20_so, SIB_21_so, SIB_22_so, SIB_23_so, SIB_24_so, SIB_25_so, SIB_26_so, SIB_30_so;
    wire SIB_10_toCE, SIB_11_toCE, SIB_12_toCE, SIB_20_toCE, SIB_21_toCE, SIB_22_toCE, SIB_23_toCE, SIB_24_toCE, SIB_25_toCE, SIB_26_toCE, SIB_30_toCE;
    wire SIB_10_toSE, SIB_11_toSE, SIB_12_toSE, SIB_20_toSE, SIB_21_toSE, SIB_22_toSE, SIB_23_toSE, SIB_24_toSE, SIB_25_toSE, SIB_26_toSE, SIB_30_toSE;
    wire SIB_10_toUE, SIB_11_toUE, SIB_12_toUE, SIB_20_toUE, SIB_21_toUE, SIB_22_toUE, SIB_23_toUE, SIB_24_toUE, SIB_25_toUE, SIB_26_toUE, SIB_30_toUE;
    wire SIB_10_toSEL, SIB_11_toSEL, SIB_12_toSEL, SIB_20_toSEL, SIB_21_toSEL, SIB_22_toSEL, SIB_23_toSEL, SIB_24_toSEL, SIB_25_toSEL, SIB_26_toSEL, SIB_30_toSEL;
    wire SIB_10_toRST, SIB_11_toRST, SIB_12_toRST, SIB_20_toRST, SIB_21_toRST, SIB_22_toRST, SIB_23_toRST, SIB_24_toRST, SIB_25_toRST, SIB_26_toRST, SIB_30_toRST;
    wire SIB_10_toTCK, SIB_11_toTCK, SIB_12_toTCK, SIB_20_toTCK, SIB_21_toTCK, SIB_22_toTCK, SIB_23_toTCK, SIB_24_toTCK, SIB_25_toTCK, SIB_26_toTCK, SIB_30_toTCK;
    wire SIB_10_toSI, SIB_11_toSI, SIB_12_toSI, SIB_20_toSI, SIB_21_toSI, SIB_22_toSI, SIB_23_toSI, SIB_24_toSI, SIB_25_toSI, SIB_26_toSI, SIB_30_toSI;

    wire sMux1_out, sMux2_out, sMux3_out, sMux4_out, sMux5_out, sMux6_out, sMux7_out;

    wire SCB1_so;
    wire SCB1_toSEL;
    wire [0:0] SCB1_do;

    wire SREG0_so;
    wire [1:0] SREG0_do;
    wire SREG1_so;
    wire [1:0] SREG1_do;
    wire CONF1_so;
    wire [conf1Size-1:0] CONF1_do;
    wire CONF2_so;
    wire [conf2Size-1:0] CONF2_do;

    wire WI_0_so, WI_1_so, WI_2_so, WI_3_so, WI_4_so, WI_5_so, WI_6_so, WI_7_so, WI_8_so;

    wire sel_WI_1;
    wire sel_WI_2;
    wire sel_WI_3;
    wire sel_WI_4;
    wire sel_WI_5;
    wire sel_SIB_25_26;
    wire sel_CONF1;
    wire sel_CONF2;

    assign SO = SCB1_so;

    SIB_mux_pre SIB_10 (
        .SI(SI), .CE(CE), .SE(SE), .UE(UE), .SEL(SEL), .RST(RST), .TCK(TCK), .SO(SIB_10_so),
        .fromSO(SIB_22_so),
        .toCE(SIB_10_toCE), .toSE(SIB_10_toSE), .toUE(SIB_10_toUE), .toSEL(SIB_10_toSEL), .toRST(SIB_10_toRST), .toTCK(SIB_10_toTCK), .toSI(SIB_10_toSI)
    );

    SIB_mux_pre SIB_11 (
        .SI(SIB_10_so), .CE(CE), .SE(SE), .UE(UE), .SEL(SEL), .RST(RST), .TCK(TCK), .SO(SIB_11_so),
        .fromSO(SIB_24_so),
        .toCE(SIB_11_toCE), .toSE(SIB_11_toSE), .toUE(SIB_11_toUE), .toSEL(SIB_11_toSEL), .toRST(SIB_11_toRST), .toTCK(SIB_11_toTCK), .toSI(SIB_11_toSI)
    );

    SIB_mux_pre SIB_12 (
        .SI(SIB_11_so), .CE(CE), .SE(SE), .UE(UE), .SEL(SEL), .RST(RST), .TCK(TCK), .SO(SIB_12_so),
        .fromSO(SIB_26_so),
        .toCE(SIB_12_toCE), .toSE(SIB_12_toSE), .toUE(SIB_12_toUE), .toSEL(SIB_12_toSEL), .toRST(SIB_12_toRST), .toTCK(SIB_12_toTCK), .toSI(SIB_12_toSI)
    );

    ScanMux #(.ControlSize(1)) sMux4 (
        .ScanMux_in({CONF2_so, SIB_12_so}),
        .SelectedBy(SCB1_do),
        .ScanMux_out(sMux4_out)
    );

    SCB SCB1 (
        .SI(sMux4_out), .CE(CE), .SE(SE), .UE(UE), .SEL(SEL), .RST(RST), .TCK(TCK), .SO(SCB1_so),
        .toSEL(SCB1_toSEL), .DO(SCB1_do)
    );

    SIB_mux_pre SIB_20 (
        .SI(SIB_10_toSI), .CE(SIB_10_toCE), .SE(SIB_10_toSE), .UE(SIB_10_toUE), .SEL(SIB_10_toSEL), .RST(SIB_10_toRST), .TCK(SIB_10_toTCK), .SO(SIB_20_so),
        .fromSO(SREG0_so),
        .toCE(SIB_20_toCE), .toSE(SIB_20_toSE), .toUE(SIB_20_toUE), .toSEL(SIB_20_toSEL), .toRST(SIB_20_toRST), .toTCK(SIB_20_toTCK), .toSI(SIB_20_toSI)
    );

    SIB_mux_pre SIB_21 (
        .SI(SIB_20_so), .CE(SIB_10_toCE), .SE(SIB_10_toSE), .UE(SIB_10_toUE), .SEL(SIB_10_toSEL), .RST(SIB_10_toRST), .TCK(SIB_10_toTCK), .SO(SIB_21_so),
        .fromSO(WI_7_so),
        .toCE(SIB_21_toCE), .toSE(SIB_21_toSE), .toUE(SIB_21_toUE), .toSEL(SIB_21_toSEL), .toRST(SIB_21_toRST), .toTCK(SIB_21_toTCK), .toSI(SIB_21_toSI)
    );

    SIB_mux_pre SIB_22 (
        .SI(SIB_21_so), .CE(SIB_10_toCE), .SE(SIB_10_toSE), .UE(SIB_10_toUE), .SEL(SIB_10_toSEL), .RST(SIB_10_toRST), .TCK(SIB_10_toTCK), .SO(SIB_22_so),
        .fromSO(sMux1_out),
        .toCE(SIB_22_toCE), .toSE(SIB_22_toSE), .toUE(SIB_22_toUE), .toSEL(SIB_22_toSEL), .toRST(SIB_22_toRST), .toTCK(SIB_22_toTCK), .toSI(SIB_22_toSI)
    );

    SReg #(.Size(2)) SREG0 (
        .SI(SIB_20_toSI), .SO(SREG0_so), .SEL(SIB_20_toSEL),
        .SE(SIB_20_toSE), .CE(SIB_20_toCE), .UE(SIB_20_toUE), .RST(SIB_20_toRST), .TCK(SIB_20_toTCK),
        .DI(2'b11), .DO(SREG0_do)
    );

    SIB_mux_pre SIB_30 (
        .SI(SIB_21_toSI), .CE(SIB_21_toCE), .SE(SIB_21_toSE), .UE(SIB_21_toUE), .SEL(SIB_21_toSEL), .RST(SIB_21_toRST), .TCK(SIB_21_toTCK), .SO(SIB_30_so),
        .fromSO(WI_8_so),
        .toCE(SIB_30_toCE), .toSE(SIB_30_toSE), .toUE(SIB_30_toUE), .toSEL(SIB_30_toSEL), .toRST(SIB_30_toRST), .toTCK(SIB_30_toTCK), .toSI(SIB_30_toSI)
    );

    WrappedInstr #(.Size(regSize)) WI_7 (
        .SI(SIB_30_so), .SO(WI_7_so), .SEL(SIB_21_toSEL),
        .SE(SIB_21_toSE), .CE(SIB_21_toCE), .UE(SIB_21_toUE), .RST(SIB_21_toRST), .TCK(SIB_21_toTCK),
        .INSTR_CLK(INSTR_CLK), .INSTR_RST(INSTR_RST)
    );

    WrappedInstr #(.Size(regSize)) WI_8 (
        .SI(SIB_30_toSI), .SO(WI_8_so), .SEL(SIB_30_toSEL),
        .SE(SIB_30_toSE), .CE(SIB_30_toCE), .UE(SIB_30_toUE), .RST(SIB_30_toRST), .TCK(SIB_30_toTCK),
        .INSTR_CLK(INSTR_CLK), .INSTR_RST(INSTR_RST)
    );

    assign sel_WI_1 = SREG0_do[0] & SIB_22_toSEL;
    assign sel_WI_2 = (~SREG0_do[0]) & SIB_22_toSEL;

    WrappedInstr #(.Size(regSize)) WI_1 (
        .SI(SIB_22_toSI), .SO(WI_1_so), .SEL(sel_WI_1),
        .SE(SIB_22_toSE), .CE(SIB_22_toCE), .UE(SIB_22_toUE), .RST(SIB_22_toRST), .TCK(SIB_22_toTCK),
        .INSTR_CLK(INSTR_CLK), .INSTR_RST(INSTR_RST)
    );

    WrappedInstr #(.Size(regSize)) WI_2 (
        .SI(SIB_22_toSI), .SO(WI_2_so), .SEL(sel_WI_2),
        .SE(SIB_22_toSE), .CE(SIB_22_toCE), .UE(SIB_22_toUE), .RST(SIB_22_toRST), .TCK(SIB_22_toTCK),
        .INSTR_CLK(INSTR_CLK), .INSTR_RST(INSTR_RST)
    );

    ScanMux #(.ControlSize(1)) sMux1 (
        .ScanMux_in({WI_1_so, WI_2_so}),
        .SelectedBy(SREG0_do[0:0]),
        .ScanMux_out(sMux1_out)
    );

    SIB_mux_pre SIB_23 (
        .SI(SIB_11_toSI), .CE(SIB_11_toCE), .SE(SIB_11_toSE), .UE(SIB_11_toUE), .SEL(SIB_11_toSEL), .RST(SIB_11_toRST), .TCK(SIB_11_toTCK), .SO(SIB_23_so),
        .fromSO(WI_6_so),
        .toCE(SIB_23_toCE), .toSE(SIB_23_toSE), .toUE(SIB_23_toUE), .toSEL(SIB_23_toSEL), .toRST(SIB_23_toRST), .toTCK(SIB_23_toTCK), .toSI(SIB_23_toSI)
    );

    SIB_mux_pre SIB_24 (
        .SI(SIB_23_so), .CE(SIB_11_toCE), .SE(SIB_11_toSE), .UE(SIB_11_toUE), .SEL(SIB_11_toSEL), .RST(SIB_11_toRST), .TCK(SIB_11_toTCK), .SO(SIB_24_so),
        .fromSO(SREG1_so),
        .toCE(SIB_24_toCE), .toSE(SIB_24_toSE), .toUE(SIB_24_toUE), .toSEL(SIB_24_toSEL), .toRST(SIB_24_toRST), .toTCK(SIB_24_toTCK), .toSI(SIB_24_toSI)
    );

    assign sel_WI_5 = (~SREG0_do[1]) & SIB_23_toSEL;

    WrappedInstr #(.Size(regSize)) WI_5 (
        .SI(SIB_23_toSI), .SO(WI_5_so), .SEL(sel_WI_5),
        .SE(SIB_23_toSE), .CE(SIB_23_toCE), .UE(SIB_23_toUE), .RST(SIB_23_toRST), .TCK(SIB_23_toTCK),
        .INSTR_CLK(INSTR_CLK), .INSTR_RST(INSTR_RST)
    );

    ScanMux #(.ControlSize(1)) sMux5 (
        .ScanMux_in({SIB_23_toSI, WI_5_so}),
        .SelectedBy(SREG0_do[1:1]),
        .ScanMux_out(sMux5_out)
    );

    WrappedInstr #(.Size(regSize)) WI_6 (
        .SI(sMux5_out), .SO(WI_6_so), .SEL(SIB_23_toSEL),
        .SE(SIB_23_toSE), .CE(SIB_23_toCE), .UE(SIB_23_toUE), .RST(SIB_23_toRST), .TCK(SIB_23_toTCK),
        .INSTR_CLK(INSTR_CLK), .INSTR_RST(INSTR_RST)
    );

    assign sel_WI_3 = SREG1_do[1] & SIB_24_toSEL;

    WrappedInstr #(.Size(regSize)) WI_3 (
        .SI(SIB_24_toSI), .SO(WI_3_so), .SEL(sel_WI_3),
        .SE(SIB_24_toSE), .CE(SIB_24_toCE), .UE(SIB_24_toUE), .RST(SIB_24_toRST), .TCK(SIB_24_toTCK),
        .INSTR_CLK(INSTR_CLK), .INSTR_RST(INSTR_RST)
    );

    ScanMux #(.ControlSize(1)) sMux2 (
        .ScanMux_in({WI_3_so, SIB_24_toSI}),
        .SelectedBy(SREG1_do[1:1]),
        .ScanMux_out(sMux2_out)
    );

    ScanMux #(.ControlSize(1)) sMux3 (
        .ScanMux_in({WI_4_so, sMux2_out}),
        .SelectedBy(SREG1_do[0:0]),
        .ScanMux_out(sMux3_out)
    );

    assign sel_WI_4 = SREG1_do[0] & SIB_24_toSEL;

    WrappedInstr #(.Size(regSize)) WI_4 (
        .SI(sMux2_out), .SO(WI_4_so), .SEL(sel_WI_4),
        .SE(SIB_24_toSE), .CE(SIB_24_toCE), .UE(SIB_24_toUE), .RST(SIB_24_toRST), .TCK(SIB_24_toTCK),
        .INSTR_CLK(INSTR_CLK), .INSTR_RST(INSTR_RST)
    );

    SReg #(.Size(2)) SREG1 (
        .SI(sMux3_out), .SO(SREG1_so), .SEL(SIB_24_toSEL),
        .SE(SIB_24_toSE), .CE(SIB_24_toCE), .UE(SIB_24_toUE), .RST(SIB_24_toRST), .TCK(SIB_24_toTCK),
        .DI(2'b00), .DO(SREG1_do)
    );

    assign sel_SIB_25_26 = (~SCB1_do[0]) & SIB_12_toSEL;

    SIB_mux_pre SIB_25 (
        .SI(SIB_12_toSI), .CE(SIB_12_toCE), .SE(SIB_12_toSE), .UE(SIB_12_toUE), .SEL(sel_SIB_25_26), .RST(SIB_12_toRST), .TCK(SIB_12_toTCK), .SO(SIB_25_so),
        .fromSO(CONF1_so),
        .toCE(SIB_25_toCE), .toSE(SIB_25_toSE), .toUE(SIB_25_toUE), .toSEL(SIB_25_toSEL), .toRST(SIB_25_toRST), .toTCK(SIB_25_toTCK), .toSI(SIB_25_toSI)
    );

    SIB_mux_pre SIB_26 (
        .SI(SIB_25_so), .CE(SIB_12_toCE), .SE(SIB_12_toSE), .UE(SIB_12_toUE), .SEL(sel_SIB_25_26), .RST(SIB_12_toRST), .TCK(SIB_12_toTCK), .SO(SIB_26_so),
        .fromSO(CONF2_so),
        .toCE(SIB_26_toCE), .toSE(SIB_26_toSE), .toUE(SIB_26_toUE), .toSEL(SIB_26_toSEL), .toRST(SIB_26_toRST), .toTCK(SIB_26_toTCK), .toSI(SIB_26_toSI)
    );

    ScanMux #(.ControlSize(1)) sMux6 (
        .ScanMux_in({SIB_12_so, SIB_25_toSI}),
        .SelectedBy(SCB1_do),
        .ScanMux_out(sMux6_out)
    );

    ScanMux #(.ControlSize(1)) sMux7 (
        .ScanMux_in({CONF1_so, SIB_26_toSI}),
        .SelectedBy(SCB1_do),
        .ScanMux_out(sMux7_out)
    );

    assign sel_CONF1 = SCB1_do[0] | SIB_25_toSEL;
    assign sel_CONF2 = SCB1_do[0] | SIB_26_toSEL;

    SReg #(.Size(conf1Size)) CONF1 (
        .SI(sMux6_out), .SO(CONF1_so), .SEL(sel_CONF1),
        .SE(SIB_25_toSE), .CE(SIB_25_toCE), .UE(SIB_25_toUE), .RST(SIB_25_toRST), .TCK(SIB_25_toTCK),
        .DI({conf1Size{1'b0}}), .DO(CONF1_do)
    );

    SReg #(.Size(conf2Size)) CONF2 (
        .SI(sMux7_out), .SO(CONF2_so), .SEL(sel_CONF2),
        .SE(SIB_26_toSE), .CE(SIB_26_toCE), .UE(SIB_26_toUE), .RST(SIB_26_toRST), .TCK(SIB_26_toTCK),
        .DI({conf2Size{1'b0}}), .DO(CONF2_do)
    );

endmodule