`timescale 1ns/1ps

module ScanRegister #(
    parameter integer Size = 1,
    parameter bool MSB_TO_LSB = 1'b1,
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

    // TDR Shift Register Core
    genvar i;
    generate
        if (MSB_TO_LSB) begin : MSBLSB_SO

            assign internal_si[Size] = SI;
            assign SO = internal_si[0];

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
        end else begin : LSBMSB_SO
            assign SO = internal_si[Size-1];

            for (i = 0; i < Size; i = i + 1) begin : SCAN_REGISTER_LOOP
                // Multiplexers
                if(i == 0) begin
                    assign se_mux[i] = (and_se) ? SI : cs_reg[i];
                end
                else begin
                    assign se_mux[i] = (and_se) ? internal_si[i-1] : cs_reg[i];
                end
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
                        u_reg[i] <= ResetValue[i];
                    end else begin
                        u_reg[i] <= ue_mux[i];
                    end
                end

                // Internal Connections
                assign internal_si[i] = cs_reg[i];
            end
        end
    endgenerate

    assign ScanRegister_out = u_reg;
endmodule

module test_icl_syntax_5 (
    input  wire SI,
    output wire SO,
    input  wire SEL,
    input  wire SE,
    input  wire CE,
    input  wire UE,
    input  wire RST,
    input  wire TCK
);
    parameter integer Size = 8;

    wire [Size-1:0] X_0;
    wire [Size-1:0] X_1;
    wire SR_0_so;
    wire SR_1_so;

    localparam [Size-1:0] ResetValue = {Size{1'b0}};

    assign SO = SR_1_so;

    ScanRegister #(
        .Size(Size),
        .MSB_TO_LSB(1'b1),
        .ResetValue(ResetValue)
    ) SR_0 (
        .SI(SI),
        .CE(CE),
        .SE(SE),
        .UE(UE),
        .SEL(SEL),
        .RST(RST),
        .TCK(TCK),
        .SO(SR_0_so),
        .CaptureSource(X_0),
        .ScanRegister_out(X_0)
    );

    ScanRegister #(
        .Size(Size),
        .MSB_TO_LSB(1'b0),
        .ResetValue(ResetValue)
    ) SR_1 (
        .SI(SR_0_so),
        .CE(CE),
        .SE(SE),
        .UE(UE),
        .SEL(SEL),
        .RST(RST),
        .TCK(TCK),
        .SO(SR_1_so),
        .CaptureSource(X_1),
        .ScanRegister_out(X_1)
    );

endmodule
