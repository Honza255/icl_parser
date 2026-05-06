// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// TAP is modification of dmi_jtag_tap from pulp-platform /riscv-dbg.
// It was modifed to test IJTAG retargeter as a simple TAP desing.

`timescale 1ns/1ps

module test_icl_syntax_7 #(
    parameter integer IrLength    = 5,
    parameter [31:0]  IdcodeValue = 32'h00000001
) (
    input  wire tck_i,
    input  wire tms_i,
    input  wire trst_ni,
    input  wire tdi_i,
    output reg  tdo_o
);

    // ── TAP state encoding ────────────────────────────────────────────────────
    localparam [3:0]
        TestLogicReset = 4'd0,
        RunTestIdle    = 4'd1,
        SelectDrScan   = 4'd2,
        CaptureDr      = 4'd3,
        ShiftDr        = 4'd4,
        Exit1Dr        = 4'd5,
        PauseDr        = 4'd6,
        Exit2Dr        = 4'd7,
        UpdateDr       = 4'd8,
        SelectIrScan   = 4'd9,
        CaptureIr      = 4'd10,
        ShiftIr        = 4'd11,
        Exit1Ir        = 4'd12,
        PauseIr        = 4'd13,
        Exit2Ir        = 4'd14,
        UpdateIr       = 4'd15;

    reg [3:0] tap_state_q, tap_state_d;

    reg capture_dr, shift_dr, update_dr;
    reg capture_ir, shift_ir, update_ir;
    reg test_logic_reset;

    // ── IR opcodes ────────────────────────────────────────────────────────────
    localparam [IrLength-1:0]
        BYPASS0   = 5'h00,
        IDCODE    = 5'h01,
        CONF_A_I  = 5'h02,
        CONF_B_I  = 5'h04,
        STATUS_I  = 5'h08,
        CTRL_I    = 5'h10;

    reg [IrLength-1:0] jtag_ir_shift_d, jtag_ir_shift_q;
    reg [IrLength-1:0] jtag_ir_d, jtag_ir_q;

    // DR select signals
    reg idcode_sel, bypass_sel;
    reg conf_a_sel, conf_b_sel, status_sel, ctrl_sel;

    // DR shift registers
    reg [31:0] idcode_shift_d, idcode_shift_q;
    reg        bypass_shift_d, bypass_shift_q;
    reg [7:0]  conf_a_shift_d, conf_a_shift_q;
    reg [15:0] conf_b_shift_d, conf_b_shift_q;
    reg [11:0] status_shift_d, status_shift_q;
    reg [31:0] ctrl_shift_d,   ctrl_shift_q;

    // DR update registers
    reg [7:0]  conf_a_q, conf_a_d;
    reg [15:0] conf_b_q, conf_b_d;
    reg [11:0] status_q, status_d;
    reg [31:0] ctrl_q,   ctrl_d;

    // IR shift register output (needed by cocotb test)
    wire [IrLength-1:0] jtag_ir_q_out;
    assign jtag_ir_q_out = jtag_ir_q;

    // Reset values
    localparam [7:0]  CONF_A_RST = 8'hA5;
    localparam [15:0] CONF_B_RST = 16'hDEAD;
    localparam [11:0] STATUS_RST = 12'hABC;
    localparam [31:0] CTRL_RST   = 32'hCAFEBABE;

    // ── TAP FSM ───────────────────────────────────────────────────────────────
    always @(*) begin : p_tap_fsm
        tap_state_d      = tap_state_q;
        test_logic_reset = 1'b0;
        capture_dr = 1'b0; shift_dr = 1'b0; update_dr = 1'b0;
        capture_ir = 1'b0; shift_ir = 1'b0; update_ir = 1'b0;

        case (tap_state_q)
            TestLogicReset: begin
                tap_state_d = tms_i ? TestLogicReset : RunTestIdle;
                test_logic_reset = 1'b1;
            end
            RunTestIdle:  tap_state_d = tms_i ? SelectDrScan : RunTestIdle;
            SelectDrScan: tap_state_d = tms_i ? SelectIrScan : CaptureDr;
            CaptureDr: begin
                capture_dr  = 1'b1;
                tap_state_d = tms_i ? Exit1Dr : ShiftDr;
            end
            ShiftDr: begin
                shift_dr    = 1'b1;
                tap_state_d = tms_i ? Exit1Dr : ShiftDr;
            end
            Exit1Dr:      tap_state_d = tms_i ? UpdateDr : PauseDr;
            PauseDr:      tap_state_d = tms_i ? Exit2Dr  : PauseDr;
            Exit2Dr:      tap_state_d = tms_i ? UpdateDr : ShiftDr;
            UpdateDr: begin
                update_dr   = 1'b1;
                tap_state_d = tms_i ? SelectDrScan : RunTestIdle;
            end
            SelectIrScan: tap_state_d = tms_i ? TestLogicReset : CaptureIr;
            CaptureIr: begin
                capture_ir  = 1'b1;
                tap_state_d = tms_i ? Exit1Ir : ShiftIr;
            end
            ShiftIr: begin
                shift_ir    = 1'b1;
                tap_state_d = tms_i ? Exit1Ir : ShiftIr;
            end
            Exit1Ir:      tap_state_d = tms_i ? UpdateIr : PauseIr;
            PauseIr:      tap_state_d = tms_i ? Exit2Ir  : PauseIr;
            Exit2Ir:      tap_state_d = tms_i ? UpdateIr : ShiftIr;
            UpdateIr: begin
                update_ir   = 1'b1;
                tap_state_d = tms_i ? SelectDrScan : RunTestIdle;
            end
            default: tap_state_d = TestLogicReset;
        endcase
    end

    always @(posedge tck_i or negedge trst_ni) begin
        if (!trst_ni) tap_state_q <= TestLogicReset;
        else          tap_state_q <= tap_state_d;
    end

    // ── IR register ───────────────────────────────────────────────────────────
    always @(*) begin
        jtag_ir_shift_d = jtag_ir_shift_q;
        jtag_ir_d       = jtag_ir_q;

        if (shift_ir)         jtag_ir_shift_d = {tdi_i, jtag_ir_shift_q[IrLength-1:1]};
        if (capture_ir)       jtag_ir_shift_d = 5'b00101;
        if (update_ir)        jtag_ir_d       = jtag_ir_shift_q;
        if (test_logic_reset) begin
            jtag_ir_shift_d = {IrLength{1'b0}};
            jtag_ir_d       = IDCODE;
        end
    end

    always @(posedge tck_i or negedge trst_ni) begin
        if (!trst_ni) begin
            jtag_ir_shift_q <= {IrLength{1'b0}};
            jtag_ir_q       <= IDCODE;
        end else begin
            jtag_ir_shift_q <= jtag_ir_shift_d;
            jtag_ir_q       <= jtag_ir_d;
        end
    end

    // ── DR selection ──────────────────────────────────────────────────────────
    always @(*) begin
        idcode_sel = 1'b0; bypass_sel = 1'b0;
        conf_a_sel = 1'b0; conf_b_sel = 1'b0;
        status_sel = 1'b0; ctrl_sel   = 1'b0;
        case (jtag_ir_q)
            BYPASS0:  bypass_sel = 1'b1;
            IDCODE:   idcode_sel = 1'b1;
            CONF_A_I: conf_a_sel = 1'b1;
            CONF_B_I: conf_b_sel = 1'b1;
            STATUS_I: status_sel = 1'b1;
            CTRL_I:   ctrl_sel   = 1'b1;
            default:  bypass_sel = 1'b1;
        endcase
    end

    // ── IDCODE DR (32-bit, read-only) ─────────────────────────────────────────
    always @(*) begin
        idcode_shift_d = idcode_shift_q;
        if (test_logic_reset)             idcode_shift_d = IdcodeValue;
        else if (idcode_sel && capture_dr) idcode_shift_d = IdcodeValue;
        else if (idcode_sel && shift_dr)   idcode_shift_d = {tdi_i, idcode_shift_q[31:1]};
    end

    always @(posedge tck_i or negedge trst_ni) begin
        if (!trst_ni) idcode_shift_q <= IdcodeValue;
        else          idcode_shift_q <= idcode_shift_d;
    end

    // ── BYPASS DR (1-bit) ─────────────────────────────────────────────────────
    always @(*) begin
        bypass_shift_d = bypass_shift_q;
        if (test_logic_reset)             bypass_shift_d = 1'b0;
        else if (bypass_sel && capture_dr) bypass_shift_d = 1'b0;
        else if (bypass_sel && shift_dr)   bypass_shift_d = tdi_i;
    end

    always @(posedge tck_i or negedge trst_ni) begin
        if (!trst_ni) bypass_shift_q <= 1'b0;
        else          bypass_shift_q <= bypass_shift_d;
    end

    // ── CONF_A DR (8-bit, R/W, reset = 0xA5) ─────────────────────────────────
    always @(*) begin
        conf_a_shift_d = conf_a_shift_q;
        conf_a_d       = conf_a_q;
        if (test_logic_reset) begin
            conf_a_shift_d = CONF_A_RST;
            conf_a_d       = CONF_A_RST;
        end else if (conf_a_sel) begin
            if (capture_dr) conf_a_shift_d = conf_a_q;
            if (shift_dr)   conf_a_shift_d = {tdi_i, conf_a_shift_q[7:1]};
            if (update_dr)  conf_a_d       = conf_a_shift_q;
        end
    end

    always @(posedge tck_i or negedge trst_ni) begin
        if (!trst_ni) begin
            conf_a_shift_q <= CONF_A_RST;
            conf_a_q       <= CONF_A_RST;
        end else begin
            conf_a_shift_q <= conf_a_shift_d;
            conf_a_q       <= conf_a_d;
        end
    end

    // ── CONF_B DR (16-bit, R/W, reset = 0xDEAD) ──────────────────────────────
    always @(*) begin
        conf_b_shift_d = conf_b_shift_q;
        conf_b_d       = conf_b_q;
        if (test_logic_reset) begin
            conf_b_shift_d = CONF_B_RST;
            conf_b_d       = CONF_B_RST;
        end else if (conf_b_sel) begin
            if (capture_dr) conf_b_shift_d = conf_b_q;
            if (shift_dr)   conf_b_shift_d = {tdi_i, conf_b_shift_q[15:1]};
            if (update_dr)  conf_b_d       = conf_b_shift_q;
        end
    end

    always @(posedge tck_i or negedge trst_ni) begin
        if (!trst_ni) begin
            conf_b_shift_q <= CONF_B_RST;
            conf_b_q       <= CONF_B_RST;
        end else begin
            conf_b_shift_q <= conf_b_shift_d;
            conf_b_q       <= conf_b_d;
        end
    end

    // ── STATUS_REG DR (12-bit, R/W, reset = 0xABC) ───────────────────────────
    always @(*) begin
        status_shift_d = status_shift_q;
        status_d       = status_q;
        if (test_logic_reset) begin
            status_shift_d = STATUS_RST;
            status_d       = STATUS_RST;
        end else if (status_sel) begin
            if (capture_dr) status_shift_d = status_q;
            if (shift_dr)   status_shift_d = {tdi_i, status_shift_q[11:1]};
            if (update_dr)  status_d       = status_shift_q;
        end
    end

    always @(posedge tck_i or negedge trst_ni) begin
        if (!trst_ni) begin
            status_shift_q <= STATUS_RST;
            status_q       <= STATUS_RST;
        end else begin
            status_shift_q <= status_shift_d;
            status_q       <= status_d;
        end
    end

    // ── CTRL DR (32-bit, R/W, reset = 0xCAFEBABE) ────────────────────────────
    always @(*) begin
        ctrl_shift_d = ctrl_shift_q;
        ctrl_d       = ctrl_q;
        if (test_logic_reset) begin
            ctrl_shift_d = CTRL_RST;
            ctrl_d       = CTRL_RST;
        end else if (ctrl_sel) begin
            if (capture_dr) ctrl_shift_d = ctrl_q;
            if (shift_dr)   ctrl_shift_d = {tdi_i, ctrl_shift_q[31:1]};
            if (update_dr)  ctrl_d       = ctrl_shift_q;
        end
    end

    always @(posedge tck_i or negedge trst_ni) begin
        if (!trst_ni) begin
            ctrl_shift_q <= CTRL_RST;
            ctrl_q       <= CTRL_RST;
        end else begin
            ctrl_shift_q <= ctrl_shift_d;
            ctrl_q       <= ctrl_d;
        end
    end

    // ── TDO mux ───────────────────────────────────────────────────────────────
    reg tdo_mux;

    always @(*) begin
        if (shift_ir) begin
            tdo_mux = jtag_ir_shift_q[0];
        end else begin
            case (jtag_ir_q)
                IDCODE:   tdo_mux = idcode_shift_q[0];
                CONF_A_I: tdo_mux = conf_a_shift_q[0];
                CONF_B_I: tdo_mux = conf_b_shift_q[0];
                STATUS_I: tdo_mux = status_shift_q[0];
                CTRL_I:   tdo_mux = ctrl_shift_q[0];
                default:  tdo_mux = bypass_shift_q;
            endcase
        end
    end

    // TDO registered on falling edge of TCK (standard JTAG)
    always @(negedge tck_i or negedge trst_ni) begin
        if (!trst_ni) tdo_o <= 1'b0;
        else          tdo_o <= tdo_mux;
    end

endmodule
