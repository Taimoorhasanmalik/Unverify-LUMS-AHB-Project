//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (c) Copyright 2025 Team-Unverified-LUMS-AHB-Project. All Rights Reserved.
//
// File name : ahb_coverage.sv
// Title     : Functional Coverage file
// Description :
// Notes :
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////


import ahb3lite_pkg::*;

module ahb_coverage (
    input logic        HCLK,
    input logic [15:0] HADDR,
    input logic [1:0]  HTRANS,
    input logic [2:0]  HBURST,
    input logic [2:0]  HSIZE,
    input logic        HREADY,
    input logic        HRESP
);

/// Coverage groups using direct signals
    covergroup address_range_cg @(posedge HCLK);
        option.per_instance = 1;
        address: coverpoint HADDR {
            bins low_range  = {[16'h0000:16'h00FF]};
            bins high_range = {[16'h1000:16'hFFFF]};
        }
    endgroup

    covergroup transfer_type_cg @(posedge HCLK);
        option.per_instance = 1;
        htrans: coverpoint HTRANS {
            bins IDLE   = {2'b00};
            bins BUSY   = {2'b01};
            bins NONSEQ = {2'b10};
            bins SEQ    = {2'b11};
        }
    endgroup

    covergroup burst_type_cg @(posedge HCLK);
        option.per_instance = 1;
        hburst: coverpoint HBURST {
            bins SINGLE  = {3'b000};
            bins INCR    = {3'b001};
            bins WRAP4   = {3'b010};
            bins INCR4   = {3'b011};
            bins WRAP8   = {3'b100};
            bins INCR8   = {3'b101};
            bins WRAP16  = {3'b110};
            bins INCR16  = {3'b111};
        }
    endgroup

    covergroup size_cg @(posedge HCLK);
        option.per_instance = 1;
        hsize: coverpoint HSIZE {
            bins BYTE  = {3'b000};
            bins HWORD = {3'b001};
            bins WORD  = {3'b010};
        }
    endgroup

    covergroup response_cg @(posedge HCLK);
        option.per_instance = 1;
        hresp: coverpoint HRESP {
            bins OKAY  = {1'b0};
        }
    endgroup

    covergroup wait_state_cg @(posedge HCLK);
        option.per_instance = 1;
        hready: coverpoint HREADY {
            bins WAIT_NONE     = {1'b1};
            bins WAIT_INSERTED = {1'b0};
        }
    endgroup

//  Cross-coverage
    covergroup xfer_vs_burst_cg @(posedge HCLK);
        option.per_instance = 1;
        trans_cp: coverpoint HTRANS {
            bins IDLE   = {2'b00};
            bins BUSY   = {2'b01};
            bins NONSEQ = {2'b10};
            bins SEQ    = {2'b11};
        }
        burst_cp: coverpoint HBURST {
            bins SINGLE  = {3'b000};
            bins INCR    = {3'b001};
            bins WRAP4   = {3'b010};
            bins INCR4   = {3'b011};
            bins WRAP8   = {3'b100};
            bins INCR8   = {3'b101};
            bins WRAP16  = {3'b110};
            bins INCR16  = {3'b111};
        }
        cross_htype_burst: cross trans_cp, burst_cp {
            ignore_bins invalid_combinations =
            binsof(trans_cp) intersect {2'b00, 2'b01} ||
            binsof(burst_cp) intersect {3'b000, 3'b001};
        }
    endgroup


    covergroup size_vs_burst_cg @(posedge HCLK);
        option.per_instance = 1;
        size_cp: coverpoint HSIZE {       
	    bins BYTE     = {3'b000};
            bins HWORD    = {3'b001};
            bins WORD     = {3'b010};
        }
        burst_cp: coverpoint HBURST {
            bins SINGLE  = {3'b000};
            bins INCR    = {3'b001};
            bins WRAP4   = {3'b010};
            bins INCR4   = {3'b011};
            bins WRAP8   = {3'b100};
            bins INCR8   = {3'b101};
            bins WRAP16  = {3'b110};
            bins INCR16  = {3'b111};
        }
        cross_size_burst: cross size_cp, burst_cp {
            ignore_bins illegal_combinations =
            binsof(size_cp) intersect {3'b000};
        }
    endgroup


    covergroup addr_vs_size_cg @(posedge HCLK);
        option.per_instance = 1;
        addr_cp: coverpoint HADDR {
            bins low_range  = {[16'h0000 : 16'h00FF]};
            bins high_range = {[16'h1000 : 16'hFFFF]};
        }
        size_cp: coverpoint HSIZE {
            bins BYTE     = {3'b000};
            bins HALFWORD = {3'b001};
            bins WORD     = {3'b010};
        }
        cross_addr_size: cross addr_cp, size_cp {
            ignore_bins illegal_combinations = 
            binsof(addr_cp) intersect {[16'h0100 : 16'h0FFF]} &&
            binsof(size_cp) intersect {3'b000};
        }
    endgroup

/// Instantiate covergroups
    address_range_cg   addr_cvg = new();
    transfer_type_cg   trans_cvg = new();
    burst_type_cg      burst_cvg = new();
    size_cg            size_cvg = new();
    response_cg        resp_cvg = new();
    wait_state_cg      wait_cvg = new();
    xfer_vs_burst_cg   xferburst_cov = new();
    size_vs_burst_cg   sizeburst_cov = new();
    addr_vs_size_cg    addrsize_cov = new();


endmodule

