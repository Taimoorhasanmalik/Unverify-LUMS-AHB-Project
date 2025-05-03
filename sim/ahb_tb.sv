//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (c) Copyright 2025 Team-Unverified-LUMS-AHB-Project. All Rights Reserved.
//
// File name : ahb_tb.sv
// Title     : TestBench
// Description :
// Notes :
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps

import ahb3lite_pkg::*;

module ahb_tb(ahb_if.master ahb_master);

    parameter TEST_TIMEOUT = 1_000_000;
    
    // Error counter
    int error_count = 0;

    //-------------------------------------------
    // Main Test Flow
    //-------------------------------------------
    initial begin : main_test
        ahb_master.reset_dut();

        fork : timeout_block
            begin
                #TEST_TIMEOUT;
                $error("[TIMEOUT] Simulation timed out");
                error_count++;
                disable main_test;
            end
        join_none

        //Uncomment the relevant test to run it
        //Comment the rest of the tests
        byte_transfer_test();
        half_word_transfer_test();
        single_word_transfer_test();
        inrc4_burst_test();
        wrap4_burst_test();
        incr8_burst_test();
        wrap8_burst_test();
        inrc16_burst_test();
        wrap16_burst_test();

        disable timeout_block;

        if (error_count == 0)
            $display("\n[PASS] All tests completed successfully");
        else
            $display("\n[FAIL] %0d errors detected", error_count);

        $finish;
    end

    //-------------------------------------------
    // Check Transaction Results
    //-------------------------------------------
    task check_result(
        input string label,
        input int index,
        input logic [31:0] expected,
        input logic [31:0] actual
    );
        if (actual !== expected) begin
            $error("[%s] Mismatch @beat%0d: Exp=0x%08h Got=0x%08h", label, index, expected, actual);
            error_count++;
        end else begin
            $display("[%s] Match @beat%0d: 0x%08h", label, index, actual);
        end
    endtask

    //-------------------------------------------
    // Test types
    //-------------------------------------------
    task byte_transfer_test();
        // Test 1: Byte-Sized Transfer (HSIZE_BYTE)
        begin
            static logic [31:0] byte_wdata[] = '{32'h000000AA};
            logic [31:0] byte_rdata[];
            $display("\n[TEST1] Byte-Sized Write/Read");
            ahb_master.ahb_write(.addr(16'h0020), .data(byte_wdata), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_BYTE));
            ahb_master.ahb_read(.addr(16'h0020), .data(byte_rdata), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_BYTE));
            check_result("TEST1", 0, 32'h000000AA, byte_rdata[0] & 32'h000000FF);
        end
    endtask

    task half_word_transfer_test();
        // Test 2: Half-Word Transfer (HSIZE_HWORD)
        begin
            static logic [31:0] hword_wdata[] = '{32'h0000_BEEF};
            logic [31:0] hword_rdata[];
            $display("\n[TEST2] Half-Word Write/Read");
            ahb_master.ahb_write(.addr(16'h0030), .data(hword_wdata), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_HWORD));
            ahb_master.ahb_read(.addr(16'h0030), .data(hword_rdata), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_HWORD));
            check_result("TEST2", 0, 32'h0000BEEF, hword_rdata[0] & 32'h0000FFFF);
        end
    endtask

    task single_word_transfer_test();
        // Test 3: Single Word Transfer
        begin
            static logic [31:0] wr_data[] = '{32'hDEAD_BEEF};
            logic [31:0] rd_data[];
            $display("\n[TEST3] Single Word Write/Read");
            ahb_master.ahb_write(.addr(16'h0010), .data(wr_data), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_WORD));
            ahb_master.ahb_read(.addr(16'h0010), .data(rd_data), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_WORD));
            check_result("TEST3", 0, wr_data[0], rd_data[0]);
        end
    endtask

    task inrc4_burst_test();
        // Test 4: 4-beat INCR4 Burst
        begin
            static logic [31:0] incr4_wdata[] = '{32'hCAFE_F00D, 32'hDEAD_BEEF, 32'hBAAD_F00D, 32'hFACE_B00C};
            logic [31:0] incr4_rdata[];
            $display("\n[TEST4] 4-beat INCR4 Burst");
            ahb_master.ahb_write(.addr(16'h1000), .data(incr4_wdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_WORD));
            ahb_master.ahb_read(.addr(16'h1000), .data(incr4_rdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_WORD));
            foreach (incr4_rdata[i]) check_result("TEST4", i, incr4_wdata[i], incr4_rdata[i]);
        end
    endtask

    task wrap4_burst_test();
        // Test 5: 4-beat WRAP4 Burst
        begin
            static logic [31:0] wrap4_wdata[] = '{32'h1111_1111, 32'h2222_2222, 32'h3333_3333, 32'h4444_4444};
            static logic [15:0] wrap4_addr = 16'h2000;
            logic [31:0] wrap4_rdata[];
            $display("\n[TEST5] 4-beat WRAP4 Burst");
            ahb_master.ahb_write(.addr(wrap4_addr), .data(wrap4_wdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_WORD));
            ahb_master.ahb_read(.addr(wrap4_addr), .data(wrap4_rdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_WORD));
            foreach (wrap4_rdata[i]) check_result("TEST5", i, wrap4_wdata[i], wrap4_rdata[i]);
        end
    endtask

    task incr8_burst_test();
        // Test 6: 8-beat INCR8 Burst
        begin
            static logic [31:0] incr8_wdata[] = '{32'h1111_1111, 32'h2222_2222, 32'h3333_3333, 32'h4444_4444,
                                                32'h5555_5555, 32'h6666_6666, 32'h7777_7777, 32'h8888_8888};
            logic [31:0] incr8_rdata[];
            $display("\n[TEST6] 8-beat INCR8 Burst");
            ahb_master.ahb_write(.addr(16'h5000), .data(incr8_wdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_WORD));
            ahb_master.ahb_read(.addr(16'h5000), .data(incr8_rdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_WORD));
            foreach (incr8_rdata[i]) check_result("TEST6", i, incr8_wdata[i], incr8_rdata[i]);
        end
    endtask

    task wrap8_burst_test();
        // Test 7: 8-beat WRAP8 Burst
        begin
            static logic [31:0] wrap8_wdata[] = '{32'hAAAA_AAAA, 32'hBBBB_BBBB, 32'hCCCC_CCCC, 32'hDDDD_DDDD,
                                                32'hEEEE_EEEE, 32'hFFFF_FFFF, 32'h1234_5678, 32'h8765_4321};
            static logic [15:0] wrap8_addr = 16'h3000;
            logic [31:0] wrap8_rdata[];
            $display("\n[TEST7] 8-beat WRAP8 Burst");
            ahb_master.ahb_write(.addr(wrap8_addr), .data(wrap8_wdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_WORD));
            ahb_master.ahb_read(.addr(wrap8_addr), .data(wrap8_rdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_WORD));
            foreach (wrap8_rdata[i]) check_result("TEST7", i, wrap8_wdata[i], wrap8_rdata[i]);
        end
    endtask

    task inrc16_burst_test();
        // Test 8: 16-beat INCR16 Burst
        begin
            static logic [31:0] incr16_wdata[] = '{
                32'hBBBB_1000, 32'hBBBB_1001, 32'hBBBB_1002, 32'hBBBB_1003,
                32'hBBBB_1004, 32'hBBBB_1005, 32'hBBBB_1006, 32'hBBBB_1007,
                32'hBBBB_1008, 32'hBBBB_1009, 32'hBBBB_100A, 32'hBBBB_100B,
                32'hBBBB_100C, 32'hBBBB_100D, 32'hBBBB_100E, 32'hBBBB_100F
            };
            logic [31:0] incr16_rdata[];
            $display("\n[TEST8] 16-beat INCR16 Burst");
            ahb_master.ahb_write(.addr(16'h6000), .data(incr16_wdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_WORD));
            ahb_master.ahb_read(.addr(16'h6000), .data(incr16_rdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_WORD));
            foreach (incr16_rdata[i]) check_result("TEST8", i, incr16_wdata[i], incr16_rdata[i]);
        end
    endtask

    task wrap16_burst_test();
        // Test 9: 16-beat WRAP16 Burst
        begin
            static logic [31:0] wrap16_wdata[] = '{
                32'hAAAA_0000, 32'hAAAA_0001, 32'hAAAA_0002, 32'hAAAA_0003,
                32'hAAAA_0004, 32'hAAAA_0005, 32'hAAAA_0006, 32'hAAAA_0007,
                32'hAAAA_0008, 32'hAAAA_0009, 32'hAAAA_000A, 32'hAAAA_000B,
                32'hAAAA_000C, 32'hAAAA_000D, 32'hAAAA_000E, 32'hAAAA_000F
            };
            static logic [15:0] wrap16_addr = 16'h4000;
            logic [31:0] wrap16_rdata[];
            $display("\n[TEST9] 16-beat WRAP16 Burst");
            ahb_master.ahb_write(.addr(wrap16_addr), .data(wrap16_wdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_WORD));
            ahb_master.ahb_read(.addr(wrap16_addr), .data(wrap16_rdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_WORD));
            foreach (wrap16_rdata[i]) check_result("TEST9", i, wrap16_wdata[i], wrap16_rdata[i]);
        end
    endtask

    //-------------------------------------------
    // Assertion Monitor (Placeholder)
    //-------------------------------------------



    //-------------------------------------------
    // Coverage Groups
    //-------------------------------------------
    covergroup address_range_cg @(posedge ahb_master.HCLK);
        option.per_instance = 1;
        address: coverpoint ahb_master.HADDR {
            bins low_addr  = {[32'h0000_0000 : 32'h0000_00FF]};
            bins high_addr = {[32'h0001_0000 : 32'hFFFF_FFFF]};
        }
    endgroup

    covergroup transfer_type_cg @(posedge ahb_master.HCLK);
        option.per_instance = 1;
        htrans: coverpoint ahb_master.HTRANS {
            bins IDLE    = {2'b00};
            bins NONSEQ  = {2'b10};
        }
    endgroup

    covergroup burst_type_cg @(posedge ahb_master.HCLK);
        option.per_instance = 1;
        hburst: coverpoint ahb_master.HBURST {
            bins SINGLE  = {3'b000};
        }
    endgroup

    covergroup size_cg @(posedge ahb_master.HCLK);
        option.per_instance = 1;
        hsize: coverpoint ahb_master.HSIZE {
            bins WORD      = {3'b010};
        }
    endgroup

    covergroup response_cg @(posedge ahb_master.HCLK);
        option.per_instance = 1;
        hresp: coverpoint ahb_master.HRESP {
            bins OKAY  = {1'b0};
        }
    endgroup

    covergroup wait_state_cg @(posedge ahb_master.HCLK);
        option.per_instance = 1;
        hready: coverpoint ahb_master.HREADY {
            bins WAIT_INSERTED = {1'b0};
            bins WAIT_NONE     = {1'b1};
        }
    endgroup

    // Instantiating covergroups
    address_range_cg addr_cvg = new();
    transfer_type_cg trans_cvg = new();
    burst_type_cg burst_cvg = new();
    size_cg size_cvg = new();
    response_cg resp_cvg = new();
    wait_state_cg wait_cvg = new();

endmodule

