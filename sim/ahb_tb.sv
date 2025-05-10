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

    // -------------------------------------------
    // Test types
    // -------------------------------------------
    task byte_transfer_test();
        // Test 1: Byte-Sized Transfer
        begin
            logic [31:0] byte_wdata[0:15];
            logic [31:0] byte_rdata[0:15];
            byte_wdata[0] = 32'h000000AA;
            $display("\n[TEST1] Byte-Sized Write/Read");
            ahb_master.ahb_write(.addr(16'h0020), .data(byte_wdata), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_BYTE));
            ahb_master.ahb_read(.addr(16'h0020), .data(byte_rdata), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_BYTE));
            check_result("TEST1", 0, 32'h000000AA, byte_rdata[0] & 32'h000000FF);
        end
    endtask

    task half_word_transfer_test();
        // Test 2: Half-Word Transfer (HSIZE_HWORD)
        begin
            logic [31:0] hword_wdata[0:15];
            logic [31:0] hword_rdata[0:15];
            hword_wdata[0] = 32'h0000BEEF;
            $display("\n[TEST2] Half-Word Write/Read");
            ahb_master.ahb_write(.addr(16'h0030), .data(hword_wdata), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_HWORD));
            ahb_master.ahb_read(.addr(16'h0030), .data(hword_rdata), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_HWORD));
            check_result("TEST2", 0, 32'h0000BEEF, hword_rdata[0] & 32'h0000FFFF);
        end
    endtask

    task single_word_transfer_test();
        // Test 3: Single Word Transfer
        begin
            logic [31:0] wr_data[0:15];
            logic [31:0] rd_data[0:15];
            wr_data[0] = 32'hDEAD_BEEF;
            $display("\n[TEST3] Single Word Write/Read");
            ahb_master.ahb_write(.addr(16'h0010), .data(wr_data), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_WORD));
            ahb_master.ahb_read(.addr(16'h0010), .data(rd_data), .num_beats(1), .burst_type(HBURST_SINGLE), .size(HSIZE_WORD));
            check_result("TEST3", 0, wr_data[0], rd_data[0]);
        end
    endtask

    task inrc4_burst_test();
        // Test 4: 4-beat INCR4 Burst
        logic [31:0] incr4_wdata[0:15];
        logic [31:0] incr4_rdata[0:15];
        
        incr4_wdata[0] = 32'hCAFE_F00D;
        incr4_wdata[1] = 32'hDEAD_BEEF;
        incr4_wdata[2] = 32'hBAAD_F00D;
        incr4_wdata[3] = 32'hFACE_B00C;

        $display("\n[TEST4] 4-beat INCR4 Burst");
        ahb_master.ahb_write(.addr(16'h1004), .data(incr4_wdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(16'h1004), .data(incr4_rdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_WORD));
        for (int i=0; i < 4; i++) 
            check_result("TEST4", i, incr4_wdata[i], incr4_rdata[i]);
    endtask

    task wrap4_burst_test();
        // Test 5: 4-beat WRAP4 Burst
        logic [31:0] wrap4_wdata[0:15];
        logic [31:0] wrap4_rdata[0:15];
        static logic [15:0] wrap4_addr = 16'h2004;

        wrap4_wdata[0] = 32'h1111_1111;
        wrap4_wdata[1] = 32'h2222_2222;
        wrap4_wdata[2] = 32'h3333_3333;
        wrap4_wdata[3] = 32'h4444_4444;

        $display("\n[TEST5] 4-beat WRAP4 Burst");
        ahb_master.ahb_write(.addr(wrap4_addr), .data(wrap4_wdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(wrap4_addr), .data(wrap4_rdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_WORD));
        for (int i = 0; i < 4; i++) begin
            check_result("TEST5", i, wrap4_wdata[i], wrap4_rdata[i]);
        end
    endtask

    task incr8_burst_test();
        // Test 6: 8-beat INCR8 Burst
        logic [31:0] incr8_wdata[0:15];
        logic [31:0] incr8_rdata[0:15];
        
        incr8_wdata[0] = 32'h1111_1111;
        incr8_wdata[1] = 32'h2222_2222;
        incr8_wdata[2] = 32'h3333_3333;
        incr8_wdata[3] = 32'h4444_4444;
        incr8_wdata[4] = 32'h5555_5555;
        incr8_wdata[5] = 32'h6666_6666;
        incr8_wdata[6] = 32'h7777_7777;
        incr8_wdata[7] = 32'h8888_8888;

        $display("\n[TEST6] 8-beat INCR8 Burst");
        ahb_master.ahb_write(.addr(16'h5000), .data(incr8_wdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(16'h5000), .data(incr8_rdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_WORD));
        for (int i=0; i < 8; i++) 
            check_result("TEST6", i, incr8_wdata[i], incr8_rdata[i]);
    endtask

    task wrap8_burst_test();
        // Test 7: 8-beat WRAP8 Burst (Fixed burst length)
        logic [31:0] wrap8_wdata[0:15];
        logic [31:0] wrap8_rdata[0:15];
        static logic [15:0] wrap8_addr = 16'h3008;

        wrap8_wdata[0] = 32'hAAAA_AAAA;
        wrap8_wdata[1] = 32'hBBBB_BBBB;
        wrap8_wdata[2] = 32'hCCCC_CCCC;
        wrap8_wdata[3] = 32'hDDDD_DDDD;
        wrap8_wdata[4] = 32'hEEEE_EEEE;
        wrap8_wdata[5] = 32'hFFFF_FFFF;
        wrap8_wdata[6] = 32'h1234_5678;
        wrap8_wdata[7] = 32'h8765_4321;

        $display("\n[TEST7] 8-beat WRAP8 Burst");
        ahb_master.ahb_write(.addr(wrap8_addr), .data(wrap8_wdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(wrap8_addr), .data(wrap8_rdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_WORD));
        for (int i = 0; i < 8; i++) begin
            check_result("TEST7", i, wrap8_wdata[i], wrap8_rdata[i]);
        end
    endtask

    task inrc16_burst_test();
        // Test 8: 16-beat INCR16 Burst
        logic [31:0] incr16_wdata[0:15];
        logic [31:0] incr16_rdata[0:15];
        
        for(int i=0; i<16; i++) begin
            incr16_wdata[i] = 32'hBBBB_1000 + i;
        end

        $display("\n[TEST8] 16-beat INCR16 Burst");
        ahb_master.ahb_write(.addr(16'h6000), .data(incr16_wdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(16'h6000), .data(incr16_rdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_WORD));
        for(int i=0; i < 16; i++) 
            check_result("TEST8", i, incr16_wdata[i], incr16_rdata[i]);
    endtask

    task wrap16_burst_test();
        // Test 9: 16-beat WRAP16 Burst
        logic [31:0] wrap16_wdata[0:15];
        logic [31:0] wrap16_rdata[0:15];
        static logic [15:0] wrap16_addr = 16'h4010;

        for(int i=0; i<16; i++) begin
            wrap16_wdata[i] = 32'hAAAA_0000 + i;
        end

        $display("\n[TEST9] 16-beat WRAP16 Burst");
        ahb_master.ahb_write(.addr(wrap16_addr), .data(wrap16_wdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(wrap16_addr), .data(wrap16_rdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_WORD));
        for(int i=0; i < 16; i++) begin
            check_result("TEST9", i, wrap16_wdata[i], wrap16_rdata[i]);
        end
    endtask

endmodule

