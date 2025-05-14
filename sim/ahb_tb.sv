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
        single_incr_burst_test();
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

    task single_incr_burst_test();
        // Test 4: Single INCR Burst
        begin
            logic [31:0] wr_data[0:15];
            logic [31:0] rd_data[0:15];
            wr_data[0] = 32'hCAFE_BABE;
            $display("\n[TEST4] Single INCR Burst");
            //Byte
            ahb_master.ahb_write(.addr(16'h0050), .data(wr_data), .num_beats(1), .burst_type(HBURST_INCR), .size(HSIZE_BYTE));
            ahb_master.ahb_read(.addr(16'h0050), .data(rd_data), .num_beats(1), .burst_type(HBURST_INCR), .size(HSIZE_BYTE));
            check_result("TEST4 (Byte)", 0, wr_data[0] & 32'h000000FF, rd_data[0] & 32'h000000FF);

            //Half Word
            ahb_master.ahb_write(.addr(16'h0050), .data(wr_data), .num_beats(1), .burst_type(HBURST_INCR), .size(HSIZE_HWORD));
            ahb_master.ahb_read(.addr(16'h0050), .data(rd_data), .num_beats(1), .burst_type(HBURST_INCR), .size(HSIZE_HWORD));
            check_result("TEST4 (Half Word)", 0, wr_data[0] & 32'h0000FFFF, rd_data[0] & 32'h0000FFFF);

            //Word
            ahb_master.ahb_write(.addr(16'h0050), .data(wr_data), .num_beats(1), .burst_type(HBURST_INCR), .size(HSIZE_WORD));
            ahb_master.ahb_read(.addr(16'h0050), .data(rd_data), .num_beats(1), .burst_type(HBURST_INCR), .size(HSIZE_WORD));
            check_result("TEST4 (Word)", 0, wr_data[0], rd_data[0]);
        end
    endtask

    task inrc4_burst_test();
        // Test 5: 4-beat INCR4 Burst
        logic [31:0] incr4_wdata[0:15];
        logic [31:0] incr4_rdata[0:15];
        logic [15:0] base_addr;

        incr4_wdata[0] = 32'hCAFE_F00D;
        incr4_wdata[1] = 32'hDEAD_BEEF;
        incr4_wdata[2] = 32'hBAAD_F00D;
        incr4_wdata[3] = 32'hFACE_B00C;

        base_addr = 16'h1004;

        $display("\n[TEST5] 4-beat INCR4 Burst");

        // 1. Byte Transfers
        ahb_master.ahb_write(.addr(base_addr), .data(incr4_wdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_BYTE));
        ahb_master.ahb_read(.addr(base_addr), .data(incr4_rdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_BYTE));
        for (int i = 0; i < 4; i++) begin
            logic [7:0] actual_byte;
            logic [15:0] curr_addr;
            curr_addr = base_addr + i;
            actual_byte = (incr4_rdata[i] >> (8 * curr_addr[1:0])) & 8'hFF;
            check_result("TEST5 (Byte)", i, incr4_wdata[i][7:0], actual_byte);
        end

        // 2. Halfword Transfers
        ahb_master.ahb_write(.addr(base_addr), .data(incr4_wdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_HWORD), .insert_busy('1));
        ahb_master.ahb_read(.addr(base_addr), .data(incr4_rdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_HWORD));
        for (int i = 0; i < 4; i++) begin
            logic [15:0] actual_halfword;
            logic [15:0] curr_addr;
            curr_addr = base_addr + (i * 2);
            actual_halfword = (incr4_rdata[i] >> (16 * curr_addr[1])) & 16'hFFFF;
            check_result("TEST5 (Half Word)", i, incr4_wdata[i][15:0], actual_halfword);
        end

        // 3. Word Transfers
        ahb_master.ahb_write(.addr(base_addr), .data(incr4_wdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(base_addr), .data(incr4_rdata), .num_beats(4), .burst_type(HBURST_INCR4), .size(HSIZE_WORD));
        for (int i = 0; i < 4; i++) begin
            check_result("TEST5 (Word)", i, incr4_wdata[i], incr4_rdata[i]);
        end
    endtask

    task wrap4_burst_test();
        // Test 6: 4-beat WRAP4 Burst
        logic [31:0] wrap4_wdata[0:15];
        logic [31:0] wrap4_rdata[0:15];
        static logic [15:0] wrap4_addr = 16'h2004;

        wrap4_wdata[0] = 32'h1111_1111;
        wrap4_wdata[1] = 32'h2222_2222;
        wrap4_wdata[2] = 32'h3333_3333;
        wrap4_wdata[3] = 32'h4444_4444;

        $display("\n[TEST6] 4-beat WRAP4 Burst");

        // 1. Byte Transfers
        ahb_master.ahb_write(.addr(wrap4_addr), .data(wrap4_wdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_BYTE));
        ahb_master.ahb_read (.addr(wrap4_addr), .data(wrap4_rdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_BYTE));
        for (int i = 0; i < 4; i++) begin
            logic [7:0] actual_byte;
            logic [15:0] curr_addr;
            curr_addr = wrap4_addr + i;
            actual_byte = (wrap4_rdata[i] >> (8 * curr_addr[1:0])) & 8'hFF;
            check_result("TEST6 (Byte)", i, wrap4_wdata[i][7:0], actual_byte);
        end

        // 2. Halfword Transfers
        ahb_master.ahb_write(.addr(wrap4_addr), .data(wrap4_wdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_HWORD));
        ahb_master.ahb_read (.addr(wrap4_addr), .data(wrap4_rdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_HWORD));
        for (int i = 0; i < 4; i++) begin
            logic [15:0] actual_halfword;
            logic [15:0] curr_addr;
            curr_addr = wrap4_addr + (i * 2);
            actual_halfword = (wrap4_rdata[i] >> (16 * curr_addr[1])) & 16'hFFFF;
            check_result("TEST6 (Half Word)", i, wrap4_wdata[i][15:0], actual_halfword);
        end

        // 3. Word Transfers
        ahb_master.ahb_write(.addr(wrap4_addr), .data(wrap4_wdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_WORD), .insert_busy('1));
        ahb_master.ahb_read (.addr(wrap4_addr), .data(wrap4_rdata), .num_beats(4), .burst_type(HBURST_WRAP4), .size(HSIZE_WORD));
        for (int i = 0; i < 4; i++) begin
            check_result("TEST6 (Word)", i, wrap4_wdata[i], wrap4_rdata[i]);
        end
    endtask

    task incr8_burst_test();
        // Test 7: 8-beat INCR8 Burst
        logic [31:0] incr8_wdata[0:15];
        logic [31:0] incr8_rdata[0:15];
        logic [15:0] base_addr;

        base_addr = 16'h5000;

        incr8_wdata[0] = 32'h1111_1111;
        incr8_wdata[1] = 32'h2222_2222;
        incr8_wdata[2] = 32'h3333_3333;
        incr8_wdata[3] = 32'h4444_4444;
        incr8_wdata[4] = 32'h5555_5555;
        incr8_wdata[5] = 32'h6666_6666;
        incr8_wdata[6] = 32'h7777_7777;
        incr8_wdata[7] = 32'h8888_8888;

        $display("\n[TEST7] 8-beat INCR8 Burst");

        // 1. Byte Transfers
        ahb_master.ahb_write(.addr(base_addr), .data(incr8_wdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_BYTE), .insert_busy('1));
        ahb_master.ahb_read(.addr(base_addr), .data(incr8_rdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_BYTE));
        for (int i = 0; i < 8; i++) begin
            logic [7:0] actual_byte;
            logic [15:0] curr_addr;
            curr_addr = base_addr + i;
            actual_byte = (incr8_rdata[i] >> (8 * curr_addr[1:0])) & 8'hFF;
            check_result("TEST7 (Byte)", i, incr8_wdata[i][7:0], actual_byte);
        end

        // 2. Halfword Transfers
        ahb_master.ahb_write(.addr(base_addr), .data(incr8_wdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_HWORD));
        ahb_master.ahb_read(.addr(base_addr), .data(incr8_rdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_HWORD));
        for (int i = 0; i < 8; i++) begin
            logic [15:0] actual_halfword;
            logic [15:0] curr_addr;
            curr_addr = base_addr + (i * 2);
            actual_halfword = (incr8_rdata[i] >> (16 * curr_addr[1])) & 16'hFFFF;
            check_result("TEST7 (Half Word)", i, incr8_wdata[i][15:0], actual_halfword);
        end

        // 3. Word Transfers
        ahb_master.ahb_write(.addr(base_addr), .data(incr8_wdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(base_addr), .data(incr8_rdata), .num_beats(8), .burst_type(HBURST_INCR8), .size(HSIZE_WORD));
        for (int i = 0; i < 8; i++) begin
            check_result("TEST7 (Word)", i, incr8_wdata[i], incr8_rdata[i]);
        end
    endtask

    task wrap8_burst_test();
        // Test 8: 8-beat WRAP8 Burst
        logic [31:0] wrap8_wdata[0:15];
        logic [31:0] wrap8_rdata[0:15];
        static logic [15:0] wrap8_addr;

        wrap8_addr = 16'h3008;

        wrap8_wdata[0] = 32'hAAAA_AAAA;
        wrap8_wdata[1] = 32'hBBBB_BBBB;
        wrap8_wdata[2] = 32'hCCCC_CCCC;
        wrap8_wdata[3] = 32'hDDDD_DDDD;
        wrap8_wdata[4] = 32'hEEEE_EEEE;
        wrap8_wdata[5] = 32'hFFFF_FFFF;
        wrap8_wdata[6] = 32'h1234_5678;
        wrap8_wdata[7] = 32'h8765_4321;

        $display("\n[TEST8] 8-beat WRAP8 Burst");

        // 1. Byte Transfers
        ahb_master.ahb_write(.addr(wrap8_addr), .data(wrap8_wdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_BYTE));
        ahb_master.ahb_read(.addr(wrap8_addr), .data(wrap8_rdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_BYTE));
        for (int i = 0; i < 8; i++) begin
            logic [7:0] actual_byte;
            logic [15:0] curr_addr;
            curr_addr = wrap8_addr + i;
            actual_byte = (wrap8_rdata[i] >> (8 * curr_addr[1:0])) & 8'hFF;
            check_result("TEST8 (Byte)", i, wrap8_wdata[i][7:0], actual_byte);
        end

        // 2. Halfword Transfers
        ahb_master.ahb_write(.addr(wrap8_addr), .data(wrap8_wdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_HWORD), .insert_busy('1));
        ahb_master.ahb_read(.addr(wrap8_addr), .data(wrap8_rdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_HWORD));
        for (int i = 0; i < 8; i++) begin
            logic [15:0] actual_halfword;
            logic [15:0] curr_addr;
            curr_addr = wrap8_addr + (i * 2);
            actual_halfword = (wrap8_rdata[i] >> (16 * curr_addr[1])) & 16'hFFFF;
            check_result("TEST8 (Half Word)", i, wrap8_wdata[i][15:0], actual_halfword);
        end

        // 3. Word Transfers
        ahb_master.ahb_write(.addr(wrap8_addr), .data(wrap8_wdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(wrap8_addr), .data(wrap8_rdata), .num_beats(8), .burst_type(HBURST_WRAP8), .size(HSIZE_WORD));
        for (int i = 0; i < 8; i++) begin
            check_result("TEST8 (Word)", i, wrap8_wdata[i], wrap8_rdata[i]);
        end
    endtask

    task inrc16_burst_test();
        // Test 9: 16-beat INCR16 Burst
        logic [31:0] incr16_wdata[0:15];
        logic [31:0] incr16_rdata[0:15];
        logic [15:0] base_addr;

        base_addr = 16'h6000;

        for(int i = 0; i < 16; i++) begin
            incr16_wdata[i] = 32'hBBBB_1000 + i;
        end

        $display("\n[TEST9] 16-beat INCR16 Burst");

        // 1. Byte Transfers
        ahb_master.ahb_write(.addr(base_addr), .data(incr16_wdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_BYTE));
        ahb_master.ahb_read(.addr(base_addr), .data(incr16_rdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_BYTE));
        for (int i = 0; i < 16; i++) begin
            logic [7:0] actual_byte;
            logic [15:0] curr_addr;
            curr_addr = base_addr + i;
            actual_byte = (incr16_rdata[i] >> (8 * curr_addr[1:0])) & 8'hFF;
            check_result("TEST9 (Byte)", i, incr16_wdata[i][7:0], actual_byte);
        end

        // 2. Halfword Transfers
        ahb_master.ahb_write(.addr(base_addr), .data(incr16_wdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_HWORD));
        ahb_master.ahb_read(.addr(base_addr), .data(incr16_rdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_HWORD));
        for (int i = 0; i < 16; i++) begin
            logic [15:0] actual_halfword;
            logic [15:0] curr_addr;
            curr_addr = base_addr + (i * 2);
            actual_halfword = (incr16_rdata[i] >> (16 * curr_addr[1])) & 16'hFFFF;
            check_result("TEST9 (Half Word)", i, incr16_wdata[i][15:0], actual_halfword);
        end

        // 3. Word Transfers
        ahb_master.ahb_write(.addr(base_addr), .data(incr16_wdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_WORD), .insert_busy('1));
        ahb_master.ahb_read(.addr(base_addr), .data(incr16_rdata), .num_beats(16), .burst_type(HBURST_INCR16), .size(HSIZE_WORD));
        for (int i = 0; i < 16; i++) begin
            check_result("TEST9 (Word)", i, incr16_wdata[i], incr16_rdata[i]);
        end
    endtask

    task wrap16_burst_test();
        // Test 10: 16-beat WRAP16 Burst
        logic [31:0] wrap16_wdata[0:15];
        logic [31:0] wrap16_rdata[0:15];
        static logic [15:0] wrap16_addr;

        wrap16_addr = 16'h4010;

        for (int i = 0; i < 16; i++) begin
            wrap16_wdata[i] = 32'hAAAA_0000 + i;
        end

        $display("\n[TEST10] 16-beat WRAP16 Burst");

        // 1. Byte Transfers
        ahb_master.ahb_write(.addr(wrap16_addr), .data(wrap16_wdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_BYTE), .insert_busy('1));
        ahb_master.ahb_read(.addr(wrap16_addr), .data(wrap16_rdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_BYTE));
        for (int i = 0; i < 16; i++) begin
            logic [7:0] actual_byte;
            logic [15:0] curr_addr;
            curr_addr = wrap16_addr + i;
            actual_byte = (wrap16_rdata[i] >> (8 * curr_addr[1:0])) & 8'hFF;
            check_result("TEST10 (Byte)", i, wrap16_wdata[i][7:0], actual_byte);
        end

        // 2. Halfword Transfers
        ahb_master.ahb_write(.addr(wrap16_addr), .data(wrap16_wdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_HWORD));
        ahb_master.ahb_read(.addr(wrap16_addr), .data(wrap16_rdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_HWORD));
        for (int i = 0; i < 16; i++) begin
            logic [15:0] actual_halfword;
            logic [15:0] curr_addr;
            curr_addr = wrap16_addr + (i * 2);
            actual_halfword = (wrap16_rdata[i] >> (16 * curr_addr[1])) & 16'hFFFF;
            check_result("TEST10 (Half Word)", i, wrap16_wdata[i][15:0], actual_halfword);
        end

        // 3. Word Transfers
        ahb_master.ahb_write(.addr(wrap16_addr), .data(wrap16_wdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_WORD));
        ahb_master.ahb_read(.addr(wrap16_addr), .data(wrap16_rdata), .num_beats(16), .burst_type(HBURST_WRAP16), .size(HSIZE_WORD));
        for (int i = 0; i < 16; i++) begin
            check_result("TEST10 (Word)", i, wrap16_wdata[i], wrap16_rdata[i]);
        end
    endtask

endmodule

