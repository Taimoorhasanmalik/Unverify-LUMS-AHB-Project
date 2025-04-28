`timescale 1ns/1ps

import ahb3lite_pkg::*;

module ahb_tb(ahb_if.master ahb_master);

    parameter TEST_TIMEOUT = 1_000_000;
    int error_count = 0;
    logic [15:0] test_rdata;

    //-------------------------------------------
    // Reset Task
    //-------------------------------------------
    task reset_dut();
        ahb_master.HSEL   = '0;
        ahb_master.HADDR  = '0;
        ahb_master.HTRANS = HTRANS_IDLE;
        ahb_master.HWRITE = 0;
        ahb_master.HSIZE  = HSIZE_WORD;
        ahb_master.HBURST = HBURST_SINGLE;
        ahb_master.HPROT  = 4'b0011;
        ahb_master.HWDATA = '0;
        
        ahb_master.HRESETn = 0;
        repeat(5) @(posedge ahb_master.HCLK);
        ahb_master.HRESETn = 1;
        $display("[%0t] Reset Completed", $time);
    endtask

    //-------------------------------------------
    // Single Write Task
    //-------------------------------------------
	task ahb_write(input logic [15:0] addr, input logic [31:0] data);
	    // Address Phase
	    ahb_master.HSEL   = 1'b1;
	    ahb_master.HADDR  = addr;
	    ahb_master.HTRANS = HTRANS_NONSEQ;
	    ahb_master.HWRITE = 1'b1;
	    ahb_master.HSIZE  = HSIZE_WORD;
	    ahb_master.HBURST = HBURST_SINGLE;
	    $display("[%0t] WR Single Addr=0x%0h", $time, addr);
	    
	    @(posedge ahb_master.HCLK);
	    
	    // Data Phase
	    ahb_master.HWDATA = data;
	    wait(ahb_master.HREADY);
	    @(posedge ahb_master.HCLK);
	    if (ahb_master.HRESP !== HRESP_OKAY) begin
		$error("[%0t] WR Single Error: HRESP=0x%0h", $time, ahb_master.HRESP);
		error_count++;
	    end
	    $display("[%0t] WR Single Data=0x%0h", $time, data);
	    
	    ahb_master.HTRANS = HTRANS_IDLE;
	    ahb_master.HSEL   = 1'b0;
	endtask

    //-------------------------------------------
    // Single Read Task
    //-------------------------------------------
	task ahb_read(input logic [15:0] addr, output logic [31:0] data);
	    // Address Phase
	    ahb_master.HSEL   = 1'b1;
	    ahb_master.HADDR  = addr;
	    ahb_master.HTRANS = HTRANS_NONSEQ;
	    ahb_master.HWRITE = 1'b0;
	    ahb_master.HSIZE  = HSIZE_WORD;
	    ahb_master.HBURST = HBURST_SINGLE;
	    $display("[%0t] RD Single Addr=0x%0h", $time, addr);
	    
	    @(posedge ahb_master.HCLK);
	    
	    // Data Phase
	    wait(ahb_master.HREADY);
	    @(posedge ahb_master.HCLK);
	    if (ahb_master.HRESP !== HRESP_OKAY) begin
		$error("[%0t] RD Single Error: HRESP=0x%0h", $time, ahb_master.HRESP);
		error_count++;
	    end
	    @(posedge ahb_master.HCLK);
	    data = ahb_master.HRDATA;
	    $display("[%0t] RD Single Data=0x%0h, HRDATA=0x%0h", $time, data, ahb_master.HRDATA);
	    
	    ahb_master.HTRANS = HTRANS_IDLE;
	    ahb_master.HSEL   = 1'b0;
	endtask

    //-------------------------------------------
    // Test Scenarios
    //-------------------------------------------
    task test_single_rw();
        static logic [31:0] wr_data = 32'hDEAD_BEEF;
        static logic [31:0] rd_data;
        
        $display("\n[TEST1] Single Write/Read");
        ahb_write(16'h0010, wr_data);
        ahb_read(16'h0010, rd_data);
        
        if(rd_data !== wr_data) begin
            $error("Single R/W mismatch: Exp=0x%8h Got=0x%8h", wr_data, rd_data);
            error_count++;
        end
    endtask

    //-------------------------------------------
    // Main Test Flow
    //-------------------------------------------
    initial begin : main_test
        reset_dut();
        
        fork : timeout_block
            begin
                #TEST_TIMEOUT;
                $error("[TIMEOUT] Simulation timed out");
                error_count++;
                disable main_test;
            end
        join_none

        test_single_rw();

        disable timeout_block;
        
        if(error_count == 0)
            $display("\n[PASS] All tests completed successfully");
        else
            $display("\n[FAIL] %0d errors detected", error_count);
        
        $finish;
    end

    //-------------------------------------------
    // Assertion Monitor (Placeholder)
    //-------------------------------------------


    //-------------------------------------------
    // Coverage Collector (Placeholder)
    //-------------------------------------------


endmodule
