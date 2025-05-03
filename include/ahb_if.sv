`timescale 1ns/1ps

import ahb3lite_pkg::*;

interface ahb_if(input logic HCLK);
    logic        HRESETn;
    logic        HSEL;
    logic [15:0] HADDR;
    logic [1:0]  HTRANS;
    logic        HWRITE;
    logic [2:0]  HSIZE;
    logic [2:0]  HBURST;
    logic [3:0]  HPROT;
    logic [31:0] HWDATA;
    logic        HREADY;
    logic [31:0] HRDATA;
    logic        HREADYOUT;
    logic        HRESP;

    clocking master_cb @(posedge HCLK);
        default input #1step output #1;
        output HSEL, HADDR, HTRANS, HWRITE, HSIZE, HBURST, HPROT, HWDATA;
        input HREADY, HRDATA, HRESP;
    endclocking

    //-------------------------------------------
    // Reset Task
    //-------------------------------------------
    task reset_dut();
        master_cb.HSEL   <= '0;
        master_cb.HADDR  <= '0;
        master_cb.HTRANS <= HTRANS_IDLE;
        master_cb.HWRITE <= 0;
        master_cb.HSIZE  <= HSIZE_WORD;
        master_cb.HBURST <= HBURST_SINGLE;
        master_cb.HPROT  <= 4'b0011;
        master_cb.HWDATA <= '0;

        HRESETn = 0;
        repeat(5) @(master_cb);
        HRESETn = 1;
        $display("[%0t] Reset Completed", $time);
    endtask
    
    //-------------------------------------------
    // Write Task
    //-------------------------------------------
    task ahb_write(
        input logic [15:0] addr,
        input logic [31:0] data[],
        input int num_beats,
        input logic [2:0] burst_type,
        input logic [2:0] size,
        input logic [3:0] prot = 4'b0011
    );
        logic [15:0] current_addr;
        int i;
        current_addr = addr;

        for (i = 0; i < num_beats; i++) begin
            // Address Phase
            master_cb.HADDR  <= current_addr;
            master_cb.HTRANS <= (i == 0) ? HTRANS_NONSEQ : HTRANS_SEQ;
            master_cb.HWRITE <= HWRITE_OP;
            master_cb.HSIZE  <= size;
            master_cb.HBURST <= burst_type;
            master_cb.HPROT  <= prot;
            master_cb.HSEL   <= 1'b1;

            // Data Phase
            @(master_cb);
            master_cb.HWDATA <= data[i];
            wait_ready();
            current_addr = calc_next_addr(current_addr, burst_type, size);
        end

        master_cb.HTRANS <= HTRANS_IDLE;
        master_cb.HSEL   <= 1'b0;
        @(master_cb);
    endtask

    //-------------------------------------------
    // Read Task
    //-------------------------------------------
    task ahb_read(
        input  logic [15:0] addr,
        output logic [31:0] data[],
        input  int num_beats,
        input  logic [2:0] burst_type,
        input  logic [2:0] size,
        input  logic [3:0] prot = 4'b0011
    );
        logic [15:0] current_addr;
        int i;
        data = new[num_beats];
        current_addr = addr;

        for (i = 0; i < num_beats; i++) begin
            master_cb.HADDR  <= current_addr;
            master_cb.HTRANS <= (i == 0) ? HTRANS_NONSEQ : HTRANS_SEQ;
            master_cb.HWRITE <= HREAD_OP;
            master_cb.HSIZE  <= size;
            master_cb.HBURST <= burst_type;
            master_cb.HPROT  <= prot;
            master_cb.HSEL   <= 1'b1;

            wait_ready();
            repeat(3)@(master_cb);
            data[i] = master_cb.HRDATA;
            current_addr = calc_next_addr(current_addr, burst_type, size);
        end

        master_cb.HTRANS <= HTRANS_IDLE;
        master_cb.HSEL   <= 1'b0;
    endtask

    //-------------------------------------------
    // Helper Tasks & Functions
    //-------------------------------------------
    task wait_ready();
        do begin
            @(master_cb);
            if (HREADY === 1'b0) begin
                HTRANS <= HTRANS;
                HADDR  <= HADDR;
                HWDATA <= HWDATA;
                HWRITE <= HWRITE;
                HSIZE  <= HSIZE;
                HBURST <= HBURST;
            end
        end while (master_cb.HREADY !== 1'b1);
    endtask

    function logic [15:0] calc_next_addr(
        input logic [15:0] current_addr,
        input logic [2:0]  burst_type,
        input logic [2:0]  size
    );
        int transfer_size;
        int burst_length;
        int wrap_boundary;
        logic [15:0] base_addr, next_addr;

        transfer_size = 2**size;  // Bytes per transfer

        case (burst_type)
            HBURST_WRAP4, HBURST_INCR4: burst_length = 4;
            HBURST_WRAP8, HBURST_INCR8: burst_length = 8;
            HBURST_WRAP16, HBURST_INCR16: burst_length = 16;
            default: burst_length = 1;
        endcase

        if (burst_type inside {HBURST_WRAP4, HBURST_WRAP8, HBURST_WRAP16}) begin
            wrap_boundary = burst_length * transfer_size;
            base_addr = current_addr & ~(wrap_boundary - 1);
            next_addr = base_addr + ((current_addr - base_addr + transfer_size) % wrap_boundary);
        end else begin
            next_addr = current_addr + transfer_size;
        end

        return next_addr;
    endfunction

    function logic validate_burst(input logic [2:0] burst_type, input int beats);
        case (burst_type)
            HBURST_SINGLE: return (beats == 1);
            HBURST_INCR4:  return (beats == 4);
            HBURST_WRAP4:  return (beats == 4);
            HBURST_INCR8:  return (beats == 8);
            HBURST_WRAP8:  return (beats == 8);
            HBURST_INCR16: return (beats == 16);
            HBURST_WRAP16: return (beats == 16);
            HBURST_INCR:   return 1;  // Undefined length
            default: return 0;
        endcase
    endfunction

    //-------------------------------------------
    // Modport
    //-------------------------------------------
    modport master(
        output HRESETn,
        input  HCLK,
        output HSEL, HADDR, HTRANS, HWRITE, HSIZE, HBURST, HPROT, HWDATA,
        input  HREADY, HRDATA, HRESP,
        clocking master_cb,
        import  reset_dut,
        import  ahb_write,
        import  ahb_read
    );

endinterface
