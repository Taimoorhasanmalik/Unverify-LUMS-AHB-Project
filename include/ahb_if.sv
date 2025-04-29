`timescale 1ns/1ps

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

    modport master(
        input  HCLK, HREADY, HRDATA, HRESP, HRESETn,
        output HSEL, HADDR, HTRANS, HWRITE, HSIZE, HBURST, HPROT, HWDATA
    );

    modport slave(
        input  HCLK, HRESETn, HSEL, HADDR, HTRANS, HWRITE, HSIZE, HBURST, HPROT, HWDATA,
        output HRDATA, HREADYOUT, HRESP
    );

endinterface
