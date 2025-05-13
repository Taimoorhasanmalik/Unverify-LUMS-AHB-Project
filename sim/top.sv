`timescale 1ns/1ps
// `define FORMAL 
// `define TEST_MASTER_OUTPUTS 1
// `define TEST_SLAVE_OUTPUTS

module top;


`ifdef SIM
    logic HCLK;
    initial begin
      HCLK = 0;
      forever #5 HCLK = ~HCLK;
    end
    assign ahb_if_inst.HREADY = ahb_if_inst.HREADYOUT;
    ahb_if ahb_if_inst(.HCLK(HCLK));
    
    // ahb_wrapper wrapper_inst(HCLK);
    ahb3liten dut_inst (
        .HCLK(HCLK),
        .HRESETn(ahb_if_inst.HRESETn),
        .HSEL(ahb_if_inst.HSEL),
        .HADDR(ahb_if_inst.HADDR),
        .HTRANS(ahb_if_inst.HTRANS),
        .HWRITE(ahb_if_inst.HWRITE),
        .HSIZE(ahb_if_inst.HSIZE),
        .HBURST(ahb_if_inst.HBURST),
        .HPROT(ahb_if_inst.HPROT),
        .HWDATA(ahb_if_inst.HWDATA),
        .HREADY(ahb_if_inst.HREADY),
        .HRDATA(ahb_if_inst.HRDATA),
        .HREADYOUT(ahb_if_inst.HREADYOUT),
        .HRESP(ahb_if_inst.HRESP)
    );
    ahb_tb tb_inst (
        .ahb_master(ahb_if_inst.master)
    );
`endif

`ifdef FORMAL
    logic        HCLK;
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


    ahb3liten dut_inst (
        .HCLK   (HCLK),
        .HRESETn(HRESETn),
        .HSEL   (HSEL),
        .HADDR  (HADDR),
        .HTRANS (HTRANS),
        .HWRITE (HWRITE),
        .HSIZE  (HSIZE),
        .HBURST (HBURST),
        .HPROT  (HPROT),
        .HWDATA (HWDATA),
        .HREADY (HREADY),
        .HRDATA (HRDATA),
        .HREADYOUT(HREADYOUT),
        .HRESP(HRESP)
    );

`ifdef TEST_MASTER_OUTPUTS
    bind dut_inst ahb_properties_master p1 (
        .HCLK, .HRESETn, .HSEL, .HADDR, .HTRANS, .HWRITE, .HSIZE, .HBURST, .HPROT, .HWDATA, .HREADY, .HRDATA, .HREADYOUT, .HRESP);
`endif

`ifdef TEST_SLAVE_OUTPUTS
    bind dut_inst ahb_properties_slave p2 (
        .HCLK, .HRESETn, .HSEL, .HADDR, .HTRANS, .HWRITE, .HSIZE, .HBURST, .HPROT, .HWDATA, .HREADY, .HRDATA, .HREADYOUT, .HRESP);
`endif


`endif

endmodule
