`timescale 1ns/1ps

module top;

    logic HCLK;
    initial begin
      HCLK = 0;
      forever #5 HCLK = ~HCLK;
    end

    assign ahb_if_inst.HREADY = ahb_if_inst.HREADYOUT;
    
    ahb_if ahb_if_inst(.HCLK(HCLK));

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

    bind dut_inst properties p1 (ahb_if_inst.master);


endmodule
