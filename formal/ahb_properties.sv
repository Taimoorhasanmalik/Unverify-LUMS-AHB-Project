//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (c) Copyright 2025 Team-Unverified-LUMS-AHB-Project. All Rights Reserved.
//
// File name : ahb_properties.sv
// Title : TestBench
// Description : File for defining properties and their corresponding assertions
// Notes :
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////


module ahb_properties  (
    input logic        HCLK,
    input logic        HRESETn,
    output logic        HSEL,
    output logic [15:0] HADDR,
    output logic [1:0]  HTRANS,
    output logic        HWRITE,
    output logic [2:0]  HSIZE,
    output logic [2:0]  HBURST,
    output logic [3:0]  HPROT,
    output logic [31:0] HWDATA,
    output logic        HREADY,
    input logic [31:0] HRDATA,
    input logic        HREADYOUT,
    input logic        HRESP
);

property successful_transfer;
    @(posedge HCLK) HREADY |-> !HRESP;
endproperty

successful_transfer_as: assert property (successful_transfer) 
    else $error("Assertion successful_transfer_as failed! at time [%0t]",$time);

property transfer_pending;
    @(posedge HCLK) !HREADY |-> !HRESP;
endproperty

transfer_pending_as: assert property (transfer_pending) 
    else $error("Assertion transfer_pending_as failed! at time [%0t]",$time);


property error_response;
    @(posedge HCLK) HRESP |-> !HREADY ##1 HREADY;
endproperty

error_response_as: assert property (error_response) 
    else $error("Assertion error_response failed! at time [%0t]",$time);






// property reset_htrans_p;
//     @(HRESETn) $fell(HRESETn) |-> HTRANS == 2'b00;
// endproperty

// reset_htrans_as: assert property (reset_htrans_p) 
//     else $error("Assertion reset_htrans_p failed! at time [%0t]",$time);


endmodule
