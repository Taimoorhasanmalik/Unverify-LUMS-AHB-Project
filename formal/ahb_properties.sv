//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (c) Copyright 2025 Team-Unverified-LUMS-AHB-Project. All Rights Reserved.
//
// File name : ahb_properties.sv
// Title : FORMAL PROPERTIES
// Description : File for defining properties and their corresponding assertions
// Notes :
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
import ahb3lite_pkg::*;


module ahb_properties_master  (
    input logic        HCLK,
    input logic        HRESETn,
    input logic        HSEL,
    input logic [15:0] HADDR,
    input logic [1:0]  HTRANS,
    input logic        HWRITE,
    input logic [2:0]  HSIZE,
    input logic [2:0]  HBURST,
    input logic [3:0]  HPROT,
    input logic [31:0] HWDATA,
    input logic        HREADY,
    output logic [31:0] HRDATA,
    output logic        HREADYOUT,
    output logic        HRESP
);

// Slave eventually completes the transfer
assume property (@(posedge HCLK)
  disable iff (!HRESETn)
  ##[1:$] HREADY);

// Master must align word accesses
assert property (@(posedge HCLK)
  disable iff (!HRESETn)
  (HTRANS inside {2'b10, 2'b11} && HSIZE == 3'b010 && HREADY) |->
  (HADDR[1:0] == 2'b00));


endmodule



module ahb_properties_slave  (
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
    @(posedge HCLK) !HREADY |-> HRESP ##1 HREADY;
endproperty

error_response_as: assert property (error_response) 
    else $error("Assertion error_response failed! at time [%0t]",$time);


property valid_addresses_burst_inc_4_p;
    @(posedge HCLK) HBURST == HBURST_WRAP4 || HBURST_INCR4 |->(HADDR % 4) == 0;

endproperty

valid_addresses_burst_inc_4_assume:assume property (valid_addresses_burst_inc_4_p);

property valid_addresses_burst_inc_8_p;
    @(posedge HCLK) HBURST == HBURST_WRAP8 || HBURST_INCR8 |->(HADDR % 8) == 0;

endproperty

valid_addresses_burst_inc_8_assume:assume property (valid_addresses_burst_inc_8_p);

property valid_addresses_burst_inc_16_p;
    @(posedge HCLK) HBURST == HBURST_WRAP16 || HBURST_INCR16 |->(HADDR % 16) == 0;

endproperty

valid_addresses_burst_inc_16_assume:assume property (valid_addresses_burst_inc_16_p);

property wrapping_4_boundary_check_p;
    @(posedge HCLK) disable iff (!HRESETn) HBURST == HBURST_WRAP4 |->  (HADDR & !(4 * HSIZE)) <= HADDR <= ((HADDR & !(4 * HSIZE)) + (4 * HSIZE));
endproperty

wrapping_4_boundary_check_as: assume property (wrapping_4_boundary_check_p);

property wrapping_8_boundary_check_p;
    @(posedge HCLK) disable iff (!HRESETn) HBURST == HBURST_WRAP8 |->  ((HADDR & !(8 * HSIZE)) <= HADDR <= (HADDR & !(8 * HSIZE)) + (8 * HSIZE));
endproperty

wrapping_8_boundary_check_as: assume property (wrapping_8_boundary_check_p);

property wrapping_16_boundary_check_p;
    @(posedge HCLK) disable iff (!HRESETn) HBURST == HBURST_WRAP16 |->  ((HADDR & !(16 * HSIZE)) <= HADDR <= (HADDR & !(16 * HSIZE)) + (16 * HSIZE));
endproperty

wrapping_16_boundary_check_as: assume property (wrapping_16_boundary_check_p);

property inc_16_boundary_check_p;
    @(posedge HCLK) disable iff (!HRESETn) HBURST == HBURST_INCR16 |->  ((HADDR & !(16 * HSIZE)) <= HADDR <= (HADDR & !(16 * HSIZE)) + (16 * HSIZE));
endproperty

inc_16_boundary_check_p_as: assume property (inc_16_boundary_check_p);



endmodule
