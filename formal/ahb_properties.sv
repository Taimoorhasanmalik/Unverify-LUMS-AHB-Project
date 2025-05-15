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

`define VERIFY_SINGLE_TRANSFERS

module ahb_properties_master  (
    output logic       HCLK,
    output logic       HRESETn,
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

///---------------ASSUMPTIONS

property reset_sequence_p;
    @(posedge HCLK)
    ##[0:2] !HRESETn ##1 $rose(HRESETn);
endproperty
assume_reset_sequence: assume property(reset_sequence_p);


property HSIZE_valid_values_p;
    @(posedge HCLK) disable iff (!HRESETn)
    HSIZE inside {HSIZE_BYTE, HSIZE_HWORD, HSIZE_WORD};
endproperty
HSIZE_valid_values_as: assume property (HSIZE_valid_values_p);


///---------------ASSERTIONS


property htrans_valid_values_p;
    @(posedge HCLK) disable iff (!HRESETn)
    HTRANS inside {HTRANS_IDLE, HTRANS_BUSY, HTRANS_NONSEQ, HTRANS_SEQ};
endproperty
assert_htrans_valid: assert property(htrans_valid_values_p);

property burst_stable_signals_p;
    @(posedge HCLK) disable iff (!HRESETn)
    (HTRANS == HTRANS_SEQ) |-> 
    ($stable(HSIZE) && $stable(HBURST) && $stable(HWRITE));
endproperty
assert_burst_stable: assert property(burst_stable_signals_p);

property write_data_stable_p;
    @(posedge HCLK) disable iff (!HRESETn)
    (HWRITE && !HREADY) |-> $stable(HWDATA);
endproperty
assert_write_data_stable: assert property(write_data_stable_p);





endmodule



module ahb_properties_slave  (
    input logic        HCLK,
    output logic        HRESETn,
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

///---------------ASSUMPTIONS
`ifdef ASSUMPTIONS
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

inc_16_boundary_check_as: assume property (inc_16_boundary_check_p);



property HTRANS_after_single_burst_p;
    @(posedge HCLK) disable iff (!HRESETn)
    HBURST == HBURST_SINGLE |-> ##[0:$] HREADYOUT ##1 HTRANS == HTRANS_IDLE;
endproperty

HTRANS_after_single_burst_as: assume property (HTRANS_after_single_burst_p);


property HSIZE_valid_values_p;
    @(posedge HCLK) disable iff (!HRESETn)
    HSIZE inside {HSIZE_BYTE, HSIZE_HWORD, HSIZE_WORD};
endproperty
HSIZE_valid_values_as: assume property (HSIZE_valid_values_p);


property HSIZE_constant_throughout_burst_p;
    @(posedge HCLK) disable iff (!HRESETn)
    !$isunknown(HBURST) |-> $stable(HSIZE)[*0:$] ##0 $stable(HBURST);
endproperty
HSIZE_constant_throughout_burst_as: assume property (HSIZE_constant_throughout_burst_p);



///---------------ASSERTIONS


property idle_transfer_response_p;  
    @(posedge HCLK) disable iff (!HRESETn) (HTRANS == HTRANS_IDLE) && HREADYOUT |-> !HRESP;
endproperty

idle_transfer_response_as: assert property (idle_transfer_response_p);

property busy_transfer_response_p;
    @(posedge HCLK) disable iff (!HRESETn) (HTRANS == HTRANS_BUSY) && HREADYOUT |-> !HRESP;
endproperty

busy_transfer_response_as: assert property (busy_transfer_response_p);


property successful_transfer_p;
    @(posedge HCLK) HREADY |-> ##[0:$] HREADY |-> !HRESP;
endproperty

successful_transfer_as: assert property (successful_transfer_p) 
    else $error("Assertion successful_transfer_as failed! at time [%0t]",$time);

property transfer_pending;
    @(posedge HCLK) !HREADY |-> !HRESP[*0:$] ##0 HREADY;
endproperty

transfer_pending_as: assert property (transfer_pending) 
    else $error("Assertion transfer_pending_as failed! at time [%0t]",$time);


property error_response;
    @(posedge HCLK) HREADY && HRESP |-> !HREADY ##1 HREADY && HRESP;
endproperty

error_response_as: assert property (error_response) 
    else $error("Assertion error_response failed! at time [%0t]",$time);
`endif

`ifdef VERIFY_SINGLE_TRANSFERS
    // Assume complete single transfer input patterns
    property assume_single_transfer_inputs_p;
        @(posedge HCLK) disable iff (!HRESETn)
        HSEL |-> (
            HTRANS == HTRANS_NONSEQ &&
            HSIZE inside {HSIZE_BYTE, HSIZE_HWORD, HSIZE_WORD} &&
            HBURST == HBURST_SINGLE &&
            HWDATA >= 0 &&  // Any valid data
            HADDR inside {[0:16-1]}
        );
    endproperty
    assume_single_transfer: assume property(assume_single_transfer_inputs_p);

    // Assert only HREADY and HRESP behavior
    property assert_single_transfer_response_p;
        @(posedge HCLK) disable iff (!HRESETn)
        (HTRANS == HTRANS_NONSEQ) |-> ##[1:4] (HREADYOUT && !HRESP);
    endproperty
    assert_single_transfer_response: assert property(assert_single_transfer_response_p);
`endif

endmodule
