//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (c) Copyright 2025 Team-Unverified-LUMS-AHB-Project. All Rights Reserved.
//
// File name : ahb_properties.sv
// Title : TestBench
// Description : File for defining properties and their corresponding assertions
// Notes :
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////


module properties  (
    ahb_if.master properties_if
);

property reset_async_p;
    @(properties_if.HCLK) 
        $rose(properties_if.HRESETn) |->
            $rose(properties_if.HCLK);
endproperty

reset_async_as: assert property (reset_async_p) 
    else $error("Assertion reset_async_as failed! at time [%0t]",$time);

property reset_htrans_p;
    @(properties_if.HRESETn) $fell(properties_if.HRESETn) |-> properties_if.HTRANS == 2'b00;
endproperty

reset_htrans_as: assert property (reset_htrans_p) 
    else $error("Assertion reset_htrans_p failed! at time [%0t]",$time);


endmodule