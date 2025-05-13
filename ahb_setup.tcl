clear -all

set MASTER_TEST 0

if {[info exists ::env(MASTER_TEST)]} {
    set MASTER_TEST $::env(MASTER_TEST)
}








analyze -sv packages/ahb3lite_pkg.sv

analyze -sv include/ahb_if.sv

analyze -sv formal/ahb_properties.sv

analyze -sv rtl/mem.sv
analyze -sv rtl/design.sv

analyze -sv sim/ahb_tb.sv
if {$MASTER_TEST} {
    puts "MASTER_TEST analysis is ENABLED"
    analyze -sv +define+FORMAL+TEST_MASTER_OUTPUTS sim/top.sv
} else {
    puts "SLAVE_TEST analysis is ENABLED"
    analyze -sv +define+FORMAL+TEST_SLAVE_OUTPUTS sim/top.sv
}

elaborate -top top

clock HCLK
reset ~HRESETn
