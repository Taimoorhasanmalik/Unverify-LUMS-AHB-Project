clear -all

# Compile packages
analyze -sv09 packages/ahb3lite_pkg.sv

# Compile interface
analyze -sv09 include/ahb_if.sv

# Compile properties
analyze -sv09 formal/ahb_properties.sv


# Compile RTL
analyze -sv09 rtl/mem.sv
analyze -sv09 rtl/design.sv

# Compile Testbenche
analyze -sv09 sim/ahb_tb.sv
analyze -sv09 sim/top.sv

elaborate -top top 

clock HCLK
reset ~HRESETn


