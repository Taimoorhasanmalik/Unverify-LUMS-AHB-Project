# Tool Configuration
XRUN       := xrun
TOP        := top
FLIST      := -f ./flist.f
COVFILE    := ./covfile.ccf
WAVEFORM   := ./signals.svwf
FORMAL     := jaspergold
MASTER_TEST ?= 0
# Directory Structure
COVDIR     := ./cov
REGRESS    := ./regression_logs
XCELIUM_LIB:= ./xcelium.d
TCL_FILE   := ./ahb_setup.tcl

# Xcelium Compilation/Simulation Options
XRUN_OPTS  := -64bit -sv -access +rwc -xmlibdirname $(XCELIUM_LIB) -clean -licqueue -nowarn DSEM2009 -timescale 1ns/1ps

COV_OPTS := -coverage all -covfile $(COVFILE) -covoverwrite -covdut ahb3liten

# Primary Targets
.PHONY: all gui cov regress clean help

all: simulate

compile:
	$(XRUN) $(XRUN_OPTS) $(FLIST) -compile

simulate: compile
	$(XRUN) $(XRUN_OPTS) $(FLIST) -top $(TOP)

gui:
	$(XRUN) $(XRUN_OPTS) $(FLIST) -top $(TOP) -gui -input $(WAVEFORM)

cov:
	@mkdir -p $(COVDIR)
	$(XRUN) $(XRUN_OPTS) $(FLIST) $(COV_OPTS) -top $(TOP) -covdb $(COVDIR)/test.ucdb
imc:
	imc -load test &

# To run Master tests use make formal_test MASTER_TEST=1
formal_test:
	MASTER_TEST=$(MASTER_TEST) jaspergold ahb_setup.tcl 

regress:
	@mkdir -p $(REGRESS) $(COVDIR)
	@echo "Running Regression Suite with Coverage..."
	$(foreach test,$(wildcard tests/*.test), \
		$(XRUN) $(XRUN_OPTS) $(FLIST) $(COV_OPTS) \
			-top $(TOP) \
			-define $(subst .test,,$(notdir $(test))) \
			-l $(REGRESS)/$(basename $(notdir $(test))).log

clean:
	@rm -rf $(COVDIR) $(REGRESS) INCA_libs xcelium.d xrun.history *.log *.key *.vcd *.fsdb *.shm *.ucdb *.vdb *.cdd .simvision jgproject
	@echo "Clean complete."

help:
	@echo "AMBA AHB Verification Project Makefile"
	@echo "--------------------------------------"
	@echo "Targets:"
	@echo "  make           - Compile & run simulation (batch mode)"
	@echo "  make gui       - Run simulation with GUI waveform viewer"
	@echo "  make cov       - Run with coverage collection (DUT only)"
	@echo "  make regress   - Execute regression test suite with coverage"
	@echo "  make clean     - Remove all generated files"
	@echo "  make help      - Show this help message"
