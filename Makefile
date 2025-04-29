# Tool Configuration
XRUN       := xrun
TOP        := top
FLIST      := -f ./flist.f
COVFILE    := ./covfile.ccf
WAVEFORM   := ./signals.svwf

# Directory Structure
COVDIR     := ./cov
REGRESS    := ./regression_logs
XCELIUM_LIB:= ./xcelium.d

# Xcelium Compilation/Simulation Options
XRUN_OPTS  := -64bit -sv -access +rwc -xmlibdirname $(XCELIUM_LIB) -clean -licqueue -nowarn DSEM2009 -timescale 1ns/1ps

COV_OPTS   := -coverage all -covfile $(COVFILE) -covoverwrite

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
	$(XRUN) $(XRUN_OPTS) $(FLIST) $(COV_OPTS) -top $(TOP)

regress:
	@mkdir -p $(REGRESS)
	@echo "Running Regression Suite..."
	$(foreach test,$(wildcard tests/*.test), \
		$(XRUN) $(XRUN_OPTS) $(FLIST) \
			-top $(TOP) \
			-define $(subst .test,,$(notdir $(test))) \
			-l $(REGRESS)/$(basename $(notdir $(test))).log;)

clean:
	@rm -rf $(COVDIR) $(REGRESS) INCA_libs xcelium.d xrun.history *.log *.key *.vcd *.fsdb *.shm *.ucdb *.vdb *.cdd .simvision
	@echo "Clean complete."

help:
	@echo "AMBA AHB Verification Project Makefile"
	@echo "--------------------------------------"
	@echo "Targets:"
	@echo "  make           - Compile & run simulation (batch mode)"
	@echo "  make gui       - Run simulation with GUI waveform viewer"
	@echo "  make cov       - Run with coverage collection"
	@echo "  make regress   - Execute regression test suite"
	@echo "  make clean     - Remove all generated files"
	@echo "  make help      - Show this help message"

