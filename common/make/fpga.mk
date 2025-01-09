# Check that given variables are set and all have non-empty values,
# die with an error otherwise.
#
# Params:
#   1. Variable name(s) to test.
#   2. (optional) Error message to print.
# c/o https://stackoverflow.com/questions/10858261/abort-makefile-if-variable-not-set
check_defined = \
    $(strip $(foreach 1,$1, \
        $(call __check_defined,$1,$(strip $(value 2)))))
__check_defined = \
    $(if $(value $1),, \
      $(error Undefined $1$(if $2, ($2))))

# variables that should be defined for all homeworks
$(call check_defined, SYNTH_SOURCES TOP_SYNTH_MODULE, Each homework Makefile should define this)

ifndef CLOCK_FREQUENCY
CLOCK_FREQUENCY=12.5
endif

ifdef TOP_IMPL_MODULE
$(call check_defined, IMPL_SOURCES TOP_IMPL_MODULE BITSTREAM_FILENAME CONSTRAINTS, Each implementation homework Makefile should define this)
endif

ifdef ZIP_SOURCES
$(call check_defined, ZIP_SOURCES ZIP_FILE, Each homework Makefile where a zip file is submitted should define this)
endif

# shorthand variables for commonly-referenced things
# NB: COMMON_DIR is wrt the Makefile in each hw's directory, not wrt this file
COMMON_DIR=../common
TCL_DIR=$(COMMON_DIR)/tcl
SDBOOT_DIR=$(COMMON_DIR)/sdcard-boot
SDBOOT_BIF=.boot.bif
PATH_UPDATE_SOURCE_FILE=~cis5710/tools/cis5710-update-path.sh
BACKEND_OUTPUT_DIR=fpga_build
CLOCK_GEN_NAME=MyClockGen
CLOCK_GEN_FILE=$(CLOCK_GEN_NAME).v

#time=/usr/bin/time -f 'command took %E m:s and %M KB'
time=/usr/bin/time

# NB: the .set_testcase.v target does create a file .set_testcase.v, but we want it to run every time so we declare it phony
.PHONY: codecheck test synth clock-gen pnr program boot clean

# if invoked with no explicit target, print out a help message
.DEFAULT: help
help:
	@echo -e "Valid targets are: codecheck test synth pnr zip program boot clean"

codecheck:
	python3 codecheck.py

test:
	@echo You can run just specific tests via:
	@echo "     pytest-3 --exitfirst --capture=no testbench.py --tests TEST1,TEST2,..."
	pytest-3 --capture=no --exitfirst testbench.py

bit: synth-yosys pnr

bit-fast: synth-yosys-fast pnr-fast check-logs

check-logs:
	-grep -iE '(warning|error|fail|removing unused)' $(BACKEND_OUTPUT_DIR)/*.log | grep -Ev '(Removing unused module ..abstract|Removing unused output signal .0.[id]cache.current_state|Replacing memory.*with list of registers)' | grep --color=always -iE '(warning|error|fail|removing unused)'

# run ecppll to set clock frequencies
clock-gen:
	mkdir -p $(BACKEND_OUTPUT_DIR)
	ecppll --internal_feedback --clkin_name input_clk_25MHz --clkin 25 --clkout0_name clk_125MHz --clkout0 125 --clkout1_name clk_25MHz --clkout1 25 --clkout2_name clk_proc --clkout2 $(CLOCK_FREQUENCY) -n $(CLOCK_GEN_NAME) -f .tmp-clk-gen.v > $(BACKEND_OUTPUT_DIR)/clock_generation_report.txt
	@echo 'check that clocks have the proper frequencies'
	grep 'clkout0 frequency: 125 MHz' $(BACKEND_OUTPUT_DIR)/clock_generation_report.txt
	grep 'clkout1 frequency: 25 MHz' $(BACKEND_OUTPUT_DIR)/clock_generation_report.txt
	@echo '//' > $(CLOCK_GEN_FILE) # overwrite existing file
	@echo '// DO NOT EDIT: This file was auto-generated by the ecppll program' >> $(CLOCK_GEN_FILE)
	@echo '//' >> $(CLOCK_GEN_FILE)
	@echo '' >> $(CLOCK_GEN_FILE)
	@echo '`timescale 1ns / 1ns' >> $(CLOCK_GEN_FILE)
	@echo '' >> $(CLOCK_GEN_FILE)
	@cat .tmp-clk-gen.v >> $(CLOCK_GEN_FILE)

# run synthesis to generate a netlist
synth-synlig: $(SYNTH_SOURCES) clock-gen
	mkdir -p $(BACKEND_OUTPUT_DIR)
	bash -c "set -o pipefail; $(time) synlig -p \"systemverilog_defines -DSYNTHESIS; read_systemverilog $(SYNTH_SOURCES); synth_ecp5 -top $(TOP_SYNTH_MODULE); write_json $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE)-netlist.json\" 2>&1 | tee $(BACKEND_OUTPUT_DIR)/synth.log"

synth: synth-yosys

synth-yosys: $(SYNTH_SOURCES) clock-gen
	mkdir -p $(BACKEND_OUTPUT_DIR)
	bash -c "set -o pipefail; $(time) yosys -p \"verilog_defines -DSYNTHESIS; read -vlog2k $(SYNTH_SOURCES); synth_ecp5 -top $(TOP_SYNTH_MODULE) -json $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE)-netlist.json\" 2>&1 | tee $(BACKEND_OUTPUT_DIR)/synth.log"

synth-yosys-fast: $(SYNTH_SOURCES) clock-gen
	mkdir -p $(BACKEND_OUTPUT_DIR)
	bash -c "set -o pipefail; $(time) yosys -p \"verilog_defines -DSYNTHESIS; read -vlog2k $(SYNTH_SOURCES); synth_ecp5 -noabc9 -run begin:check -top $(TOP_SYNTH_MODULE); hierarchy -check; stat; check -noinit; blackbox =A:whitebox; write_json $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE)-netlist.json\" 2>&1 | tee $(BACKEND_OUTPUT_DIR)/synth.log"

# run pnr to generate a bitstream
pnr: $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE)-netlist.json
	bash -c "set -o pipefail; $(time) nextpnr-ecp5 --report $(BACKEND_OUTPUT_DIR)/report.json --85k --package CABGA381 --json $< --textcfg $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE).config --lpf $(CONSTRAINTS) 2>&1 | tee $(BACKEND_OUTPUT_DIR)/pnr.log"
	python3 -m json.tool $(BACKEND_OUTPUT_DIR)/report.json > $(BACKEND_OUTPUT_DIR)/resource-report.json
	bash -c "set -o pipefail; ecppack --compress --freq 62.0 --input $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE).config --bit $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE).bit 2>&1 | tee $(BACKEND_OUTPUT_DIR)/ecppack.log"

pnr-fast: $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE)-netlist.json
	bash -c "set -o pipefail; $(time) nextpnr-ecp5 --report $(BACKEND_OUTPUT_DIR)/report.json --85k --package CABGA381 --json $< --textcfg $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE).config --lpf $(CONSTRAINTS) --no-tmdriv --placer heap 2>&1 | tee $(BACKEND_OUTPUT_DIR)/pnr.log"
	python3 -m json.tool $(BACKEND_OUTPUT_DIR)/report.json > $(BACKEND_OUTPUT_DIR)/resource-report.json
	bash -c "set -o pipefail; ecppack --compress --freq 62.0 --input $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE).config --bit $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE).bit 2>&1 | tee $(BACKEND_OUTPUT_DIR)/ecppack.log"

# program the device with a bitstream
program:
	openFPGALoader --freq 3000000 --board ulx3s $(BACKEND_OUTPUT_DIR)/$(TOP_SYNTH_MODULE).bit

# create a zip archive of source code, bitstream, and power/performance/area reports. We filter out warnings because for the ALU-only version of the processor labs we pull in a bitstream, even though the bitstream is only for the full version of the lab
zip: $(ZIP_SOURCES)
	zip -j $(ZIP_FILE) $(ZIP_SOURCES) | grep -v warning

# make BOOT.BIN image for programming FPGA from an SD card
# TODO: not working for ULX3S, I don't think it can program FPGA from the SD card
boot: vivado_output/$(BITSTREAM_FILENAME) $(SDBOOT_DIR)/zynq_fsbl_0.elf
ifndef XILINX_VIVADO
	$(error ERROR cannot find Vivado, run "source $(PATH_UPDATE_SOURCE_FILE)")
endif
	echo "the_ROM_image:{[bootloader]"$(SDBOOT_DIR)/zynq_fsbl_0.elf > $(SDBOOT_BIF)
	echo vivado_output/$(BITSTREAM_FILENAME)"}" >> $(SDBOOT_BIF)
	bootgen -image $(SDBOOT_BIF) -arch zynq -o vivado_output/BOOT.BIN

# remove build files
clean:
	rm -rf points.json sim_build/ $(BACKEND_OUTPUT_DIR)/ slpp_all/
