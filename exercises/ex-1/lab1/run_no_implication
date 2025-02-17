#!/bin/csh -fx

\rm -rf work
\rm test_dut_no_implication.log

vlib work

#--------------------------------------------------
#To compile without implication
#--------------------------------------------------
vlog -sv dut.v dut_property.sv test_dut.sv +define+no_implication

#Simulate
vsim test_dut -assertdebug -coverage -c -l test_dut_no_implication.log -do "run -all; quit"
