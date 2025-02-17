#!/bin/csh -fx

\rm -rf work
\rm test_counter_nobugs.log

vlib work

#--------------------------------------------------
#To compile with RTL with NO BUGS
#--------------------------------------------------
vlog -sv counter.v counter_property.sv test_counter.sv

#Simulate
vsim -assertdebug -coverage -c test_counter -l test_counter_nobugs.log -do " run -all; quit"
