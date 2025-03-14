rm -rf work
vlib work
vlog +cover=bcefsx -sv alu_tb.sv
vcom alu.vhd 
vsim -c -coverage alu_tb -do "run 1000ns; coverage report -memory -cvg -details -file coverage_rep.txt;exit"
