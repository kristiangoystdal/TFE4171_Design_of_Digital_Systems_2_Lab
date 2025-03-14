
program alu_props(input clk,a,b,op,reg1,reg2,reg3,r);

//assert property (@(posedge clk) .... );

endprogram


module sva_wrapper;
	bind alu 				// Bind to all occurrences of alu 
	alu_props alu_sva_bind 	// Bind alu_props to alu and call this
							// instantiation alu_sva_bind
	(
	.clk(Clk),				// Connect the SystemVerilog ports to 
	.a(A),					// VHDL ports(CLK, A, B, OP, R) 
	.b(B),
	.op(Op),
	.r(R),
	.reg1(Reg1),			//and to the internal signals 
	.reg2(Reg2),			//(REG1, REG2, REG3)
	.reg3(Reg3)
	); 	
endmodule


