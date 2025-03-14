module addern #(parameter N = 4)(input [N-1:0] op1, op2, output [N:0] sum);
//op1 := N bit Addend; op2 := N bit Augend; sum := N+1 bit result, includes carry
    assign sum = {1'b0, op1} + {1'b0, op2};
endmodule

