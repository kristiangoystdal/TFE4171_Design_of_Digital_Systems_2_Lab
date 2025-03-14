module jkff(clk, j_i, k_i, q_o);
    input clk;
    input j_i;
    input k_i;
    output q_o;

    wire d;
    wire q;

    assign d = ((~q & j_i) | (q & ~k_i)); //bitwise operations

    dff dff0(.clk(clk), .d_i(d), .q_o(q));

    assign q_o = q;

endmodule


module dff(clk, d_i, q_o);
    input clk;
    input d_i;
    output q_o;

    reg q_o;

    always @(posedge clk) 
    begin
        q_o <= d_i;
    end
endmodule