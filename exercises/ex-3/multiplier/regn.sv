module regn #(parameter N = 4) (d_in, d_out, clk, load, shift, clear, ser_in);
//clock (rising edge), load enable, shift enable, clear enable, serial input
input clk, load, shift, clear, ser_in;
//N bit input
input [N-1:0] d_in;
//N bit output
output [N-1:0] d_out;
//temporary register
reg [N-1:0] t_reg;

always @(posedge clk)
begin
    //clear
    if(clear) begin
        t_reg <= 0;
    end
    //load shifted
    else if (load & shift) begin
        t_reg <= {ser_in, d_in[N-1:1]};
    end
    //load
    else if (load) begin
        t_reg <= d_in;
    end
    //shift
    else if (shift) begin
        t_reg <= {ser_in, t_reg[N-1:1]};
    end
end
assign d_out = t_reg;
endmodule