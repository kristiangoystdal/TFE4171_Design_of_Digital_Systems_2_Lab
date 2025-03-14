timeunit 10ns; 

module toplevel();
    logic clk, rst, validi;
    logic [31:0] data_in;
    wire 	     valido;
    wire  [31:0] data_out;
    bit   [31:0] add_a;
    bit   [31:0] add_b;
    bit   [31:0] add_res;
    bit   [31:0] mult_a;
    bit   [31:0] mult_b;
    bit   [31:0] mult_res;

    alu u_alu_add (
        .Clk(clk),
        .A(add_a),
        .B(add_b),
        .Op(3'b000),
        .R(add_res)
    );

    alu u_alu_mult (
        .Clk(clk),
        .A(mult_a),
        .B(mult_b),
        .Op(3'b111),
        .R(mult_res)
    );

    ex1_1 u_ex1_1 (
        clk, rst, validi,
        data_in,
        valido,
        data_out,
        add_a,
        add_b,
        add_res,
        mult_a,
        mult_b,
        mult_res
    );

    bind ex1_1 ex1_1_property ex1_1_bind (
        clk, rst, validi,
        data_in,
        valido,
        data_out
    );

    initial begin
        clk=1'b0;
        set_stim;
        @(posedge clk); $finish(2);
    end

    always @(posedge clk) begin
        $display($stime,,,"rst=%b clk=%b validi=%b DIN=%0d valido=%b DOUT=%0d add_a=%0d add_b=%0d add_res=%0d mult_a=%0d mult_b=%0d mult_res=%0d",
            rst, clk, validi, data_in, valido, data_out, add_a, add_b, add_res, mult_a, mult_b, mult_res);
    end

    always #5 clk=!clk;

    task set_stim;
        rst=1'b0; validi=0'b1; data_in=32'b1;
        @(negedge clk) rst=1;
        @(negedge clk) rst=0;
        
        @(negedge clk); validi=1'b0; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b0; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b0; data_in+=32'b1;
        @(negedge clk); validi=1'b0; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b0; data_in+=32'b1;
        
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b0; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b0; data_in+=32'b1;
        @(negedge clk); validi=1'b0; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b1; data_in+=32'b1;
        @(negedge clk); validi=1'b0; data_in+=32'b1;

        @(negedge clk);
    endtask

endmodule : toplevel
