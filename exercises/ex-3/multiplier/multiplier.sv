module multiplier(clk, rst, multiplier, multiplicand, product, ready, start);
    input clk, rst, start;
    input [3:0] multiplicand, multiplier;
    output [7:0] product;
    output ready;

    enum {ready_s = 0, check_s, add_s, shift_s} state; //is allowed to be modified for optimization purposes
    logic [3:0] m_out, q_out;
    logic init, shift, add, ser_in; // ser_in := shift value from A to Q
    logic [4:0] sum, a_out;
    logic unsigned [1:0] cnt; //counter for keeping track of iterations

    //load M and Q, clear A
    assign init = (state == ready_s)? start: 0;
    //indicates that multiplier (result) is ready
    assign ready = (state == ready_s)? 1: 0;
    //indirect way of shifting values from A to Q
    assign ser_in = (add & sum[0]) | (~add & a_out[0]);
    //the product is composed out of A and Q contents 
    assign product = {a_out[3:0], q_out};

    addern ADDER(.op1(a_out[3:0]), .op2(m_out), .sum(sum)); //4-bit adder; 5-bit output includes carry
    //4-bit multiplicand register
    regn #(.N(4)) M(.d_in(multiplicand), .d_out(m_out), .clk(clk), .load(init), .shift(1'b0), .clear(1'b0), .ser_in(1'b0));
    //4-bit multiplier register
    regn #(.N(4)) Q(.d_in(multiplier), .d_out(q_out), .clk(clk), .load(init), .shift(shift), .clear(1'b0), .ser_in(ser_in));
    //5-bit accumulator register
    regn #(.N(5)) A(.d_in(sum), .d_out(a_out), .clk(clk), .load(add), .shift(shift), .clear(init), .ser_in(1'b0));

    //-------------------------------------------------------------------------------
    //    -- code outside this region should not be modified (except state_t data type)
    //-------------------------------------------------------------------------------
    always @(posedge clk)
    begin
        if (rst) begin
            state <= add_s;
            shift <= 1'b0;
            add <= 1'b0;
        end
        else begin
           case (state)
                ready_s: begin
                    if (start) begin //start pulse applied?
                        state <=check_s; //start the algorithm
                        cnt <= 0; //reset cnt when loading new operands
                    end
                end

                check_s: begin
                    if(q_out[0]) begin //check the current LSB of the multiplier
                        state <= add_s; //add if multiplier bit = 1
                        add <= 1'b1;
                    end
                    else begin
                        state <= shift_s; //skip add if multiplier bit = 0
                        shift <= 1'b1;
                    end
                end

                add_s: begin
                    state <= shift_s; //shift after add
                    shift <= 1'b1;
                    add <= 1'b0;
                end

                shift_s: begin
                    if (cnt == 2) begin
                        state <= ready_s; //indicate that the computation is finished
                    end
                    else begin
                        state <= check_s; //next iteration of algorithm
                    end
		    shift <= 1'b0;
		    cnt <= cnt + 1; 
                end           
            endcase
        end
    end
    //-------------------------------------------------------------------------------
    //-- end of the region
    //-------------------------------------------------------------------------------
endmodule