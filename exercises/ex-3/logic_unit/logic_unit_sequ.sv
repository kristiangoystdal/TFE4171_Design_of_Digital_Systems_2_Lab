// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------

`default_nettype none

module logic_unit_sequ #(
    parameter    WIDTH = 64
)(
    input  logic             clk,
    input  logic             rst,
    input  logic [WIDTH-1:0] req_vec,
    input  logic             valid,
    output logic             out,
    output logic             done
);

    //////////////////////
    // Internal Signals //
    //////////////////////
    logic [WIDTH-1:0] req_vec_reg;
    logic [WIDTH-1:0] counter;
    logic             or_result_reg;
    logic             out_reg;
    logic             busy;
    logic             done_reg;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            out_reg       <= 1'b0;
            done_reg      <= 1'b1;
            busy          <= 1'b0;
            req_vec_reg   <= WIDTH'(0);
            counter       <= WIDTH'(0);
            or_result_reg <= (WIDTH-1)'(0);
        end else begin
            if (valid && done_reg) begin
                busy     <= 1'b1;
                req_vec_reg   <= req_vec;
                or_result_reg <= req_vec[0];
                done_reg      <= 1'b0;
                counter       <= WIDTH'(0);
            end

            if (busy) begin
                if (counter < (WIDTH-2)) begin
                    or_result_reg <= or_result_reg || req_vec_reg[counter+1];
                    counter <= counter + WIDTH'(1);
                end else if (counter == (WIDTH-2)) begin
                    out_reg <= req_vec_reg[(WIDTH-1)] && or_result_reg;
                    done_reg <= 1'b1;
                end
                if (counter == (WIDTH-2)) begin
                    busy <= 1'b0;
                end else begin
                    out_reg  <= 1'b0;
                    done_reg <= 1'b0;
                end
            end else begin
                out_reg <= 1'b0;
		    end
        end
    end

    assign out = out_reg;
    assign done = done_reg;

endmodule
