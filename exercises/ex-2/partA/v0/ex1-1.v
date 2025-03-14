/*
 * ex1_1
 * 
 * Purpose:
 * - Reset on rst=1
 * - When validi=1 three clk's in a row, compute data_out=a*b+c
 *   where a is data_in on the first clk, b on the second and c
 *   on the third. Also set valido=1. Else valido=0 which means
 *   data_out is not valid.
 */

module ex1_1 (
    input               clk,
    rst,
    validi,
    input        [31:0] data_in,
    output logic        valido,
    output logic [31:0] data_out
);

  enum {
    S0,
    S1,
    S2
  }
      state = S0, next = S0;

  logic [31:0] a;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      data_out <= 32'b0;
      valido   <= 1'b0;
      state = S0;
    end else begin
      case (state)

        // S0
        S0: begin
          valido <= 1'b0;
          if (validi) begin
            a = data_in;
            next = S1;
          end
        end

        // S1
        S1: begin
          if (validi) begin
            a *= data_in;
            next = S2;
          end else next = S0;
        end

        // S2
        S2: begin
          if (validi) begin
            a += data_in;
            data_out <= a;
            valido   <= 1'b1;
          end
          next = S0;
        end

      endcase
      state = next;

    end
  end
endmodule
