/*
-- serial receiver
--
-- Design description:
--
-- This module watches an input line, 'rxd', for serial transmissions of bytes
-- (8 bits). A transmission begins with a '0' start bit, followed by 8 data
-- bits.
-- Byte transmissions may follow each other immediately.
-- If after a transmission the input line is '1' the transmission is considered
-- 'idle' and the receiver waits for a start bit.
--
-- There is no parity bit and no stop bit.
*/

module readserial(input clk, reset_n, rxd, output [7:0] data, output logic valid);
    //clock signal, reset signal, serial in, data out, data valid
    enum {IDLE, READ_DATA} state_s;
    reg [7:0] data_i;
    shortint unsigned cnt_s;
    logic cnt_en;

    always @(posedge clk or negedge reset_n) begin: counter
        if(~reset_n) begin //asynchronous reset (active low)
            cnt_s <= 0;
        end
        else begin //rising clock edge
            if (cnt_en) begin
                cnt_s <= (cnt_s + 1) % 8;
            end
        end
    end

    always @(posedge clk) begin: shift_reg
        data_i[7:1] <= data_i[6:0];
        data_i[0] <= rxd;
    end

    always @(posedge clk or negedge reset_n) begin: ctrl
        if (~reset_n) begin //asynchronous reset (active low)
            state_s <= IDLE;
            valid <= 0;
            cnt_en <= 0;
        end

        else begin //rising clock edge
            case (state_s)
                IDLE: begin
                    if(~rxd) begin
                        state_s <= READ_DATA;
                        cnt_en <= 1;
                    end
                    valid <= 0;
                end

                READ_DATA: begin
                    if (cnt_s == 7) begin
                        state_s <= IDLE;
                        valid <= 1;
                        cnt_en <= 0;
                    end
                end    
            endcase
        end
    end
    assign data = data_i;
endmodule