# Part A

## a)
```SystemVerilog
property reset_asserted;
  @(posedge clk) rst |-> data_out == 0; 
endproperty

reset_check: assert property(reset_asserted)
  $display($stime,,,"\t\tRESET CHECK PASS:: rst_=%b data_out=%0d \n",
	   rst, data_out);
else $display($stime,,,"\t\RESET CHECK FAIL:: rst_=%b data_out=%0d \n",
	      rst, data_out);
```
At time 15 rst is high, which should make data out low. The test passes since data out is 0. 

## b) 

```SystemVerilog
property valido_asserted;
   @(posedge clk) 
   disable iff (rst) 
   validi[*3] |-> ##1 valido;
endproperty

valido_check: assert property(valido_asserted)
   $display($stime,,,"\t\tVALIDO CHECK PASS:: validi=%b valido=%b \n",
         validi, valido);
   else $display($stime,,,"\t\tVALIDO CHECK FAIL:: validi=%b valido=%b \n",
          validi, valido);
```

At time 135 it passes since valido == 1 after 3 cycles with validi == 1. It failed at time 35, since we got a reset during the 3 cycles of validi. We chose to change the assertion by adding disable iff (rst) as we thought it was expected that you need 3 cycles validi=1 AFTER a system reset, before output is ready.

## c) 

```SystemVerilog
property valido_not_asserted;
    // validi=1 and has not been high for the last 2 cycles
    @(posedge clk) !($past(validi, 2) && $past(validi, 1)) && validi |-> ##1 !valido
   //@(posedge clk) $rose(validi) && validi[*0:2] |-> ##1 !valido;
endproperty


valido_check: assert property(valido_not_asserted)
   $display($stime,,,"\t\tVALIDO_NOT CHECK PASS:: validi=%b valido=%b \n",
         validi, valido);
   else $display($stime,,,"\t\tVALIDO_NOT CHECK FAIL:: validi=%b valido=%b \n",
          validi, valido);
```
We read the task as "each string of 0, 1 or 2 length validi should be checked for a consequent low on valido". Our best solution to this was to utilize past(..., 1) and past(..., 2). This lead to the wanted checks throughout the runtime, but fails to check the first 2 cycles, as the past value of validi is before the start of the program and therefore undefined. Also, we dont check for length 0 (essentially valido always low when validi is low) becuase this does not make sense with the behaviour described in the pdf ( validi[*3] |-> ##1 valido) As for the tests themselves, they all passed as expected, since valido remained low when it was supposed to.


## d) 

```SystemVerilog
property data_out_value;
   @(posedge clk) valido |-> data_out == $past(data_in, 3) * $past(data_in, 2) + $past(data_in, 1);
endproperty

data_out_check: assert property(data_out_value)
   $display($stime,,,"\t\tDATA_OUT CHECK PASS:: a = %0d b = %0d c = %0d data_out=%0d \n",
         $past(data_in, 3), $past(data_in, 2), $past(data_in, 1), data_out);
   else $display($stime,,,"\t\tDATA_OUT CHECK FAIL:: a = %0d b = %0d c = %0d data_out=%0d \n",
          $past(data_in, 3), $past(data_in, 2), $past(data_in, 1), data_out);
```

The calculation for data out is correct using the 3 past values for a,b and c. It passes at time 135 using a = 9, b = 10 and c = 11 to get data out = 101. We are assuming validi[*3] |-> ##1 valid0 as defined in the lab PDF, which differs from the comment above check4 in the code.

## e) 

At timestamp 35 we see a FAIL, likely because of a rst=1 during the 3 cycles of validi, which our assertion does not take into account

At timestamp 185/195 we see FAIL, because validi=1 for more than 3 cycles, and valido only goes high after exactly 3 cycles, instead of remaining high for (#validi - 2) cycles

The same issue from holding validi high can be seen at 245/305/315

At 325 it once again passes, at the 6th cycle of validi. This indicates the code uses a counter which overflows from 3 to 0, instead of remaining at 3

## f) 

```SystemVerilog
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
    S2,
    S3
  }
      state = S0, next = S0;

  logic [31:0] a, b;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      valido   <= 1'b0;
      state = S0;
    end else begin
      case (state)

        // S0
        S0: begin
          if (validi) begin
            next = S1;
          end
        end

        // S1
        S1: begin
          if (validi) begin
            next = S2;
          end else next = S0;
        end

        // S2
        S2: begin
          if (validi) begin
            valido <= 1'b1;
            next = S3;
          end else begin
            next = S0;
          end
        end

        S3: begin
          if (validi) begin
            next = S3;
          end else begin
            next = S0;
            valido <= 1'b0;
          end
        end

      endcase
      state = next;
      b <= data_in;
      a <= b;
      data_out <= a * b + data_in;

    end
  end
endmodule
```

We defined a S3 for the instances where we have received 3 (or more) validi in a row. In addition to this, we moved from using a single register a that holds the calculation, to saving b and c in a shift-register layout. data_out is also calculated using the saved b and c together with data_in every cycle, as there was no defined behaviour for data_out when valido is 0. If this is not wanted, you could simply rename the data_out register, and mux the output between 0 and the calculated output.

Our solution passes all tests. It seems they overwrite each other in the logfile, but we get no errors, and ir tuns through test 4. Previously when we had errors on earlier tests, it stopped at the test that had an error.


# Part C

## b)
We ran into overflow with the provided ALU, and had to change it from 8 bit to 32 bit to reflect what the state machine expects

Mult was missing from the ALU, so we changed out 'b111 from XOR to mult, and used that

Since ALU only provides output on the positive flank we don't see a way to do this without comprehensive rewriting (since we need to provied output the same cycle that we get the final input, and within that cycle we need to process through 2 different ALUs).
We therefore decided not to finish this task, as the workload seemed too heavy to do now. We would appreciate feedback on a good way to do it with less work.

## c)
Since we did not rewrite the code properly, this does not makes sense to do. However, we expect lower coverage on opcode, since we only use 2 of them. We expect higher coverage on a, as we will have both large and small inputs due to the nature of our testvectors. We therefore also expect better crosscoverage on aXb