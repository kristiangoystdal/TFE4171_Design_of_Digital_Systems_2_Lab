/* bus_protocol.v module

   This module drives the bus protocol
   timing diagram discussed in the class.
                                                                                                   
   This module acts as the bus interface unit of 
   your design whose protocol you are trying to verify.

*/
                                                                                                   
module bus_protocol (input bit clk, reset,
                     output bit dValid, dAck,
                     output logic [7:0] data
);
                                                                                                   
initial
begin
  $display("SCENARIO 1");
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");

  $display("SCENARIO 2");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");
                                                                                                   
  $display("SCENARIO 3");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");
  
`ifdef nobugs   
  $display("SCENARIO 4");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");
`else 
  $display("SCENARIO 4");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");
`endif
                                                                                                   
`ifdef nobugs   
  $display("SCENARIO 5");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");
`else 
  $display("SCENARIO 5");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");
`endif
                                                                                                   
`ifdef nobugs   
  $display("SCENARIO 6");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");
`else
  $display("SCENARIO 6");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");
`endif

`ifdef nobugs
  $display("SCENARIO 7");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;
  $display("\n");
`else
  $display("SCENARIO 7");
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'hx; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;

  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h1; dAck=1'b0;
  @(negedge clk); dValid=1'b1; data=8'h0; dAck=1'b1;
  @(negedge clk); dValid=1'b0; data=8'h0; dAck=1'b0;

  @(negedge clk); 
  @(negedge clk);
  $display("\n");
`endif
                                                                                                   
  @(negedge clk);

  $finish(2);
end
endmodule
