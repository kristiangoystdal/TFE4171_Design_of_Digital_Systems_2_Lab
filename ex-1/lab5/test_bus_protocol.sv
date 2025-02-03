/* test_bus_protocol.v module
*/
                                                                                                   
module test_bus_protocol (output bit clk, reset,
                          input logic dValid, dAck,
                          input logic [7:0] data);
                                                                                                   
bus_protocol bp1(.*);
bind bus_protocol bus_protocol_property bpb1 (.*);
                                                                                                   
initial begin clk=1; reset=1; end
always #5 clk=!clk;
                                                                                                   
initial
begin
  @(negedge clk); reset=1;
  @(negedge clk); reset=0;
end
                                                                                                   
always @(posedge clk)
  $display($stime,,,"clk=%b dValid=%b data=%h dAck=%b",
                clk,dValid,data,dAck);
                                                                                                   
endmodule
