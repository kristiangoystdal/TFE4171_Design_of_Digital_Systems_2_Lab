/* test_pci_protocol.sv module
*/

module test_pci_protocol;
logic clk, reset_;

wire TRDY_, DEVSEL_;
wire FRAME_, IRDY_;
wire [3:0] C_BE_;
wire [31:0] AD;

pci_master pcim (clk, reset_, TRDY_, DEVSEL_, FRAME_, IRDY_, C_BE_, AD);
pci_target pcit (clk, reset_, TRDY_, DEVSEL_, FRAME_, IRDY_, C_BE_, AD);

pci_protocol_property pciPrp (clk, reset_, TRDY_, DEVSEL_, FRAME_, IRDY_, C_BE_, AD);
                                                                                                   
initial begin clk=1; reset_=1; end
always #5 clk=!clk;

initial
begin
  @(negedge clk); reset_=0;
  @(negedge clk); reset_=1;

  #200;
  @(negedge clk); $finish(2);
end

always @(posedge clk)
  $display($stime,,,"clk=%b reset_=%b FRAME_=%b AD=%h C_BE_=%b IRDY_=%b TRDY_=%b DEVSEL_=%b", 
  	             clk, reset_, FRAME_, AD, C_BE_, IRDY_, TRDY_, DEVSEL_
	);

endmodule
