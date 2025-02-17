/* pci_master.v module

   This is a simple behavioral model that drives only a
   simple (canned!) PCI Read Transaction from the master.
   This is -not- a complete PCI master model.

*/
                                                                                                   
module pci_master (input bit clk, reset_,
		   input logic TRDY_, DEVSEL_,
                   output logic FRAME_, IRDY_,
		   output logic [3:0] C_BE_,
                   inout wire [31:0] AD
);

reg [31:0] data [0:7];

bit AD_enb;
reg [31:0] AD_reg;
assign AD = AD_enb ? AD_reg:32'hZ;

initial
begin

	//On assertion of reset_
	@(negedge reset_);

	//de-assert control signals
	FRAME_=1'b1; IRDY_=1'b1; 	
	
	//Don't drive AD - yet.
	AD_enb=1'b0;

	//On de-assertion of reset_
	@(posedge reset_);

	//Drive FRAME_, AD and C_BE_ (for a memory read)
	@(negedge clk); 
		FRAME_ = 1'b0;
	//check1
	`ifdef check1
		AD_reg = 32'h 0000_1234;
	`else
		AD_reg = 32'h 0000_1234; AD_enb=1'b1;
	`endif
		C_BE_ = 4'b 0110;
		$display("\n","\tDrive FRAME_, AD and Read Command");

	//Start the cycle (and drive Byte Enables)
	@(negedge clk);
		IRDY_ = 1'b0;
		AD_enb=1'b0;
		C_BE_ = 4'b 1111;
		$display("\n","\tDrive IRDY_ and Byte Enables");

	//Wait for TRDY_ to assert
	@(negedge TRDY_);

	//Read data received
	  if (! DEVSEL_) data[0] = AD;
		$display("\n","\tData Transfer Phase");

	//Wait for the next TRDY_ to assert
	@(negedge TRDY_);

	//Read data received
	  if (! DEVSEL_) data[1] = AD;
		$display("\n","\tData Transfer Phase");

	//Insert a wait state from the master
	@(negedge clk);
		IRDY_ = 1'b1;
		$display("\n","\tMaster Wait Mode");

	//Remove wait state
	@(negedge clk);
	  if (! DEVSEL_ && !TRDY_) data[1] = AD;
	//check3
	`ifdef check3
		IRDY_ = 1'b1;
	`else
		IRDY_ = 1'b0;
	`endif
		$display("\n","\tData Transfer Phase");

	//De-assert FRAME_
	@(negedge clk);
		FRAME_ = 1'b1;
		$display("\n","\tFRAME_ De-asserted");

	//De-assert C_BE_ just to introduce bug for check#5
	`ifdef check5
		C_BE_ = 4'b zzzz;
	`endif

	//De-assert IRDY_
	@(negedge clk);
		IRDY_ = 1'b1;
		$display("\n","\tCYCLE COMPLETE");

end
endmodule
