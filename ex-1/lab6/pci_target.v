/* pci_target.v module

   This is a simple behavioral model that drives only a
   simple (canned!) PCI Read Transaction from the target.
   This is -not- a complete PCI target model.

*/
                                                                                                   
module pci_target (input bit clk, reset_,
		   output logic TRDY_, DEVSEL_,
                   input logic FRAME_, IRDY_,
		   input logic [3:0] C_BE_,
                   inout wire [31:0] AD
);

bit AD_enb;
reg [31:0] AD_reg;
assign AD = AD_enb ? AD_reg:32'hZ;

initial
begin

	//Keep AD float...until you want to drive data on it
	//You are not yet selected, so keep DEVSEL_ de-asserted
	AD_enb = 1'b0;
	DEVSEL_ = 1'b1;

	//On assertion of IRDY_ 
	@(negedge IRDY_);

	//Drive DEVSEL_
	//Check 4
        `ifdef check4
		DEVSEL_=1'b1; 
	`else
		DEVSEL_=1'b0; 
	`endif
                //$display("\tTARGET selected");

	//Drive TRDY_  and data
	@(negedge clk); 
		TRDY_ = 1'b0;

	//For Check2
        `ifdef check2
		AD_reg = 32'h CAFE_CAFE; 
	`else
		AD_reg = 32'h CAFE_CAFE; AD_enb = 1'b1;
	`endif

	//Insert a WAIT state
	@(negedge clk);
		TRDY_ = 1'b1;
		AD_enb = 1'b0;
                $display("\n","\tTARGET Wait Mode");

	//Drive TRDY_  and second data
	@(negedge clk); 
		TRDY_ = 1'b0;
	//For Check2
        `ifdef check2
		AD_enb = 1'b0;	
	`else
		AD_reg = 32'h FACE_FACE; AD_enb = 1'b1;
	`endif

	//Drive TRDY_  and third data
	@(negedge clk); 
		TRDY_ = 1'b0;
	//For Check2
        `ifdef check2
		AD_enb = 1'b0;
	`else
		AD_reg = 32'h CAFE_FACE; AD_enb = 1'b1;
	`endif

	@(negedge clk); 
	//De-assert TRDY_ and DEVSEL_
	@(negedge clk);
		TRDY_ = 1'b1;
		DEVSEL_ = 1'b1;
		AD_enb = 1'b0;

end
endmodule
