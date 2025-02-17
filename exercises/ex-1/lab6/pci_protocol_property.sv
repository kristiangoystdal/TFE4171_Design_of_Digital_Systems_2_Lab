/* Properties (assertions) for bus_protocol.v
*/
                                                                                                   
module pci_protocol_property (input logic clk, reset_, TRDY_, DEVSEL_, FRAME_, IRDY_,
                              input logic [3:0] C_BE_,
                              input logic [31:0] AD
);

        /*--------------------------------------------------
        CHECK # 1. On falling edge of FRAME_, AD or C_BE_ cannot be unknown. 
          --------------------------------------------------*/
`ifdef check1
        property checkPCI_AD_CBE;
          @(posedge clk) disable iff (!reset_) 
		FRAME_ ##1 !FRAME_ |-> !$isunknown(AD) && !$isunknown(C_BE_);
        endproperty
        assert property (checkPCI_AD_CBE) else $display($stime,,,"CHECK1:checkPCI_AD_CBE FAIL\n");
`endif

        /*--------------------------------------------------
        CHECK # 2. When IRDY_ and TRDY_ are asserted (low) AD or C_BE_ cannot be unknown.
          --------------------------------------------------*/
`ifdef check2
        property checkPCI_DataPhase;
          @(posedge clk) disable iff (!reset_) 
		!IRDY_ && !TRDY_ |-> !$isunknown(AD) && !$isunknown(C_BE_);
        endproperty
        assert property (checkPCI_DataPhase) else $display($stime,,,"CHECK2:checkPCI_DataPhase FAIL\n");
`endif

        /*--------------------------------------------------
        CHECK # 3. FRAME_ can go High only if IRDY_ is asserted. 
		   In other words, master can signify end of cycle only if IRDY_ is asserted.
          --------------------------------------------------*/
`ifdef check3
        property checkPCI_Frame_Irdy; 
          @(posedge clk) disable iff (!reset_) 
		!FRAME_ ##1 FRAME_ |-> !$past(IRDY_);
        endproperty
        assert property (checkPCI_Frame_Irdy) else $display($stime,,,"CHECK3:checkPCI_frmIrdy FAIL\n");
`endif

        /*--------------------------------------------------
        CHECK # 4. TRDY_ can be asserted (low) only if DEVSEL_ is asserted (low)
          --------------------------------------------------*/
`ifdef check4
        property checkPCI_trdyDevsel; 
          @(posedge clk) disable iff (!reset_) 
		!TRDY_ |-> !DEVSEL_;
        endproperty
        assert property (checkPCI_trdyDevsel) else $display($stime,,,"CHECK4:checkPCI_trdyDevsel FAIL\n");
`endif

        /*--------------------------------------------------
        CHECK # 5. Once the cycle starts (i.e. at FRAME_ assertion) 
	           C_BE_ should not float until FRAME_ is de-asserted 
          --------------------------------------------------*/
`ifdef check5
        property checkPCI_CBE_during_trx; 
          @(posedge clk) disable iff (!reset_) 
		!FRAME_ |-> !$isunknown(C_BE_);
        endproperty
        assert property (checkPCI_CBE_during_trx) else $display($stime,,,"CHECK5:checkPCI_CBE_during_trx FAIL\n");
`endif

endmodule
