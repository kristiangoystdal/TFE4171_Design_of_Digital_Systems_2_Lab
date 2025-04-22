module coverage_tb(
  in_hdlc uin_hdlc
);
  
  covergroup hdlc_cg @(posedge uin_hdlc.Clk);

    // RX
    Rx_Ready_cp : coverpoint uin_hdlc.Rx_SC[0]; 
    Rx_Drop_cp : coverpoint uin_hdlc.Rx_SC[1];
    Rx_FrameError_cp : coverpoint uin_hdlc.Rx_SC[2];
    Rx_AbortSignal_cp : coverpoint uin_hdlc.Rx_SC[3];
    Rx_Overflow_cp : coverpoint uin_hdlc.Rx_SC[4];
    Rx_FCSen_cp : coverpoint uin_hdlc.Rx_SC[5];

    Rx_FrameSize_cp : coverpoint uin_hdlc.Rx_FrameSize {
      bins small_ = {[3:20]}; 
      bins large_ = {[80:$]};
      bins max = {126};
      bins others = default;
    }

    // TX
    Tx_Done_cp : coverpoint uin_hdlc.Tx_SC[0];
    Tx_Enable_cp : coverpoint uin_hdlc.Tx_SC[1];
    Tx_AbortFrame_cp : coverpoint uin_hdlc.Tx_SC[2];
    Tx_AbortedTrans_cp : coverpoint uin_hdlc.Tx_SC[3];
    Tx_Full_cp : coverpoint uin_hdlc.Tx_SC[4];

  endgroup:hdlc_cg

  hdlc_cg cg_hdlc;
  initial begin
    cg_hdlc = new();
  end
   

endmodule:coverage_tb