//////////////////////////////////////////////////
// Title:   testPr_hdlc
// Author: 
// Date:  
//////////////////////////////////////////////////

/* testPr_hdlc contains the simulation and immediate assertion code of the
   testbench. 

   For this exercise you will write immediate assertions for the Rx module which
   should verify correct values in some of the Rx registers for:
   - Normal behavior
   - Buffer overflow 
   - Aborts

   HINT:
   - A ReadAddress() task is provided, and addresses are documentet in the 
     HDLC Module Design Description
*/

program testPr_hdlc(
  in_hdlc uin_hdlc
);
  
  int TbErrorCnt;
  logic TxActive;

  /****************************************************************************
   *                                                                          *
   *                               Student code                               *
   *                                                                          *
   ****************************************************************************/

  // VerifyAbortReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer is zero after abort.
  task VerifyAbortReceive(logic [127:0][7:0] data, int Size, int Overflow);
    logic [7:0] ReadData;

    ReadAddress(3'b010, ReadData); 
    
    assert (ReadData[0] == 1'b0) else $error("Rx_Ready high after abort");
    assert (ReadData[2] == 1'b0) else $error("Rx_FrameError high after abort");
    assert (ReadData[3] == 1'b1) else $error("Rx_AbortSignal low after abort");
    assert (ReadData[4] == 1'b0) else $error("Rx_Overflow high after abort");

    for(int i = 0; i<Size; i++) begin
      ReadAddress(3'b011, ReadData);
      assert(ReadData == 8'h00) else $error("Rx_Buff not equal to zero after abort in row %d", i);
    end

  endtask

  // VerifyDropReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer is zero after abort.
  task VerifyDropReceive(logic [127:0][7:0] data, int Size, int Overflow);
    logic [7:0] ReadData;

    ReadAddress(3'b010, ReadData); 
    
    assert (ReadData[0] == 1'b0) else $error("Rx_Ready high after drop");
    assert (ReadData[2] == 1'b0) else $error("Rx_FrameError high after drop");
    assert (ReadData[3] == 1'b0) else $error("Rx_AbortSignal high after drop");
    assert (ReadData[4] == Overflow) else $error("Rx_Overflow %d after drop. Expecting %d", ReadData[4], Overflow);

    for(int i = 0; i<Size; i++) begin
      ReadAddress(3'b011, ReadData);
      assert(ReadData == 8'h00) else $error("Rx_Buff not equal to zero after drop in row %d", i);
    end

  endtask

  // VerifyNormalReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer contains correct data.
  task VerifyNormalReceive(logic [127:0][7:0] data, int Size, int Overflow);
    logic [7:0] ReadData;
    wait(uin_hdlc.Rx_Ready);

    ReadAddress(3'b010, ReadData); 
    
    assert (ReadData[0] == 1'b1) else $error("Rx_Ready low after receive");
    assert (ReadData[2] == 1'b0) else $error("Rx_FrameError high after receive");
    assert (ReadData[3] == 1'b0) else $error("Rx_AbortSignal high after receive");
    assert (ReadData[4] == Overflow) else $error("Rx_Overflow %d after receive. Expecting %d", ReadData[4], Overflow);

    for(int i = 0; i<Size; i++) begin
      ReadAddress(3'b011, ReadData);
      assert(ReadData == data[i]) else $error("Rx_Buff not equal to matrix row %d", i);
    end

    
  
  endtask

  // VerifyFrameError should verify correct value in the Rx status/control
  // register
  task VerifyFrameErrorReceive(logic [127:0][7:0] data, int Size, int Overflow);
    logic [7:0] ReadData;
    wait(uin_hdlc.Rx_FrameError);

    ReadAddress(3'b010, ReadData); 

    assert (ReadData[0] == 1'b0) else $error("Rx_Ready high after frame error");
    assert (ReadData[2] == 1'b1) else $error("Rx_FrameError low after frame error");
    assert (ReadData[3] == 1'b0) else $error("Rx_AbortSignal high after frame error");
    assert (ReadData[4] == Overflow) else $error("Rx_Overflow %d after frame error. Expecting %d", ReadData[4], Overflow);

    for(int i = 0; i<Size; i++) begin
      ReadAddress(3'b011, ReadData);
      assert(ReadData == 8'h00) else $error("Rx_Buff not equal to zero after frame error in row %d", i);
    end

  endtask

  // VerifyOverflowReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer contains correct data.
  task VerifyOverflowReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;
    wait(uin_hdlc.Rx_Ready);

    ReadAddress(3'b010, ReadData); 

    assert (ReadData[0] == 1'b1) else $error("Rx_Ready low after overflow");
    assert (ReadData[2] == 1'b0) else $error("Rx_FrameError high after overflow");
    assert (ReadData[3] == 1'b0) else $error("Rx_AbortSignal high after overflow");
    assert (ReadData[4] == 1'b1) else $error("Rx_Overflow low after overflow");

  endtask

  // VerifyRX_FrameSize should verify correct frame size 
  task VerifyRX_FrameSize(int Size);
    int InternalSize;

    InternalSize = uin_hdlc.Rx_FrameSize;
    assert (InternalSize == Size) else $error("Rx_FrameSize = %d and not equal to expected Size %d", InternalSize, Size);
    
  endtask

  /****************************************************************************
   *                                                                          *
   *                             Simulation code                              *
   *                                                                          *
   ****************************************************************************/

  initial begin
    $display("*************************************************************");
    $display("%t - Starting Test Program", $time);
    $display("*************************************************************");

    Init();

    //Receive: Size, Abort, FCSerr, NonByteAligned, Overflow, Drop, SkipRead
    Receive( 10, 0, 0, 0, 0, 0, 0); //Normal
    // Receive( 40, 1, 0, 0, 0, 0, 0); //Abort
    // Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
    // Receive( 45, 0, 0, 0, 0, 0, 0); //Normal
    // Receive(126, 0, 0, 0, 0, 0, 0); //Normal
    Receive(122, 1, 0, 0, 0, 0, 0); //Abort
    // Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
    // Receive( 25, 0, 0, 0, 0, 0, 0); //Normal
    // Receive( 47, 0, 0, 0, 0, 0, 0); //Normal
    Receive(  5, 0, 0, 0, 0, 1, 0); //Drop
    // Receive(126, 1, 0, 0, 1, 0, 0); //Overflow and Abort
    // Receive(126, 0, 0, 0, 1, 1, 0); //Overflow and Drop
    // Receive(126, 0, 0, 0, 1, 0, 0); //Overflow and Normal
    Receive(  5, 0, 1, 0, 0, 0, 0); //FCS error
    Receive(  5, 0, 0, 1, 0, 0, 0); //Non-byte aligned

    // Transmit( 10, 0, 0, 0, 0, 0, 0); //Normal
    // Transmit( 40, 0, 0, 0, 0, 0, 0); //Normal
    // Transmit(128, 0, 0, 0, 1, 0, 0); //Overflow
    // Transmit(126, 0, 0, 0, 0, 0, 0); //Normal
    // Transmit(126, 0, 0, 0, 0, 0, 0); //Normal
    // Transmit( 40, 1, 0, 0, 0, 0, 0); //Abort

    
    

    $display("*************************************************************");
    $display("%t - Finishing Test Program", $time);
    $display("*************************************************************");
    $stop;
  end

  final begin

    $display("*********************************");
    $display("*                               *");
    $display("* \tAssertion Errors: %0d\t  *", TbErrorCnt + uin_hdlc.ErrCntAssertions);
    $display("*                               *");
    $display("*********************************");

  end

  task Init();
    uin_hdlc.Clk         =   1'b0;
    uin_hdlc.Rst         =   1'b0;
    uin_hdlc.Address     = 3'b000;
    uin_hdlc.WriteEnable =   1'b0;
    uin_hdlc.ReadEnable  =   1'b0;
    uin_hdlc.DataIn      =     '0;
    uin_hdlc.TxEN        =   1'b1;
    uin_hdlc.Rx          =   1'b1;
    uin_hdlc.RxEN        =   1'b1;

    TbErrorCnt = 0;

    #1000ns;
    uin_hdlc.Rst         =   1'b1;
  endtask

  task WriteAddress(input logic [2:0] Address ,input logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address     = Address;
    uin_hdlc.WriteEnable = 1'b1;
    uin_hdlc.DataIn      = Data;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.WriteEnable = 1'b0;
  endtask

  task ReadAddress(input logic [2:0] Address ,output logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address    = Address;
    uin_hdlc.ReadEnable = 1'b1;
    #100ns;
    Data                = uin_hdlc.DataOut;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.ReadEnable = 1'b0;
  endtask

  task InsertFlagOrAbort(int flag);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    if(flag)
      uin_hdlc.Rx = 1'b0;
    else
      uin_hdlc.Rx = 1'b1;
  endtask

  task MakeRxStimulus(logic [127:0][7:0] Data, int Size);
    logic [4:0] PrevData;
    PrevData = '0;
    for (int i = 0; i < Size; i++) begin
      for (int j = 0; j < 8; j++) begin
        if(&PrevData) begin
          @(posedge uin_hdlc.Clk);
          uin_hdlc.Rx = 1'b0;
          PrevData = PrevData >> 1;
          PrevData[4] = 1'b0;
        end

        @(posedge uin_hdlc.Clk);
        uin_hdlc.Rx = Data[i][j];

        PrevData = PrevData >> 1;
        PrevData[4] = Data[i][j];
      end
    end
  endtask

  task Receive(int Size, int Abort, int FCSerr, int NonByteAligned, int Overflow, int Drop, int SkipRead);
    logic [127:0][7:0] ReceiveData;
    logic       [15:0] FCSBytes;
    logic   [2:0][7:0] OverflowData;
    string msg;
    if(Abort)
      msg = "- Abort";
    else if(FCSerr)
      msg = "- FCS error";
    else if(NonByteAligned)
      msg = "- Non-byte aligned";
    else if(Overflow)
      msg = "- Overflow";
    else if(Drop)
      msg = "- Drop";
    else if(SkipRead)
      msg = "- Skip read";
    else
      msg = "- Normal";
    $display("*************************************************************");
    $display("%t - Starting task Receive %s", $time, msg);
    $display("*************************************************************");

    for (int i = 0; i < Size; i++) begin
      ReceiveData[i] = $urandom;
    end
    ReceiveData[Size]   = '0;
    ReceiveData[Size+1] = '0;

    //Calculate FCS bits;
    GenerateFCSBytes(ReceiveData, Size, FCSBytes);
    if (FCSerr) begin
      FCSBytes ^= 16'h0001;
    end
    ReceiveData[Size]   = FCSBytes[7:0];
    ReceiveData[Size+1] = FCSBytes[15:8];

    //Enable FCS
    if(!Overflow && !NonByteAligned)
      WriteAddress(3'b010, 8'h20);
    // else if (FCSerr)
    //   WriteAddress(3'b010, 8'h04);    
    else
      WriteAddress(3'b010, 8'h00);

    //Generate stimulus
    InsertFlagOrAbort(1);
    
    MakeRxStimulus(ReceiveData, Size + 2);
    if (NonByteAligned) begin
      // Inject 3 random bits
      for (int i = 0; i < 3; i++) begin
        @(posedge uin_hdlc.Clk);
        uin_hdlc.Rx = $urandom;
      end
    end

    
    if(Overflow) begin
      OverflowData[0] = 8'h44;
      OverflowData[1] = 8'hBB;
      OverflowData[2] = 8'hCC;
      MakeRxStimulus(OverflowData, 3);
    end

    if (Abort) begin
      InsertFlagOrAbort(0);
    end else if(Drop) begin
      WriteAddress(3'b010, 8'h02);
    end else begin
      InsertFlagOrAbort(1);
    end

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;

    repeat(6) begin
      @(posedge uin_hdlc.Clk);
      // Verify that RX_EoF is high
    end
    
    if(!Drop)
      assert(uin_hdlc.Rx_EoF == 1'b1) else $error("Rx_EoF low after receive");

    repeat(2) 
      @(posedge uin_hdlc.Clk);


    if(Abort)
      VerifyAbortReceive(ReceiveData, Size, Overflow);
    else if (Drop)
      VerifyDropReceive(ReceiveData, Size, Overflow);
    else if (FCSerr || NonByteAligned)
      VerifyFrameErrorReceive(ReceiveData, Size, Overflow);
    else if(!SkipRead) begin
      VerifyNormalReceive(ReceiveData, Size, Overflow);
      VerifyRX_FrameSize(Size);
    end

    #5000ns;
  endtask

  task GenerateFCSBytes(logic [127:0][7:0] data, int size, output logic[15:0] FCSBytes);
    logic [23:0] CheckReg;
    CheckReg[15:8]  = data[1];
    CheckReg[7:0]   = data[0];
    for(int i = 2; i < size+2; i++) begin
      CheckReg[23:16] = data[i];
      for(int j = 0; j < 8; j++) begin
        if(CheckReg[0]) begin
          CheckReg[0]    = CheckReg[0] ^ 1;
          CheckReg[1]    = CheckReg[1] ^ 1;
          CheckReg[13:2] = CheckReg[13:2];
          CheckReg[14]   = CheckReg[14] ^ 1;
          CheckReg[15]   = CheckReg[15];
          CheckReg[16]   = CheckReg[16] ^1;
        end
        CheckReg = CheckReg >> 1;
      end
    end
    FCSBytes = CheckReg;
  endtask

  // ------------------------------------------------------
  // Transmit part 
  // ------------------------------------------------------
  task CheckFlagOrAbort(int abort);
    @(posedge uin_hdlc.Clk);
    assert(uin_hdlc.Tx == 1'b0) else $error("Error in flag sequence bit 0");
    @(posedge uin_hdlc.Clk);
    assert(uin_hdlc.Tx == 1'b1) else $error("Error in flag sequence bit 1");
    @(posedge uin_hdlc.Clk);
    assert(uin_hdlc.Tx == 1'b1) else $error("Error in flag sequence bit 2");
    @(posedge uin_hdlc.Clk);
    assert(uin_hdlc.Tx == 1'b1) else $error("Error in flag sequence bit 3");
    @(posedge uin_hdlc.Clk);
    assert(uin_hdlc.Tx == 1'b1) else $error("Error in flag sequence bit 4");
    @(posedge uin_hdlc.Clk);
    assert(uin_hdlc.Tx == 1'b1) else $error("Error in flag sequence bit 5");
    @(posedge uin_hdlc.Clk);
    assert(uin_hdlc.Tx == 1'b1) else $error("Error in flag sequence bit 6");
    @(posedge uin_hdlc.Clk);
    if(abort)
      assert(uin_hdlc.Tx == 1'b1) else $error("Error in flag sequence bit 7 (abort bit)");
    else
      assert(uin_hdlc.Tx == 1'b0) else $error("Error in flag sequence bit 7");
  endtask

  task CheckFCSBytes(logic [127:0][7:0] TransmitData, int Size, logic [5:0] PrevBits);
    logic [15:0] FCSBytes;
    GenerateFCSBytes(TransmitData, Size, FCSBytes);
    for (int i = 0; i < 16; i++) begin
      @(posedge uin_hdlc.Clk);
      assert(uin_hdlc.Tx == FCSBytes[i]) else $error("FCS bit %0d has value %0d. Expecting %0d", i, uin_hdlc.Tx, FCSBytes[i]);
      PrevBits = {PrevBits[4:0], uin_hdlc.Tx};
        if (PrevBits == 5'b11111) begin
          @(posedge uin_hdlc.Clk);
          assert(uin_hdlc.Tx == 'b0) else $error("Missing zero insertion");
        end 
    end
  endtask

  task Transmit(int Size, int Abort, int FCSerr, int NonByteAligned, int Overflow, int Drop, int SkipRead);
    logic [127:0][7:0] TransmitData;
    logic   [2:0][7:0] OverflowData;
    logic [7:0] ReadData;
    logic [5:0] PrevBits; //TODO: WHY do I need this at 6 bits instead of 5 for stuff to work?

    string msg;
    if(Abort)
      msg = "- Abort";
    else if(FCSerr)
      msg = "- FCS error";
    else if(NonByteAligned)
      msg = "- Non-byte aligned";
    else if(Overflow)
      msg = "- Overflow";
    else if(Drop)
      msg = "- Drop";
    else if(SkipRead)
      msg = "- Skip read";
    else
      msg = "- Normal";
    $display("*************************************************************");
    $display("%t - Starting task Transmit %s", $time, msg);
    $display("*************************************************************");
    
    //Generate data
    for (int i = 0; i < Size; i++) begin
      TransmitData[i] = $urandom;
    end
   
    //Verify that the Tx buffer is empty
    ReadAddress(3'b000, ReadData);
    assert(ReadData[0] == 1'b1) else $error("Tx buffer not empty before transmit");

    //Write data to Tx buffer
    for (int i = 0; i < Size; i++) begin
      WriteAddress(3'b001, TransmitData[i]);
    end

    //Verify Overflow
    ReadAddress(3'b000, ReadData);
    assert(ReadData[4] == Overflow) else $error("Tx_Overflow %0d. Expecting %0d", ReadData[4], Overflow);

    //Verify Tx_Full
    if (Size >= 126) begin
      assert(uin_hdlc.Tx_Full == 'b1) else $error("Tx_Full low when buffer should be full");
    end else begin
      assert(uin_hdlc.Tx_Full == 'b0) else $error("Tx_Full high when buffer is not expected to be full");
    end

    //Verify buffer content
    for (int i = 0; i < ((126 < Size) ? 126 : Size ); i++ ) begin
      assert(uin_hdlc.Tx_DataArray[i] == TransmitData[i]) else $error("Tx_DataArray[%0d] = %0h. Expecting %0h", i, uin_hdlc.Tx_DataArray[i], TransmitData[i]);
    end

    //Enable Tx
    WriteAddress(3'b000, 8'h02);

    //Wait until TxChannel actually begins transmitting, 1 cycle after ValidFrame is asserted
    @(posedge uin_hdlc.Tx_ValidFrame);
    @(posedge uin_hdlc.Clk);
    TxActive = 'b1;

    //Check that the bitstream is correct
    CheckFlagOrAbort(0);

    PrevBits = 5'b00000;
    for (int i = 0; i < ((126 < Size) ? 126 : Size); i++) begin
      for (int j = 0; j < 8; j++) begin
        @(posedge uin_hdlc.Clk);
        assert(uin_hdlc.Tx == TransmitData[i][j]) else $error("Tx bitstream mimatch with data at byte %0d, bit %0d", i, j);
        PrevBits = {PrevBits[4:0], uin_hdlc.Tx}; 
        if (PrevBits == 5'b11111) begin //TODO: WHY do I need to not specifify the correct 5 bits here for it to work
          @(posedge uin_hdlc.Clk);
          assert(uin_hdlc.Tx == 'b0) else $error("Missing zero insertion");
        end   
      end
    end

    //TODO: Getting lots of errors in here
    CheckFCSBytes(TransmitData, Size, PrevBits);

    /*if (Abort) begin
      WriteAddress(3'b000, 8'h04);
      @(posedge uin_hdlc.Tx_AbortedTrans);
      CheckFlagOrAbort(1);
    end else begin*/
    CheckFlagOrAbort(Abort); // Not quite
    //end

    //Verify that the Tx buffer is empty
    ReadAddress(3'b000, ReadData);
    assert(ReadData[0] == 1'b1) else $error("Tx buffer not empty after transmit");
    assert(uin_hdlc.Tx_Done == 1'b1) else $error("Tx_Done not asserted after finished transmission");

    @(posedge uin_hdlc.Clk);
    TxActive = 'b0;
  endtask

  property TxIdle;
    disable iff (TxActive)
    @(posedge uin_hdlc.Clk)
    uin_hdlc.Tx == 'b1;
  endproperty

  a_TxIdle: assert property(TxIdle);

endprogram
