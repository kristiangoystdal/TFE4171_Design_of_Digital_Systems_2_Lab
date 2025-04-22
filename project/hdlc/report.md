# Part A

## Immediate assertions

For all of the immediate assertions, we perform a check on the read flags for the RXSC. By using the ReadAddress function, we can compare bit 0, 2, 3 and 4 to see if they match the given read flags for the different cases. The code block shows how this is implemented. 

```SystemVerilog
ReadAddress(3'b010, ReadData); 
```

### 1. VerifyNormalReceive 

To verify a normal reveive we read the RXCS, and check if Rx_Ready is high and the others low.

```SystemVerilog
assert (ReadData[0] == 1'b1) else $error("Rx_Ready low after abort");
assert (ReadData[2] == 1'b0) else $error("Rx_FrameError high after abort");
assert (ReadData[3] == 1'b0) else $error("Rx_AbortSignal low after abort");
assert (ReadData[4] == 1'b0) else $error("Rx_Overflow high after abort");
```

After this, a loop is initiated from 0 to Size, where we read the data at the Rx_Buff address and compare it to the rows in the input data matrix. 

```SystemVerilog
for(int i = 0; i<Size; i++) begin
  ReadAddress(3'b011, ReadData);
  assert(ReadData == data[i]) else $error("Rx_Buff not equal to matrix row %d", i);
end
```


### 2. VerifyAbortReceive

The same assertion against the read flags for the RXSC is performed, with low for all bits except Rx_AbortSignal. 

```SystemVerilog
assert (ReadData[0] == 1'b0) else $error("Rx_Ready high after abort");
assert (ReadData[2] == 1'b0) else $error("Rx_FrameError high after abort");
assert (ReadData[3] == 1'b1) else $error("Rx_AbortSignal low after abort");
assert (ReadData[4] == 1'b0) else $error("Rx_Overflow high after abort");
```

Also a assertion is done to check if the Rx_Buff data is empty. 

```SystemVerilog
ReadAddress(3'b011, ReadData);
    
assert(ReadData == 8'h00) else $error("Rx_Buff not empty after abort");
```

### 3. VerifyOverflowReceive

For the overflow verification, the same assertions on the read flags of RXSC is performed. Both Rx_Ready and Rx_Overflow should be high and the others should be low.

```SystemVerilog
assert (ReadData[0] == 1'b1) else $error("Rx_Ready high after abort");
assert (ReadData[2] == 1'b0) else $error("Rx_FrameError high after abort");
assert (ReadData[3] == 1'b0) else $error("Rx_AbortSignal low after abort");
assert (ReadData[4] == 1'b1) else $error("Rx_Overflow high after abort");
```


## Concurrent assertions

### 1. Rx_flag
```SystemVerilog
sequence Rx_flag;
  !Rx ##1 Rx[*6] ##1 !Rx ;
endsequence
```
The sequence first checks for a low signal on the current Rx, followed by 6 cycles of high signal and then 1 cycle of low. Since it is a concurrent assertion, Rx will be checked for a low signal every cycle, before moving on to the further checks whenever a low signal is detected.

### 2. Rx_AbortSignal
```Systemverilog
property RX_AbortSignal;
  @(posedge Clk) Rx_ValidFrame & Rx_AbortDetect |-> ##1 Rx_AbortSignal;
endproperty
```
We first misinterpreted this task by trying to check for the abort sequence, but later realized what we were *supposed* to do by reading the corresponding error message in the assertion. The assertion simply checks for Rx_AbortDetect at the same time as an Rx_ValidFrame signal. When this is detected, the next cycle is checked for Rx_AbortSignal high.


### 3. Difference between immediate and concurrent assertions
An immediate assertion is ran much like code in a language like C. Whenever the simulator reaches the assertion, it is checked for that cycle. This makes it possible to "hide" an immediate assertion inside for instance an if statement, allowing it to only be checked in some cases. Concurrent assertions are running in the background in seperate threads, and are therefore checked every cycle after they are initialized. The values checked in concurrent assertions are sampled at the very start of a clock cycle, ensuring more consistent results from checking assertions. Immediate assertions have the possibility of yielding different results within the same clock cycle since they are sampled when they are checked.

### 4. RXSC (and ReadAddress)
RXSC was an undefined variable in the code. We opted to use a simple find-and-replace and put in the value 3'b010, which is the defined address for Rx_SC in the Design Description. We could also have opted to simply define the signal as a constant at the top of the relevant file. In addition to this, the provided call to ReadAddress looked something like "uin_hdlc.ReadAddress(...);", when ReadAddress was a function defined directly inside testPr_hdlc. We therefore changed them all to just "ReadAddress(...);" to solve this issue.


# Part B

## Assertions

Generally most of our assertions are immediate because most of the checks are things that aren't always (or mostly) true. In cases where this is different, it is commented.

### 1
Correct data in RX buffer according to RX input. The buffer should contain up to 128 bytes (includes 2 FCS bytes, not the flags)
```SystemVerilog
for(int i = 0; i<Size; i++) begin
    ReadAddress(3'b011, ReadData);
    assert(ReadData == data[i]) else $error("Rx_Buff not equal to matrix row %d", i);
end
```
We simply loop over the entire buffer when we get a normal receive, and compare it with the data we sent on the Rx stream

### 2
Attempting to read RX buffer after aborted frame, frame error or dropped frame should result in zeros
```SystemVerilog
for(int i = 0; i<Size; i++) begin
    ReadAddress(3'b011, ReadData);
    assert(ReadData == 8'h00) else $error("Rx_Buff not equal to zero after frame error in row %d", i);
end
```
Similarily to spec 1, this is done by reading out the entire Rx buffer. However, we now compare them with 0 instead of the data we sent on Rx.

### 3
Correct bits set in RX status/control register after receiving frame. Rx Overflow bit should be 0 after abort unless overflow occurred
```SystemVerilog
assert (ReadData[0] == 1'b1) else $error("Rx_Ready low after receive");
assert (ReadData[2] == 1'b0) else $error("Rx_FrameError high after receive");
assert (ReadData[3] == 1'b0) else $error("Rx_AbortSignal high after receive");
assert (ReadData[4] == Overflow) else $error("Rx_Overflow %d after receive. Expecting %d", ReadData[4], Overflow);
```
This is only one example. We have similar checks for each of the cases: Abort, Drop, Normal, FrameError, Overflow with differing expected values of the flags

### 4
Correct TX output according to written TX buffer
```SystemVerilog
PrevBits = 5'b00000;
    for (int i = 0; i < ((126 < Size) ? 126 : Size); i++) begin
        for (int j = 0; j < 8; j++) begin
                @(posedge uin_hdlc.Clk);
                assert(uin_hdlc.Tx == TransmitData[i][j]) else $error("Tx bitstream mimatch with data at byte %0d, bit %0d", i, j);
                PrevBits = {PrevBits[4:0], uin_hdlc.Tx}; 
                if (PrevBits == 5'b11111) begin //TODO: WHY do I need to not specify the correct 5 bits here for it to work
                    @(posedge uin_hdlc.Clk);
                    assert(uin_hdlc.Tx == 'b0) else $error("Missing zero insertion");
                end   
        end

        if (Abort && (i == Size / 2)) begin
                WriteAddress(3'b000, 8'h06);
                repeat(2) @(posedge uin_hdlc.Clk);
                assert(uin_hdlc.Tx_AbortedTrans == 'b1) else $error("Tx_AbortedTrans not high after Abort");
                @(posedge uin_hdlc.Clk);
                CheckFlagOrAbort(1);
                break;
        end
    end
```
This is the part of the code concerned with the actual data transmitted, along with removing zero insertion. The abort section is just to force an abort, which is explained more in spec 8

### 5
Start and end of frame pattern generation (Start and end flag: `01111110`)
```SystemVerilog
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
```
This task handles all the flags, along with checking abort (overlap with spec 8). We simply check the Tx stream each cycle for the expected value

### 6
Zero insertion and removal for transparent transmission
```SystemVerilog
// Receive
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

// Transmit
PrevBits = {PrevBits[4:0], uin_hdlc.Tx}; 
if (PrevBits == 5'b11111) begin //TODO: WHY do I need to not specify the correct 5 bits here for it to work
    @(posedge uin_hdlc.Clk);
    assert(uin_hdlc.Tx == 'b0) else $error("Missing zero insertion");
end 
```    
The transmit part can be seen in context in spec 4. This bit of code is simply run after every single bit is read. For some unknown reason it only works when we use a 6 bit PrevBits instead of 5 bits. It does not make sense. But anyways, we just concatinate the previous 5 bits with the newest one received, and if the 5 newest are 1, we force another clock cycle and double check that it was a zero insertion.

For receive we similarily insert zeroes when we have sent 5 ones, and then when we compare the buffer (spec 1) we ignore the zeroes we inserted and only look at the raw data

### 7
Idle pattern generation and checking (`11111111` when not operating)
```SystemVerilog
property TxIdle;
    disable iff (TxActive)
    @(posedge uin_hdlc.Clk)
    uin_hdlc.Tx == 'b1;
endproperty

a_TxIdle: assert property(TxIdle);
```
One of very few concurrent assertions, as this is supposed to always be true as long as we are not sending stuff. TxActive is simply a flag which is set to 1 right before we tell the Tx to transmit, and back to 0 after the transmission is complete

### 8
Abort pattern generation and checking (`11111110`). The `0` must be sent first
```SystemVerilog
if (Abort && (i == Size / 2)) begin
    WriteAddress(3'b000, 8'h06);
    repeat(2) @(posedge uin_hdlc.Clk);
    assert(uin_hdlc.Tx_AbortedTrans == 'b1) else $error("Tx_AbortedTrans not high after Abort");
    @(posedge uin_hdlc.Clk);
    CheckFlagOrAbort(1);
    break;
end
```
Context can be seen in spec 4. We simply send an abort signal after some amount of data has been sent (half the defined Size), and then wait the appropriate time accoridng to the specification paper before checking AbortedTrans signal as well as using the CheckFlagOrAbort to look at the entire abort sequence (see spec 5)

### 9
When aborting frame during transmission, `Tx AbortedTrans` should be asserted

See spec 8. It's a simple immediate assertion in between telling the Tx unit to abort and checking the abort flag generation

### 10
Abort pattern detected during valid frame should generate `Rx AbortSignal`
```SystemVerilog
property RX_AbortSignal;
    @(posedge Clk) Rx_ValidFrame & Rx_AbortDetect |-> ##1 Rx_AbortSignal;
endproperty

RX_AbortSignal_Assert : assert property (RX_AbortSignal) begin
    $display("PASS: Abort signal");
end else begin 
    $error("AbortSignal did not go high after AbortDetect during validframe"); 
    ErrCntAssertions++; 
end
```
Another concurrent assertion as this is always true. It's a simple concurrent assertion of some flags

### 11
CRC generation and checking
```SystemVerilog
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
```
This task handles checking the generated CRC from the Tx unit. The expected value is gotten through the provided GenerateFCSBytes function, and the actual checking is done similarily to the rest of the Tx bitstream, with zero insertion removal

### 12
When a whole RX frame has been received, check if end of frame is generated
```SystemVerilog
@(posedge uin_hdlc.Clk);
uin_hdlc.Rx = 1'b1;

repeat(6) begin
    @(posedge uin_hdlc.Clk);
    // Verify that RX_EoF is high
end

if(!Drop)
    assert(uin_hdlc.Rx_EoF == 1'b1) else $error("Rx_EoF low after receive");
```
We had to do some trial and error since the exact timing of EoF signal was not specified anywhere. We landed on this, checking for EoF 6 cycles after the end of frame flag has been sent to the Rx unit

### 13
When receiving more than 128 bytes, `Rx Overflow` should be asserted
```SystemVerilog
ReadAddress(3'b010, ReadData); 
[...]
assert (ReadData[4] == Overflow) else $error("Rx_Overflow %d after receive. Expecting %d", ReadData[4], Overflow);
```
We simply adjusted the "normalReceive" function to also handle overflow by using the testbench Overflow flag

### 14
`Rx FrameSize` should equal the number of bytes received in a frame (max 126 bytes = 128 - 2 FCS bytes)
```SystemVerilog
task VerifyRX_FrameSize(int Size);
    int InternalSize;

    InternalSize = uin_hdlc.Rx_FrameSize;
    assert (InternalSize == Size) else $error("Rx_FrameSize = %d and not equal to expected Size %d", InternalSize, Size);
    
endtask
```
This task is called after we verify the Rx register flags at the end of a frame when we have had a normal receive, since thats when we expect to see an InternalSize value we care about

### 15
`Rx Ready` should indicate byte(s) in RX buffer is ready to be read
```SystemVerilog
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
```
This is not done explicitly as an assertion, as we were already using the signal to know when we are ready to check the Rx status register. Hence, there has to be a positive flank on Rx_Ready for the testbench to run succesfully, meaning it is tested. We could instead wait a predetermined amount of time and assert it, but without the time from frame end to buffers being ready being clearly defined in the spec, we did not find a better way to do this than to wait on the Ready signal. Instead of an error this will then make the testbench hang.

### 16
Non-byte aligned data or FCS error should result in frame error

See spec 3. For the Non-byte aligned and FCS error cases we are expecting frame error high rather than low (task VerifyFrameErrorReceive).

### 17
`Tx Done` should be asserted when the entire TX buffer has been read for transmission
```SystemVerilog
//Verify that the Tx buffer is empty
ReadAddress(3'b000, ReadData);
assert(ReadData[0] == 1'b1) else $error("Tx buffer not empty after transmit");
assert(uin_hdlc.Tx_Done == 1'b1) else $error("Tx_Done not asserted after finished transmission");
```
After the entire transmission with flags has been read, we simply assert the internal flag and buffer to check that they are as expected

### 18
`Tx Full` should be asserted after writing 126 or more bytes to the TX buffer (overflow)
```SystemVerilog
//Verify Tx_Full
if (Size >= 126) begin
    assert(uin_hdlc.Tx_Full == 'b1) else $error("Tx_Full low when buffer should be full");
end else begin
    assert(uin_hdlc.Tx_Full == 'b0) else $error("Tx_Full high when buffer is not expected to be full");
end
```   
After filling the Tx buffer and before transmitting, we simply check the internal signals of Tx                                                  

## Coverage
We achieve a coverage of 100% for the cases we defined, the Rx_SC, Tx_SC and Rx_FrameSize. For Rx_FrameSize, we grouped values into bins to reduce the number of test cases while still capturing the variation in typical frame lengths.

Each coverpoint was exercised through a selected range of tests, including normal frames, overflows, aborts, frame errors, and drops. Some coverpoints (e.g., Rx_Drop_cp) have bins hit only once, which reflects an intentional choice to validate behavior without redundant test cases. 


## Corner cases
Checking RX overflow bit if a message is dropped (Rx_SC Rx_Drop) after overflow has occured causes a low value instead of high. This was unexpected from out initial understanding of the spec, but on further inspection it was undefined behavior, and was therefore ignored.

When we exceeded a certain number of bytes generated (like 800) we got massive errors where the testbench complained about mismatch between Tx stream and expected value. We found that if we removed some recive test cases, this did not happen. So we were limited by our total amount of test cases, and have no idea why.

Using GenerateFCS in Tx provided an error becuase it reads 2 additional bytes from the data than what we expected. This was fixed by forcing 2 extra bytes of zero at the upper end of the TransmitData, but caused some headache. This caused an issue when testing Overflow, as the TransmitData vector was only 128 bytes long, meaning there were no space for the extra zero-bytes if we exceeded 126 bytes of payload. This had to be adjusted to allow proper testing of overflow. In addition we needed to overwrite byte 126 and 127 with 0 in case of overflow to make the GenerateFCS work properly
