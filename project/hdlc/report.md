# Status
| #   | Description                                                                                                                                     | Progress |
|-----|-------------------------------------------------------------------------------------------------------------------------------------------------|----------|
| 1   | Correct data in RX buffer according to RX input. The buffer should contain up to 128 bytes (includes 2 FCS bytes, not the flags).               |   Done   |
| 2   | Attempting to read RX buffer after aborted frame, frame error or dropped frame should result in zeros.                                          |          |
| 3   | Correct bits set in RX status/control register after receiving frame. Rx Overflow bit should be 0 after abort unless overflow occurred.         |          |
| 4   | Correct TX output according to written TX buffer.                                                                                               |          |
| 5   | Start and end of frame pattern generation (Start and end flag: `01111110`).                                                                     |          |
| 6   | Zero insertion and removal for transparent transmission.                                                                                        |          |
| 7   | Idle pattern generation and checking (`11111111` when not operating).                                                                           |          |
| 8   | Abort pattern generation and checking (`11111110`). The `0` must be sent first.                                                                 |          |
| 9   | When aborting frame during transmission, `Tx AbortedTrans` should be asserted.                                                                  |          |
| 10  | Abort pattern detected during valid frame should generate `Rx AbortSignal`.                                                                     |          |
| 11  | CRC generation and checking.                                                                                                                    |          |
| 12  | When a whole RX frame has been received, check if end of frame is generated.                                                                    |          |
| 13  | When receiving more than 128 bytes, `Rx Overflow` should be asserted.                                                                           |          |
| 14  | `Rx FrameSize` should equal the number of bytes received in a frame (max 126 bytes = 128 - 2 FCS bytes).                                        |          |
| 15  | `Rx Ready` should indicate byte(s) in RX buffer is ready to be read.                                                                            |          |
| 16  | Non-byte aligned data or FCS error should result in frame error.                                                                                |          |
| 17  | `Tx Done` should be asserted when the entire TX buffer has been read for transmission.                                                          |          |
| 18  | `Tx Full` should be asserted after writing 126 or more bytes to the TX buffer (overflow).                                                       |          |


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


## Other Errors

