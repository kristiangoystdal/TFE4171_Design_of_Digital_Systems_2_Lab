### Lab 1

#### Task 1


```SystemVerilog
bind dut dut_property dut_bind_inst (.pclk(clk), .preq(req), .pgnt(gnt));
```

#### Task 2

a. No. This would be a syntax error, as those signals do not exist in the scope of dut

b. the test that was started at 10 has not failed yet, but it not checked for pass before 50. The test that starts at 30 passes initially, since req is 1

c. req is 0, so the new test it tries to start immediately fails, as it requires req to be high, and gnt high 2 cycles later

d. When the assert is checked at 30, req is high, activating the assert to check at 70. gnt is then checked to be 1, granting a PASS. The FAIL comes from req being 0, immediately failing the new test that is started

e. at 90, req is 1, leading to a check of gnt at 130. Since both gnt and req is 0 at 130, both the new test of req as well as the continuation of the test from 90 fails


#### Task 3

a. When you get a PASS from an assertion due to the antecedent being false, leading to the consequent never needing to be checked

b. At 70, one of the PASSES come from req=1 at 30 and gnt=1 at 70

c. One is proper as explained in b. The other is vacuous, because of req being 0 at this timestep

d. We have a FAIL because gnt=0 after req=1 at 90. The PASS is vacuous from req=0 at 130


#### Task 4

a. These are the only "true" PASS and FAILs. Their reasoning is explained in task 3b and 3d. The cover feature is what provides us with only "true" PASSES



### Lab 2

#### Task 1

a. cstart=1 while req=0, leading to an instant fail of the consequent

b. We still need to wait 2 cycles to check if gnt=1 at 90, before we can know if the assertion passed

c. As explained in b, it is the assertion that was initialized at 50

d. cstart=1 and req=1 at 110, gnt=1 at 150, leading to a PASS

e. cstart=1 req=1 at 130, but gnt=0 at 170 leading to a FAIL in the consequent

f. Same as e, but with 150 and 190 instead


#### Task 2

a. Since we use a non-overlapping implication, req isn't checked before 1 cycle later, at 50

b. cstart=1 at 50, but req=0 at 70

c. cstart=1 at 30, req=1 at 50, gnt=1 at 90

d. cstart=1 at 110, req=1 at 130, but then gnt=0 at 170, failing

e. cstart=1 at 130, req=1 at 150, but gnt=0 at 190

f. Same, but offset 20. This time gnt is actually 1, so it passes



### Lab 3

We got a warning for -assertdebug and -coverage for every single run, that weren't in the solution file. We ignored these, as it's probably caused by newer tool versions or something similar.


#### Check 1

```SystemVerilog
property check_reset;
  @(posedge clk) !rst_ |-> (`rd_ptr==0) && (`wr_ptr==0) && (`cnt==0) && fifo_empty && !fifo_full;
endproperty
```
It fails both the checks, because fifo_empty is not set to 0, but remains x


#### Check 2

```SystemVerilog
property fifoempty;
  disable iff (!rst_)
  @(posedge clk) (`cnt==0) |-> fifo_empty;
endproperty
```
It fails at 225 due to fifo_empty staying 0 when cnt is counted down to 0


#### Check 3

```SystemVerilog
property fifofull;
  disable iff (!rst_)
  @(posedge clk) (`cnt > 7) |-> fifo_full;
endproperty
```
It fails at 125, due to fifo_full being 1 cycle late at becoming 1


#### Check 4

```SystemVerilog
property fifo_full_write_stable_wrptr;
  @(posedge clk) fifo_full & fifo_write |-> ##1 `wr_ptr==$past(`wr_ptr);
endproperty
```
Fails at 135, due to wr_ptr increasing to 9, when it should stay at 8 since the fifo is full


#### Check 5

```SystemVerilog
property fifo_empty_read_stable_rdptr;
  @(posedge clk) fifo_empty & fifo_read |-> ##1 `rd_ptr==$past(`rd_ptr);
endproperty
```
Fails at 235, due to rd_ptr increasing to 9, even though fifo is empty, so it should stay the same


#### Check 6

```SystemVerilog
property write_on_full_fifo;
  @(posedge clk) fifo_full |-> !fifo_write | fifo_read; 
endproperty
```
Warns at 125, due to writing to a full fifo without simultaneously reading


#### Check 7

```SystemVerilog
property read_on_empty_fifo;
  @(posedge clk) fifo_empty |-> !fifo_read;
endproperty
```
Warns at 225 and 235, both because we are reading from an empty fifo



### Lab 4


#### Check 1

```SystemVerilog
property counter_reset;
  @(posedge clk) !rst_ |-> (data_out == 0);
endproperty
```
Fails at 15 and 25, because data_out is kept at x instead of becoming 0


#### Check 2

```SystemVerilog
property counter_hold;
  disable iff (!rst_)
  @(posedge clk) ld_cnt_ && !count_enb |-> ##1 (data_out == $past(data_out))
endproperty
```
Fails at 45, 185, 195. All times because it keeps counting even if count_enb=0


#### Check 3

```SystemVerilog
property counter_count_up;
  disable iff(!rst_)
  @(posedge clk) ld_cnt_ && count_enb |-> updn_cnt ##1 (($past(data_out) + 1) == data_out);
endproperty

property counter_count_dn;
  disable iff(!rst_)
  @(posedge clk) ld_cnt_ && count_enb |-> !updn_cnt ##1 (($past(data_out) - 1) == data_out);
endproperty

counter_count_up_check: assert property(counter_count_up) 
  else $display($stime,,,"\t\tCOUNTER COUNT CHECK FAIL:: UPDOWN COUNT using $past \n"); 
counter_count_dn_check: assert property(counter_count_dn) 
  else $display($stime,,,"\t\tCOUNTER COUNT CHECK FAIL:: UPDOWN COUNT using $past \n"); 

```
It fails alot. It counts the wrong way at all times



### Lab 5


#### Check 1

```SystemVerilog
property checkValidMinimum;
    @(posedge clk) !dValid ##1 dValid |-> dValid ##1 dValid;
endproperty
property checkValidMaximum; 
    @(posedge clk) dValid ##1 dValid ##1 dValid ##1 dValid |-> dValid ##1 !dValid;
endproperty

assert property (checkValidMinimum) else $display($stime,,,"checkValid FAIL");
assert property (checkValidMaximum) else $display($stime,,,"checkValid FAIL");
```
The provided solution seems to accept dValid high for 5 cycles, but we assume that is a mistake. Anyways, the code fails multiple times due to dValid staying high for longer than 4 cycles. It never stays high too short. Our code correctly finds any sequence longer than 4


#### Check 2

```SystemVerilog
property checkdataValid;
    disable iff (reset)
    @(posedge clk) dValid |-> !$isunknown(data);
endproperty
property checkdataStable;
    disable iff (reset)
    @(posedge clk) dValid ##1 dValid && !dAck |-> $stable(data);
endproperty

assert property (checkdataValid) else $display($stime,,,"checkdataValid FAIL");
assert property (checkdataStable) else $display($stime,,,"checkdataStable FAIL");
```
It fails at 410 because the data becomes XX. And again on 440 because the data changes while dValid is high


#### Check 3

```SytemVerilog
property checkdAck;
    @(posedge clk) dAck |-> ##1 !dValid;
endproperty
    property checkdAckBlock;
    @(posedge clk) !dValid ##1 dValid |-> !dAck;
endproperty
    property checkdAckOnTime;
    @(posedge clk) !dValid ##1 dValid && !dAck ##1 !dAck ##1 !dAck |-> ##1 dAck;
endproperty

assert property (checkdAck) else $display($stime,,,"checkdAck FAIL");
assert property (checkdAckBlock) else $display($stime,,,"checkdAckBlock FAIL");
assert property (checkdAckOnTime) else $display($stime,,,"checkdAckOnTime FAIL");
```
We have alot of discrepencies from the solution, mostly due to the solution accepting 5 cycle long transfers. We also assumed dValid to be high before ack arrives, since this wasn't specified. This is different from the provided solution. Our test for dAck not arriving too late, as well as dValid going low after dAck work as intended


#### Checkall

A bunch of dValid staying high for long and ack arriving too late. At 320 we also see dValid staying high after ack has arrived, which causes another error (checkAck). Generally, it still fails all the same as before, which we already explained somewhat



### Lab 6


#### Check 1

```SystemVerilog
property checkPCI_AD_CBE;
    @(posedge clk) disable iff (!reset_) 
    FRAME_ ##1 !FRAME_ |-> !$isunknown(AD) && !$isunknown(C_BE_);
endproperty
assert property (checkPCI_AD_CBE) else $display($stime,,,"CHECK1:checkPCI_AD_CBE FAIL\n");
```
It fails at 30, same as solution, because AD is unknown after the negedge of FRAME_


#### Check 2

```SystemVerilog
property checkPCI_DataPhase;
    @(posedge clk) disable iff (!reset_) 
    !IRDY_ && !TRDY_ |-> !$isunknown(AD) && !$isunknown(C_BE_);
endproperty
assert property (checkPCI_DataPhase) else $display($stime,,,"CHECK2:checkPCI_DataPhase FAIL\n");
```
Fails as expected at 50, 70, 90 because AD is often unknown, and IRDY and TRDY goes low at the same time


#### Check 3

```SystemVerilog
property checkPCI_Frame_Irdy; 
    @(posedge clk) disable iff (!reset_) 
    !FRAME_ ##1 FRAME_ |-> !$past(IRDY_);
endproperty
assert property (checkPCI_Frame_Irdy) else $display($stime,,,"CHECK3:checkPCI_frmIrdy FAIL\n");
```
Fails as expected at 100, where we see a posedge on FRAME without IRDY being low


#### Check 4

```SystemVerilog
property checkPCI_trdyDevsel; 
    @(posedge clk) disable iff (!reset_) 
    !TRDY_ |-> !DEVSEL_;
endproperty
assert property (checkPCI_trdyDevsel) else $display($stime,,,"CHECK4:checkPCI_trdyDevsel FAIL\n");
```
Fails as expected. TRDY is only allowed low if DEVSEL is also low.


#### Check 5

```SystemVerilog
property checkPCI_CBE_during_trx; 
    @(posedge clk) disable iff (!reset_) 
    !FRAME_ |-> !$isunknown(C_BE_);
endproperty
assert property (checkPCI_CBE_during_trx) else $display($stime,,,"CHECK5:checkPCI_CBE_during_trx FAIL\n");
```
We deviate from the solution at one point, where B_CE becomes zzz at the same time that FRAME_ is deasserted. We argue that this is allowed behaviour from the provided information, and should not fail, like the solution does
