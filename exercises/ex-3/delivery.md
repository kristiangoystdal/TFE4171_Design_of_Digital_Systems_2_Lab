# 3.1

## 3.1.1
Assertion 1 holds, assertion 2 fails within 1 cycle from reset

## 3.1.2
The assertion itself is wrong based on how a D-flip flop is expected to behave. The input 2 cycles ago is not necessarily the same as the current output. For instance with the input sequence 1 0 0, at the third cycle Q will be 0, while D 2 cycles ago was 1.


# 3.2

## 3.2.1
We forgot to add a specific property to check the behavior when applying 0 0 to the inputs.

