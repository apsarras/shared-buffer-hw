# A multiple-queue shared buffer and its formal verification testbench #

## What's in the Package ##
+ Directory `./rtl`: SystemVerilog RTL description files
+ Directory `./tb-fv`: Formal Verification Testbench files
+ File `./flist`: compilation filelist

## Info ##
RTL Implementation of a multiple-parallel-queue buffer with dynamic buffer space allocation and its associated Formal Verification Testbench

Single-clock implementation (common write-read clocks) of the dual-clock (separate write-read clocks) design appearing in *A Dual-Clock Multiple-Queue Shared Buffer*, A. Psarras, M. Paschou, C. Nicopoulos, G. Dimitrakopoulos @ IEEE Transactions on Computers, 2017. Check it out [here](https://goo.gl/8f9gBy).

For more information on the design of Multiple Parallel Queues with Dynamic Shared Buffer Allocation, check:
+ Chapter 6.3 "Buffer Sharing" @ *Microarchitecture of Network-on-Chip Routers*, G. Dimitrakopoulos, A. Psarras, I. Seitanidis, Springer 2014 -- [Google Books](https://goo.gl/WNBVqH)
+ Chapter 3.2 "Buffer Memory" @ "Designing Network-on-Chip Architectures in the Nanoscale Era", J. Flich, D. Bertozzi (editors), CRC Press 2010 [Google Books](https://goo.gl/nqoMfQ)

## License ##
See [license.md](./license.md)
