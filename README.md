# High-Level Data Link Controller

This is a project part of the NTNU course TFE4171 - Design of Digitial Systems 2, focused on design verification of digital systems. In the project we were handed out a system verilog implementation of a High-Data Link Controller (HDLC), and were tasked to verify the correct functioning according a set of specifications.

## Verification goals

1. Correct data in RX buffer according to RX input. The buffer should contain up to 128 bytes (this includes the 2 FCS bytes, but not the flags).
2. Attempting to read RX buffer after aborted frame, frame error or dropped frame should result
in zeros.
3. Correct bits set in RX status/control register after receiving frame. Remember to check all bits.
I.e. after an abort the Rx_Overflow bit should be 0, unless an overflow also occurred.
4. Correct TX output according to written TX buffer.
5. Start and end of frame pattern generation (Start and end flag: 0111_1110).
6. Zero insertion and removal for transparent transmission.
7. Idle pattern generation and checking (1111_1111 when not operating).
8. Abort pattern generation and checking (1111_1110). Remember that the 0 must be sent first.
9. When aborting frame during transmission, Tx_AbortedTrans should be asserted.
10. Abort pattern detected during valid frame should generate Rx_AbortSignal.
11. CRC generation and Checking.
12. When a whole RX frame has been received, check if end of frame is generated.
13. When receiving more than 128 bytes, Rx_Overflow should be asserted.
14. Rx_FrameSize should equal the number of bytes received in a frame (max. 126 bytes =128 bytes in buffer – 2 FCS bytes).
15. Rx_Ready should indicate byte(s) in RX buffer is ready to be read.
16. Non-byte aligned data or error in FCS checking should result in frame error.
17. Tx_Done should be asserted when the entire TX buffer has been read for transmission.
18. Tx_Full should be asserted after writing 126 or more bytes to the TX buffer (overflow).
