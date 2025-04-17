//////////////////////////////////////////////////
// Title:   assertions_hdlc
// Author:  
// Date:    
//////////////////////////////////////////////////

/* The assertions_hdlc module is a test module containing the concurrent
   assertions. It is used by binding the signals of assertions_hdlc to the
   corresponding signals in the test_hdlc testbench. This is already done in
   bind_hdlc.sv 
*/

module assertions_hdlc (
  output int   ErrCntAssertions,
  input  logic Clk,
  input  logic Rst,
  input  logic Rx,
  input  logic Tx,
  input  logic Rx_FlagDetect,
  input  logic Rx_ValidFrame,
  input  logic Rx_AbortDetect,
  input  logic Rx_AbortSignal,
  input  logic Rx_Overflow,
  input  logic Rx_WrBuff,
  input  logic Tx_AbortFrame,
  input  logic Tx_AbortedTrans,
  input  logic Tx_ValidFrame
);

  initial begin
    ErrCntAssertions  =  0;
  end

  /*******************************************
   * Flag sequences                          *
   *******************************************/

  sequence Flag_Sequence(signal);
    !signal ##1 signal[*6] ##1 !signal; // flag is 0111_1110
  endsequence

  sequence Abort_Flag(signal);
    !signal ##1 signal[*7]; // abort flag is 1111_1110
  endsequence

  sequence Idle_Pattern(signal);
    signal[*8]; // idle pattern is 1111_1111
  endsequence

  /*******************************************
   * Verify correct Rx_FlagDetect behavior   *
   *******************************************/

  // Check if flag sequence is detected
  property RX_FlagDetect;
    @(posedge Clk)
    Flag_Sequence(Rx) |-> ##2 Rx_FlagDetect;
  endproperty

  RX_FlagDetect_Assert : assert property (RX_FlagDetect) begin
    $display("PASS: Flag detect");
  end else begin 
    $error("Flag sequence did not generate FlagDetect"); 
    ErrCntAssertions++; 
  end

  /********************************************
   * Verify correct Rx_AbortSignal behavior   *
   ********************************************/

  //If abort is detected during valid frame. then abort signal should go high
  property RX_AbortSignal;
    @(posedge Clk)
    Rx_AbortDetect && Rx_ValidFrame |=> Rx_AbortSignal;
  endproperty

  RX_AbortSignal_Assert : assert property (RX_AbortSignal) begin
    $display("PASS: Abort signal asserted after abort detected");
  end else begin 
    $error("AbortSignal did not go high after AbortDetect during validframe"); 
    ErrCntAssertions++; 
  end

  /********************************************
   * Verify detection of abort flag on RX     *
   ********************************************/

  property RX_AbortDetect;
    @(posedge Clk) 
    // avoids detecting the final 0 of end flag as start of abort
    disable iff (!Rx_ValidFrame)
    Abort_Flag(Rx) |=> ##1 Rx_AbortDetect;
  endproperty

  Rx_AbortDetect_Assert : assert property (RX_AbortDetect) begin
    $display("PASS: Abort flag detected after received abort sequence");
  end else begin 
    $error("Abort flag not detected after received abort sequence"); 
    ErrCntAssertions++; 
  end

  /********************************************
   * Verify generation of abort flag          *
   ********************************************/

  property TX_AbortFrame;
    @(posedge Clk)
    !Tx_AbortFrame ##1 Tx_AbortFrame |=> ##3 Abort_Flag(Tx);
  endproperty

  TX_AbortFrame_Assert : assert property (TX_AbortFrame) begin 
    $display("PASS: Abort flag generated on TX abort");
  end else begin
    $error("Abort flag not generated on aborted TX frame");
    ErrCntAssertions++;
  end

  /********************************************
   * Verify correct Tx_AbortedTrans behaviour *
   ********************************************/

  property TX_AbortedTrans;
    @(posedge Clk)
    !Tx_AbortFrame ##1 Tx_AbortFrame && Tx_ValidFrame |=> Tx_AbortedTrans;
  endproperty

  TX_AbortedTrans_Assert : assert property (TX_AbortFrame) begin 
    $display("PASS: Tx_AbortedTrans asserted after aborting frame during transmission");
  end else begin
    $error("Tx_AbortedTrans not assert after aborting frame during transmission");
    ErrCntAssertions++;
  end
  
  /********************************************
   * Verify idle pattern generation           *
   ********************************************/

  property TX_IdlePattern;
    @(posedge Clk)
    !Tx_ValidFrame |-> Flag_Sequence(Tx) or Tx;
  endproperty

  TX_IdlePattern_Assert : assert property (TX_IdlePattern) begin 
    $display("PASS: idle pattern generated on invalid TX frame");
  end else begin
    $error("idle pattern not generated on invalid TX frame");
    ErrCntAssertions++;
  end

endmodule
