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
  input  logic Tx_ValidFrame,
  input  logic Tx_Enable
);
  /*******************************************
   * Local signals and error count           *
   *******************************************/

  logic TransmittingFrame;
  logic TransmittingFrameContent;

  initial begin
    ErrCntAssertions  =  0;
    TransmittingFrame = 0'b0;
    TransmittingFrameContent = 0'b0;
  end

  initial begin // TransmittingFrame is asserted during frame transmition, including flags
    while (1) begin
      wait(Tx_ValidFrame);

      TransmittingFrame = 0'b1;

      wait(!Tx_ValidFrame);

      repeat(9) // give time to generate end/abort flag
        @(posedge Clk);

      TransmittingFrame = 0'b0;
    end
  end

  initial begin // TransmittingFrameContent is assert during frame transmition, not including flags
    while (1) begin
      wait(Tx_ValidFrame);

      repeat(10) // give time to generate start flag
        @(posedge Clk);

      TransmittingFrameContent = 0'b1;

      wait(!Tx_ValidFrame);

      TransmittingFrameContent = 0'b0;
    end
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
    $error("FAIL: Flag sequence did not generate FlagDetect"); 
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
    $error("FAIL: AbortSignal did not go high after AbortDetect during validframe"); 
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
    $error("FAIL: Abort flag not detected after received abort sequence"); 
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
    $error("FAIL: Abort flag not generated on aborted TX frame");
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
    $error("FAIL: Tx_AbortedTrans not assert after aborting frame during transmission");
    ErrCntAssertions++;
  end
  
  /********************************************
   * Verify idle pattern generation           *
   ********************************************/

  property TX_IdlePattern;
    @(posedge Clk)
    !TransmittingFrame |-> Tx;
  endproperty

  TX_IdlePattern_Assert : assert property (TX_IdlePattern)
  else begin
    $error("FAIL: Idle pattern not generated when not transmitting");
    ErrCntAssertions++;
  end

  /********************************************
   * Verify zero insertion                    *
   ********************************************/

  property TX_ZeroInsertion;
    @(posedge Clk)
    disable iff (!TransmittingFrameContent)
    Tx[*5] |=> !Tx;
  endproperty

  TX_ZeroInsertion_Assert : assert property (TX_ZeroInsertion)
  else begin
    $error("FAIL: Zero not inserted after five consecutive ones");
    ErrCntAssertions++;
  end

  /********************************************
   * Verify Tx_ValidFrame                     *
   ********************************************/

  property TX_ValidFrameAssert;
    @(posedge Clk)
    // Tx_ValidFrame should always be asserted after Tx_Enable
    // After Tx_ValidFrame is asserter there should always be generated a start flag
    // unless the frame is aborted before transmission starts
    disable iff (Tx_AbortFrame)
    Tx_Enable |=> ##[0:$] Tx_ValidFrame ##1 Flag_Sequence(Tx);
  endproperty

  property TX_ValidFrameDeassert;
    @(posedge Clk)
    // The Tx_ValidFrame should always go low again after some time
    // and when it goes low there should always be generated a flag
    !Tx_ValidFrame ##1 Tx_ValidFrame |=> ##[0:$] !Tx_ValidFrame ##1 (Flag_Sequence(Tx) or Abort_Flag(Tx));
  endproperty

  TX_ValidFrameAssert_Assert : assert property (TX_ValidFrameAssert)
    $display("Pass: Tx_ValidFrame asserted after Tx_Enable");
  else begin
    $error("FAIL: Tx_ValidFrame not asserted after Tx_Enable");
    ErrCntAssertions++;
  end

  TX_ValidFrameDeassert_Assert : assert property (TX_ValidFrameDeassert)
  $display("Pass: Tx_ValidFrame deasserted and end/abort flag generated");
  else begin
    $error("FAIL: Tx_ValidFrame not deasserted or end/abort flag not generated");
    ErrCntAssertions++;
  end

endmodule
