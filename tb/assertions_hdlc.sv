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
  input  logic Tx_AbortFrame
);

  initial begin
    ErrCntAssertions  =  0;
  end

  /*******************************************
   *  Flag sequences                         *
   *******************************************/

  sequence Flag_Sequence;
    !Rx ##1 Rx[*6] ##1 !Rx; // flag is 0111_1110
  endsequence

  sequence Abort_Flag;
    !Tx ##1 Tx[*7]; // abort flag is 1111_1110
  endsequence

  /*******************************************
   *  Verify correct Rx_FlagDetect behavior  *
   *******************************************/

  // Check if flag sequence is detected
  property RX_FlagDetect;
    @(posedge Clk) Flag_Sequence |-> ##2 Rx_FlagDetect;
  endproperty

  RX_FlagDetect_Assert : assert property (RX_FlagDetect) begin
    $display("PASS: Flag detect");
  end else begin 
    $error("Flag sequence did not generate FlagDetect"); 
    ErrCntAssertions++; 
  end

  /********************************************
   *  Verify correct Rx_AbortSignal behavior  *
   ********************************************/

  //If abort is detected during valid frame. then abort signal should go high
  property RX_AbortSignal;
    @(posedge Clk) Rx_AbortDetect && Rx_ValidFrame |=> Rx_AbortSignal;
  endproperty

  RX_AbortSignal_Assert : assert property (RX_AbortSignal) begin
    $display("PASS: Abort signal");
  end else begin 
    $error("AbortSignal did not go high after AbortDetect during validframe"); 
    ErrCntAssertions++; 
  end

  /********************************************
   *  Verify detection of abort flag on RX    *
   ********************************************/

  property RX_AbortDetect;
    @(posedge Clk) Abort_Flag |=> Rx_AbortDetect;
  endproperty

  Rx_AbortDetect_Assert : assert property (RX_AbortDetect) begin
    $display("PASS: Abort flag detected");
  end else begin 
    $error("Abort flag not detected"); 
    ErrCntAssertions++; 
  end

  /********************************************
   *  Verify generation of abort flag         *
   ********************************************/

  property TX_AbortFrame;
    @(posedge Clk) !Tx_AbortFrame ##1 Tx_AbortFrame |=> Abort_Flag;
  endproperty

  TX_AbortFrame_Assert : assert property (TX_AbortFrame) begin 
    $display("PASS: Abort flag generated");
  end else begin
    $error("Abort flag not generated on aborted TX frame");
    ErrCntAssertions++;
  end

endmodule
