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

  /****************************************************************************
   *                                                                          *
   *                               Student code                               *
   *                                                                          *
   ****************************************************************************/

  enum logic[2:0] {
    Tx_SC,
    Tx_Buff,
    Rx_SC,
    Rx_Buff,
    Rx_Len
  } RegAddr;

  enum int {        
    Rx_Ready,
    Rx_Drop,
    Rx_FrameError,
    Rx_AbortSignal,
    Rx_Overflow,
    Rx_FCSen
  } RxSC_bits;

  enum int {        
    Tx_Done,
    Tx_Enable,
    Tx_AbortFrame,
    Tx_AbortedTrans,
    Tx_Full
  } TxSC_bits;
  
  // VerifyAbortReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer is zero after abort.
  task VerifyAbortReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;

    // Verify status register bits
    ReadAddress(Rx_SC, ReadData);

    assert (ReadData[Rx_Ready] == 0)
      $display("PASS: Rx_Buff has no data");
      else $error("FAIL: Rx_Ready asserted in Rx_SC");

    assert (ReadData[Rx_FrameError] == 0)
      $display("PASS: No frame error");
      else $error("FAIL: Rx_FrameError asserted in Rx_SC");

    assert (ReadData[Rx_AbortSignal] == 1)
      $display("PASS: Abort signal asserted");
      else $error("FAIL: Rx_Abortsignal not asserted in Rx_SC");

    assert (ReadData[Rx_Overflow] == 0)
      $display("PASS: No overflow signal");
      else $error("FAIL: Rx_Overflow asserted in Rx_SC");

    // check Rx buffer empty
    ReadAddress(Rx_Buff, ReadData);
    assert (ReadData == 0)
      $display("PASS: Rx_Buff is empty");
      else $error("FAIL: Rx_Buff not empty on aborted frame");

  endtask

  // VerifyNormalReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer contains correct data.
  task VerifyNormalReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;
    wait(uin_hdlc.Rx_Ready);

    // Verify status register bits
    ReadAddress(Rx_SC, ReadData);
    
    assert (ReadData[Rx_Ready] == 1)
      $display("PASS: Rx_Buff has data to read");
      else $error("FAIL: Rx_Ready not set in Rx_SC");

    assert (ReadData[Rx_FrameError] == 0)
      $display("PASS: No frame error");
      else $error("FAIL: Rx_FrameError asserted in Rx_SC");

    assert (ReadData[Rx_AbortSignal] == 0)
      $display("PASS: No abort signal");
      else $error("FAIL: Rx_AbortSignal asserted in Rx_SC");

    assert (ReadData[Rx_Overflow] == 0)
      $display("PASS: No overflow signal");
      else $error("FAIL: Rx_Overflow asserted in Rx_SC");

    // Verify received data
    for (int i = 0; i < Size; i++) begin
      ReadAddress(Rx_Buff, ReadData);
      assert (ReadData == data[i])
        $display("PASS: Rx buff has correct data");
        else $error("FAIL: Data mismatch on byte %d: got %b, expected %b", i, ReadData, data[i]);
    end
    
  endtask

  task VerifyFrameSizeReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;

    //Verify frame size
    ReadAddress(Rx_Len, ReadData);
    assert (ReadData == Size)
      $display("PASS: Rx_frameSize equal the number of bytes received");
      else $error("FAIL: Rx_frameSize does not equal the number of bytes received");

  endtask

  task VerifyOverflowReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;
    wait(uin_hdlc.Rx_Ready);

    // Verify status register bits
    ReadAddress(Rx_SC, ReadData);
    
    assert (ReadData[Rx_Ready] == 1)
      $display("PASS: Rx_Buff has data to read");
      else $error("FAIL: Rx_Ready not set in Rx_SC");

    assert (ReadData[Rx_FrameError] == 0)
      $display("PASS: No frame error");
      else $error("FAIL: Rx_FrameError asserted in Rx_SC");

    assert (ReadData[Rx_AbortSignal] == 0)
      $display("PASS: No abort signal");
      else $error("FAIL: Rx_AbortSignal asserted in Rx_SC");

    assert (ReadData[Rx_Overflow] == 1)
      $display("PASS: Overflow signal asserted");
      else $error("FAIL: Rx_Overflow not asserted in Rx_SC");
  
    // Verify received data
    for (int i = 0; i < Size; i++) begin
      ReadAddress(Rx_Buff, ReadData);
      assert (ReadData == data[i])
        $display("PASS: Rx buff has correct data");
        else $error("FAIL: Data mismatch on byte %d: got %b, expected %b", i, ReadData, data[i]);
    end
  endtask

  task VerifyErrorReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;

    // Verify status register bits
    ReadAddress(Rx_SC, ReadData);

    assert (ReadData[Rx_Ready] == 0)
      $display("PASS: Rx_Buff has no data");
      else $error("FAIL: Rx_Ready asserted in Rx_SC");

    assert (ReadData[Rx_FrameError] == 1)
      $display("PASS: Frame error detected");
      else $error("FAIL: Rx_FrameError not asserted in Rx_SC");

    assert (ReadData[Rx_AbortSignal] == 0)
      $display("PASS: No abort signal");
      else $error("FAIL: Rx_AbortSignal asserted in Rx_SC");

    assert (ReadData[Rx_Overflow] == 0)
      $display("PASS: No overflow signal");
      else $error("FAIL: Rx_Overflow asserted in Rx_SC");

    // check Rx buffer empty
    ReadAddress(Rx_Buff, ReadData);
    assert (ReadData == 0)
      $display("PASS: Rx_Buff is empty");
      else $error("FAIL: Rx_Buff not empty on error frame");
  endtask

  task VerifyDroppedReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;

    // Verify status register bits
    ReadAddress(Rx_SC, ReadData);

    assert (ReadData[Rx_Ready] == 0)
      $display("PASS: Rx_Buff has no data");
      else $error("FAIL: Rx_Ready asserted in Rx_SC");

    assert (ReadData[Rx_FrameError] == 0)
      $display("PASS: No frame error");
      else $error("FAIL: Rx_FrameError asserted in Rx_SC");

    assert (ReadData[Rx_AbortSignal] == 0)
      $display("PASS: No abort signal");
      else $error("FAIL: Rx_AbortSignal asserted in Rx_SC");

    assert (ReadData[Rx_Overflow] == 0)
      $display("PASS: No overflow signal");
      else $error("FAIL: Rx_Overflow asserted in Rx_SC");

    // check Rx buffer empty
    ReadAddress(Rx_Buff, ReadData);
    assert (ReadData == 0)
      $display("PASS: Rx_Buff is empty after dropped frame");
      else $error("FAIL: Rx_Buff not empty on dropped frame");
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

    //Transmit: Size, Abort, Overflow
    Transmit( 10, 0, 0);            //Normal
    Transmit(126, 0, 1);            //Overflow
    Transmit( 42, 1, 0);            //Abort

    //Receive: Size, Abort, FCSerr, NonByteAligned, Overflow, Drop, SkipRead
    Receive( 10, 0, 0, 0, 0, 0, 0); //Normal
    Receive( 40, 1, 0, 0, 0, 0, 0); //Abort
    Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
    Receive( 45, 0, 0, 0, 0, 0, 0); //Normal
    Receive(126, 0, 0, 0, 0, 0, 0); //Normal
    Receive(122, 1, 0, 0, 0, 0, 0); //Abort
    Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
    Receive( 25, 0, 0, 0, 0, 0, 0); //Normal
    Receive( 47, 0, 0, 0, 0, 0, 0); //Normal
    Receive( 23, 0, 1, 0, 0, 0, 0); //FrameError FCSerr
    Receive(  5, 0, 0, 0, 0, 0, 0); //Normal
    Receive( 42, 0, 0, 0, 0, 1, 0); //FrameDropped
    Receive(  6, 0, 0, 0, 0, 0, 0); //Normal
    Receive( 33, 0, 0, 1, 0, 0, 0); //FrameError NonByteAligned

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

  task Transmit(int Size, int Abort, int Overflow);
    logic [125:0][7:0] TransmitData;
    logic        [7:0] TxStatus;

    string msg;
    if(Abort)
      msg = "- Abort";
    else if(Overflow)
      msg = "- Overflow";
    else
      msg = "- Normal";
    $display("*************************************************************");
    $display("%t - Starting task Transmit %s", $time, msg);
    $display("*************************************************************");

    do begin // wait for TX module ready
      ReadAddress(Tx_SC, TxStatus);
    end while (!TxStatus[Tx_Done]);

    // write data to TX buffer
    for (int i = 0; i < Size; i++) begin
      TransmitData[i] = $urandom;
      WriteAddress(Tx_Buff, TransmitData[i]);
    end

    if (Overflow) // write overflow data
      WriteAddress(Tx_Buff, $urandom);

    WriteAddress(Tx_SC, 8'b1 << Tx_Enable);

    // wait for CRC calculation to finish
    wait(!uin_hdlc.Tx);

    if (Abort) begin
      repeat(16) // give time to generate start flag and one data byte
        @(posedge uin_hdlc.Clk);

      WriteAddress(Tx_SC, 8'b1 << Tx_AbortFrame);
    end

    // TODO: insert immediate assertion tasks

    #10000ns;
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
    ReceiveData[Size]   = FCSBytes[7:0];
    ReceiveData[Size+1] = FCSBytes[15:8];

    //Enable FCS
    if(!Overflow && !NonByteAligned)
      WriteAddress(Rx_SC, 8'b1 << Rx_FCSen);
    else
      WriteAddress(Rx_SC, 8'h00);

      //Generate stimulus
      InsertFlagOrAbort(1);

    if(FCSerr) begin
      ReceiveData[Size-1] -= 1;
    end

    MakeRxStimulus(ReceiveData, Size + 2);
  
    if(Overflow) begin
      OverflowData[0] = 8'h44;
      OverflowData[1] = 8'hBB;
      OverflowData[2] = 8'hCC;
      MakeRxStimulus(OverflowData, 3);
    end

    if (NonByteAligned) begin
      @(posedge uin_hdlc.Clk);
      uin_hdlc.Rx = 0;
    end

    if(Abort) begin
      InsertFlagOrAbort(0);
    end else begin
      InsertFlagOrAbort(1);
    end

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;

    repeat(8)
      @(posedge uin_hdlc.Clk);

    if(Drop) begin //Only check scenario when frame is dropped after Rx_ready gone high
      WriteAddress(Rx_SC, 8'b1 << Rx_Drop);
    end

    if(Abort)
      VerifyAbortReceive(ReceiveData, Size);
    else if(Overflow) begin
      VerifyOverflowReceive(ReceiveData, Size);
      VerifyFrameSizeReceive(ReceiveData, Size);
    end
    else if(FCSerr || NonByteAligned)
      VerifyErrorReceive(ReceiveData, Size);
    else if(Drop)
      VerifyDroppedReceive(ReceiveData, Size);
    else if(!SkipRead) begin
      VerifyNormalReceive(ReceiveData, Size);
      VerifyFrameSizeReceive(ReceiveData, Size);
    end

    #10000ns;
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

endprogram
