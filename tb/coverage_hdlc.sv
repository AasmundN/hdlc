//////////////////////////////////////////////////
// Title:   coverage_hdlc
// Author: Aasmund and Mathias
// Date: 19.04.2025 
//////////////////////////////////////////////////

module coverage_hdlc(
  in_hdlc uin_hdlc
);
  `include "hdlc_packet.sv"
  
  covergroup hdlc_cg @(posedge uin_hdlc.Clk);
    Tx_FrameSize_cp : coverpoint uin_hdlc.Tx_FrameSize {
      bins small_ = {[3:10]}; // address + control + 1 data byte
      bins large_ = {[100:$]};
      bins max = {126};
      bins others = default;
    }

    Rx_FrameSize_cp : coverpoint uin_hdlc.Rx_FrameSize {
      bins small_ = {[3:10]}; // address + control + 1 data byte
      bins large_ = {[100:$]};
      bins max = {126};
      bins others = default;
    }

    // Check all bits in Rx_SC register have been toggled
    Rx_Ready_cp : coverpoint uin_hdlc.Rx_SC[Rx_Ready];
    Rx_Drop_cp : coverpoint uin_hdlc.Rx_SC[Rx_Drop];
    Rx_FrameError_cp : coverpoint uin_hdlc.Rx_SC[Rx_FrameError];
    Rx_AbortSignal_cp : coverpoint uin_hdlc.Rx_SC[Rx_AbortSignal];
    Rx_Overflow_cp : coverpoint uin_hdlc.Rx_SC[Rx_Overflow];
    Rx_FCSen_cp : coverpoint uin_hdlc.Rx_SC[Rx_FCSen];

    // Check all bits in Tx_SC register have been toggled
    Tx_Done_cp : coverpoint uin_hdlc.Rx_SC[Tx_Done];
    Tx_Enable_cp : coverpoint uin_hdlc.Rx_SC[Tx_Enable];
    Tx_AbortFrame_cp : coverpoint uin_hdlc.Rx_SC[Tx_AbortFrame];
    Tx_AbortedTrans_cp : coverpoint uin_hdlc.Rx_SC[Tx_AbortedTrans];
    Tx_Full_cp : coverpoint uin_hdlc.Rx_SC[Tx_Full];

  endgroup

  //Initialize coverage group
  hdlc_cg coverage_inst;
  initial begin
      coverage_inst = new();
  end

endmodule:coverage_hdlc
