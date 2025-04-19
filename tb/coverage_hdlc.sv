//////////////////////////////////////////////////
// Title:   coverage_hdlc
// Author: Aasmund and Mathias
// Date: 19.04.2025 
//////////////////////////////////////////////////

`include "hdlc_packet.sv"

module coverage_hdlc(
  in_hdlc uin_hdlc
);
  covergroup hdlc_cg @(posedge uin_hdlc.Clk);
    Tx_FrameSize_cp : coverpoint uin_hdlc.Tx_FrameSize {
      bins zero = {2}; // address + control + 0 data bytes
      bins small_ = {[3:10]};
      bins large_ = {[100:$]};
      bins max = {126};
      bins others = default;
    }

    Rx_FrameSize_cp : coverpoint uin_hdlc.Rx_FrameSize {
      bins zero = {2}; // address + control + 0 data bytes
      bins small_ = {[3:10]};
      bins large_ = {[100:$]};
      bins max = {126};
      bins others = default;
    }

  endgroup

  //Initialize coverage group
  hdlc_cg coverage_inst;
  initial begin
      coverage_inst = new();
  end

endmodule:coverage_hdlc
