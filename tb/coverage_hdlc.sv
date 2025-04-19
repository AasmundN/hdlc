//////////////////////////////////////////////////
// Title:   coverage_hdlc
// Author: Aasmund and Mathias
// Date: 19.04.2025 
//////////////////////////////////////////////////

module coverage_hdlc(
  in_hdlc uin_hdlc
);
  covergroup hdlc_cg @(posedge uin_hdlc.Clk);
    Tx_FrameSize_cp : coverpoint uin_hdlc.Tx_FrameSize {

    }

    Rx_FrameSize_cp : coverpoint uin_hdlc.Rx_FrameSize {

    }

    Tx_SC_cp : coverpoint uin_hdlc.Tx_SC {

    }

    Rx_SC_cp : coverpoint uin_hdlc.Rx_SC {

    }
  endgroup

  //Initialize coverage group
  hdlc_cg coverage_inst;
  initial begin
      coverage_inst = new();
  end

  always @(posedge uin_hdlc.Clk) begin
    coverage_inst.sample();
  end

endmodule:coverage_hdlc
