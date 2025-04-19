// shared enums

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
