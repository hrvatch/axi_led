module axi_led_formal_tb #(
  parameter int AXI_ADDR_BW_p = 12,
  parameter int LED_NBR_p = 32
) (
  input wire logic  clk,
  input wire logic  rst_n,
  input wire logic [$clog2(AXI_ADDR_BW_p)-1:0] i_axi_awaddr,
  input wire logic  i_axi_awvalid,
  input wire logic [31:0] i_axi_wdata,
  input wire logic [3:0] i_axi_wstrb,
  input wire logic i_axi_wvalid,
  input wire logic i_axi_bready,
  input wire logic [$clog2(AXI_ADDR_BW_p)-1:0] i_axi_araddr,
  input wire logic i_axi_arvalid,
  input wire logic i_axi_rready,
  output wire logic o_axi_awready,
  output wire logic o_axi_wready,
  output wire logic [1:0] o_axi_bresp,
  output wire logic o_axi_bvalid,
  output wire logic o_axi_arready,
  output wire logic [31:0] o_axi_rdata,
  output wire logic [1:0] o_axi_rresp,
  output wire logic o_axi_rvalid,
  output wire logic [LED_NBR_p-1:0] o_led
);

  localparam logic [1:0] RESP_OKAY   = 2'b00;
  localparam logic [1:0] RESP_EXOKAY = 2'b10;
  localparam logic [1:0] RESP_SLVERR = 2'b10;
  localparam logic [1:0] RESP_DECERR = 2'b11;
  
  // Default clock
  default clocking cb @(posedge clk);
  endclocking

  // Default reset
  default disable iff (!rst_n);

  // Valid-ready handshake
  property valid_ready_handshake(valid, ready, data);
    valid && !ready |=> valid && $stable(data)
  endproperty : valid_ready_handshake

  // ------------------------
  // Assumptions
  // ------------------------
  // Handshake
  assume_araddr_valid_ready_handshake : assume property(valid_ready_handshake(i_axi_arvalid, o_axi_arready, i_axi_araddr));
  assume_awaddr_valid_ready_handshake : assume property(valid_ready_handshake(i_axi_awvalid, o_axi_awready, i_axi_awaddr));
  assume_wdata_valid_ready_handshake  : assume property(valid_ready_handshake(i_axi_wvalid, o_axi_wready, i_axi_wdata));
  assume_wstrb_valid_ready_handshake  : assume property(valid_ready_handshake(i_axi_wvalid, o_axi_wready, i_axi_wstrb));

  // ------------------------
  // Assertions
  // ------------------------
  // Handshake
  assert_rdata_valid_ready_handshake : assert property(valid_ready_handshake(o_axi_rvalid, i_axi_rready, o_axi_rdata));
  assert_rresp_valid_ready_handshake : assert property(valid_ready_handshake(o_axi_rvalid, i_axi_rready, o_axi_rresp));
  assert_bresp_valid_ready_handshake : assert property(valid_ready_handshake(o_axi_bvalid, i_axi_bready, o_axi_bresp));

  // We want to prove there are no more then one outstanding read or write requests
  // Auxilliary logic for read requests
  int read_request_cnt;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      read_request_cnt <= 1'b0;
    end else begin
      // If we get immediate response for the read request
      if (!(i_axi_arvalid && o_axi_arready && o_axi_rvalid && i_axi_rready)) begin
        if (i_axi_arvalid && o_axi_arready) begin
          read_request_cnt++;
        end else if (i_axi_rready && o_axi_rvalid) begin
          read_request_cnt--;
        end
      end
    end
  end

  assert_valid_number_of_read_requests : assert property ( read_request_cnt >= 0 && read_request_cnt <= 1);

  // Correct write data
  //assert_correct_data_7_0 : assert property (
  //  i_axi_wvalid && o_axi_wready && i_axi_wstrb[0] |-> ##1 o_led[7:0] == $past(i_axi_wdata[7:0])
  //);
  //assert_correct_data_15_8 : assert property (
  //  i_axi_wvalid && o_axi_wready && i_axi_wstrb[1] |-> ##1 o_led[15:8] == $past(i_axi_wdata[15:8])
  //);
  //assert_correct_data_23_16 : assert property (
  //  i_axi_wvalid && o_axi_wready && i_axi_wstrb[2] |-> ##1 o_led[23:16] == $past(i_axi_wdata[23:16])
  //);
  //assert_correct_data_31_24 : assert property (
  //  i_axi_wvalid && o_axi_wready && i_axi_wstrb[3] |-> ##1 o_led[31:24] == $past(i_axi_wdata[31:24])
  //);
  

  // ------------------------
  // Covers
  // ------------------------
  // Cover 5 consecutive read requests
  cov_5_conecutive_read_requests : cover property (
    (i_axi_arvalid && o_axi_arready)[*5]
  );
  
  // ------------------------
  // Instantiate DUT
  // ------------------------
  axi_led #(
    .AXI_ADDR_BW_p(AXI_ADDR_BW_p),
    .LED_NBR_p(LED_NBR_p)
  ) axi_led_dut (
    .clk ( clk ),
    .rst_n ( rst_n ),
    .i_axi_awaddr ( i_axi_awaddr ),
    .i_axi_awvalid ( i_axi_awvalid ),
    .i_axi_wdata ( i_axi_wdata ),
    .i_axi_wstrb ( i_axi_wstrb ),
    .i_axi_wvalid ( i_axi_wvalid ),
    .i_axi_bready ( i_axi_bready ),
    .i_axi_araddr ( i_axi_araddr ),
    .i_axi_arvalid ( i_axi_arvalid ),
    .i_axi_rready ( i_axi_rready ),
    .o_axi_awready ( o_axi_awready ),
    .o_axi_wready ( o_axi_wready ),
    .o_axi_bresp ( o_axi_bresp ),
    .o_axi_bvalid ( o_axi_bvalid ),
    .o_axi_arready ( o_axi_arready ),
    .o_axi_rdata ( o_axi_rdata ),
    .o_axi_rresp ( o_axi_rresp ),
    .o_axi_rvalid ( o_axi_rvalid ),
    .o_led ( o_led )
  );

endmodule : axi_led_formal_tb
