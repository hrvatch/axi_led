// AXI4-Lite module used to control LEDs via the AXI slave. Led related register is located at
// offset 0x0.
//
// Writing '1' to wdata[0] will turn on LED, '0' will turn it off.
// Writing '1' to wdata[1] will turn on LED, '0' will turn it off.
// i.e.
// *(volatile uint32 *)(LED_AXI_ADDRESS + 0x0) = 0xf; // Turn on leds[3:0]
//
// 4k address space by default. Writing to the unused address will result in SLVERR response.
// LED_NBR_p parameter greater than the bus data width will result in synthesis issues.

module led_axi #(
  parameter AXI_ADDR_BW_p = 12,    // 4k boundary by default
  parameter LED_NBR_p = 8          // Number of LEDs. Maximum length = bus data width 
) (
  input wire logic  clk,
  input wire logic  rst_n,
  input wire logic [$clog2(AXI_ADDR_BW_p)-1:0] i_axi_awaddr,
  input wire logic  i_axi_awvalid,
  input wire logic [31:0] i_axi_wdata,
  input wire logic [3:0] i_axi_wstrb,
  input wire logic i_axi_wvalid,
  input wire logic i_axi_bready,
  input wire logic [$clog2(AXI_ADDR_BW_p-1):0] i_axi_araddr,
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
  
  // Internal signals
  logic [31:0] s_axi_rdata;
  logic [1:0] s_axi_rresp;
  logic [1:0] s_axi_bresp;
  logic s_axi_rvalid;
  logic s_axi_bvalid;
  logic s_axi_awready;
  logic s_axi_wready;
  logic s_axi_arready;
  logic [LED_NBR_p-1:0] s_led;
  
  assign o_axi_awready = s_axi_awready;
  assign o_axi_wready = s_axi_wready;
  assign o_axi_bresp = s_axi_bresp;
  assign o_axi_bvalid = s_axi_bvalid;
  assign o_axi_arready = s_axi_arready;
  assign o_axi_rdata = s_axi_rdata;
  assign o_axi_rresp = s_axi_rresp;
  assign o_axi_rvalid = s_axi_rvalid;
  assign o_led = s_led;

  // Write address handshake
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_awready <= 1'b0;
    end else if (i_axi_awvalid && !s_axi_awready) begin
      s_axi_awready <= 1'b1;
    end else begin
      s_axi_awready <= 1'b0;
    end
  end

  // Write data handshake
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_wready <= 1'b0;
      s_axi_bresp <= RESP_OKAY;
      s_axi_bvalid <= 1'b0;
      s_led <= 8'b0;
    end else begin
      if (i_axi_wvalid && !s_axi_wready) begin
        s_axi_wready <= 1'b1;
        s_axi_bresp <= RESP_OKAY;
        case (i_axi_awaddr[$clog2(AXI_ADDR_BW_p)-1:2])
          'd0: begin
            if (i_axi_wstrb[0]) begin
              s_led[7:0] <= i_axi_wdata[7:0];
            end
            if (i_axi_wstrb[1] && LED_NBR_p >= 8) begin
              s_led[15:8] <= i_axi_wdata[15:8];
            end
            if (i_axi_wstrb[2] && LED_NBR_p >= 16) begin
              s_led[23:16] <= i_axi_wdata[23:16];
            end
            if (i_axi_wstrb[3] && LED_NBR_p >= 24) begin
              s_led[31:24] <= i_axi_wdata[31:24];
            end
          end
          default: begin
            s_axi_bresp <= RESP_SLVERR;
          end
        endcase
        s_axi_bvalid <= 1'b1;
      end else if (i_axi_bready && s_axi_bvalid) begin
        s_axi_bvalid <= 1'b0;
      end else begin
        s_axi_wready <= 1'b0;
      end
    end
  end

  // Read address handshake
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_arready <= 1'b0;
      s_axi_rresp = RESP_OKAY;
      s_axi_rvalid <= 1'b0;
    end else begin
      if (i_axi_arvalid && !s_axi_arready) begin
        s_axi_arready <= 1'b1;
        s_axi_rresp <= RESP_OKAY;
        case (i_axi_araddr[$clog2(AXI_ADDR_BW_p)-1:2])
          'd0: begin
            s_axi_rdata <= s_led;
          end
          default: begin
            s_axi_rdata <= 32'hdeaddead;
            s_axi_rresp <= RESP_SLVERR;
          end
        endcase
        s_axi_rvalid <= 1'b1;
      end else if (i_axi_rready && s_axi_rvalid) begin
        s_axi_rvalid <= 1'b0;
      end else begin
        s_axi_arready <= 1'b0;
      end
    end
  end

endmodule : led_axi
