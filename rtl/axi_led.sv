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

module axi_led #(
  parameter AXI_ADDR_BW_p = 12,    // 4k boundary by default
  parameter LED_NBR_p = 8          // Number of LEDs. Maximum length = bus data width 
) (
  input wire logic  clk,
  input wire logic  rst_n,
  input wire logic [AXI_ADDR_BW_p-1:0] i_axi_awaddr,
  input wire logic  i_axi_awvalid,
  input wire logic [31:0] i_axi_wdata,
  input wire logic i_axi_wvalid,
  input wire logic i_axi_bready,
  input wire logic [AXI_ADDR_BW_p-1:0] i_axi_araddr,
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
  localparam logic [1:0] RESP_EXOKAY = 2'b01;
  localparam logic [1:0] RESP_SLVERR = 2'b10;
  localparam logic [1:0] RESP_DECERR = 2'b11;
  
  logic [31:0] s_led;
  
  // --------------------------------------------------------------
  // Write address, write data and write wresponse
  // --------------------------------------------------------------
  logic [1:0]  c_axi_wresp;
  logic [3:0]  c_axi_wstrb;
  logic [31:0] c_axi_wdata;
  logic s_axi_wdata_buf_used;
  logic [31:0] s_axi_wdata_buf;
  logic [3:0]  s_axi_wstrb_buf;
  logic [1:0]  s_axi_bresp;
  logic [AXI_ADDR_BW_p-1:0] s_axi_awaddr_buf;
  logic [AXI_ADDR_BW_p-1:0] c_axi_awaddr;
  logic s_axi_awaddr_buf_used;
  logic s_axi_awvalid;
  logic s_axi_wvalid;
  // Internal signals
  logic s_axi_bvalid;
  logic s_axi_awready;
  logic s_axi_wready;
  logic s_awaddr_done;
  logic [AXI_ADDR_BW_p-1:0] s_axi_awaddr;
 
  // We want to stall the address write if either we received write request without write data
  // or if the write address buffer is full and master is stalling write response channel
  assign o_axi_awready = !s_axi_awaddr_buf_used & s_axi_awvalid;

  // We want to stall the data write if either we received write data without a write request
  // or if the write data buffer is full and master is stalling write response channel
  assign o_axi_wready  = !s_axi_wdata_buf_used & s_axi_wvalid;

  logic write_response_stalled;
  logic valid_write_address;
  logic valid_write_data;

  assign write_response_stalled = o_axi_bvalid & ~i_axi_bready;
  assign valid_write_address = s_axi_awaddr_buf_used | (i_axi_awvalid & o_axi_awready);
  assign valid_write_data = s_axi_wdata_buf_used | (i_axi_wvalid & o_axi_wready);

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_awvalid <= 1'b0;
      s_axi_awaddr_buf_used <= 1'b0;
    end else begin
      s_axi_awvalid <= 1'b1;
      // When master is stalling on the response channel or if we didn't receive
      // write data, we need to buffer the address
      if (i_axi_awvalid && o_axi_awready && (write_response_stalled || !valid_write_data)) begin
        s_axi_awaddr_buf <= i_axi_awaddr;
        s_axi_awaddr_buf_used <= 1'b1;
      end else if (s_axi_awaddr_buf_used && valid_write_data && (!o_axi_bvalid || i_axi_bready)) begin
        s_axi_awaddr_buf_used <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_wdata_buf_used <= 1'b0;
      s_axi_wvalid <= 1'b0;
    end else begin
      s_axi_wvalid <= 1'b1;
      // We want to fill the buffer if either we're getting a response stall, or we 
      // get a write data without a write address
      if (i_axi_wvalid && o_axi_wready && (write_response_stalled || !valid_write_address)) begin
        s_axi_wdata_buf <= i_axi_wdata;
        s_axi_wdata_buf_used <= 1'b1;
      end else if (s_axi_wdata_buf_used && valid_write_address && (!o_axi_bvalid || i_axi_bready)) begin
        s_axi_wdata_buf_used <= 1'b0;
      end
    end
  end

  // Muxes to select write address and write data either from the buffer or from the AXI bus
  assign c_axi_awaddr = s_axi_awaddr_buf_used ? s_axi_awaddr_buf : i_axi_awaddr;
  assign c_axi_wdata  = s_axi_wdata_buf_used  ? s_axi_wdata_buf : i_axi_wdata;

  // Store write data to the correct register and generate a response
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_bvalid <= 1'b0;
    end else begin
      // If there is write address and write data in the buffer
      if (valid_write_address && valid_write_data && (!o_axi_bvalid || i_axi_bready)) begin
        case (c_axi_awaddr[AXI_ADDR_BW_p-1:2])
          '0 : begin
            s_led <= c_axi_wdata[LED_NBR_p-1:0];
            s_axi_bresp <= RESP_OKAY;
          end

          default: begin
            s_axi_bresp <= RESP_SLVERR;
          end
        endcase
        s_axi_bvalid <= 1'b1;
      end else if (o_axi_bvalid && i_axi_bready && !(valid_write_address && valid_write_data)) begin
        s_axi_bvalid <= 1'b0;
      end
    end
  end
  
  assign o_axi_bresp = s_axi_bresp;
  assign o_led = s_led;

  // Assign intermediate signals to outputs 
  assign o_axi_bvalid = s_axi_bvalid;
  
  // --------------------------------------------------------------
  // Read address and read response
  // --------------------------------------------------------------
  logic s_axi_rvalid;
  logic [31:0] s_axi_rdata;
  logic [1:0] s_axi_rresp;
  logic s_axi_arready;

  // Read address buffer
  logic [AXI_ADDR_BW_p-1:0] s_araddr_buf;
  logic s_araddr_buf_used;
  logic [AXI_ADDR_BW_p-1:0] c_araddr;

  // Address buffer management
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_araddr_buf_used <= 1'b0;
      s_axi_arready <= 1'b0;
    end else begin
      s_axi_arready <= 1'b1;

      // Fill buffer when response is stalled
      if (i_axi_arvalid && o_axi_arready && o_axi_rvalid && !i_axi_rready) begin
        s_araddr_buf <= i_axi_araddr;
        s_araddr_buf_used <= 1'b1;
      end 
      // Clear buffer when address is consumed
      else if (s_araddr_buf_used && (!o_axi_rvalid || i_axi_rready)) begin
        s_araddr_buf_used <= 1'b0;
      end
    end
  end

  // Mux to select address 
  assign c_araddr = s_araddr_buf_used ? s_araddr_buf : i_axi_araddr;

  // Ready signal blocks when buffer full
  assign o_axi_arready = !s_araddr_buf_used & s_axi_arready;

  // Response generation
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_rvalid <= 1'b0;
    end else begin
      // Generate response when address is available (buffer or direct)
      if ((s_araddr_buf_used || (i_axi_arvalid && o_axi_arready)) && (!o_axi_rvalid || i_axi_rready)) begin
        case (c_araddr[AXI_ADDR_BW_p-1:2])
          'd0: begin
            // Forward write data if write is happening to same address
            s_axi_rdata <= '0;
            s_axi_rdata[LED_NBR_p-1:0] <= s_led;
            s_axi_rresp <= RESP_OKAY;
          end
          default: begin
            s_axi_rdata <= 32'hdeaddead;
            s_axi_rresp <= RESP_SLVERR;
          end
        endcase
        s_axi_rvalid <= 1'b1;
      // Clear response when handshake completes and no new transaction
      end else if (o_axi_rvalid && i_axi_rready && !s_araddr_buf_used && !(i_axi_arvalid && o_axi_arready)) begin
        s_axi_rvalid <= 1'b0;
      end
    end
  end

  assign o_axi_rdata = s_axi_rdata;
  assign o_axi_rresp = s_axi_rresp;
  assign o_axi_rvalid = s_axi_rvalid;

endmodule : axi_led
