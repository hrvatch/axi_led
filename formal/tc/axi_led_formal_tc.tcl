clear -all
analyze -sv12 $env(AXI_LITE_LED_PATH)/formal/src/axi_led_formal_tb.sv $env(AXI_LITE_LED_PATH)/rtl/axi_led.sv
elaborate -top axi_led_formal_tb
clock clk
reset !rst_n
