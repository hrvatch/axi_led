clear -all
analyze -sv12 ../src/axi_led_formal_tb.sv ../../rtl/axi_led.sv
elaborate -top axi_led_formal_tb
clock clk
reset !rst_n
