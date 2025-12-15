## AXI-Lite LED controller

This module is used to control LEDs on the various FPGA dev boards. Intent is to connect it to 
the system bus via AXI-Lite interface. It can be used to control between 0 and AXI_DATA_BW-1 where
AXI_DATA_BW is the bit-width of the AXI data bus.

LED register is located at offset 0x0. Writing '1' to a bit of the register will turn on the LED,
writing '0' will turn off the led.
