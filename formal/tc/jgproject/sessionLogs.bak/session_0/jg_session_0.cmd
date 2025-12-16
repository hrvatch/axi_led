# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2024.03
# platform  : Linux 6.17.9-arch1-1
# version   : 2024.03 FCS 64 bits
# build date: 2024.03.27 15:42:27 UTC
# ----------------------------------------
# started   : 2025-12-16 00:47:09 CET
# hostname  : mashina.(none)
# pid       : 1833228
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:34045' '-style' 'windows' '-data' 'AAABBHicY2RgYLCp////PwMYMFcBCTYGfwY3IIQDxgdQhg0jAyoA8ZlQRQIbUGgGBlaYZpgSZiDWYtBlSGTIAcJ8hnKGeIZShjyGYiBZAIT5DEUMJQypDClAcX+GYDJU50D5iQwVDJlAOg2sKhdsRjxQdTKDHpjMAbsHAIWPIeY=' '-proj' '/ssd1/workspace/axi_led/formal/tc/jgproject/sessionLogs/session_0' '-init' '-hidden' '/ssd1/workspace/axi_led/formal/tc/jgproject/.tmp/.initCmds.tcl' 'led_axi_formal_tc.tcl'
clear -all
analyze -sv12 ../src/led_axi_formal_tb.sv ../../rtl/led_axi.sv
elaborate -top led_axi_formal_tb
clock clk
reset !rst_n
include led_axi_formal_tc.tcl
prove -bg -task {<embedded>}
visualize -violation -property <embedded>::led_axi_formal_tb.assert_bresp_okay -new_window
