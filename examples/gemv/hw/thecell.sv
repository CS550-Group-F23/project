`include "def.vh"

module thecell (
    input [`DW-1:0] W,
    input [`DW-1:0] A,
    input [`DW-1:0] I,
    output [`DW-1:0] O
);

assign O = I + A * W;
    
endmodule