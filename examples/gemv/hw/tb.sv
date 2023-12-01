
module tb();
`include "def.vh"

reg clk;
reg [`DW-1:0] win [`SZ-1:0];
reg [`DW-1:0] ain [`SZ-1:0];
wire [`DW-1:0] O;

array iDUT (
    .clk(clk),
    .A(ain),
    .W(win),
    .O(O)
);

integer i;
always @(posedge clk) begin
    i = i + 1;
end

initial begin
    win = {16'h3, 16'h2, 16'h1};
    i = 0;

    repeat (10) @(posedge clk);
    $finish();
end

always @(i) begin
    case (i)
        0: ain = {0,0,16'h1};
        1: ain = {0,16'h2,16'h4};
        2: ain = {16'h3,16'h5,16'h7};
        3: ain = {16'h6,16'h8,0};
        4: ain = {16'h9,0,0};
        default: ain = {0,0,0};
    endcase    
end

initial begin
    clk = 0;
    forever clk = #5 ~clk;
end

always @(posedge clk) begin
    $display("Systolic array output: %d", O);
end

endmodule