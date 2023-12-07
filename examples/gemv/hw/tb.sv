
module tb();
`include "def.vh"

reg clk;
reg en;
reg [`DW-1:0] A [`SZ*`SZ-1:0];
reg [`DW-1:0] W [`SZ-1:0];
wire [`DW-1:0] O [`SZ-1:0];
wire valid;

array_top iDUT (
    .clk(clk),
    .A(A),
    .W(W),
    .O(O),
    .en_i(en),
    .valid_o(valid)
);

//integer i;
integer j;
//always @(posedge clk) begin
//    i = i + 1;
//end

task automatic testMatmul();
    fork
        begin: waiting
            wait (valid);
            $write("Result: ");
            for (j = 0; j < `SZ; j = j + 1) begin
                $write("%d ", O[j]); 
            end
            $display("");
            disable timeout;
        end
        begin: timeout
            repeat (10) @(posedge clk);
            $display("Timeout..");
            $stop();
        end
    join
endtask //automatic

initial begin
    A = {16'h9, 16'h8, 16'h7, 16'h6, 16'h5, 16'h4, 16'h3, 16'h2, 16'h1};
    W = {16'h3, 16'h2, 16'h1};
    en = 1'b1;
    @(posedge clk);
    @(negedge clk);
    en = 1'b0;

    testMatmul();

    W = {16'h6, 16'h4, 16'h2};
    en = 1'b1;
    @(posedge clk);
    @(negedge clk);
    en = 1'b0;

    testMatmul();

    $finish();
end

initial begin
    clk = 0;
    forever clk = #5 ~clk;
end

/*always @(posedge clk) begin
    $display("Systolic array output: %d", O);
end*/

endmodule