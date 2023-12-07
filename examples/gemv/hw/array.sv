`include "def.vh"
module array 
(
    input clk,
    input [`DW-1:0] A [`SZ-1:0],
    input [`DW-1:0] W [`SZ-1:0],
    output [`DW-1:0] O,
    input en,
    output valid
);

wire [`DW-1:0] yout [`SZ-1:0];
reg [`DW-1:0] yin [`SZ-1:0];
reg yvalid [`SZ-1:0];

generate
    genvar i;

    for (i = 0; i < `SZ; i = i + 1) begin
        initial begin
            yin[i] = 0;
        end
        if (i == 0) begin
            thecell iCELL (
                .W(W[i]),
                .A(A[i]),
                .I(0),
                .O(yout[i])
            );
        end else begin
            thecell iCELL (
                .W(W[i]),
                .A(A[i]),
                .I(yin[i-1]),
                .O(yout[i])
            );
        end
        always @(posedge clk) begin
            yin[i] <= yout[i];
            if (i == 0) begin
                yvalid[i] <= en;
            end else begin
                yvalid[i] <= yvalid[i-1];
            end
        end
    end
endgenerate

assign O = yin[`SZ-1];
assign valid = yvalid[`SZ-1];


endmodule