`include "def.vh"
module array_top (
    input clk,
    input [`DW-1:0] A [`SZ*`SZ-1:0],
    input [`DW-1:0] W [`SZ-1:0],
    output [`DW-1:0] O [`SZ-1:0],
    input en_i,
    output valid_o
);

localparam SREG_SZ = `DW*(`SZ*2-1);
localparam SREG_SZ_SLICE = `DW*(`SZ*2-2);
reg [SREG_SZ-1:0] ain0_sr; 
reg [SREG_SZ-1:0] ain1_sr;
reg [SREG_SZ-1:0] ain2_sr;
reg [`SZ*2-2:0] en_sr;
reg [`DW-1:0] w0_sr;
reg [`DW-1:0] w1_sr;
reg [`DW-1:0] w2_sr;

always_ff @(posedge clk) begin
    if (en_i) begin
        ain0_sr <= {{(`DW){1'b0}},{(`DW){1'b0}},A[6],A[3],A[0]};
        ain1_sr <= {{(`DW){1'b0}},A[7],A[4],A[1],{(`DW){1'b0}}};
        ain2_sr <= {A[8],A[5],A[2],{(`DW){1'b0}},{(`DW){1'b0}}};
        en_sr <= {{(`SZ-1){1'b0}},{(`SZ){1'b1}}};
        w0_sr <= W[0];
        w1_sr <= W[1];
        w2_sr <= W[2];
    end else begin
        ain0_sr <= {{(`DW){1'b0}},ain0_sr[SREG_SZ-1:`DW]};
        ain1_sr <= {{(`DW){1'b0}},ain1_sr[SREG_SZ-1:`DW]};
        ain2_sr <= {{(`DW){1'b0}},ain2_sr[SREG_SZ-1:`DW]};
        en_sr <= {1'b0,en_sr[`SZ*2-2:1]};
        w0_sr <= w0_sr;
        w1_sr <= w1_sr;
        w2_sr <= w2_sr;
    end
end
wire [`DW-1:0] ain0 = ain0_sr[`DW-1:0];
wire [`DW-1:0] ain1 = ain1_sr[`DW-1:0];
wire [`DW-1:0] ain2 = ain2_sr[`DW-1:0];
wire en = en_sr[0];

wire [`DW-1:0] o_w;
wire valid_w;

array iARR (
    .clk(clk),
    .A({ain2, ain1, ain0}),
    .W({w2_sr, w1_sr, w0_sr}),
    .O(o_w),
    .en(en),
    .valid(valid_w)
);


reg [`DW-1:0] O_r [`SZ-1:0];
reg valid_r;
reg valid_r_r;
generate
    genvar i;

    for (i = 0; i < `SZ; i = i + 1) begin
        always_ff @(posedge clk) begin
            if (valid_w) begin
                if (i == 0) begin
                    O_r[i] <= o_w;
                end else begin
                    O_r[i] <= O_r[i-1];
                end
            end else begin
                O_r[i] <= O_r[i];
            end
        end
    end
endgenerate

always_ff @(posedge clk) begin 
    valid_r <= valid_w;
    valid_r_r <= valid_r;
end

assign O=O_r;
assign valid_o=valid_r_r & ~valid_r;
    
endmodule