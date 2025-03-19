/* SARAH ALSAYED 5681 3836 */

`timescale 1ns / 1ns

// quotient = dividend / divisor
`define REG_SIZE 31:0

typedef struct packed{
    logic [`REG_SIZE] divisor;
    logic [`REG_SIZE] dividend;
    logic [`REG_SIZE] remainder;
    logic [`REG_SIZE] quotient;
} divu_4iter_stage;

module divu_4iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output logic [31:0] o_dividend,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient,
	output logic [31:0] o_divisor
); 
	logic [31:0] rem [4:0] ;
	logic [31:0] q [4:0];
	logic [31:0] k [4:0];
	
	assign rem[0] = i_remainder;
	assign q[0] = i_quotient;
	assign k[0] = i_dividend;
	
	genvar i ;
	generate 
		for(i = 0;i<4;i=i+1) begin : iter
			divu_1iter du(
				.i_dividend (k[i]), 
				.i_divisor (i_divisor), 
				.i_remainder (rem[i]), 
				.i_quotient (q[i]), 
				.o_dividend (k[i+1]), 
				.o_remainder (rem[i+1]), 
				.o_quotient (q[i+1])
				);
		end 
	endgenerate
	
	assign o_remainder = rem[4] ;
	assign o_quotient = q[4];
	assign o_dividend = k[4];
	assign o_divisor = i_divisor;
endmodule 

module DividerUnsignedPipelined (
    input wire clk, rst, stall,
    input  wire  [31:0] i_dividend,
    input  wire  [31:0] i_divisor,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient
);
	
    // TODO: your code here
	//logic [`REG_SIZE] input_divisor = i_divisor;
	divu_4iter_stage div_stage0_in, div_stage0_out;

	divu_4iter du0( .i_dividend (i_dividend), .i_divisor (i_divisor), .i_remainder (32'h0), .i_quotient (32'h0), 
					.o_dividend (div_stage0_in.dividend), .o_remainder (div_stage0_in.remainder), .o_quotient (div_stage0_in.quotient), .o_divisor(div_stage0_in.divisor));

	divu_4iter_stage div_stage1_in , div_stage1_out;
	divu_4iter du1(
				.i_dividend (div_stage0_out.dividend), .i_divisor (div_stage0_out.divisor), .i_remainder (div_stage0_out.remainder), .i_quotient (div_stage0_out.quotient), 
				.o_dividend (div_stage1_in.dividend), .o_remainder (div_stage1_in.remainder), .o_quotient (div_stage1_in.quotient), .o_divisor(div_stage1_in.divisor));
				
	divu_4iter_stage div_stage2_in , div_stage2_out;
	divu_4iter du2(
		.i_dividend (div_stage1_out.dividend), .i_divisor (div_stage1_out.divisor), .i_remainder (div_stage1_out.remainder), .i_quotient (div_stage1_out.quotient),
		.o_dividend (div_stage2_in.dividend), .o_remainder (div_stage2_in.remainder), .o_quotient (div_stage2_in.quotient), .o_divisor(div_stage2_in.divisor));
				
	divu_4iter_stage div_stage3_in , div_stage3_out;
	divu_4iter du3(
		.i_dividend (div_stage2_out.dividend), .i_divisor (div_stage2_out.divisor), .i_remainder (div_stage2_out.remainder), .i_quotient (div_stage2_out.quotient),
		.o_dividend (div_stage3_in.dividend), .o_remainder (div_stage3_in.remainder), .o_quotient (div_stage3_in.quotient), .o_divisor(div_stage3_in.divisor));

	divu_4iter_stage div_stage4_in , div_stage4_out;
	divu_4iter du4(
		.i_dividend (div_stage3_out.dividend), .i_divisor (div_stage3_out.divisor), .i_remainder (div_stage3_out.remainder), .i_quotient (div_stage3_out.quotient),
		.o_dividend (div_stage4_in.dividend), .o_remainder (div_stage4_in.remainder), .o_quotient (div_stage4_in.quotient), .o_divisor(div_stage4_in.divisor));

	divu_4iter_stage div_stage5_in , div_stage5_out;
	divu_4iter du5(
		.i_dividend (div_stage4_out.dividend), .i_divisor (div_stage4_out.divisor), .i_remainder (div_stage4_out.remainder), .i_quotient (div_stage4_out.quotient),
		.o_dividend (div_stage5_in.dividend), .o_remainder (div_stage5_in.remainder), .o_quotient (div_stage5_in.quotient), .o_divisor(div_stage5_in.divisor));

	divu_4iter_stage div_stage6_in , div_stage6_out;
	divu_4iter du6(
		.i_dividend (div_stage5_out.dividend), .i_divisor (div_stage5_out.divisor), .i_remainder (div_stage5_out.remainder), .i_quotient (div_stage5_out.quotient),
		.o_dividend (div_stage6_in.dividend), .o_remainder (div_stage6_in.remainder), .o_quotient (div_stage6_in.quotient), .o_divisor(div_stage6_in.divisor));
	
	wire [`REG_SIZE] out_dividend,out_divisor;
	divu_4iter du7(
				.i_dividend (div_stage6_out.dividend), .i_divisor (div_stage6_out.divisor), .i_remainder (div_stage6_out.remainder), .i_quotient (div_stage6_out.quotient), 
				.o_dividend (out_dividend), .o_remainder (o_remainder), .o_quotient (o_quotient),.o_divisor(out_divisor));
	
	always_ff @(posedge clk) begin
		if(rst) begin
			div_stage0_out.dividend <= 0;
			div_stage0_out.remainder <=0;
			div_stage0_out.quotient <= 0;
			div_stage0_out.divisor <= 0;

			div_stage1_out.dividend <= 0;
			div_stage1_out.remainder <= 0;
			div_stage1_out.quotient <= 0;
			div_stage1_out.divisor <= 0;

			div_stage2_out.dividend <= 0;
			div_stage2_out.remainder <= 0;
			div_stage2_out.quotient <= 0;
			div_stage2_out.divisor <= 0;

			div_stage3_out.dividend <= 0;
			div_stage3_out.remainder <= 0;
			div_stage3_out.quotient <= 0;
			div_stage3_out.divisor <= 0;

			div_stage4_out.dividend <= 0;
			div_stage4_out.remainder <= 0;
			div_stage4_out.quotient <= 0;
			div_stage4_out.divisor <= 0;

			div_stage5_out.dividend <= 0;
			div_stage5_out.remainder <= 0;
			div_stage5_out.quotient <= 0;
			div_stage5_out.divisor <= 0;

			div_stage6_out.dividend <= 0;
			div_stage6_out.remainder <= 0;
			div_stage6_out.quotient <= 0;
			div_stage6_out.divisor <= 0;
		end

		div_stage0_out.dividend <= (div_stage0_in.dividend);
		div_stage0_out.remainder <=(div_stage0_in.remainder);
		div_stage0_out.quotient <= (div_stage0_in.quotient);
		div_stage0_out.divisor <= (div_stage0_in.divisor);

		div_stage1_out.dividend <= (div_stage1_in.dividend);
		div_stage1_out.remainder <=(div_stage1_in.remainder);
		div_stage1_out.quotient <= (div_stage1_in.quotient);
		div_stage1_out.divisor <= (div_stage1_in.divisor);

		div_stage2_out.dividend <= (div_stage2_in.dividend);
		div_stage2_out.remainder <=(div_stage2_in.remainder);
		div_stage2_out.quotient <= (div_stage2_in.quotient);
		div_stage2_out.divisor <= (div_stage2_in.divisor);

		div_stage3_out.dividend <= (div_stage3_in.dividend);
		div_stage3_out.remainder <=(div_stage3_in.remainder);
		div_stage3_out.quotient <= (div_stage3_in.quotient);
		div_stage3_out.divisor <= (div_stage3_in.divisor);

		div_stage4_out.dividend <= (div_stage4_in.dividend);
		div_stage4_out.remainder <=(div_stage4_in.remainder);
		div_stage4_out.quotient <= (div_stage4_in.quotient);
		div_stage4_out.divisor <= (div_stage4_in.divisor);

		div_stage5_out.dividend <= (div_stage5_in.dividend);
		div_stage5_out.remainder <=(div_stage5_in.remainder);
		div_stage5_out.quotient <= (div_stage5_in.quotient);
		div_stage5_out.divisor <= (div_stage5_in.divisor);

		div_stage6_out.dividend <= (div_stage6_in.dividend);
		div_stage6_out.remainder <=(div_stage6_in.remainder);
		div_stage6_out.quotient <= (div_stage6_in.quotient);
		div_stage6_out.divisor <= (div_stage6_in.divisor);
	end

endmodule


module divu_1iter (
    input  wire  [31:0] i_dividend,
    input  wire  [31:0] i_divisor,
    input  wire  [31:0] i_remainder,
    input  wire  [31:0] i_quotient,
    output logic [31:0] o_dividend,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient
);

  // TODO: copy your code from HW2A here
	logic [31:0] rem2,q0,q1;
	logic [32:0] rem3; 
	logic [0:0] lt ;
	
	assign rem2 = {i_remainder[30:0],i_dividend[31]};
	assign rem3 = rem2 - i_divisor ;
	assign lt = rem3[32] ; 
	assign q0 = {i_quotient[30:0],1'b0};
	assign q1 = {i_quotient[30:0],1'b1};
	assign o_quotient = (lt)? q0: q1;
	assign o_remainder = (lt)? rem2: rem3[31:0]; 
	assign o_dividend = {i_dividend[30:0],1'b0};

endmodule
