/* SARAH ALSAYED PENNKEY:SALSAYED */

`timescale 1ns / 1ns

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here
	wire [31:0] rem [32:0] ;
	wire [31:0] q [32:0];
	wire [31:0] k [32:0];
	
	assign rem[0] = 32'h0000_0000;
	assign q[0] = 32'h0000_0000;
	assign k[0] = i_dividend;
	
	genvar i ;
	generate 
		for(i = 0;i<32;i=i+1) begin : iter
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
	assign o_remainder = rem[32] ;
	assign o_quotient = q[32]; 
	
endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    // TODO: your code here
	wire [31:0] rem2,q0,q1;
	wire [32:0] rem3; 
	wire [0:0] lt ;
	
	assign rem2 = {i_remainder[30:0],i_dividend[31]}; //implement shift using rewiring instead of shifter to reduce area and delay 
	assign rem3 = rem2 - i_divisor ; //if result is negative then rem2< i_divisor. the number being negative or positive depends on the msb of rem3 given it has 33 bits.
	assign lt = rem3[32] ; // instead of using a comparator block repeatedly which increases delay and area the msb of the subtraction as subtraction is used anyways.
	assign q0 = {i_quotient[30:0],1'b0};
	assign q1 = {i_quotient[30:0],1'b1};
	assign o_quotient = (lt)? q0: q1;
	assign o_remainder = (lt)? rem2: rem3[31:0]; 
	assign o_dividend = {i_dividend[30:0],1'b0};
	

endmodule


