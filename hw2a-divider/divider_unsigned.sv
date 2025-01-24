/* INSERT NAME AND PENNKEY HERE 
* Alexander Cho (aycho)
* */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here
	wire [31:0] dividendPartial;
	wire [31:0] quotientPartial;
	wire [31:0] remainderPartial;
	assign remainderPartial[0] = 32'h0000_0000;
	assign quotientPartial[0] = 32'h0000_0000;
	assign dividendPartial[0] = i_dividend;
	generate
		for (i=0; i < 32; i = i+1) begin: iter
			divu_1iter thisOne(
                .i_dividend (dividendPartial[i]),
                .i_divisor (i_divisor),
                .i_remainder (remainderPartial[i]),
                .i_quotient (quotientPartial[i]),
                .o_dividend (dividendPartial[i+1]),
                .o_remainder (remainderPartial[i+1]),
                .o_quotient (quotientPartial[i+1])    
            );
        end
    endgenerate
    assign o_remainder = remainderPartial[32];
    assign o_quotient = quotientPartial[32];
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

    wire[31:0] shifted = (i_remainder << 1) | (i_dividend[31] & 1'b1);
    wire [0:0] isLess = shifted < i_divisor;
    assign o_remainder = isLess ? shifted : (shifted - i_divisor);
    assign o_quotient = isLess ? (i_quotient << 1) : ((i_quotient << 1) | 32'h0000_0001);
    assign o_dividend = i_dividend << 1;

endmodule
