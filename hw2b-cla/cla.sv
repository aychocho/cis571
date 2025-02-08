`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a ^ b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */

module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   // TODO: your code here

   wire g0_1, p0_1, g2_3, p2_3;
   assign g0_1 = gin[1] | ( pin[1] & gin[0]);
   assign p0_1 = & (pin[1:0]);
   
   assign cout[0] = gin[0] | (pin[0] & cin);
   
   assign g2_3 = gin[3] | (pin[3] & gin[2]);
   assign p2_3 = & (pin[3:2]);
   
   assign cout[1] = g0_1 | (p0_1 & cin); 
   
   assign gout = g2_3 | (p2_3 & g0_1) ;
   assign pout = p2_3 & p0_1 ; 
   assign cout[2] = gin[2] | (pin[2] & (g0_1 | (p0_1 & cin)));
   
endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here
  wire g03, p03, g47, p47;
  gp4 gp4_lower( .gin(gin[3:0]), .pin(pin[3:0]), .cin(cin), .gout(g03), .pout(p03), .cout(cout[2:0])) ; 
  wire carry_lower;
  assign carry_lower = g03 | (p03 & cin) ;
  assign cout[3] = g03 | (p03 & cin) ;
  gp4 gp4_upper( .gin(gin[7:4]), .pin(pin[7:4]), .cin(carry_lower), .gout(g47), .pout(p47), .cout(cout[6:4]));
  assign gout = g47 | (p47 & g03);
  assign pout = p47 & p03 ; 

endmodule
/*

module gp(parameter N = 2, 
		   input wire [(1<<(N-1))-1:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [(1<<(N-1))-2:0] cout);

   wire [0:0] g[0:1] ;
   wire [0:0] p [0:1];
   generate 
   if(N==2) begin
		assign g[1] = gin[1] ; 
		assign g[0] = gin[0] ;
		assign p[1] = pin[1];
		assign p[0] = pin[0];
		
   end
   else begin
	gp #(N>>1) gp0(.gin(gin[(1<<(N-2))-1:0]),
		.pin(pin[(1<<(N-2))-1:0]),
		.cin(cin),
		.gout(g[0]),
		.pout(p[0]),
		.cout(cout[(1<<(N-2))-2:0])
		);
		
	gp #(N>>1) gp1(.gin(gin[(1<<(N-1))-1:(1<<(N-2))]),
		.pin(pin[(1<<(N-1))-1:(1<<(N-2))]),
		.cin(cin),
		.gout(g[1]),
		.pout(p[1]),
		.cout(cout[(1<<(N-1))-3:(1<<(N-2))-1])
		);

	end 
		
	endgenerate
	assign gout = g[1] + (p[1] & g[0]);
	assign pout = p[1] & p[0];
	assign cout[(1<<(N-1))-2] = gout + (pout & cin);

endmodule
*/
module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   // TODO: your code here
   
   wire [30:0] cout;
   genvar i ;
   wire [31:0] g ;
   wire [31:0] p ;
   generate 
	for(i = 0;i<32;i=i+1) begin
		gp1 gp1_block(.a(a[i]), .b(b[i]), .g(g[i]), .p(p[i]));
	end
   endgenerate
	wire [7:0] gout ;
	wire [7:0] pout ;

	gp4 gp4_block0(.gin(g[3:0]), .pin(p[3:0]), .cin(cin), .gout(gout[0]), .pout(pout[0]), .cout(cout[2:0]));
	
	wire c0 = gout[0] | (pout[0] & cin); 
	gp4 gp4_block1(.gin(g[7:4]), .pin(p[7:4]), .cin(c0), .gout(gout[1]), .pout(pout[1]), .cout(cout[6:4]));
	
	wire c1 = gout[1] | (pout[1] & c0); 
	gp4 gp4_block2(.gin(g[11:8]), .pin(p[11:8]), .cin(c1), .gout(gout[2]), .pout(pout[2]), .cout(cout[10:8]));
	
	wire c2 = gout[2] | (pout[2] & c1); 
	gp4 gp4_block3(.gin(g[15:12]), .pin(p[15:12]), .cin(c2), .gout(gout[3]), .pout(pout[3]), .cout(cout[14:12]));
	
	wire c3 = gout[3] | (pout[3] & c2); 
	gp4 gp4_block4(.gin(g[19:16]), .pin(p[19:16]), .cin(c3), .gout(gout[4]), .pout(pout[4]), .cout(cout[18:16]));
	
	wire c4 = gout[4] | (pout[4] & c3); 
	gp4 gp4_block5(.gin(g[23:20]), .pin(p[23:20]), .cin(c4), .gout(gout[5]), .pout(pout[5]), .cout(cout[22:20]));
	
	wire c5 = gout[5] | (pout[5] & c4); 
	gp4 gp4_block6(.gin(g[27:24]), .pin(p[27:24]), .cin(c5), .gout(gout[6]), .pout(pout[6]), .cout(cout[26:24]));
	
	wire c6 = gout[6] | (pout[6] & c5); 
	gp4 gp4_block7(.gin(g[31:28]), .pin(p[31:28]), .cin(c6), .gout(gout[7]), .pout(pout[7]), .cout(cout[30:28]));
	
	
   wire [6:0] c_final;
   wire g0_31 , p0_31;
	gp8 gp8_block( .gin(gout), .pin(pout), .cin(cin), .gout(g0_31), .pout(p0_31), .cout(c_final));
	assign {cout[27], cout[23], cout[19], cout[15], cout[11], cout[7], cout[3] } = c_final;
	wire [31:0] carry_out = {cout,cin};
	assign sum = p ^ carry_out;
   

endmodule

module cla_with_carryout
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum,
   output wire c_out);

   // TODO: your code here
   
   wire [30:0] cout;
   genvar i ;
   wire [31:0] g ;
   wire [31:0] p ;
   generate 
	for(i = 0;i<32;i=i+1) begin
		gp1 gp1_block(.a(a[i]), .b(b[i]), .g(g[i]), .p(p[i]));
	end
   endgenerate
	wire [7:0] gout ;
	wire [7:0] pout ;

	gp4 gp4_block0(.gin(g[3:0]), .pin(p[3:0]), .cin(cin), .gout(gout[0]), .pout(pout[0]), .cout(cout[2:0]));
	
	wire c0 = gout[0] | (pout[0] & cin); 
	gp4 gp4_block1(.gin(g[7:4]), .pin(p[7:4]), .cin(c0), .gout(gout[1]), .pout(pout[1]), .cout(cout[6:4]));
	
	wire c1 = gout[1] | (pout[1] & c0); 
	gp4 gp4_block2(.gin(g[11:8]), .pin(p[11:8]), .cin(c1), .gout(gout[2]), .pout(pout[2]), .cout(cout[10:8]));
	
	wire c2 = gout[2] | (pout[2] & c1); 
	gp4 gp4_block3(.gin(g[15:12]), .pin(p[15:12]), .cin(c2), .gout(gout[3]), .pout(pout[3]), .cout(cout[14:12]));
	
	wire c3 = gout[3] | (pout[3] & c2); 
	gp4 gp4_block4(.gin(g[19:16]), .pin(p[19:16]), .cin(c3), .gout(gout[4]), .pout(pout[4]), .cout(cout[18:16]));
	
	wire c4 = gout[4] | (pout[4] & c3); 
	gp4 gp4_block5(.gin(g[23:20]), .pin(p[23:20]), .cin(c4), .gout(gout[5]), .pout(pout[5]), .cout(cout[22:20]));
	
	wire c5 = gout[5] | (pout[5] & c4); 
	gp4 gp4_block6(.gin(g[27:24]), .pin(p[27:24]), .cin(c5), .gout(gout[6]), .pout(pout[6]), .cout(cout[26:24]));
	
	wire c6 = gout[6] | (pout[6] & c5); 
	gp4 gp4_block7(.gin(g[31:28]), .pin(p[31:28]), .cin(c6), .gout(gout[7]), .pout(pout[7]), .cout(cout[30:28]));
	
	
   wire [6:0] c_final;
   wire g0_31 , p0_31;
	gp8 gp8_block( .gin(gout), .pin(pout), .cin(cin), .gout(g0_31), .pout(p0_31), .cout(c_final));
	assign {cout[27], cout[23], cout[19], cout[15], cout[11], cout[7], cout[3] } = c_final;
	wire [31:0] carry_out = {cout,cin};
	assign sum = p ^ carry_out;
   assign c_out = g0_31 | (p0_31&cin);

endmodule
