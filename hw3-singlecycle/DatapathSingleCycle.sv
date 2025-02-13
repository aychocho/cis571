`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0
`define REG_DIM 32
// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0


`define RESET 32'b0

`define I_ALU 7'b00_100_11
`define R 7'h33 
`define LUI 7'h37
`define I_unsigned 3'b011 //sltiu
`define DIVU 7'h01 

`include "../hw2a-divider/divider_unsigned.sv"
`include "../hw2b-cla/cla.sv"



module decoder5_32(
	input wire [4:0] in,
	output wire [31:0] out
);
	assign out = 32'b1<<in;
endmodule 


module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  // TODO: your code here

  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];
  assign regs[0] = 32'b0;
  wire [31:0] write_register;
  decoder5_32 dec(.in(rd),.out(write_register));
  wire [30:0] we_32 = {31{we}};
  wire [30:0] w_enable = we_32&write_register[31:1];
  int i;
  always_ff @(posedge clk) begin
	for(i = 1;i<32;i=i+1) begin
		if(rst) regs[i] <= `RESET;
		else if (w_enable[i-1] ) regs[i]<= rd_data;
		end
	end
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];
endmodule

module const_shift_left #(
	parameter N = 20,
	parameter shift_by = 1
	)(
	input [N-1:0]in,
	output [N+shift_by -1:0] out
	);
	assign out = {in,{(shift_by){1'b0}}};
endmodule


module extend #(
	parameter N = 12,
	parameter sign_extend = 1
	)(
	input wire [N-1:0] in,
	output wire [`REG_SIZE] out);
	
	wire extend_num;
	assign extend_num = (sign_extend) ? in[N-1] : 1'b0;
	assign out = {{(`REG_DIM - N){extend_num}}, in};
endmodule

module divider_signed(
	input  wire [`REG_SIZE] i_dividend,
    input  wire [`REG_SIZE] i_divisor,
    output wire [`REG_SIZE] o_remainder,
    output wire [`REG_SIZE] o_quotient
	);
	wire N = i_dividend[`REG_DIM-1] ^ i_divisor[`REG_DIM-1];
	wire [`REG_SIZE] i_dividend_mag = (i_dividend[`REG_DIM-1]==1'b1) ? (~i_dividend)+32'b1 : i_dividend;
	wire [`REG_SIZE] i_divisor_mag = (i_divisor[`REG_DIM-1]==1'b1) ? (~i_divisor)+32'b1 : i_divisor;
	
	wire [`REG_SIZE] rem,q ;
	divider_unsigned div_mag(.i_dividend(i_dividend_mag),.i_divisor(i_divisor_mag),.o_remainder(rem),.o_quotient(q));
	assign o_remainder = (N) ? {{1'b1},rem[30:0]} : rem;
	assign o_quotient = (N) ? {{1'b1},q[30:0]} : q;
endmodule 
module ALU(
	input logic [`REG_SIZE] in1,
	input logic [`REG_SIZE] in2,
	output logic [`REG_SIZE] out,
	input logic [2:0] fun3,
	input logic [6:0] fun7,
	input logic [6:0] opcode,
	output wire Z, // ZERO FLAG
	output wire N, //SIGNED NEGATIVE FLAG
	output wire V, //UNSIGNED NEGATIVE FLAG
	output wire INF //divide by zero
	);
	
	wire [`REG_SIZE] add_res;
	wire [`REG_SIZE] sub_res;
	wire [`REG_SIZE] xor_res;
	wire [`REG_SIZE] and_res;
	wire [`REG_SIZE] or_res;
	wire [`REG_SIZE] sll_res;
	wire [`REG_SIZE] sra_res;
	wire [`REG_SIZE] srl_res;
	wire [`REG_SIZE] slt_res;
	wire [`REG_SIZE] sltu_res;
	wire [`REG_SIZE] divu_res;
	wire [`REG_SIZE] remu_res;
	wire[`REG_SIZE] div_res;
	wire[`REG_SIZE] rem_res;
	wire[`REG_SIZE] mul_res;
	
	cla CLA_add(.a(in1),
			.b(in2),
			.cin(1'b0),
			.sum(add_res));
	cla CLA_sub(.a(in1),
			.b(~in2),
			.cin(1'b1),
			.sum(sub_res));
	divider_unsigned divu(.i_dividend(in1), .i_divisor(in2), .o_remainder(remu_res), .o_quotient(divu_res)); 
	divider_signed div(.i_dividend(in1), .i_divisor(in2), .o_remainder(rem_res), .o_quotient(div_res));
	
	assign xor_res = in1 ^ in2;
	assign and_res = in1 & in2;
	assign or_res = in1 | in2;
	assign sll_res = in1<<(in2[4:0]);
	assign srl_res = in1>>(in2[4:0]);
	assign sra_res = in1>>>(in2[4:0]);
	assign slt_res = {{(`REG_DIM-1){1'b0}},sub_res[`REG_DIM-1]};
	assign sltu_res = (in1<in2) ? {{(`REG_DIM-1){1'b0}},1'b1}: {(`REG_DIM){1'b0}};
	assign mul_res = in1*in2;
	
	wire [`REG_SIZE] sra_or_srl = (fun7 == 7'h0) ? srl_res: sra_res; 
	wire[`REG_SIZE] sub_or_mul = (fun7==7'h01) ? mul_res: sub_res;
	wire [`REG_SIZE] add_or_sub_r_or_mul = (fun7 == 7'h0) ? add_res: sub_or_mul; 
	wire [`REG_SIZE] add_or_sub = (opcode == `I_ALU) ? add_res :  add_or_sub_r_or_mul;
	
	assign Z = ~(|sub_res);
	assign N = sub_res[`REG_DIM-1];
	assign V = sltu_res[0];
	assign INF = ~(|in2);
	
	wire[`REG_SIZE] divu_or_sr = (fun7 == `DIVU) ? divu_res : sra_or_srl;
	wire[`REG_SIZE] remu_or_and = (fun7 == `DIVU) ? remu_res : and_res;
	wire[`REG_SIZE] div_or_xor = (fun7 == `DIVU) ? div_res : xor_res;
	wire[`REG_SIZE] rem_or_or = (fun7 == `DIVU) ? rem_res : or_res;
	
	always_comb begin
		case(fun3)
		3'b000 : out = add_or_sub;
		3'b001: out = sll_res;
		3'b010: out = slt_res;
		3'b011: out = sltu_res;
		3'b100: out = xor_res;
		3'b101: out = divu_or_sr;
		3'b110: out = rem_or_or;
		3'b111: out = remu_or_and;
		default: out = 32'b0;
		
		endcase
	end
	
endmodule

module DatapathSingleCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output logic [`REG_SIZE] addr_to_dmem,
    input logic [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem
);

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui   = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal   = insn_opcode == OpJal;
  wire insn_jalr  = insn_opcode == OpJalr;

  wire insn_beq  = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne  = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt  = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge  = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb  = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh  = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw  = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi  = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti  = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori  = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori   = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi  = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or   = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

	
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  `ifndef SYNTHESIS
  `include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  `endif

  // program counter
  logic if_blt = N & (!Z) ; 
  logic if_bltu = V & (!Z);
  logic if_branch = (Z & insn_beq)|((!Z)&insn_bne)|(if_blt & insn_blt)|(!if_blt & insn_bge)|(if_bltu & insn_bltu)| (!if_bltu & insn_bgeu) ;
  wire [13:0] target_shifted;
  const_shift_left #(.N(13)) csl_branch_target(.in(imm_b), .out(target_shifted));
  wire [`REG_SIZE] target_shifted_se;
  extend #(.N(14)) se_target(.in(target_shifted), .out(target_shifted_se));
  
  
  logic [`REG_SIZE] pcNext, pcCurrent;
  wire [`REG_SIZE] pcInc = (if_branch)? target_shifted_se : 32'h0000_0004;
  assign pcNext = pcCurrent + pcInc;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end

  // NOTE: don't rename your RegFile instance as the tests expect it to be `rf`
  assign halt = (insn_ecall)?1'b1:1'b0;
	wire [19:0] lui_imm = {insn_funct7, insn_rs2, insn_rs1, insn_funct3};
	wire [`REG_SIZE] lui_imm_32;// = {insn_from_imem[31:12],12'b0};
	const_shift_left #(.N(20),.shift_by(12)) csl_lui(.in(insn_from_imem[31:12]),.out(lui_imm_32)); 
	logic [`REG_SIZE] r1_data, r2_data;
	
	wire [`REG_SIZE] add_res;

	
	wire [`REG_SIZE] imm_i_se, imm_i_ze;
	extend SE_imm(.in(imm_i), .out(imm_i_se));
	extend #(.sign_extend(0)) ZE_imm(.in(imm_i),.out(imm_i_ze));
	wire [`REG_SIZE] imm_i_32 = (insn_sltiu) ? imm_i_ze : imm_i_se;
	wire [`REG_SIZE] alu_in2_data = (insn_opcode == OpRegReg) ? r2_data : imm_i_32;
	logic[`REG_SIZE] rf_data_in;// = (insn_lui) ? lui_imm_32 : alu_out;
	
	
	
	

  logic [`REG_SIZE] alu_out;
  wire Z,N,V,INF;
  
  ALU alu(.in1(r1_data),
		  .in2(alu_in2_data),
		  .out(alu_out),
	      .fun3(insn_funct3),
		  .fun7(insn_funct7),
	      .opcode(insn_opcode),
		  .Z(Z), 
		  .N(N), 
		  .V(V),
		  .INF(INF)
		  );


  wire write_en1 = (insn_opcode==OpBranch) ? 1'b0 : 1'b1;
  wire write_en2 = (insn_ecall)? 1'b0: write_en1;
  	RegFile rf (
	.rd(insn_rd) ,
    .rd_data(rf_data_in) ,
    .rs1(insn_rs1) ,
    .rs1_data(r1_data) ,
    .rs2(insn_rs2) ,
    .rs2_data(r2_data) ,
    .clk(clk) ,
    .we(write_en2) ,
    .rst(rst)
  );
  
  // TODO: you will need to edit the port connections, however.



  logic illegal_insn;

  always_comb begin
    illegal_insn = 1'b0;

    case (insn_opcode)
      OpLui: begin
        // TODO: start here by implementing lui
		rf_data_in = lui_imm_32;
      end
	 
      default: begin
        //illegal_insn = 1'b1;
		rf_data_in = alu_out;
      end
    endcase
  end

endmodule


/* A memory module that supports 1-cycle reads and writes, with one read-only port
 * and one read+write port.
 */
module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem_array[NUM_WORDS];

`ifdef SYNTHESIS
  initial begin
    $readmemh("mem_initial_contents.hex", mem_array);
  end
`endif

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module Processor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathSingleCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );
  
  
endmodule

