/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0
`define RESET 32'd0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0
`define REG_DIM 32


`ifndef RISCV_FORMAL
`include "../hw2b-cla/cla.sv"
`include "../hw4-multicycle/DividerUnsignedPipelined.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`endif





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

  // TODO: copy your HW3B code here
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];
  //grab data from rs1 and rs2
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];

  always_ff @(posedge clk) begin
    if (rst) begin
      integer i;
      for (i = 0; i < NumRegs; i = i + 1) begin
        regs[i] <= `RESET;
      end
    end else if (we && (rd != 5'd0)) begin
      regs[rd] <= rd_data;
    end
  end

endmodule

module DatapathMultiCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem
);

  // TODO: your code here (largely based on HW3B)
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

  // this code is only for simulation, not synthesis
  `ifndef SYNTHESIS
  `include "../hw3-singlecycle/RvDisassembler.sv"
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
  logic [`REG_SIZE] pcNext, pcCurrent;
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
  
  //divison state
  always @(posedge clk) begin
    if (rst) begin
      while_divide_current <= 0;
      div_counter_current<= 0;
    end else begin
      div_counter_current <= div_counter_next;
      while_divide_current <=while_divide_next;
    end
 end

  // NOTE: don't rename your RegFile instance as the tests expect it to be `rf`
  // TODO: you will need to edit the port connections, however.
  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;
  logic[`REG_SIZE] dataReg;
  logic[4:0] rd;
  logic[4:0] rs1;
  logic[4:0] rs2;
  //write enable
  logic regwe;
  logic while_divide_current;
  logic [3:0] div_counter_current; 
  logic while_divide_next;
  logic [3:0] div_counter_next; 

  RegFile rf (
    .clk(clk),
    .rst(rst),
    .we(regwe),
    .rd(rd),
    .rd_data(dataReg),
    .rs1(rs1),
    .rs2(rs2),
    .rs1_data(rs1_data),
    .rs2_data(rs2_data)
  );

  cla mathematatics(
    .a(a),
    .b(b),
    .cin(cin),
    .sum(sum)
  );
	logic [`REG_SIZE] remu_res;
	logic [`REG_SIZE] quotient_res;
	logic [`REG_SIZE] dividend, divisor;
	logic [`REG_SIZE] dividend_s, divisor_s;
	logic [`REG_SIZE] rem_res,div_res;
	
	wire stall = 1'b0;
	DividerUnsignedPipelined div_inst(.i_dividend(dividend), .i_divisor(divisor), .o_remainder(remu_res), .o_quotient(quotient_res),.clk(clk),.rst(rst),.stall(stall));
  
	
	
	logic [63:0] rsd1,rsd2;


  logic [`REG_SIZE] sum;
  logic [`REG_SIZE] a;
  logic [`REG_SIZE] b;
  logic cin;



  logic branchTime; //are we branching?
  logic [`REG_SIZE] branchTo; //target addy

  logic illegal_insn;
  logic [`REG_SIZE] mem_addr;
  logic [1:0] mem_off;
  logic[63:0] mulhu_res, mulh_res;
  logic[63:0] mulhsu_res;
  logic N;
  logic [`REG_SIZE] i_dividend_mag ;
  logic [`REG_SIZE] i_divisor_mag ;
  

  always_comb begin
    illegal_insn = 1'b0;
    //write enable bit, need to declare elsewhere
    regwe = 1'b0;
    //data reg, need to implement elsewhere
    dataReg = 32'd0;
    //default no branch
    branchTime = 1'b0;
    branchTo = 32'd0;
    a = 0;
	rsd1 = 64'b1;
	rsd2 = 64'b1;
    b = 0;
    cin = 0;
	//signed division stuffs 
	N = 0;
	i_dividend_mag = 32'd1;
	i_divisor_mag = 32'd1;
	
	//divide state stuffs 
	div_counter_next = 0;
	while_divide_next = 0;
	
	
	divisor = 32'b1;
	dividend = 32'd2;
	divisor_s = 32'b1;
	dividend_s = 32'b1;
	
	
    rd = insn_rd;
    rs1 = insn_rs1;
    rs2 = insn_rs2;
    halt = 0;
    pcNext = pcCurrent + 4;
	addr_to_dmem = 4;
	mem_off = 0;
	mem_addr = 0;
	store_we_to_dmem = 0;
	store_data_to_dmem = 0;
	mulhu_res = rs1_data*rs2_data;
	mulh_res = $signed(rs1_data)*$signed(rs2_data);
	mulhsu_res = $signed(rs1_data)*$signed({{1'b0},rs2_data});
    case (insn_opcode)
      OpLui: begin
        // TODO: start here by implementing lui
        // is there a 20 bit immediate? Not sure abt that, added it above for safety's sake
        // imm_u should be u type immediate
        //set write enable
        regwe = 1'b1;
        //send immu plus zeros to data
        dataReg = {insn_from_imem[31:12], 12'b0};
      end
	  OpAuipc: begin
		if(insn_auipc) begin
			regwe = 1'b1;
			dataReg = pcCurrent + (insn_from_imem[31:12]<<12) ;
		end
	  end
	  OpJalr: begin
		if(insn_jalr) begin
			regwe = 1'b1;
			dataReg = pcCurrent + 4;
			pcNext = (rs1_data+imm_i_sext) & ~(32'h1);
		end
	  end
      OpRegImm: begin
        // TODO: do stuff that takes regs and an immediate, probably math log and shifts
        regwe = 1'b1;
        // case on fun3
        if (insn_addi) begin
          // logic for addi
          a = rs1_data;
          b = imm_i_sext;
          cin = 1'b0;
          dataReg = sum;
        end

        else if (insn_slti) begin
          // logic for slti
          dataReg = ($signed(rs1_data) < $signed(imm_i_sext)) ? 1:0;
        end

        else if (insn_sltiu) begin
          // logic for sltiu
          dataReg = ((rs1_data) < (imm_i_sext)) ? 1:0;
        end

        else if (insn_xori) begin
          // logic for xori
          dataReg = rs1_data ^ imm_i_sext;
        end

        else if (insn_ori) begin
          // logic for ori
          dataReg = rs1_data | imm_i_sext;
        end

        else if (insn_andi) begin
          // logic for andi
          dataReg = rs1_data & imm_i_sext;
        end

        else if (insn_slli) begin
          // logic for slli
          dataReg = rs1_data << imm_i[4:0];
        end

        else if (insn_srli) begin
          dataReg = rs1_data >> imm_i[4:0];
        end

        else if (insn_srai) begin
          // logic for srai
          dataReg = $signed(rs1_data) >>> imm_i[4:0];
        end
        else //illegal case
          begin
            regwe = 1'b0;
            illegal_insn = 1'b1;
          end
      end
      OpRegReg: begin
        // TODO: do stuff that takes all regs, same as above
        //TODO: DONT FORGET ABT MULS!!! Need to add ifs
        regwe = 1'b1;
        // case on fun3
        if (insn_add) begin
          // add/sub case
          // TODO: logic for add
          a = rs1_data;
          b = rs2_data;
          cin = 1'b0;
          dataReg = sum;
        end
        else if (insn_sub) begin
          // TODO: logic for sub
          a = rs1_data;
          b = ~rs2_data;
          cin = 1'b1;
          dataReg = sum;
        end
        else if (insn_sll) begin
          //TODO: THIS IS THE SAME FOR MULH
          // logic for sll
          dataReg = rs1_data << (rs2_data[4:0]);
        end
        else if (insn_slt) begin
          // logic for slt
          dataReg = $signed(rs1_data) < $signed(rs2_data) ? 32'd1:32'd0;
        end
        else if (insn_sltu) begin
          // logic for sltu
          dataReg = rs1_data < rs2_data ? 32'd1:32'd0;
        end
        else if (insn_xor) begin
          // logic for xor
          dataReg = rs1_data ^ rs2_data;
        end
        else if (insn_srl) begin
          dataReg = rs1_data >> rs2_data[4:0];
        end 
        else if (insn_sra) begin
          // logic for sra
          dataReg = $signed(rs1_data) >>> rs2_data[4:0];
        end
        else if (insn_or) begin
          // logic for or
          dataReg = rs1_data | rs2_data;
        end
        else if (insn_and) begin
          // logic for and
          dataReg = rs1_data & rs2_data;
        end
		else if(insn_mul) begin
		dataReg = rs1_data * rs2_data;
		end
		else if(insn_divu) begin
			if(while_divide_current) begin
				if(div_counter_current == 4'd7) begin
					while_divide_next = 1'b0;
					div_counter_next = 4'b0;
					regwe = 1'b1;
					dataReg = quotient_res;
					pcNext = pcCurrent + 4;
				end
				else begin
					regwe = 1'b0;
					div_counter_next = div_counter_current + 4'b001;
					while_divide_next = 1'b1;
					pcNext = pcCurrent; 
				end
			end
			else begin
				while_divide_next = 1'b1;
				div_counter_next = 4'b0001;
				dividend = rs1_data;
				divisor = rs2_data;
				regwe = 1'b0;
				pcNext = pcCurrent; 
			end
		end
		else if(insn_remu) begin
			if(while_divide_current) begin
				if(div_counter_current == 4'd7) begin
					while_divide_next = 1'b0;
					div_counter_next = 4'b0;
					regwe = 1'b1;
					dataReg = remu_res;
					pcNext = pcCurrent + 4;
				end
				else begin
					regwe = 1'b0;
					div_counter_next = div_counter_current + 4'b001;
					while_divide_next = 1'b1;
					pcNext = pcCurrent; 
				end
			end
			else begin
				while_divide_next = 1'b1;
				div_counter_next = 4'b0001;
				dividend = rs1_data;
				divisor = rs2_data;
				regwe = 1'b0;
				pcNext = pcCurrent; 
			end
		end
		else if(insn_rem) begin
			if(while_divide_current) begin
				if(div_counter_current == 4'd7) begin
					while_divide_next = 1'b0;
					div_counter_next = 4'b0;
					regwe = 1'b1;
					dataReg = (rs1_data[`REG_DIM-1]) ?( (~remu_res) + 32'b1): remu_res;
					pcNext = pcCurrent + 4;
				end
				else begin
					regwe = 1'b0;
					div_counter_next = div_counter_current + 4'b001;
					while_divide_next = 1'b1;
					pcNext = pcCurrent; 
				end
			end
			else begin
				while_divide_next = 1'b1;
				div_counter_next = 4'b0001;
				i_dividend_mag = (rs1_data[`REG_DIM-1]==1'b1) ? (~rs1_data)+32'b1 : rs1_data;
				i_divisor_mag = (rs2_data[`REG_DIM-1]==1'b1) ? (~rs2_data)+32'b1 : rs2_data;
				dividend = i_dividend_mag;
				divisor = i_divisor_mag;
				regwe = 1'b0;
				pcNext = pcCurrent; 
			end
		end
		else if(insn_div) begin
			if(while_divide_current) begin
				if(div_counter_current == 4'd7) begin
					N = rs1_data[`REG_DIM-1] ^ rs2_data[`REG_DIM-1];
					while_divide_next = 1'b0;
					div_counter_next = 4'b0;
					regwe = 1'b1;
					if(rs2_data==0) begin
						dataReg = 32'hffff_ffff;
					end
					else begin
						dataReg = (N)? ( (~quotient_res) + 32'b1) : quotient_res;
					end
					pcNext = pcCurrent + 4;
				end
				else begin
					regwe = 1'b0;
					div_counter_next = div_counter_current + 4'b001;
					while_divide_next = 1'b1;
					pcNext = pcCurrent; 
				end
			end
			else begin
				while_divide_next = 1'b1;
				div_counter_next = 4'b0001;
				i_dividend_mag = (rs1_data[`REG_DIM-1]==1'b1) ? (~rs1_data)+32'b1 : rs1_data;
				i_divisor_mag = (rs2_data[`REG_DIM-1]==1'b1) ? (~rs2_data)+32'b1 : rs2_data;
				dividend = i_dividend_mag;
				divisor = i_divisor_mag;
				regwe = 1'b0;
				pcNext = pcCurrent; 
			end
		end
		else if(insn_mulhu) begin
			dataReg = mulhu_res[63:32];
		end
		else if(insn_mulh) begin
			dataReg = mulh_res[63:32];
		end
		else if(insn_mulhsu) begin
			dataReg = mulhsu_res[63:32];
		end
        else begin
          regwe = 1'b0;
          illegal_insn = 1'b1;
        end
      end
	  OpLoad: begin
		if(insn_lw) begin
			if(((rs1_data + imm_i_sext)&(32'h0000_0003))==0) begin
				regwe = 1'b1;
				addr_to_dmem = rs1_data + imm_i_sext;
				dataReg = load_data_from_dmem ; 
			end
			else begin
				illegal_insn = 1'b1;
			end
		end
		else if(insn_lb || insn_lbu) begin
			regwe = 1'b1;
			addr_to_dmem = (rs1_data + imm_i_sext)&(32'hffff_fffc);
			mem_addr = rs1_data + imm_i_sext;
			mem_off = mem_addr[1:0];
			case (mem_off)
				2'b00: dataReg = (insn_lb) ? {{24{load_data_from_dmem[7]}},load_data_from_dmem[7:0]} : {{24{1'b0}},load_data_from_dmem[7:0]};
				2'b01: dataReg = (insn_lb) ?{{24{load_data_from_dmem[15]}},load_data_from_dmem[15:8]}: {{24{1'b0}},load_data_from_dmem[15:8]};
				2'b10: dataReg = (insn_lb) ?{{24{load_data_from_dmem[23]}},load_data_from_dmem[23:16]}: {{24{1'b0}},load_data_from_dmem[23:16]};
				2'b11: dataReg = (insn_lb) ?{{24{load_data_from_dmem[31]}},load_data_from_dmem[31:24]}: {{24{1'b0}},load_data_from_dmem[31:24]};
			endcase 
			
		end
		else if(insn_lh || insn_lhu) begin
			regwe = 1'b1;
			addr_to_dmem = (rs1_data + imm_i_sext)&(32'hffff_fffc);
			mem_addr = rs1_data + imm_i_sext;
			mem_off = mem_addr[1:0];
			case (mem_off)
				2'b00: dataReg = (insn_lh) ? {{16{load_data_from_dmem[15]}},load_data_from_dmem[15:0]} : {{16{1'b0}},load_data_from_dmem[15:0]};
				2'b01: dataReg = (insn_lh) ? {{16{load_data_from_dmem[23]}},load_data_from_dmem[23:8]} : {{16{1'b0}},load_data_from_dmem[23:8]};
				2'b10: dataReg = (insn_lh) ?{{16{load_data_from_dmem[31]}},load_data_from_dmem[31:16]}: {{16{1'b0}},load_data_from_dmem[31:16]};
				2'b11: begin
				regwe = 1'b0;
				illegal_insn = 1'b1;
				end
			endcase 
			
		end
		
		else begin
		  regwe = 1'b0;
          illegal_insn = 1'b1;
		end
	  end
	  OpStore: begin
		if(insn_sw) begin
			if(((rs1_data + imm_s_sext)&(32'h0000_0003))==0) begin
				addr_to_dmem = rs1_data + imm_s_sext;
				store_we_to_dmem = 4'hf;
				store_data_to_dmem = rs2_data;
			end
			else begin
				illegal_insn = 1'b1;
			end
		end
		else if(insn_sh) begin
			addr_to_dmem = (rs1_data + imm_s_sext)&(32'hffff_fffc);
			mem_addr = rs1_data + imm_s_sext;
			mem_off = mem_addr[1:0];
			
			case (mem_off)
				2'b00: begin
					store_we_to_dmem = 4'h3;
					store_data_to_dmem = rs2_data;
				end
				2'b01: begin 
					store_we_to_dmem = 4'h6;
					store_data_to_dmem = {rs2_data[23:0],{8{1'b0}}};
				end
				2'b10: begin 
					store_we_to_dmem = 4'hc;
					store_data_to_dmem = {rs2_data[15:0],{16{1'b0}}};
				end
				2'b11: begin 
					store_we_to_dmem = 4'h0;
					store_data_to_dmem = 0;
				end
			endcase
		end
		else if(insn_sb) begin
			addr_to_dmem = (rs1_data + imm_s_sext)&(32'hffff_fffc);
			mem_addr = rs1_data + imm_s_sext;
			mem_off = mem_addr[1:0];
			
			case (mem_off)
				2'b00: begin
					store_we_to_dmem = 4'h1;
					store_data_to_dmem = rs2_data;
				end
				2'b01: begin 
					store_we_to_dmem = 4'h2;
					store_data_to_dmem = {rs2_data[23:0],{8{1'b0}}};
				end
				2'b10: begin 
					store_we_to_dmem = 4'h4;
					store_data_to_dmem = {rs2_data[15:0],{16{1'b0}}};
				end
				2'b11: begin 
					store_we_to_dmem = 4'h8;
					store_data_to_dmem = {rs2_data[7:0],{24{1'b0}}};
				end
			endcase
				
		end
		else begin
          illegal_insn = 1'b1;
		end
	  end
      OpBranch: begin // Branch operations
          if (insn_beq) begin
            if (rs1_data == rs2_data) begin
            branchTime = 1'b1; // Set branch condition true if registers are equal
            branchTo = pcCurrent + imm_b_sext; // Calculate branch target
            end
          end else if (insn_bne) begin
            if (rs1_data != rs2_data) begin
            branchTime = 1'b1; // Set branch condition true if registers are not equal
            branchTo = pcCurrent + imm_b_sext; // Calculate branch target
            end
          end else if (insn_blt) begin
            if ($signed(rs1_data) < $signed(rs2_data)) begin
            branchTime = 1'b1; // Set branch condition true if rs1 < rs2
            branchTo = pcCurrent + imm_b_sext; // Calculate branch target
            end
          end else if (insn_bge) begin
            if ($signed(rs1_data) >= $signed(rs2_data)) begin
            branchTime = 1'b1; // Set branch condition true if rs1 >= rs2
            branchTo = pcCurrent + imm_b_sext; // Calculate branch target
            end
          end else if (insn_bltu) begin
            if (rs1_data < rs2_data) begin
            branchTime = 1'b1; // Set branch condition true if rs1 < rs2 (unsigned)
            branchTo = pcCurrent + imm_b_sext; // Calculate branch target
            end
          end else if (insn_bgeu) begin
            if (rs1_data >= rs2_data) begin
            branchTime = 1'b1; // Set branch condition true if rs1 >= rs2 (unsigned)
            branchTo = pcCurrent + imm_b_sext; // Calculate branch target
            end
          end 
      end
	  OpJal : begin
		regwe = 1'b1;
		if(insn_jal) begin
			dataReg = pcCurrent + 4;
			pcNext = pcCurrent+ imm_j_sext;
		end
	  end
      OpEnviron: begin  // ECALL and EBREAK
          if (insn_ecall) begin
            halt = 1'b1; 
          end
      end
      default: begin
        illegal_insn = 1'b1;
      end
    endcase
    
    if (branchTime) begin
      pcNext = branchTo; // change pc to branch target
    end
  end
  

endmodule

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

  DatapathMultiCycle datapath (
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
