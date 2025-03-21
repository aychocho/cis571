`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef DIVIDER_STAGES
`define DIVIDER_STAGES 8
`endif

`ifndef SYNTHESIS
`include "../hw3-singlecycle/RvDisassembler.sv"
`endif
`include "../hw2b-cla/cla.sv"
`include "../hw4-multicycle/DividerUnsignedPipelined.sv"
`include "cycle_status.sv"

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
`ifndef SYNTHESIS
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
`endif
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
  localparam int NumRegs = 32;
  genvar i;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here

  //write to rd on clk up
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < NumRegs; i++) begin
        regs[i] <= '0;
      end
    end else begin
      if (we && (rd != 0)) begin
        regs[rd] <= rd_data;
      end
    end
  end
endmodule

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See the cycle_status.sv file for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  //SETUP
  
  //instantiate regfile

  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;
  logic[`REG_SIZE] dataReg;
  logic[4:0] rd;
  logic[4:0] rs1;
  logic[4:0] rs2;
  //write enable
  logic regwe;

  assign rs1= decode_state.insn[19:15];
  assign rs2= decode_state.insn[24:20];

  RegFile rf(
    .rd(rd),
    .rd_data(dataReg),
    .rs1(rs1),
    .rs1_data(rs1_data),
    .rs2(rs2),
    .rs2_data(rs2_data),
    .clk(clk),
    .we(regwe),
    .rst(rst)
  );

  //cla

  logic[`REG_SIZE] a;
  logic[`REG_SIZE] b;
  logic[`REG_SIZE] sum;
  logic[`REG_SIZE] cin;

  cla mathematatics(
    .a(a),
    .b(b),
    .cin(cin),
    .sum(sum)
  );

  //divider

  logic [`REG_SIZE] remu_res;
	logic [`REG_SIZE] quotient_res;
	logic [`REG_SIZE] dividend, divisor;
	logic [`REG_SIZE] dividend_s, divisor_s;
	logic [`REG_SIZE] rem_res,div_res;
	
	wire stall = 1'b0;
	DividerUnsignedPipelined div_inst(
    .i_dividend(dividend),
    .i_divisor(divisor),
    .o_remainder(remu_res),
    .o_quotient(quotient_res),
    .clk(clk),
    .rst(rst),
    .stall(stall)
  );
  
  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  logic [`REG_SIZE] thisFetchInstruction;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  //TODO: BRANCHING LOGIC

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

  //wd bypass

  logic[`REG_SIZE] thisRs1Data;
  logic[`REG_SIZE] thisRs2Data;
  logic[`REG_SIZE] thisDecodeInstruction;
  logic[`REG_SIZE] nextDecodePc;
  cycle_status_e thisDecodeCycleStatus;

  always_comb begin
    thisRs1Data = rs1_data;
    //forwarding
    if (regwe == 1'b1 && rd == rs1 && rs1 != 5'd0) begin
      thisRs1Data = writebackData.result;
    end
    thisRs2Data = rs2_data;
    if (regwe == 1'b1 && rd == rs2 && rs2 != 5'd0) begin
      thisRs2Data = writebackData.result;
    end
    //TODO: IF BRANCH
    
    //TODO: Essentially handle branches, and otherwise package up state in a packed struct

  // EXECUTE

  //TODO: SET STAGE STATE PACKED
  /*
  always_ff @(posedge clk) begin
    if (rst) begin
      set pc to 0
      set instruction to 0
      cycle status is reset
    end else begin
      pc is next
      insn is current
      cycle status is current
      load rs1 and rs2
    end
  end  
  */


  //TODO: COPY PASTED FROM HW4, DEBUG LATER

  //TODO: SET STATE

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

  // MEMORY

  

  // WRITEBACK

  stage_writeback_t writebackState;
  data writebackData;

  //update registers
  always_ff @(posedge clk) begin
    if (rst) begin
      writebackState.pc <= 0;
      writebackState.insn <= 0;
      writebackState.cycle_status <= CYCLE_RESET;
      writebackData.we <= 0;
      writebackData.result <= 0;
      writebackData.rs1_data <= 0;
      writebackData.rs2_data <= 0;
    end else begin
      begin
          writebackState <= memory_state;
          writebackData <= memory_data;
      end
    end
  end

  //writeback logic + halting
  always_comb begin
    regwe = writebackData.we;
    dataReg = writebackData.result;
    rd = writebackState.insn[11:7];
    trace_writeback_cycle_status = writebackState.cycle_status;
    trace_writeback_insn = writebackState.insn;
    trace_writeback_pc = writeback_state.pc;

    halt = 1'b0;
    if(writebackState.insn == opcodeEnviron) begin
      halt = 1'b1;
    end
  end


  //TODO:disasm step

endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

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

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
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

/* This design has just one clock for both processor and memory. */
module Processor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
