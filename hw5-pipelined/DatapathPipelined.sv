`timescale 1ns / 1ns
//cur version S
// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0
`define RESET 32'd0
// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`define NOP 32'h0000_0000

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
 
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  
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

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

/** state at the start of Execute stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] reg_s1_data;
  logic [`REG_SIZE] reg_s2_data;
  logic [4:0] rd;
  
} stage_execute_t;

/** state at the start of Memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] reg_s2_data;
  logic[`REG_SIZE] exe_out;
  logic reg_write_en;
  logic halt;
  logic [1:0] mem_or_alu;
  logic [4:0] rd;
  logic [4:0] mem_insn;
  
} stage_memory_t;

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic[`REG_SIZE] exe_out;
  logic[`REG_SIZE] mem_out;
  logic reg_write_en;
  logic halt;
  logic [1:0] mem_or_alu;
  logic [4:0] rd;
  
} stage_writeback_t;

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

  logic [`REG_SIZE] f_pc_current,x_pc_next;
  wire [`REG_SIZE] f_to_d_pc;
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
      f_pc_current <= ((xd_lw_dep_stall || fence_stall)? f_pc_current:x_pc_next);
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_to_d_pc = (x_branchinTime || x_jumpinTime) ? 32'b0 : f_pc_current;
  assign f_insn = (x_branchinTime || x_jumpinTime) ? `NOP: insn_from_imem;
  

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
	end else if(xd_lw_dep_stall || fence_stall) begin
      begin
        decode_state <= '{
          pc: d_pc_current,
          insn: d_insn,
          cycle_status: decode_state.cycle_status
        };
      end
    end else begin
      begin
        decode_state <= '{
          pc: f_to_d_pc,
          insn: f_insn,
          cycle_status: ((x_branchinTime || x_jumpinTime)? CYCLE_TAKEN_BRANCH : f_cycle_status)
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
 
  wire [`REG_SIZE] d_pc_current = (x_branchinTime || x_jumpinTime)? 32'b0: decode_state.pc;
  wire [`REG_SIZE] d_insn = ((x_branchinTime || x_jumpinTime) ? `NOP: decode_state.insn);
  
  wire [`OPCODE_SIZE] d_insn_opcode = decode_state.insn[6:0];
  
  wire d_reg_write1 = (d_insn_opcode == OpcodeLoad) || (d_insn_opcode == OpcodeLui) || (d_insn_opcode == OpcodeRegImm) || (d_insn_opcode == OpcodeRegReg);
  wire d_reg_write2 = d_reg_write1 || (d_insn_opcode == OpcodeAuipc) || (d_insn_opcode == OpcodeJal) || (d_insn_opcode == OpcodeJalr) ;
  wire [4:0] d_reg_rd = (d_reg_write2)?decode_state.insn[11:7]:0;
  
  wire [`REG_SIZE] d_to_x_insn ;
  
  cycle_status_e d_cycle_status = ((x_branchinTime || x_jumpinTime) ? CYCLE_TAKEN_BRANCH:decode_state.cycle_status);
  wire [4:0] d_insn_rs1 = decode_state.insn[19:15];
  wire [4:0] d_insn_rs2 = decode_state.insn[24:20];
  wire [`REG_SIZE] d_rs1_data;
  wire [`REG_SIZE] d_rs2_data;
  
  logic [`REG_SIZE] d_rs1_data_reg;
  logic [`REG_SIZE] d_rs2_data_reg;
  
  
  
    RegFile rf (
    .clk(clk),
    .rst(rst),
    .we(w_regwe),
    .rd( w_insn_rd),
    .rd_data(w_dataReg),
    .rs1(d_insn_rs1),
    .rs2(d_insn_rs2),
    .rs1_data(d_rs1_data_reg),
    .rs2_data(d_rs2_data_reg)
  );
  //fence stall 
  wire fence_stall = (d_insn_opcode == OpcodeMiscMem) && (w_insn_opcode!=OpcodeStore);
  
  //load use stall 
  wire mx_rs1_load_dep = (d_insn_opcode == OpcodeRegReg)||(d_insn_opcode == OpcodeRegImm)||(d_insn_opcode == OpcodeStore)||(d_insn_opcode == OpcodeBranch);
  wire mx_rs2_load_dep = (d_insn_opcode == OpcodeRegReg)||(d_insn_opcode == OpcodeBranch);
  wire xd_load_dep = ( ( mx_rs1_load_dep && (x_insn_rd == d_insn_rs1) ) )||( ( mx_rs2_load_dep && (x_insn_rd == d_insn_rs2) ) ); 
  wire xd_lw_dep_stall = (~x_branchinTime && ~x_jumpinTime)&&(|x_insn_rd )&&(x_insn_opcode == OpcodeLoad)&&xd_load_dep;
  
  assign d_to_x_insn = (xd_lw_dep_stall || fence_stall) ? `NOP: d_insn;
  
  wire wd_bypass_s1 = (w_insn_rd == d_insn_rs1 ) && (|w_insn_rd);
  wire wd_bypass_s2 = (w_insn_rd == d_insn_rs2 ) && (|w_insn_rd);
  
  assign d_rs1_data = (wd_bypass_s1)? w_dataReg : d_rs1_data_reg;
  assign d_rs2_data = (wd_bypass_s2)? w_dataReg : d_rs2_data_reg;
  
  
   /****************/
  /* EXECUTE STAGE */
  /****************/
  
  //first set up state at the begining of execution
  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
		reg_s1_data: 0,
		reg_s2_data: 0,
		rd: 0
		
      };
	end else if(xd_lw_dep_stall || fence_stall) begin
		begin
		execute_state <= '{
        pc:  0,
        insn: d_to_x_insn,
        cycle_status: (fence_stall)? CYCLE_FENCEI: CYCLE_LOAD2USE,
		reg_s1_data: 0 ,
		reg_s2_data: 0,
		rd: 0
      };
	  end 
    end else begin
      begin
        execute_state <= '{
          pc: d_pc_current,
          insn: d_insn ,
          cycle_status: ((x_branchinTime || x_jumpinTime)? CYCLE_TAKEN_BRANCH: decode_state.cycle_status),
		  reg_s1_data: d_rs1_data,
		  reg_s2_data: d_rs2_data,
		  rd: (x_branchinTime || x_jumpinTime)? 0 : d_reg_rd
        };
      end
    end
  end
  
  //parse instruction
  wire [`REG_SIZE] x_pc_current = execute_state.pc;
  wire [`REG_SIZE] x_insn = execute_state.insn;
  wire [6:0] x_insn_funct7 = x_insn[31:25];
  wire [2:0] x_insn_funct3 = x_insn[14:12];
  wire [4:0] x_insn_rd = x_insn[11:7];
  wire [`OPCODE_SIZE] x_insn_opcode = x_insn[6:0];
  
  // I - short immediates and loads
  wire [11:0] x_imm_i;
  assign x_imm_i = x_insn[31:20];
  wire [ 4:0] x_imm_shamt = x_insn[24:20];
  
  // B - conditionals
  wire [12:0] x_imm_b;
  assign {x_imm_b[12], x_imm_b[10:5]} = x_insn_funct7, {x_imm_b[4:1], x_imm_b[11]} = x_insn_rd, x_imm_b[0] = 1'b0;
  
  // S - stores
  wire [11:0] x_imm_s;
  assign x_imm_s[11:5] = x_insn_funct7, x_imm_s[4:0] = x_insn_rd;
  
  // J - unconditional jumps
  wire [20:0] x_imm_j;
  assign {x_imm_j[20], x_imm_j[10:1], x_imm_j[11], x_imm_j[19:12], x_imm_j[0]} = {x_insn[31:12], 1'b0};
  
  wire [`REG_SIZE] x_imm_i_sext = {{20{x_imm_i[11]}}, x_imm_i[11:0]};
  wire [`REG_SIZE] x_imm_s_sext = {{20{x_imm_s[11]}}, x_imm_s[11:0]};
  wire [`REG_SIZE] x_imm_b_sext = {{19{x_imm_b[12]}}, x_imm_b[12:0]};
  wire [`REG_SIZE] x_imm_j_sext = {{11{x_imm_j[20]}}, x_imm_j[20:0]};
  
  //identify instruction 
  wire x_insn_lui   = x_insn_opcode == OpcodeLui;
  wire x_insn_auipc = x_insn_opcode == OpcodeAuipc;
  wire x_insn_jal   = x_insn_opcode == OpcodeJal;
  wire x_insn_jalr  = x_insn_opcode == OpcodeJalr;
  
  wire x_insn_beq  = x_insn_opcode == OpcodeBranch && x_insn[14:12] == 3'b000;
  wire x_insn_bne  = x_insn_opcode == OpcodeBranch && x_insn[14:12] == 3'b001;
  wire x_insn_blt  = x_insn_opcode == OpcodeBranch && x_insn[14:12] == 3'b100;
  wire x_insn_bge  = x_insn_opcode == OpcodeBranch && x_insn[14:12] == 3'b101;
  wire x_insn_bltu = x_insn_opcode == OpcodeBranch && x_insn[14:12] == 3'b110;
  wire x_insn_bgeu = x_insn_opcode == OpcodeBranch && x_insn[14:12] == 3'b111;
  
  wire x_insn_lb  = x_insn_opcode == OpcodeLoad && x_insn[14:12] == 3'b000;
  wire x_insn_lh  = x_insn_opcode == OpcodeLoad && x_insn[14:12] == 3'b001;
  wire x_insn_lw  = x_insn_opcode == OpcodeLoad && x_insn[14:12] == 3'b010;
  wire x_insn_lbu = x_insn_opcode == OpcodeLoad && x_insn[14:12] == 3'b100;
  wire x_insn_lhu = x_insn_opcode == OpcodeLoad && x_insn[14:12] == 3'b101;
  
  wire x_insn_sb = x_insn_opcode == OpcodeStore && x_insn[14:12] == 3'b000;
  wire x_insn_sh = x_insn_opcode == OpcodeStore && x_insn[14:12] == 3'b001;
  wire x_insn_sw = x_insn_opcode == OpcodeStore && x_insn[14:12] == 3'b010;
  
  wire x_insn_addi  = x_insn_opcode == OpcodeRegImm && x_insn[14:12] == 3'b000;
  wire x_insn_slti  = x_insn_opcode == OpcodeRegImm && x_insn[14:12] == 3'b010;
  wire x_insn_sltiu = x_insn_opcode == OpcodeRegImm && x_insn[14:12] == 3'b011;
  wire x_insn_xori  = x_insn_opcode == OpcodeRegImm && x_insn[14:12] == 3'b100;
  wire x_insn_ori   = x_insn_opcode == OpcodeRegImm && x_insn[14:12] == 3'b110;
  wire x_insn_andi  = x_insn_opcode == OpcodeRegImm && x_insn[14:12] == 3'b111;
  
  wire x_insn_slli = x_insn_opcode == OpcodeRegImm && x_insn[14:12] == 3'b001 && x_insn[31:25] == 7'd0;
  wire x_insn_srli = x_insn_opcode == OpcodeRegImm && x_insn[14:12] == 3'b101 && x_insn[31:25] == 7'd0;
  wire x_insn_srai = x_insn_opcode == OpcodeRegImm && x_insn[14:12] == 3'b101 && x_insn[31:25] == 7'b0100000;
  
  wire x_insn_add  = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b000 && x_insn[31:25] == 7'd0;
  wire x_insn_sub  = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b000 && x_insn[31:25] == 7'b0100000;
  wire x_insn_sll  = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b001 && x_insn[31:25] == 7'd0;
  wire x_insn_slt  = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b010 && x_insn[31:25] == 7'd0;
  wire x_insn_sltu = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b011 && x_insn[31:25] == 7'd0;
  wire x_insn_xor  = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b100 && x_insn[31:25] == 7'd0;
  wire x_insn_srl  = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b101 && x_insn[31:25] == 7'd0;
  wire x_insn_sra  = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b101 && x_insn[31:25] == 7'b0100000;
  wire x_insn_or   = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b110 && x_insn[31:25] == 7'd0;
  wire x_insn_and  = x_insn_opcode == OpcodeRegReg && x_insn[14:12] == 3'b111 && x_insn[31:25] == 7'd0;

  wire x_insn_mul    = x_insn_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b000;
  wire x_insn_mulh   = x_insn_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b001;
  wire x_insn_mulhsu = x_insn_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b010;
  wire x_insn_mulhu  = x_insn_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b011;
  wire x_insn_div    = x_insn_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b100;
  wire x_insn_divu   = x_insn_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b101;
  wire x_insn_rem    = x_insn_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b110;
  wire x_insn_remu   = x_insn_opcode == OpcodeRegReg && x_insn[31:25] == 7'd1 && x_insn[14:12] == 3'b111;

  wire x_insn_ecall = x_insn_opcode == OpcodeEnviron && x_insn[31:7] == 25'd0;
  wire x_insn_fence = x_insn_opcode == OpcodeMiscMem;
  
  logic[`REG_SIZE] x_out;
  wire [4:0] x_insn_rs1 = x_insn[19:15];
  wire [4:0] x_insn_rs2 = x_insn[24:20];
  
  //MX bypass
  
  wire mx_bypass_s1 = (m_insn_rd == x_insn_rs1)&&(|m_insn_rd) ;
  wire mx_bypass_s2 = (m_insn_rd == x_insn_rs2)&&(|m_insn_rd) ;
  
  // WX bypass 
  wire wx_bypass_s1 = (w_insn_rd == x_insn_rs1)&&(|w_insn_rd) ;
  wire wx_bypass_s2 = (w_insn_rd == x_insn_rs2)&&(|w_insn_rd) ;
  
  wire[`REG_SIZE] x_rs1_data_wx = (wx_bypass_s1) ? w_dataReg : execute_state.reg_s1_data;
  wire[`REG_SIZE] x_rs2_data_wx = (wx_bypass_s2) ? w_dataReg : execute_state.reg_s2_data;
  
  //priority is given to mx bypass as its the most recent.
  wire[`REG_SIZE] x_rs1_data = (mx_bypass_s1) ? m_exe_out : x_rs1_data_wx;
  wire[`REG_SIZE] x_rs2_data = (mx_bypass_s2) ? m_exe_out : x_rs2_data_wx;
  
  cycle_status_e x_cycle_status = execute_state.cycle_status;
  
  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("x")
  ) disasm_2execute (
      .insn  (x_insn),
      .disasm(x_disasm)
  );
  
  logic [`REG_SIZE] x_sum;
  logic [`REG_SIZE] x_a;
  logic [`REG_SIZE] x_b;
  logic x_cin;
  cla mathematatics(
    .a(x_a),
    .b(x_b),
    .cin(x_cin),
    .sum(x_sum)
  );
  
  logic x_illegal_insn;
  logic x_branchinTime;
  logic x_jumpinTime;
  
  logic[63:0] x_mulhu_res, x_mulh_res;
  logic[63:0] x_mulhsu_res;
  
  logic[`REG_SIZE] x_branchTo ; 
  
  logic x_halt_next;
  logic [1:0] x_mem_off ;
  logic [`REG_SIZE] x_mem_addr;
  
  logic x_reg_write_en ;
  logic [1:0] x_mem_or_alu;
  logic [4:0] x_mem_insn; // used to encode memory instruction to pass it to the memory stage
  /* encoding of x_mem_insn:
		lw: 0x05
		lhu: 0x04
		lh: 0x03
		lbu: 0x02
		lb: 0x01
		
		sw: 0x30
		sh: 0x20
		sb: 0x10
		
  */
  
  always_comb begin
	x_halt_next = 0;
	x_out = 0;
	x_illegal_insn = 1'b0;
	x_reg_write_en = 1'b0;
	x_mem_or_alu = 2'b00;
	x_mem_insn = 5'b0;
	x_mem_addr = 32'h0;
	
	x_a = 0;
	x_b = 0;
    x_cin = 0;
	
	x_mulhu_res = x_rs1_data*x_rs2_data;
	x_mulh_res = $signed(x_rs1_data)*$signed(x_rs2_data);
	x_mulhsu_res = $signed(x_rs1_data)*$signed({{1'b0},x_rs2_data});
	
	x_pc_next = f_pc_current + 4;
	x_branchTo = 32'd0;
	x_branchinTime = 0;
	x_jumpinTime = 0;
	
	case(x_insn_opcode)
        OpcodeLui: begin
			x_reg_write_en = 1'b1;
			x_mem_or_alu = 2'b10;
			x_out = {x_insn[31:12], 12'b0};
		end
		OpcodeRegImm: begin
			x_reg_write_en = 1'b1;
			x_mem_or_alu = 2'b10;
			if(x_insn_addi) begin
				x_a = x_rs1_data;
				x_b = x_imm_i_sext;
				x_cin = 1'b0;
				x_out = x_sum;
			end
			else if (x_insn_slti) begin
				// logic for slti
				x_out = ($signed(x_rs1_data) < $signed(x_imm_i_sext)) ? 1:0;
			end
			else if (x_insn_sltiu) begin
				// logic for sltiu
				x_out = ((x_rs1_data) < (x_imm_i_sext)) ? 1:0;
			end
			else if (x_insn_xori) begin
				// logic for xori
				x_out = x_rs1_data ^ x_imm_i_sext;
			end
			else if (x_insn_ori) begin
				// logic for ori
				x_out = x_rs1_data | x_imm_i_sext;
			end

			else if (x_insn_andi) begin
				// logic for andi
				x_out = x_rs1_data & x_imm_i_sext;
			end

			else if (x_insn_slli) begin
				// logic for slli
				x_out = x_rs1_data << x_imm_i[4:0];
			end

			else if (x_insn_srli) begin
				x_out = x_rs1_data >> x_imm_i[4:0];
			end

			else if (x_insn_srai) begin
				// logic for srai
				x_out = $signed(x_rs1_data) >>> x_imm_i[4:0];
			end
			else //illegal case
			begin
				x_reg_write_en = 1'b0;
				x_mem_or_alu = 2'b0;
				x_illegal_insn = 1'b1;
			end		
		end
		OpcodeRegReg: begin
			x_reg_write_en = 1'b1;
			x_mem_or_alu = 2'b10;
			if (x_insn_add) begin
				x_a = x_rs1_data;
				x_b = x_rs2_data;
				x_cin = 1'b0;
				x_out = x_sum;
			end
			else if (x_insn_sub) begin
				x_a = x_rs1_data;
				x_b = ~x_rs2_data;
				x_cin = 1'b1;
				x_out = x_sum;
			end
			else if (x_insn_sll) begin
				x_out = x_rs1_data << (x_rs2_data[4:0]);
			end
			else if (x_insn_slt) begin
				x_out = $signed(x_rs1_data) < $signed(x_rs2_data) ? 32'd1:32'd0;
			end
			else if (x_insn_sltu) begin
				x_out = x_rs1_data < x_rs2_data ? 32'd1:32'd0;
			end
			else if (x_insn_xor) begin
				x_out = x_rs1_data ^ x_rs2_data;
			end
			else if (x_insn_srl) begin
				x_out = x_rs1_data >> x_rs2_data[4:0];
			end 
			else if (x_insn_sra) begin
				x_out = $signed(x_rs1_data) >>> x_rs2_data[4:0];
			end
			else if (x_insn_or) begin
			  x_out = x_rs1_data | x_rs2_data;
			end
			else if (x_insn_and) begin
			  x_out = x_rs1_data & x_rs2_data;
			end
			else if(x_insn_mul) begin
			x_out = x_rs1_data * x_rs2_data;
			end
			else if(x_insn_mulhu) begin
				x_out = x_mulhu_res[63:32];
			end
			else if(x_insn_mulh) begin
				x_out = x_mulh_res[63:32];
			end
			else if(x_insn_mulhsu) begin
				x_out = x_mulhsu_res[63:32];
			end
			else begin
				x_reg_write_en = 1'b0;
				x_mem_or_alu = 2'b0;
				x_illegal_insn = 1'b1;
			end
		end
		OpcodeBranch: begin // Branch operations
			x_reg_write_en = 1'b0;
			x_mem_or_alu = 2'b0;
			if (x_insn_beq) begin
				if (x_rs1_data == x_rs2_data) begin // Set branch condition true if rs1 = rs2
					x_branchTo = x_pc_current + x_imm_b_sext ; // Calculate branch target
					x_branchinTime = 1'b1;
				end
			end else if (x_insn_bne) begin // Set branch condition true if rs1 != rs2
				if (x_rs1_data != x_rs2_data) begin
					x_branchTo = x_pc_current + x_imm_b_sext; // Calculate branch target
					x_branchinTime = 1'b1;
				end
            end else if (x_insn_blt) begin // Set branch condition true if signed rs1 < signed rs2
				if ($signed(x_rs1_data) < $signed(x_rs2_data)) begin
					x_branchTo = x_pc_current + x_imm_b_sext; // Calculate branch target
					x_branchinTime = 1'b1;
				end
			end else if (x_insn_bge) begin // Set branch condition true if rs1 >= rs2
				if ($signed(x_rs1_data) >= $signed(x_rs2_data)) begin
					x_branchTo = x_pc_current + x_imm_b_sext; // Calculate branch target
					x_branchinTime = 1'b1;
				end
			end else if (x_insn_bltu) begin // Set branch condition true if rs1 < rs2
				if (x_rs1_data < x_rs2_data) begin
					x_branchTo = x_pc_current + x_imm_b_sext; // Calculate branch target
					x_branchinTime = 1'b1;
				end
			end else if (x_insn_bgeu) begin // Set branch condition true if rs1 >= rs2 (unsigned)
				if (x_rs1_data >= x_rs2_data) begin
					x_branchTo = x_pc_current + x_imm_b_sext; // Calculate branch target
					x_branchinTime = 1'b1;
				end
          end 
		end
		OpcodeEnviron: begin  // ECALL and EBREAK
			if(x_insn_ecall) begin
				x_halt_next = 1'b1;
				x_reg_write_en = 1'b0;
				x_mem_or_alu = 2'b0;
			end
		end
		OpcodeAuipc: begin
			if(x_insn_auipc) begin
				x_reg_write_en = 1'b1;
				x_mem_or_alu = 2'b10;
				x_out = x_pc_current + (x_insn[31:12]<<12) ;
			end
		end
		OpcodeJalr: begin
			if(x_insn_jalr) begin
				x_reg_write_en = 1'b1;
				x_mem_or_alu = 2'b10;
				x_out = x_pc_current + 4;
				x_pc_next = (x_rs1_data+ x_imm_i_sext) & ~(32'h1);
				x_jumpinTime = 1'b1;
			end
		end
		OpcodeJal : begin
			if(x_insn_jal) begin
				x_reg_write_en = 1'b1;
				x_mem_or_alu = 2'b10;
				x_out = x_pc_current + 4;
				x_pc_next = x_pc_current + x_imm_j_sext;
				x_jumpinTime = 1'b1;
			end
		end
		OpcodeLoad: begin
			x_reg_write_en = 1'b1;
			x_mem_or_alu = 2'b11;
			x_out = x_rs1_data + x_imm_i_sext;
			x_mem_addr = x_rs1_data + x_imm_i_sext;
			if(x_insn_lw) begin
				if(&(~x_mem_addr[1:0])) begin
					x_mem_insn = 5'b00_101;
				end 
				else begin
					x_reg_write_en = 1'b0;
					x_mem_or_alu = 2'b00;
					x_mem_insn = 5'b0;
					x_out = 0;
					x_illegal_insn = 1'b1;
				end
			end	
			else if(x_insn_lhu||x_insn_lh) begin
				if(&(x_mem_addr[1:0])) begin
					x_reg_write_en = 1'b0;
					x_mem_or_alu = 2'b00;
					x_out = 0;
					x_mem_insn = 5'b0;
					x_illegal_insn = 1'b1;
				end
				else begin
					if(x_insn_lhu) begin
						x_mem_insn = 5'b00_100;
					end
					else if(x_insn_lh) begin
						x_mem_insn = 5'b00_011;
					end
				end
			end
			else if(x_insn_lbu) begin
				x_mem_insn = 5'b00_010;
			end
			else if(x_insn_lb) begin
				x_mem_insn = 5'b00_001;
			end
			else begin
				x_reg_write_en = 1'b0;
				x_mem_or_alu = 2'b0;
				x_out = 0;
				x_illegal_insn = 1'b1;
				x_mem_insn = 5'b0;
			end
		end
		OpcodeStore: begin
			x_reg_write_en = 1'b0;
			x_mem_or_alu = 2'b0;
			x_out = x_rs1_data + x_imm_s_sext;
			x_mem_addr = x_rs1_data + x_imm_s_sext;
			if(x_insn_sw) begin
				if(&(~x_mem_addr[1:0])) begin
					x_mem_insn = 5'b11_000;
				end
				else begin
					x_mem_insn = 5'b00_000;
					x_illegal_insn = 1'b1;
				end
			end
			else if(x_insn_sh) begin
				x_mem_insn = 5'b10_000;
			end
			else if(x_insn_sb) begin
				x_mem_insn = 5'b01_000;
			end
			else begin
				x_mem_insn = 5'b00_000;
				x_illegal_insn = 1'b1;
			end
	  end
		default: begin
		//:)
			x_illegal_insn = 1'b1;
		end
      endcase
	  if (x_branchinTime) begin
		x_pc_next = x_branchTo; // change pc to branch target
      end
	  /*
	  if(xd_lw_dep_stall) begin
		x_pc_next = f_pc_current; 
	  end
	  */
	  
  
  end
 
  
  
  
   /****************/
  /* MEMORY STAGE */
  /****************/
  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
		pc:0,
        insn: 0,
        cycle_status: CYCLE_RESET,
		reg_s2_data: 0,
		exe_out: x_out,
		reg_write_en:0,
		halt:0,
		mem_or_alu: 0,
		rd :0,
		mem_insn: 0 
      };
    end else begin
      begin
        memory_state <= '{
		  pc: execute_state.pc,
          insn: x_insn,
		  cycle_status: execute_state.cycle_status,
		  reg_s2_data: x_rs2_data,
		  exe_out:x_out,
		  reg_write_en: x_reg_write_en,
		  halt: x_halt_next,
		  mem_or_alu: x_mem_or_alu,
		  rd: execute_state.rd,
		  mem_insn: x_mem_insn
        };
      end
    end
  end
  
  //:)
  
  wire [`INSN_SIZE] m_insn = memory_state.insn;
  wire [`REG_SIZE] m_pc = memory_state.pc;
  wire[4:0] m_insn_rs2 = m_insn[24:20];
  
  wire [4:0] m_mem_insn = memory_state.mem_insn;
  
  wire[4:0] m_insn_rd = memory_state.rd;
  
  
  
  
  cycle_status_e m_cycle_status = memory_state.cycle_status;
  wire [`REG_SIZE] m_reg_s2_data = memory_state.reg_s2_data;
  wire[`REG_SIZE] m_exe_out = memory_state.exe_out;
  
  wire m_is_load = (|m_mem_insn[2:0]);
  wire m_is_store = (|m_mem_insn[4:3]);
  
  
  
  wire m_insn_lw  = (m_is_load) && (~m_is_store) &&(m_mem_insn[2:0] == 3'b101);
  wire m_insn_lhu = (m_is_load) && (~m_is_store) &&(m_mem_insn[2:0] == 3'b100);
  wire m_insn_lh  = (m_is_load) && (~m_is_store) &&(m_mem_insn[2:0] == 3'b011);
  wire m_insn_lbu = (m_is_load) && (~m_is_store) &&(m_mem_insn[2:0] == 3'b010);
  wire m_insn_lb  = (m_is_load) && (~m_is_store) &&(m_mem_insn[2:0] == 3'b001);
  
  wire m_insn_sw = (~m_is_load) && (m_is_store) &&(m_mem_insn[4:3] == 2'b11);
  wire m_insn_sh = (~m_is_load) && (m_is_store) &&(m_mem_insn[4:3] == 2'b10);
  wire m_insn_sb = (~m_is_load) && (m_is_store) &&(m_mem_insn[4:3] == 2'b01);
  
  //WM bypass:
  
  wire wm_bypass = (m_is_store) && (m_insn_rs2 == w_insn_rd) && (|w_insn_rd) ;  
  
  wire[`REG_SIZE] m_rs2_data = (wm_bypass)? w_dataReg: memory_state.reg_s2_data;
  
	
	logic m_illegal_insn;
	logic [`REG_SIZE] m_mem_data ;
	always_comb begin
		m_illegal_insn = 1'b0;
		addr_to_dmem = 4;
		store_we_to_dmem = 0;
		store_data_to_dmem = 0;
		m_mem_data = 0;
		if (m_is_load) begin
			if(m_insn_lw) begin
				addr_to_dmem = m_exe_out;
				m_mem_data = load_data_from_dmem ; 
			end
			else if(m_insn_lb || m_insn_lbu) begin
				addr_to_dmem = (m_exe_out)&(32'hffff_fffc);
				case (m_exe_out[1:0])
					2'b00: m_mem_data = (m_insn_lb) ? {{24{load_data_from_dmem[7]}},load_data_from_dmem[7:0]} : {{24{1'b0}},load_data_from_dmem[7:0]};
					2'b01: m_mem_data = (m_insn_lb) ?{{24{load_data_from_dmem[15]}},load_data_from_dmem[15:8]}: {{24{1'b0}},load_data_from_dmem[15:8]};
					2'b10: m_mem_data = (m_insn_lb) ?{{24{load_data_from_dmem[23]}},load_data_from_dmem[23:16]}: {{24{1'b0}},load_data_from_dmem[23:16]};
					2'b11: m_mem_data = (m_insn_lb) ?{{24{load_data_from_dmem[31]}},load_data_from_dmem[31:24]}: {{24{1'b0}},load_data_from_dmem[31:24]};
				endcase 
			end
			else if(m_insn_lh || m_insn_lhu) begin
				addr_to_dmem = (m_exe_out)&(32'hffff_fffc);
				case (m_exe_out[1:0])
					2'b00: m_mem_data = (m_insn_lh) ? {{16{load_data_from_dmem[15]}},load_data_from_dmem[15:0]} : {{16{1'b0}},load_data_from_dmem[15:0]};
					2'b01: m_mem_data = (m_insn_lh) ? {{16{load_data_from_dmem[23]}},load_data_from_dmem[23:8]} : {{16{1'b0}},load_data_from_dmem[23:8]};
					2'b10: m_mem_data = (m_insn_lh) ?{{16{load_data_from_dmem[31]}},load_data_from_dmem[31:16]}: {{16{1'b0}},load_data_from_dmem[31:16]};
					2'b11: begin
						m_illegal_insn = 1'b1;
					end
				endcase 
	        end
			else begin
				m_illegal_insn = 1'b1;
			end
		end
		else if(m_is_store) begin
			if(m_insn_sw) begin
				addr_to_dmem = m_exe_out;
				store_we_to_dmem = 4'hf;
				store_data_to_dmem = m_rs2_data;
			end
			else if(m_insn_sh) begin
				addr_to_dmem = (m_exe_out)&(32'hffff_fffc);
				case (m_exe_out[1:0])
					2'b00: begin
						store_we_to_dmem = 4'h3;
						store_data_to_dmem =m_rs2_data;
					end
					2'b01: begin 
						store_we_to_dmem = 4'h6;
						store_data_to_dmem = {m_rs2_data[23:0],{8{1'b0}}};
					end
					2'b10: begin 
						store_we_to_dmem = 4'hc;
						store_data_to_dmem = {m_rs2_data[15:0],{16{1'b0}}};
					end
					2'b11: begin 
						store_we_to_dmem = 4'h0;
						store_data_to_dmem = 0;
					end
				endcase
			end
			else if(m_insn_sb) begin
				addr_to_dmem = (m_exe_out)&(32'hffff_fffc);
				case (m_exe_out[1:0])
					2'b00: begin
						store_we_to_dmem = 4'h1;
						store_data_to_dmem = m_rs2_data;
					end
					2'b01: begin 
						store_we_to_dmem = 4'h2;
						store_data_to_dmem = {m_rs2_data[23:0],{8{1'b0}}};
					end
					2'b10: begin 
						store_we_to_dmem = 4'h4;
						store_data_to_dmem = {m_rs2_data[15:0],{16{1'b0}}};
					end
					2'b11: begin 
						store_we_to_dmem = 4'h8;
						store_data_to_dmem = {m_rs2_data[7:0],{24{1'b0}}};
					end
				endcase	
			end
			else begin
				m_illegal_insn = 1'b1;
			end
		end
		else begin
			m_illegal_insn = 1'b1;
		end
	end
  
  
   /****************/
  /* WRITEBACK STAGE */
  /****************/
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
  
      writeback_state <= '{
		pc:0,
        insn: 0,
        cycle_status: CYCLE_RESET,
		exe_out:0,
		mem_out:0,
		reg_write_en:0,
		halt:0,
		mem_or_alu:0,
		rd: 0
		
      };
    end else begin
      begin
        writeback_state <= '{
		  pc: m_pc,
          insn: m_insn,
		  cycle_status: memory_state.cycle_status,
		  exe_out:m_exe_out,
		  mem_out: m_mem_data,
		  reg_write_en: memory_state.reg_write_en,
		  halt: memory_state.halt,
		  mem_or_alu: memory_state.mem_or_alu,
		  rd: memory_state.rd
        };
      end
    end
  end
  
  //register write stuffs to be modified in writeback stage
  wire [`INSN_SIZE] w_insn = writeback_state.insn;
  wire [`OPCODE_SIZE] w_insn_opcode = w_insn[6:0];
  wire[4:0] w_insn_rd = writeback_state.rd;
  
  wire[1:0] w_mem_or_alu = writeback_state.mem_or_alu;
  
  
  wire [`REG_SIZE] w_alu_out = writeback_state.exe_out;
  wire[`REG_SIZE] w_mem_out = writeback_state.mem_out;
  
  wire[`REG_SIZE] w_datareg_mem_or_alu = (w_mem_or_alu[0])? w_mem_out : w_alu_out;
  wire w_regwe = writeback_state.reg_write_en;
  wire[`REG_SIZE] w_dataReg = (w_mem_or_alu[1])? w_datareg_mem_or_alu :0;
  assign halt = writeback_state.halt;
  
  
  assign trace_writeback_pc = writeback_state.pc;
  assign trace_writeback_insn = w_insn;
  assign trace_writeback_cycle_status = writeback_state.cycle_status;

  

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
