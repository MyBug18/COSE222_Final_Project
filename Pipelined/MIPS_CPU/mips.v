`timescale 1ns/1ps
`define mydelay 1

//--------------------------------------------------------------
// mips.v
// David_Harris@hmc.edu and Sarah_Harris@hmc.edu 23 October 2005
// Single-cycle MIPS processor
//--------------------------------------------------------------

// single-cycle MIPS processor
module mips(input         clk, reset,
            output [31:0] pc,
            input  [31:0] instr,
            output        memwrite,
            output [31:0] memaddr,
            output [31:0] memwritedata,
            input  [31:0] memreaddata);

  wire        pcsrc, zero;

  // Instantiate Datapath
  datapath dp(
    .clk        (clk),
    .reset      (reset),
    .final_zero       (zero),
    .final_pc         (pc),
    .instr      (instr),
	 .final_memwrite   (memwrite),
    .final_aluout     (memaddr), 
    .final_writedata  (memwritedata),
    .readdata   (memreaddata));

endmodule

module controller(input  [5:0] op, funct,
						input        keep_write,
                  output       signext,
                  output       shiftl16,
                  output       memtoreg, memwrite,
                  output       branch, alusrc,
                  output       regdst, regwrite,
                  output       jump,
                  output [2:0] alucontrol);

  wire [1:0] aluop;

  maindec md(
    .op       (op),
	 .keep_write (keep_write),
    .signext  (signext),
    .shiftl16 (shiftl16),
    .memtoreg (memtoreg),
    .memwrite (memwrite),
    .branch   (branch),
    .alusrc   (alusrc),
    .regdst   (regdst),
    .regwrite (regwrite),
    .jump     (jump),
    .aluop    (aluop));

  aludec ad( 
    .funct      (funct),
    .aluop      (aluop), 
	 .keep_write (keep_write),
    .alucontrol (alucontrol));

endmodule


module maindec(input  [5:0] op,
					input        keep_write,
               output       signext,
               output       shiftl16,
               output       memtoreg, memwrite,
               output       branch, alusrc,
               output       regdst, regwrite,
               output       jump,
               output [1:0] aluop);

  reg [10:0] controls;

  assign {signext, shiftl16, regwrite, regdst, alusrc, branch, memwrite,
          memtoreg, jump, aluop} = controls;

  always @(*)
    if (keep_write == 1'b0) controls <= #`mydelay 11'b00000000000;
    else case(op)
      6'b000000: controls <= #`mydelay 11'b00110000011; // Rtype
      6'b100011: controls <= #`mydelay 11'b10101001000; // LW
      6'b101011: controls <= #`mydelay 11'b10001010000; // SW
      6'b000100: controls <= #`mydelay 11'b10000100001; // BEQ
      6'b001000, 
      6'b001001: controls <= #`mydelay 11'b10101000000; // ADDI, ADDIU: only difference is exception
      6'b001101: controls <= #`mydelay 11'b00101000010; // ORI
      6'b001111: controls <= #`mydelay 11'b01101000000; // LUI
      6'b000010: controls <= #`mydelay 11'b00000000100; // J
      default:   controls <= #`mydelay 11'bxxxxxxxxxxx; // ???
    endcase

endmodule

module aludec(input      [5:0] funct,
              input      [1:0] aluop,
				  input            keep_write,
              output reg [2:0] alucontrol);

  always @(*)
    if (keep_write == 1'b0) alucontrol <= 3'b000;
    else case(aluop)
      2'b00: alucontrol <= #`mydelay 3'b010;  // add
      2'b01: alucontrol <= #`mydelay 3'b110;  // sub
      2'b10: alucontrol <= #`mydelay 3'b001;  // or
      default: case(funct)          // RTYPE
          6'b100000,
          6'b100001: alucontrol <= #`mydelay 3'b010; // ADD, ADDU: only difference is exception
          6'b100010,
          6'b100011: alucontrol <= #`mydelay 3'b110; // SUB, SUBU: only difference is exception
          6'b100100: alucontrol <= #`mydelay 3'b000; // AND
          6'b100101: alucontrol <= #`mydelay 3'b001; // OR
          6'b101010: alucontrol <= #`mydelay 3'b111; // SLT
          default:   alucontrol <= #`mydelay 3'bxxx; // ???
        endcase
    endcase
    
endmodule

module forward_mux(input [31:0] val_from_ID_EX,
						input [31:0] val_from_EX_MEM,
						input [31:0] val_from_MEM_WB,
						input [1:0] control,
						output reg [31:0] val);
						
  always @(*)
    case(control)
	 2'b00: val <= #`mydelay val_from_ID_EX;
	 2'b01: val <= #`mydelay val_from_EX_MEM;
	 2'b10: val <= #`mydelay val_from_MEM_WB;
	 endcase
endmodule

module forwarding_unit(input [4:0] rs, rt, rd_EX_MEM, rd_MEM_WB, 
							  input regwrite_EX_MEM, regwrite_MEM_WB,
							 output reg [1:0] control_rs, control_rt);
  always @(*)
    begin
	   if ((rt == rd_MEM_WB) && regwrite_MEM_WB == 1'b1)
			control_rt <= 2'b10;
		else if (rt == rd_EX_MEM)
			control_rt <= 2'b01;
		else control_rt <= 2'b00;
		
		if ((rs == rd_MEM_WB) && regwrite_EX_MEM == 1'b1)
			control_rs <= 2'b10;
		else if (rs == rd_EX_MEM)
			control_rs <= 2'b01;
		else control_rs <= 2'b00;
	  end
endmodule

module IF_ID(input clk,
				 input [31:0] instr,
				 input [31:0] pc_added_four,
				 output reg [31:0] instr_out,
				 output reg [31:0] pc_out);

  always @(posedge clk)
    begin
	   instr_out <= #`mydelay instr;
	   pc_out <= pc_added_four;
	 end
endmodule

module hazard_detection_unit (input [4:0] rs_IF_ID, rt_IF_ID, rt,
										input memtoreg,
										output reg keep_write);

  always @(*)
    if ((memtoreg == 1'b1 && ((rt == rt_IF_ID) || (rt == rs_IF_ID))))
		keep_write <= #`mydelay 1'b0;
	 else keep_write <= #`mydelay 1'b1;
	 
endmodule

module ID_EX(input clk, 
				 input memtoreg, memwrite, branch, alusrc, regdst, regwrite, jump,
				 input [2:0] alucontrol,
				 input [31:0] pc, 
				 input [31:0] rd1, rd2,
				 input [31:0] imm_val,
				 input [4:0] inst25_21, inst20_16, inst15_11,
				 output reg memtoreg_out, memwrite_out, branch_out, alusrc_out, regdst_out, regwrite_out, jump_out, 
				 output reg [2:0] alucontrol_out, 
				 output reg [31:0] pc_out, 
				 output reg [31:0] rd1_out, rd2_out, 
				 output reg [31:0] imm_val_out,
				 output reg [4:0] inst25_21_out, inst20_16_out, inst15_11_out);
				 
  always @(posedge clk)
    begin
		memtoreg_out <= #`mydelay memtoreg;
		memwrite_out <= #`mydelay memwrite;
		branch_out <= #`mydelay branch;
		alusrc_out <= #`mydelay alusrc;
		regdst_out <= #`mydelay regdst;
		regwrite_out <= #`mydelay regwrite;
		jump_out <= #`mydelay jump;
		alucontrol_out <= #`mydelay alucontrol;
		pc_out <= #`mydelay pc;
		rd1_out <= #`mydelay rd1;
		rd2_out <= #`mydelay rd2;
		imm_val_out <= #`mydelay imm_val;
		inst25_21_out <= #`mydelay inst25_21;
		inst20_16_out <= #`mydelay inst20_16;
		inst15_11_out <= #`mydelay inst15_11;
	 end
endmodule
			
module EX_MEM(input clk, 
				  input memtoreg, memwrite, branch, regwrite, jump,
				  input [31:0] pc_for_j, pc_for_beq, alu_result,
				  input is_zero,
				  input [31:0] writedata,
				  input [4:0] regdst_addr,
				  output reg memtoreg_out, memwrite_out, branch_out, regwrite_out, jump_out,
				  output reg [31:0] pc_for_j_out, pc_for_beq_out, alu_result_out,
				  output reg is_zero_out, 
				  output reg [31:0] writedata_out, 
				  output reg [4:0] regdst_addr_out);
				  
  always @(posedge clk)
    begin
		memtoreg_out <= #`mydelay memtoreg;
		memwrite_out <= #`mydelay memwrite;
		branch_out <= #`mydelay branch;
		regwrite_out <= #`mydelay regwrite;
		jump_out <= #`mydelay jump;
		is_zero_out <= #`mydelay is_zero;
		alu_result_out <= #`mydelay alu_result;
		writedata_out <= #`mydelay writedata;
		regdst_addr_out <= #`mydelay regdst_addr;
	 end
endmodule
		
module MEM_WB (input clk, 
					input regwrite, memtoreg, 
					input [31:0] readdata, aluresult, 
					input [4:0] regdst_addr,
					output reg regwrite_out, memtoreg_out, 
					output reg [31:0] readdata_out, aluresult_out,
					output reg [4:0] regdst_addr_out);
  always @(posedge clk)			
	 begin
	   regwrite_out <= #`mydelay regwrite;
		memtoreg_out <= #`mydelay memtoreg;
		regdst_addr_out <= #`mydelay regdst_addr;
		readdata_out <= #`mydelay readdata;
		memtoreg_out <= #`mydelay memtoreg;
	 end
endmodule
		
module datapath(input         clk, reset,
                output        final_zero,
					 output        final_memwrite,
                output [31:0] final_pc,
                input  [31:0] instr,
                output [31:0] final_aluout, final_writedata,
                input  [31:0] readdata);

  wire [4:0]  writereg;
  wire [31:0] pcnext, pcnextbr, pcplus4, pcbranch;
  wire [31:0] signimm, signimmsh, shiftedimm;
  wire [31:0] rd1, srcb;
  wire [31:0] result;
  wire [31:0] rd2;
  wire        shift;
  
  wire [31:0] instr_after_IF_ID, pc_after_IF_ID, pc_after_ID_EX;
  wire [31:0] rd1_after_ID_EX, rd2_after_ID_EX;
  
  wire signext, shiftl16, memtoreg, memwrite, branch, alusrc, regdst, regwrite,jump;
  wire memtoreg_after_ID_EX, memwrite_after_ID_EX, branch_after_ID_EX, alusrc_after_ID_EX, regdst_after_ID_EX, regwrite_after_ID_EX,jump_after_ID_EX;
  wire [2:0] alucontrol, alucontrol_after_ID_EX;
  
  wire [31:0] imm_val_after_ID_EX, shifted16_val_after_ID_EX;
  wire [4:0] inst25_21_after_ID_EX, inst20_16_after_ID_EX, inst15_11_after_ID_EX;
  
  wire memtoreg_after_EX_MEM, memwrite_after_EX_MEM, branch_after_EX_MEM, regwrite_after_EX_MEM,jump_after_EX_MEM;
  
  wire [31:0] pc_for_j, pc_for_branch, writedata_after_ID_EX;
  
  wire is_zero;
  
  wire [4:0] regdst_addr, regdst_addr_after_MEM_WB;
  
  wire memtoreg_after_MEM_WB, regwrite_after_MEM_WB, aluresult_after_MEM_WB, readdata_after_MEM_WB;
  
  wire [1:0] control_rs, control_rt;
  
  wire [31:0] forwarded_rs_data, forwarded_rt_data;
  
  wire keep_write;

  adder pcadd1(
    .a (final_pc),
    .b (32'b100),
    .y (pcplus4));
  
  IF_ID if_id( 
  .clk (clk & keep_write), 
  .instr (instr), 
  .pc_added_four (pcplus4), 
  .instr_out (instr_after_IF_ID), 
  .pc_out (pc_after_IF_ID));
  
  controller c( 
  .op (instr_after_IF_ID[31:26]), 
  .funct (instr_after_IF_ID[5:0]), 
  .keep_write (keep_write),
  .signext (signext), 
  .shiftl16 (shiftl16), 
  .memtoreg (memtoreg), 
  .memwrite (memwrite), 
  .branch (branch), 
  .alusrc (alusrc), 
  .regdst (regdst), 
  .regwrite (regwrite), 
  .jump (jump), 
  .alucontrol (alucontrol));
 
  // register file logic
  regfile rf(
    .clk     (clk),
    .we      (regwrite_after_MEM_WB),
    .ra1     (instr_after_IF_ID[25:21]),
    .ra2     (instr_after_IF_ID[20:16]),
    .wa      (regdst_addr_after_MEM_WB),
    .wd      (result),
    .rd1     (rd1),
    .rd2     (rd2));
 
  sign_zero_ext sze(
    .a       (instr_after_IF_ID[15:0]),
    .signext (signext),
    .y       (signimm[31:0]));

  shift_left_16 sl16(
    .a         (signimm[31:0]),
    .shiftl16  (shiftl16),
    .y         (shiftedimm[31:0]));
	 
  ID_EX id_ex( 
  .clk (clk), 
  .memtoreg (memtoreg), 
  .memwrite (memwrite), 
  .branch (branch), 
  .alusrc (alusrc), 
  .regdst (regdst), 
  .regwrite (regwrite), 
  .jump (jump),
  .alucontrol (alucontrol),
  .pc (pc_after_IF_ID), 
  .rd1 (rd1),
  .rd2 (rd2),
  .imm_val (shiftedimm),
  .inst25_21 (instr_after_IF_ID[25:21]),
  .inst20_16 (instr_after_IF_ID[20:16]),
  .inst15_11 (instr_after_IF_ID[15:11]),
  .memtoreg_out (memtoreg_after_ID_EX),
  .memwrite_out (memwrite_after_ID_EX),
  .branch_out (branch_after_ID_EX),
  .alusrc_out (alusrc_after_ID_EX),
  .regdst_out (regdst_after_ID_EX),
  .regwrite_out (regwrite_after_ID_EX),
  .jump_out (jump_after_ID_EX),
  .alucontrol_out (alucontrol_after_ID_EX),
  .pc_out (pc_after_ID_EX),
  .rd1_out (rd1_after_ID_EX),
  .rd2_out (rd2_after_ID_EX),
  .imm_val_out (imm_val_after_ID_EX),
  .inst25_21_out (inst25_21_after_ID_EX),
  .inst20_16_out (inst20_16_after_ID_EX),
  .inst15_11_out (inst15_11_after_ID_EX));
  
  mux2 #(5) wrmux(
    .d0  (inst20_16_after_ID_EX),
    .d1  (inst15_11_after_ID_EX),
    .s   (regdst_after_ID_EX),
    .y   (writereg));

  alu alu(
    .a       (forwarded_rs_data),
    .b       (srcb),
    .alucont (alucontrol_after_ID_EX),
    .result  (aluout),
    .zero    (zero));	 

  sl2 immsh(
    .a (imm_val_after_ID_EX),
    .y (signimmsh));
	 
  adder pcadd2(
    .a (pc_after_ID_EX),
    .b (signimmsh),
    .y (pcbranch));

  EX_MEM ex_mem (
    .clk (clk), 
	 .memtoreg (memtoreg_after_ID_EX), 
	 .memwrite (memwrite_after_ID_EX), 
	 .branch (branch_after_ID_EX), 
	 .regwrite (regwrite_after_ID_EX), 
	 .jump (jump_after_ID_EX), 
	 .pc_for_j ({pc_after_ID_EX[31:28], instr[25:0], 2'b00}), 
	 .pc_for_beq (pcbranch), 
	 .alu_result (aluout),
	 .is_zero (zero), 
	 .writedata (rd2_after_ID_EX), 
	 .regdst_addr (writereg),
	 .memtoreg_out (memtoreg_after_EX_MEM), 
	 .memwrite_out (final_memwrite), 
	 .branch_out (branch_after_EX_MEM), 
	 .regwrite_out (regwrite_after_EX_MEM), 
	 .jump_out (jump_after_EX_MEM), 
	 .pc_for_j_out (pc_for_j), 
	 .pc_for_beq_out (pc_for_branch), 
	 .alu_result_out (final_aluout),
	 .is_zero_out (is_zero), 
	 .writedata_out (final_writedata), 
	 .regdst_addr_out (regdst_addr)
	 );
  flopr #(32) pcreg(
    .clk   (clk & keep_write),
    .reset (reset),
    .d     (pcnext),
    .q     (final_pc));

  mux2 #(32) pcbrmux(
    .d0  (pcplus4),
    .d1  (pc_for_branch),
    .s   (branch_after_EX_MEM & is_zero),
    .y   (pcnextbr));

  mux2 #(32) pcmux(
    .d0   (pcnextbr),
    .d1   (pc_for_j),
    .s    (jump_after_EX_MEM),
    .y    (pcnext));



  mux2 #(32) resmux(
    .d0 (aluresult_after_MEM_WB),
    .d1 (readdata_after_MEM_WB),
    .s  (memtoreg_after_MEM_WB),
    .y  (result));

  // ALU logic
  mux2 #(32) srcbmux(
    .d0 (forwarded_rt_data),
    .d1 (imm_val_after_ID_EX),
    .s  (alusrc_after_ID_EX),
    .y  (srcb));
	 
  MEM_WB mem_wb(
  .clk (clk), 
  .regwrite (regwrite_after_EX_MEM),
  .memtoreg (memtoreg_after_EX_MEM),
  .regdst_addr (regdst_addr),
  .readdata (readdata),
  .aluresult(final_aluout),
  .regwrite_out (regwrite_after_MEM_WB),
  .memtoreg_out (memtoreg_after_MEM_WB),
  .regdst_addr_out (regdst_addr_after_MEM_WB),
  .readdata_out (readdata_after_MEM_WB),
  .aluresult_out(aluresult_after_MEM_WB));
  
  forwarding_unit fu(
  .rs (inst25_21_after_ID_EX),
  .rt (inst20_16_after_ID_EX),
  .rd_EX_MEM (regdst_addr), 
  .rd_MEM_WB (regdst_addr_after_MEM_WB), 
  .regwrite_EX_MEM (regwrite_after_EX_MEM),
  .regwrite_MEM_WB (regwrite_after_MEM_WB),
  .control_rs (control_rs),
  .control_rt (control_rt));
  
  forward_mux forward_rs_mux( 
  .val_from_ID_EX (rd1_after_ID_EX),
  .val_from_EX_MEM (final_aluout), 
  .val_from_MEM_WB (result),
  .control (control_rs),
  .val (forwarded_rs_data));
  
  forward_mux forward_rt_mux( 
  .val_from_ID_EX (rd2_after_ID_EX),
  .val_from_EX_MEM (final_aluout), 
  .val_from_MEM_WB (result),
  .control (control_rt),
  .val (forwarded_rt_data));
  
  hazard_detection_unit hzu(
  .rs_IF_ID (instr_after_IF_ID[25:21]), 
  .rt_IF_ID (instr_after_IF_ID[20:16]),
  .rt (inst20_16_after_ID_EX), 
  .memtoreg (memtoreg_after_ID_EX),
  .keep_write (keep_write));
endmodule
