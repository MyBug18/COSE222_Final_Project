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
  
  wire [3:0]  alucontrol_id, alucontrol_ex;
  

   wire [31:0] pc_plus4_if, pc_plus4_id, pc_plus4_ex, pc_plus4_mem, pc_plus4_wb;
   wire [31:0] instr_if, instr_id, instr_ex;
   wire [4:0] rt_id, rt_ex;
   wire [4:0] rd_id, rd_ex;
   wire [4:0] rs_id, rs_ex;
   wire [4:0] writereg_ex, writereg_mem, writereg_wb;
   wire [31:0] write_data_ex, write_data_mem;
   wire [31:0] pc_next;
   wire [31:0] readreg_1_id, readreg_1_ex;
   wire [31:0] readreg_2_id, readreg_2_ex;
   wire [31:0] signimm_id, signimm_ex;
   wire [31:0] aluout_ex, aluout_mem, aluout_wb;
   wire [31:0] memread_mem, memread_wb;
   wire [31:0] result_wb;
   wire aluzero_ex, aluzero_mem;
   wire flush_pc_move, flush_ifid;
	
   wire [1:0] foward_rs, foward_rt;
  
   wire shiftl16_id, shiftl16_ex;
   wire regdst_id,regdst_ex;     
   wire [1:0] aluop_id, aluop_ex;
   wire alusrc_id, alusrc_ex;    
   wire branch_id, branch_ex;   
   wire branchN_id, branchN_ex;  
   wire jump_id, jump_ex;     
   wire memwrite_id, memwrite_ex, memwrite_mem;
   wire isjal_id, isjal_ex, isjal_mem, isjal_wb;  
   wire regwrite_id, regwrite_ex, regwrite_mem, regwrite_wb;
   wire memtoreg_id, memtoreg_ex, memtoreg_mem, memtoreg_wb;              
  
   assign instr_if = instr;
   assign memread_mem = memreaddata;
   assign memwrite = memwrite_mem;
   assign memaddr = aluout_mem;
   assign memwritedata = write_data_mem;
	
	wire flush_idex_or_reset;
	wire flush_idex;
	wire keep_write_pc, keep_write_ifid;
	assign flush_idex_or_reset = flush_pc_move | flush_idex | reset;
	
	assign flush_ifid = flush_pc_move | reset;
  
	if_part if_part(
		.clk        (clk),
		.reset      (reset),
		.keep_write     (keep_write_pc),
		.pc_next     (pc_next),
		.pc         (pc),
		.pc_plus4    (pc_plus4_if));
		
	ppline_ifid ff_ifid(
		.clk       (clk),
		.reset     (flush_ifid),
		.keep_write    (keep_write_ifid),
		.pc_plus4_d (pc_plus4_if),
		.instr_d   (instr_if),
		.pc_plus4   (pc_plus4_id),
		.instr     (instr_id));
		
	id_part id_part(
		.clk          (clk),
		.instr        (instr_id),
		.writereg     (writereg_wb),
		.result       (result_wb),
		.pc_plus4     (pc_plus4_id),
		.readreg_1    (readreg_1_id),
		.readreg_2    (readreg_2_id),
		.signimm      (signimm_id),
		.rs			  (rs_id),
		.rt			  (rt_id),
		.rd			  (rd_id),
		.shiftl16     (shiftl16_id),
		.regdst       (regdst_id),  
		.alusrc       (alusrc_id),  
		.branch       (branch_id),
		.branchN     (branchN_id),
		.jump         (jump_id),
		.memwrite     (memwrite_id),
		.isjal     (isjal_id), 
		.memtoreg     (memtoreg_id), 
		.regwrite (regwrite_id), 
		.alucontrol   (alucontrol_id),
		.regwrite_wb  (regwrite_wb)
		);
		
	flowcheck flowcheck(
		.alucontrol	  (alucontrol_ex),
		.branch		  (branch_ex),
		.branchN      (branchN_ex),
		.jump         (jump_ex),
		.aluzero			  (aluzero_ex),
		.flush		  (flush_pc_move)
		);
		
   ppline_idex ff_idex(
		.clk          (clk),
		.reset        (flush_idex_or_reset),
		.pc_plus4_d    (pc_plus4_id),
		.rd1_d        (readreg_1_id),
		.rd2_d        (readreg_2_id),
		.immex_d      (signimm_id),
		.instr_d      (instr_id),
		.rs_d			  (rs_id),
		.rt_d			  (rt_id),
		.rd_d			  (rd_id),
		.shiftl16_d   (shiftl16_id),
		.regdst_d     (regdst_id),  
		.alucontrol_d      (alucontrol_id),   
		.alusrc_d     (alusrc_id),  
		.branch_d		  (branch_id),
		.branchN_d		  (branchN_id),
		.jump_d			  (jump_id),
		.memwrite_d   (memwrite_id),
		.isjal_d   (isjal_id), 
		.memtoreg_d   (memtoreg_id), 
		.regwrite_d   (regwrite_id), 
		.pc_plus4      (pc_plus4_ex),
		.rd1          (readreg_1_ex),
		.rd2          (readreg_2_ex),
		.immex        (signimm_ex),
		.instr        (instr_ex),
		.rs			  (rs_ex),
		.rt			  (rt_ex),
		.rd			  (rd_ex),
		.shiftl16     (shiftl16_ex),
		.regdst       (regdst_ex),  
		.alucontrol   (alucontrol_ex),   
		.alusrc       (alusrc_ex),  
		.branch		  (branch_ex),
		.branchN		  (branchN_ex),
		.jump			  (jump_ex),
		.memwrite     (memwrite_ex),
		.isjal     (isjal_ex), 
		.regwrite     (regwrite_ex), 
		.memtoreg     (memtoreg_ex)); 
		
	ex_part ex_part(
		.instr			(instr_ex),
		.readreg_1     (readreg_1_ex),
		.readreg_2     (readreg_2_ex),
		.foward_mem 	(aluout_mem),
		.foward_wd     (result_wb),
		.foward_rs     (foward_rs),
		.foward_rt     (foward_rt),
		.signimm       (signimm_ex),
		.pc_plus4		(pc_plus4_ex),
		.compare_pc_plus4 (pc_plus4_if),
		.rt  			   (rt_ex),
		.rd  			   (rd_ex),
		.shiftl16      (shiftl16_ex),
		.regdst        (regdst_ex),  
		.alucontrol    (alucontrol_ex),   
		.alusrc        (alusrc_ex),  
		.branch			(branch_ex), 
		.branchN			(branchN_ex),
		.jump				(jump_ex),
		.isjal      (isjal_ex), 
		.aluzero       (aluzero_ex),
		.aluout        (aluout_ex),
		.pc_next			(pc_next),
		.writereg      (writereg_ex),
		.write_data		(write_data_ex)
		);
	
	ppline_exmem ff_exmem(
		.clk            (clk),
		.reset          (reset),
		.pc_plus4_d   	(pc_plus4_ex),
		.aluzero_d      (aluzero_ex),
		.aluout_d       (aluout_ex),
		.write_data_d          (write_data_ex),
		.writereg_d (writereg_ex),
		.memwrite_d     (memwrite_ex),
		.isjal_d  (isjal_ex),  
		.regwrite_d     (regwrite_ex), 
		.memtoreg_d     (memtoreg_ex),  
		.pc_plus4        (pc_plus4_mem),
		.aluzero        (aluzero_mem),
		.aluout         (aluout_mem),
		.write_data            (write_data_mem),
		.writereg   (writereg_mem),   
		.memwrite       (memwrite_mem),
		.isjal    (isjal_mem),  
		.regwrite       (regwrite_mem),  
		.memtoreg       (memtoreg_mem)   
		);		
		
	ppline_memwb ff_memwb(
		.clk            (clk),
		.reset          (reset),
		.pc_plus4_d      (pc_plus4_mem),
		.readdata_d     (memread_mem),
		.aluout_d       (aluout_mem),
		.writereg_d     (writereg_mem),
		.isjal_d  (isjal_mem),  
		.regwrite_d     (regwrite_mem),  
		.memtoreg_d     (memtoreg_mem),  
		.pc_plus4        (pc_plus4_wb),
		.readdata       (memread_wb),
		.aluout         (aluout_wb),
		.writereg       (writereg_wb),
		.isjal       (isjal_wb),  
		.regwrite       (regwrite_wb),
		.memtoreg       (memtoreg_wb)  
		);
		
	wb_part wb_part(
		.pc_plus4   (pc_plus4_wb),
		.aluout    (aluout_wb),
		.readdata  (memread_wb),
		.isjal  (isjal_wb),
		.memtoreg  (memtoreg_wb),
		.result    (result_wb));
		
	forwarding forwarding(
		.regwrite_wb	(regwrite_wb),
		.regwrite_mem	(regwrite_mem),
		.rs				(rs_ex),
		.rt				(rt_ex),
		.writereg_mem	(writereg_mem),
		.writereg_wb	(writereg_wb),
		.foward_rs		(foward_rs),
		.foward_rt		(foward_rt));
		
	
	hazard_detect_unit hdu(
		.op_ex			(instr_ex[31:26]),
		.load_reg		(rt_ex),
		.rs_id			(rs_id),
		.rt_id			(rt_id),
		.keep_write_pc		(keep_write_pc),
		.keep_write_ifid	(keep_write_ifid),
		.flush_idex		(flush_idex));

endmodule


module maindec(input  [5:0] op,
               output       signext,
               output       shiftl16,
               output       memtoreg, memwrite,
               output       branch, alusrc, branchN,
               output       regdst, regwrite,
               output       jump, isjal,
               output [2:0] aluop);

  reg [13:0] controls;

  assign {signext, shiftl16, regwrite, regdst, alusrc, branch, memwrite,
          memtoreg, jump, aluop, branchN, isjal} = controls;

  always @(*)
    case(op)
      6'b000000: controls <= #`mydelay 14'b00110000001100; // Rtype
      6'b100011: controls <= #`mydelay 14'b10101001000000; // LW
      6'b101011: controls <= #`mydelay 14'b10001010000000; // SW
      6'b000100: controls <= #`mydelay 14'b10000100000100; // BEQ
      6'b001000, 
      6'b001001: controls <= #`mydelay 14'b10101000000000; // ADDI, ADDIU: only difference is exception
      6'b001101: controls <= #`mydelay 14'b00101000001000; // ORI
		6'b001010: controls <= #`mydelay 14'b10101000011000; // SLTI
		6'b001011: controls <= #`mydelay 14'b10101000011100; // SLTIU
      6'b001111: controls <= #`mydelay 14'b01101000000000; // LUI
      6'b000010: controls <= #`mydelay 14'b00000000100000; // J
		6'b000101: controls <= #`mydelay 14'b10000100000110; // BNE   added
		6'b000011: controls <= #`mydelay 14'b00100000100001; // JAL   added
      default:   controls <= #`mydelay 14'b00000000000000; // ???
    endcase

endmodule

module aludec(input      [5:0] funct,
              input      [2:0] aluop,
              output reg [3:0] alucontrol,
				  output reg disregwrite);

  always @(*) begin
    case(aluop)
      3'b000: alucontrol <= #`mydelay 4'b0010;  // add
      3'b001: alucontrol <= #`mydelay 4'b0110;  // sub
      3'b010: alucontrol <= #`mydelay 4'b0001;  // or
		3'b110: alucontrol <= #`mydelay 4'b0111;  // SLTI
		3'b111: alucontrol <= #`mydelay 4'b1111;  // SLTIU
      default: case(funct)          // RTYPE
		    6'b001000: alucontrol <= #`mydelay 4'b1010; // JR  need addition with rs and $zero
          6'b100000,
          6'b100001: alucontrol <= #`mydelay 4'b0010; // ADD, ADDU: only difference is exception
          6'b100010,
          6'b100011: alucontrol <= #`mydelay 4'b0110; // SUB, SUBU: only difference is exception
          6'b100100: alucontrol <= #`mydelay 4'b0000; // AND
          6'b100101: alucontrol <= #`mydelay 4'b0001; // OR
          6'b101010: alucontrol <= #`mydelay 4'b0111; // SLT
			 6'b101011: alucontrol <= #`mydelay 4'b1111; // SLTU
          default:   alucontrol <= #`mydelay 4'b0000;
        endcase
    endcase	 
	 if (aluop == 3'b011 && funct == 6'b001000) begin
	     disregwrite <= #`mydelay 1'b0;
	 end
	 else begin
	     disregwrite <= #`mydelay 1'b1;
	 end
  end    
endmodule

module if_part(input			clk, reset,
					input			  keep_write,
					input	 [31:0] pc_next,
					output [31:0] pc,
					output [31:0] pc_plus4);
					
	flopenr #(32) pcreg(
		.clk	 (clk),
		.reset (reset),
		.en	 (keep_write),
		.d		 (pc_next),
		.q		 (pc));
		
	adder pcadd_4(
		.a (pc),
		.b (32'b100),
		.y (pc_plus4));

endmodule

module id_part(input			clk,
					input	[31:0]  instr,
					input   [4:0]   writereg,
					input   [31:0]  result,
					input   [31:0]  pc_plus4,
					input         regwrite_wb,
					output [31:0] readreg_1,
					output [31:0] readreg_2,
					output [31:0] signimm,
					output [4:0]  rs,
					output [4:0]  rd,
					output [4:0]  rt,
					output		  shiftl16,
					output		  regdst,   
					output		  alusrc,
					output        branch,
					output        branchN,
					output        jump,
					output        memwrite,
					output        isjal,
					output        memtoreg,
					output        regwrite,
					output [3:0]  alucontrol
					);
    wire 		 signext;
	 wire        regwrite_mid;
	 wire        disregwrite;
	 wire [31:0] readreg_1_mid, readreg_2_mid;
	 wire [2:0]	 aluop;
	 
	 assign rs = instr[25:21];
	 assign rt = instr[20:16];
	 assign rd = instr[15:11];
	 
    regfile rf(
		.clk     (clk),
		.we      (regwrite_wb),
		.ra1     (rs),
		.ra2     (rt),
		.wa      (writereg),
		.wd      (result),
		.rd1     (readreg_1_mid),
		.rd2     (readreg_2_mid));
		
	rf_readwrite_time rd1(
		.writereg	(writereg),
		.readreg		(rs),
		.result		(result),
		.read			(readreg_1_mid),
		.realread	(readreg_1));
		
	rf_readwrite_time rd2(
		.writereg	(writereg),
		.readreg		(rt),
		.result		(result),
		.read			(readreg_2_mid),
		.realread	(readreg_2));
		
    sign_zero_ext sze(
		.a       (instr[15:0]),
		.signext (signext),
		.y       (signimm[31:0]));
		
    maindec md(
		.op       (instr[31:26]),
		.signext  (signext),
		.shiftl16 (shiftl16),
		.memtoreg (memtoreg),
		.memwrite (memwrite),
		.branch   (branch),
		.branchN  (branchN),
		.alusrc   (alusrc),
		.regdst   (regdst),
		.regwrite (regwrite_mid),
		.jump     (jump),
		.isjal (isjal),
		.aluop    (aluop));
		
	aludec ad(
		.funct       (instr[5:0]),
		.aluop       (aluop), 
		.alucontrol  (alucontrol),
		.disregwrite (disregwrite));
		
		assign regwrite = disregwrite & regwrite_mid;

endmodule


module ex_part(input	[31:0]  instr,
					input [31:0]  readreg_1,
					input [31:0]  readreg_2,
					input [31:0]  foward_mem,
					input [31:0]  foward_wd,
					input [1:0]	  foward_rs,
					input [1:0]	  foward_rt,
					input [31:0]  signimm,
					input [31:0]  pc_plus4,
					input [31:0]  compare_pc_plus4,
					input [4:0]   rt,
					input [4:0]   rd,
					input			  shiftl16,
					input			  regdst,
					input [3:0]   alucontrol,
					input         alusrc,
					input         branch,
					input         branchN,
					input         jump,
					input         isjal,
					output        aluzero,
					output [31:0] aluout,
					output [31:0] pc_next,
					output [4:0]  writereg,
					output [31:0] write_data
					);
					
	  wire [31:0] signimmsh2, signimmsh16;
	  wire [31:0] pc_branch;
	  wire [31:0] pc_next_jr, pc_next_mid;
	  wire [31:0] aluin1, aluin2, aluin2_mid;
	  wire [4:0]  writereg_mid;
	  wire        pcsrc;
	  
	  assign write_data = aluin2_mid;
	  
	  shift_left_16 sl16(
		.a         (signimm[31:0]),
		.shiftl16  (shiftl16),
		.y         (signimmsh16[31:0]));
		
	  mux4 #(32) is_foward_rs(
		.d0 (readreg_1),
		.d1 (foward_mem),
		.d2 (foward_wd),
		.d3 (32'b0),
		.s	 (foward_rs),
		.y  (aluin1));
		
	  mux4 #(32) is_foward_rt(
		.d0 (readreg_2),
		.d1 (foward_mem),
		.d2 (foward_wd),
		.d3 (32'b0),
		.s	 (foward_rt),
		.y  (aluin2_mid));
		
	  mux2 #(32) aluin2_mux(
		.d0 (aluin2_mid),
		.d1 (signimmsh16[31:0]),
		.s  (alusrc),
		.y  (aluin2));
		
	  alu alu(
		.a       (aluin1),
		.b       (aluin2),
		.alucont (alucontrol),
		.result  (aluout),
		.zero    (aluzero));
		
	  mux2 #(5) wrdst_reg_mux(
		.d0  (rt),
		.d1  (rd),
		.s   (regdst),
		.y   (writereg_mid));
		
	assign pcsrc = branchN ? (branch & !aluzero) : (branch & aluzero);
	
	sl2 immshift(
		.a (signimm),
		.y (signimmsh2));
		
	adder pcadd_signimm(
		.a (pc_plus4),
		.b (signimmsh2),
		.y (pc_branch));
	 
	mux2 #(32) pcbrmux(
		.d0  (compare_pc_plus4),
		.d1  (pc_branch),
		.s   (pcsrc),
		.y   (pc_next_mid));
		
	jrmux jrpcmux(
		.d0       (pc_next_mid),
		.d1       (aluin1),
		.alucontrol (alucontrol),
		.y       (pc_next_jr));
		
    mux2 #(32) pcmux(
		.d0   (pc_next_jr),
		.d1   ({pc_plus4[31:28], instr[25:0], 2'b00}),
		.s    (jump),
		.y    (pc_next));
		
	mux2 #(5) wrdst_jal_mux(
		.d0  (writereg_mid),
		.d1  (5'b11111),
		.s   (isjal),
		.y   (writereg));
	  
endmodule

module wb_part(input  [31:0] pc_plus4,
					input  [31:0] aluout,
					input  [31:0] readdata,
					input         isjal,
					input         memtoreg,
					output [31:0] result);
					
    wire [31:0] result_mid;
	 
	 mux2 #(32) resmux(
		.d0 (aluout),
		.d1 (readdata),
		.s  (memtoreg),
		.y  (result_mid));
		
    mux2 #(32) jalresmux(
		.d0 (result_mid),
		.d1 (pc_plus4),
		.s  (isjal),
		.y  (result));
endmodule
