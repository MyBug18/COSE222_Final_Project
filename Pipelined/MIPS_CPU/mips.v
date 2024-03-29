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
   wire [1:0] aluop_id, aluop_ex;
  
// ###### Minsoo Kim: Start ######
   wire [31:0] pc_plus4_if, pc_plus4_id, pc_plus4_ex, pc_plus4_mem, pc_plus4_wb, pc_next;
   wire [31:0] instr_id, instr_ex;
   wire [4:0] writereg_ex, writereg_mem, writereg_wb;
   wire [31:0] write_data_ex, write_data_mem;
   wire [31:0] rd1_id, rd1_ex, rd2_id, rd2_ex;
   wire [31:0] signimm_id, signimm_ex;
   wire [31:0] aluout_ex, aluout_mem, aluout_wb;
   wire [31:0] memread_wb;
   wire [31:0] result_wb;
   wire aluzero_ex;
   wire nullify_pc_move, nullify_pipe;
	
   wire [1:0] foward_rs_control, foward_rt_control;
  
   wire shiftl16_id, shiftl16_ex;
   wire regdst_id,regdst_ex;
   wire alusrc_id, alusrc_ex;
   wire branch_id, branch_ex;
   wire branch_bne_id, branch_bne_ex;
   wire jump_id, jump_ex;
   wire memwrite_id, memwrite_ex, memwrite_mem;
   wire isjal_id, isjal_ex, isjal_mem, isjal_wb;
   wire regwrite_id, regwrite_ex, regwrite_mem, regwrite_wb;
   wire memtoreg_id, memtoreg_ex, memtoreg_mem, memtoreg_wb;

   assign memwrite = memwrite_mem;
   assign memaddr = aluout_mem;
   assign memwritedata = write_data_mem;
	
	wire nullify_idex;
	wire keep_write;	
  
	IF_STAGE if_stage(
		.clk        (clk),
		.reset      (reset),
		.keep_write     (keep_write),
		.pc_next     (pc_next),
		.pc         (pc),
		.pc_plus4    (pc_plus4_if));
		
	IF_ID if_id(
		.clk       (clk),
		.reset     (nullify_pipe),
		.keep_write    (keep_write),
		.pc_plus4_in (pc_plus4_if),
		.instr_in   (instr),
		.pc_plus4   (pc_plus4_id),
		.instr     (instr_id));
		
	ID_STAGE id_stage(
		.clk          (clk),
		.instr        (instr_id),
		.writereg     (writereg_wb),
		.result       (result_wb),
		.pc_plus4     (pc_plus4_id),
		.rd1    (rd1_id),
		.rd2    (rd2_id),
		.signimm      (signimm_id),
		.shiftl16     (shiftl16_id),
		.regdst       (regdst_id),  
		.alusrc       (alusrc_id),  
		.branch       (branch_id),
		.branch_bne     (branch_bne_id),
		.jump         (jump_id),
		.memwrite     (memwrite_id),
		.isjal     (isjal_id), 
		.memtoreg     (memtoreg_id), 
		.regwrite (regwrite_id), 
		.alucontrol   (alucontrol_id),
		.regwrite_wb  (regwrite_wb)
		);
		
	// ###### Minsoo Kim (for milestone 5): Start ######

	assign nullify_pipe = nullify_pc_move | reset;
	assign nullify_idex = nullify_pipe | !keep_write;

	control_hazard_unit chu(
		.alucontrol	  (alucontrol_ex),
		.branch		  (branch_ex),
		.branch_bne      (branch_bne_ex),
		.jump         (jump_ex),
		.aluzero			  (aluzero_ex),
		.nullify		  (nullify_pc_move)
		);
				
	// ###### Minsoo Kim (for milestone 5): End ######

   ID_EX id_ex(
		.clk          (clk),
		.reset        (nullify_idex),
		.instr_in      (instr_id),
		.pc_plus4_in    (pc_plus4_id),
		.rd1_in        (rd1_id),
		.rd2_in        (rd2_id),
		.immex_in      (signimm_id),
		.shiftl16_in   (shiftl16_id),
		.regdst_in     (regdst_id),  
		.alucontrol_in (alucontrol_id),   
		.alusrc_in     (alusrc_id),  
		.branch_in	   (branch_id),
		.branch_bne_in (branch_bne_id),
		.jump_in	   (jump_id),
		.memwrite_in   (memwrite_id),
		.isjal_in   (isjal_id), 
		.memtoreg_in   (memtoreg_id), 
		.regwrite_in   (regwrite_id), 
		.pc_plus4      (pc_plus4_ex),
		.instr        (instr_ex),
		.rd1          (rd1_ex),
		.rd2          (rd2_ex),
		.immex        (signimm_ex),
		.shiftl16     (shiftl16_ex),
		.regdst       (regdst_ex),  
		.alucontrol   (alucontrol_ex),   
		.alusrc       (alusrc_ex),  
		.branch		  (branch_ex),
		.branch_bne	  (branch_bne_ex),
		.jump		  (jump_ex),
		.memwrite     (memwrite_ex),
		.isjal        (isjal_ex), 
		.regwrite     (regwrite_ex), 
		.memtoreg     (memtoreg_ex)); 
		
	EX_STAGE ex_stage(
		.instr			(instr_ex),
		.rd1     (rd1_ex),
		.rd2     (rd2_ex),
		.foward_mem 	(aluout_mem),
		.foward_wd     (result_wb),
		.foward_rs_control     (foward_rs_control),
		.foward_rt_control     (foward_rt_control),
		.signimm       (signimm_ex),
		.pc_plus4		(pc_plus4_ex),
		.compare_pc_plus4 (pc_plus4_if),
		.shiftl16      (shiftl16_ex),
		.regdst        (regdst_ex),  
		.alucontrol    (alucontrol_ex),
		.alusrc        (alusrc_ex),
		.branch			(branch_ex),
		.branch_bne		(branch_bne_ex),
		.jump			(jump_ex),
		.isjal      	(isjal_ex), 
		.aluzero       (aluzero_ex),
		.aluout        (aluout_ex),
		.pc_next		(pc_next),
		.writereg      (writereg_ex),
		.write_data		(write_data_ex)
		);
	
	EX_MEM ex_mem(
		.clk            (clk),
		.reset          (reset),
		.pc_plus4_in   	(pc_plus4_ex),
		.aluzero_in      (aluzero_ex),
		.aluout_in       (aluout_ex),
		.write_data_in          (write_data_ex),
		.writereg_in (writereg_ex),
		.memwrite_in     (memwrite_ex),
		.isjal_in  (isjal_ex),  
		.regwrite_in     (regwrite_ex), 
		.memtoreg_in     (memtoreg_ex),  
		.pc_plus4        (pc_plus4_mem),
		.aluout         (aluout_mem),
		.write_data            (write_data_mem),
		.writereg   (writereg_mem),   
		.memwrite       (memwrite_mem),
		.isjal    (isjal_mem),  
		.regwrite       (regwrite_mem),  
		.memtoreg       (memtoreg_mem)   
		);		
		
	MEM_WB mem_wb(
		.clk            (clk),
		.reset          (reset),
		.pc_plus4_in      (pc_plus4_mem),
		.readdata_in     (memreaddata),
		.aluout_in       (aluout_mem),
		.writereg_in     (writereg_mem),
		.isjal_in  (isjal_mem),  
		.regwrite_in     (regwrite_mem),  
		.memtoreg_in     (memtoreg_mem),  
		.pc_plus4        (pc_plus4_wb),
		.readdata       (memread_wb),
		.aluout         (aluout_wb),
		.writereg       (writereg_wb),
		.isjal       (isjal_wb),  
		.regwrite       (regwrite_wb),
		.memtoreg       (memtoreg_wb)  
		);
		
	WB_STAGE wb_stage(
		.pc_plus4   (pc_plus4_wb),
		.aluout    (aluout_wb),
		.readdata  (memread_wb),
		.isjal  (isjal_wb),
		.memtoreg  (memtoreg_wb),
		.result    (result_wb));

// ###### Minsoo Kim (for milestone 4): Start ######

	forwarding_unit fu(
		.regwrite_wb	(regwrite_wb),
		.regwrite_mem	(regwrite_mem),
		.rs				(instr_ex[25:21]),
		.rt				(instr_ex[20:16]),
		.writereg_mem	(writereg_mem),
		.writereg_wb	(writereg_wb),
		.foward_rs_control		(foward_rs_control),
		.foward_rt_control		(foward_rt_control));
		
	
	hazard_detect_unit hdu(
		.op_ex			(instr_ex[31:26]),
		.load_reg		(instr_ex[20:16]),
		.rs_id			(instr_id[25:21]),
		.rt_id			(instr_id[20:16]),
		.keep_write		(keep_write));

// ###### Minsoo Kim (for milestone 4): End ######

endmodule

// ###### Minsoo Kim: End ######
