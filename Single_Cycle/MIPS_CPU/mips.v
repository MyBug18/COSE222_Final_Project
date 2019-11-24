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

  wire        signext, shiftl16, memtoreg, branch;
  wire        pcsrc, zero;
  wire        alusrc, regdst, regwrite, jump, isjal;
  wire [3:0]  alucontrol;

  // Instantiate Controller
  controller c(
    .op         (instr[31:26]), 
		.funct      (instr[5:0]), 
		.zero       (zero),
		.signext    (signext),
		.shiftl16   (shiftl16),
		.memtoreg   (memtoreg),
		.memwrite   (memwrite),
		.pcsrc      (pcsrc),
		.alusrc     (alusrc),
		.regdst     (regdst),
		.regwrite   (regwrite),
		.jump       (jump),
		.isjal(isjal),
		.alucontrol (alucontrol));

  // Instantiate Datapath
  datapath dp(
    .clk        (clk),
    .reset      (reset),
    .signext    (signext),
    .shiftl16   (shiftl16),
    .memtoreg   (memtoreg),
    .pcsrc      (pcsrc),
    .alusrc     (alusrc),
    .regdst     (regdst),
    .regwrite   (regwrite),
    .jump       (jump),
	 .isjal(isjal),
    .alucontrol (alucontrol),
    .zero       (zero),
    .pc         (pc),
    .instr      (instr),
    .aluout     (memaddr), 
    .writedata  (memwritedata),
    .readdata   (memreaddata));

endmodule

module controller(input  [5:0] op, funct,
                  input        zero,
                  output       signext,
                  output       shiftl16,
                  output       memtoreg, memwrite,
                  output       pcsrc, alusrc,
                  output       regdst, regwrite,
                  output       jump, isjal,
                  output [3:0] alucontrol);

  wire [2:0] aluop;
  wire       branch;
  wire 		   branch_bne;      //for bne 
  wire       pc_beq;    //beq
  wire       pc_bne;    //bne
  wire       origin_regwrite;  //original regwrite signal
  wire       jr_no_regwrite;  //JR need control regwrite signal (1 -> 0)

  maindec md(
    .op       (op),
    .signext  (signext),
    .shiftl16 (shiftl16),
    .memtoreg (memtoreg),
    .memwrite (memwrite),
    .branch   (branch),
    .alusrc   (alusrc),
    .regdst   (regdst),
    .regwrite (origin_regwrite),
    .jump     (jump),
    .aluop    (aluop),
	  .branch_bne  (branch_bne),
	  .isjal     (isjal));

  aludec ad( 
    .funct          (funct),
    .aluop          (aluop), 
    .alucontrol     (alucontrol),
	  .jr_no_regwrite (jr_no_regwrite));

  assign pc_beq = branch & zero;     //beq
  assign pc_bne = branch & ~zero;    //bne
  assign pcsrc = branch_bne ? pc_bne : pc_beq;    // 0: beq, 1: bne
  assign regwrite = origin_regwrite & jr_no_regwrite;       // if jr regwrite should be zero

endmodule


module maindec(input  [5:0] op,
               output       signext,
               output       shiftl16,
               output       memtoreg, memwrite,
               output       branch, alusrc, branch_bne,
               output       regdst, regwrite,
               output       jump, isjal,
               output [2:0] aluop);

  reg [13:0] controls;

  assign {signext, shiftl16, regwrite, regdst, alusrc, branch, memwrite,
          memtoreg, jump, aluop, branch_bne, isjal} = controls;

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
				  output reg jr_no_regwrite);

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
          default:   alucontrol <= #`mydelay 4'b0000; // ???
        endcase
    endcase	 
	 if (aluop == 3'b011 && funct == 6'b001000) begin
	     jr_no_regwrite <= #`mydelay 1'b0;     // if JR do not write reg
	 end
	 else begin
	     jr_no_regwrite <= #`mydelay 1'b1;     // else write reg
	 end
  end    
endmodule

module datapath(input         clk, reset,
                input         signext,
                input         shiftl16,
                input         memtoreg, pcsrc,
                input         alusrc, regdst,
                input         regwrite, jump, isjal,
                input  [3:0]  alucontrol,
                output        zero,
                output [31:0] pc,
                input  [31:0] instr,
                output [31:0] aluout, writedata,
                input  [31:0] readdata);

  wire [4:0]  writereg;
  wire [4:0]  writeregdst;
  wire [31:0] pcnext, pcnextbr, pcplus4, pcbranch, pcbefornext;
  wire [31:0] signimm, signimmsh, shiftedimm;
  wire [31:0] srca, srcb;
  wire [31:0] resultPre;
  wire [31:0] result;
  wire        shift;

  // next PC logic
  flopr #(32) pcreg(
    .clk   (clk),
    .reset (reset),
    .d     (pcnext),
    .q     (pc));

  adder pcadd1(
    .a (pc),
    .b (32'b100),
    .y (pcplus4));

  sl2 immsh(
    .a (signimm),
    .y (signimmsh));
				 
  adder pcadd2(
    .a (pcplus4),
    .b (signimmsh),
    .y (pcbranch));

  mux2 #(32) pcbrmux(
    .d0  (pcbefornext),
    .d1  (pcbranch),
    .s   (pcsrc),
    .y   (pcnextbr));
	 
  jrmux jrmux(
    .d0  (pcplus4),
    .d1  (aluout),
    .alucontrol   (alucontrol),
    .y   (pcbefornext));

  mux2 #(32) pcmux(
    .d0   (pcnextbr),
    .d1   ({pcplus4[31:28], instr[25:0], 2'b00}),
    .s    (jump),
    .y    (pcnext));

  // register file logic
  regfile rf(
    .clk     (clk),
    .we      (regwrite),
    .ra1     (instr[25:21]),
    .ra2     (instr[20:16]),
    .wa      (writereg),
    .wd      (result),
    .rd1     (srca),
    .rd2     (writedata));

  mux2 #(5) wrmux(
    .d0  (instr[20:16]),
    .d1  (instr[15:11]),
    .s   (regdst),
    .y   (writeregdst));
	 
  mux2 #(5) jalmux(     //added for jal, where to save, 0: rt or rd(decided before this), 1: 11111($ra)
    .d0  (writeregdst),
    .d1  (5'b11111),
    .s   (isjal),
    .y   (writereg));

  mux2 #(32) resmux(
    .d0 (aluout),
    .d1 (readdata),
    .s  (memtoreg),
    .y  (resultPre));
	 
  mux2 #(32) jal_writemux(     //added for jal, what to save, 0: aluout or readdata(decided before this), 1: pc + 4
    .d0 (resultPre),
    .d1 (pcplus4),
    .s  (isjal),
    .y  (result));

  sign_zero_ext sze(
    .a       (instr[15:0]),
    .signext (signext),
    .y       (signimm[31:0]));

  shift_left_16 sl16(
    .a         (signimm[31:0]),
    .shiftl16  (shiftl16),
    .y         (shiftedimm[31:0]));

  // ALU logic
  mux2 #(32) srcbmux(
    .d0 (writedata),
    .d1 (shiftedimm[31:0]),
    .s  (alusrc),
    .y  (srcb));

  alu alu(
    .a       (srca),
    .b       (srcb),
    .alucont (alucontrol),
    .result  (aluout),
    .zero    (zero));
    
endmodule
