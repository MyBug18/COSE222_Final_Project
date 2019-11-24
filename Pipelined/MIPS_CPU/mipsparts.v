`timescale 1ns/1ps
`define mydelay 1

//------------------------------------------------
// mipsparts.v
// David_Harris@hmc.edu 23 October 2005
// Components used in MIPS processor
//------------------------------------------------

`define REGFILE_FF
`ifdef REGFILE_FF

module regfile(input             clk, 
               input             we, 
               input      [4:0]  ra1, ra2, wa, 
               input      [31:0] wd, 
               output reg [31:0] rd1, rd2);

	reg [31:0] R1;
	reg [31:0] R2;
	reg [31:0] R3;
	reg [31:0] R4;
	reg [31:0] R5;
	reg [31:0] R6;
	reg [31:0] R7;
	reg [31:0] R8;
	reg [31:0] R9;
	reg [31:0] R10;
	reg [31:0] R11;
	reg [31:0] R12;
	reg [31:0] R13;
	reg [31:0] R14;
	reg [31:0] R15;
	reg [31:0] R16;
	reg [31:0] R17;
	reg [31:0] R18;
	reg [31:0] R19;
	reg [31:0] R20;
	reg [31:0] R21;
	reg [31:0] R22;
	reg [31:0] R23;
	reg [31:0] R24;
	reg [31:0] R25;
	reg [31:0] R26;
	reg [31:0] R27;
	reg [31:0] R28;
	reg [31:0] R29;
	reg [31:0] R30;
	reg [31:0] R31;

	always @(negedge clk)
	begin
  	 if (we) 
   		case (wa[4:0])
   		5'd0:   ;
   		5'd1:   R1  <= wd;
   		5'd2:   R2  <= wd;
   		5'd3:   R3  <= wd;
   		5'd4:   R4  <= wd;
   		5'd5:   R5  <= wd;
   		5'd6:   R6  <= wd;
   		5'd7:   R7  <= wd;
   		5'd8:   R8  <= wd;
   		5'd9:   R9  <= wd;
   		5'd10:  R10 <= wd;
   		5'd11:  R11 <= wd;
   		5'd12:  R12 <= wd;
   		5'd13:  R13 <= wd;
   		5'd14:  R14 <= wd;
   		5'd15:  R15 <= wd;
   		5'd16:  R16 <= wd;
   		5'd17:  R17 <= wd;
   		5'd18:  R18 <= wd;
   		5'd19:  R19 <= wd;
   		5'd20:  R20 <= wd;
   		5'd21:  R21 <= wd;
   		5'd22:  R22 <= wd;
   		5'd23:  R23 <= wd;
   		5'd24:  R24 <= wd;
   		5'd25:  R25 <= wd;
   		5'd26:  R26 <= wd;
   		5'd27:  R27 <= wd;
   		5'd28:  R28 <= wd;
   		5'd29:  R29 <= wd;
   		5'd30:  R30 <= wd;
   		5'd31:  R31 <= wd;
   		endcase
	end

	always @(*)
	begin
		case (ra2[4:0])
		5'd0:   rd2 = 32'b0;
		5'd1:   rd2 = R1;
		5'd2:   rd2 = R2;
		5'd3:   rd2 = R3;
		5'd4:   rd2 = R4;
		5'd5:   rd2 = R5;
		5'd6:   rd2 = R6;
		5'd7:   rd2 = R7;
		5'd8:   rd2 = R8;
		5'd9:   rd2 = R9;
		5'd10:  rd2 = R10;
		5'd11:  rd2 = R11;
		5'd12:  rd2 = R12;
		5'd13:  rd2 = R13;
		5'd14:  rd2 = R14;
		5'd15:  rd2 = R15;
		5'd16:  rd2 = R16;
		5'd17:  rd2 = R17;
		5'd18:  rd2 = R18;
		5'd19:  rd2 = R19;
		5'd20:  rd2 = R20;
		5'd21:  rd2 = R21;
		5'd22:  rd2 = R22;
		5'd23:  rd2 = R23;
		5'd24:  rd2 = R24;
		5'd25:  rd2 = R25;
		5'd26:  rd2 = R26;
		5'd27:  rd2 = R27;
		5'd28:  rd2 = R28;
		5'd29:  rd2 = R29;
		5'd30:  rd2 = R30;
		5'd31:  rd2 = R31;
		endcase
	end

	always @(*)
	begin
		case (ra1[4:0])
		5'd0:   rd1 = 32'b0;
		5'd1:   rd1 = R1;
		5'd2:   rd1 = R2;
		5'd3:   rd1 = R3;
		5'd4:   rd1 = R4;
		5'd5:   rd1 = R5;
		5'd6:   rd1 = R6;
		5'd7:   rd1 = R7;
		5'd8:   rd1 = R8;
		5'd9:   rd1 = R9;
		5'd10:  rd1 = R10;
		5'd11:  rd1 = R11;
		5'd12:  rd1 = R12;
		5'd13:  rd1 = R13;
		5'd14:  rd1 = R14;
		5'd15:  rd1 = R15;
		5'd16:  rd1 = R16;
		5'd17:  rd1 = R17;
		5'd18:  rd1 = R18;
		5'd19:  rd1 = R19;
		5'd20:  rd1 = R20;
		5'd21:  rd1 = R21;
		5'd22:  rd1 = R22;
		5'd23:  rd1 = R23;
		5'd24:  rd1 = R24;
		5'd25:  rd1 = R25;
		5'd26:  rd1 = R26;
		5'd27:  rd1 = R27;
		5'd28:  rd1 = R28;
		5'd29:  rd1 = R29;
		5'd30:  rd1 = R30;
		5'd31:  rd1 = R31;
		endcase
	end

endmodule

`else

module regfile(input         clk, 
               input         we, 
               input  [4:0]  ra1, ra2, wa, 
               input  [31:0] wd, 
               output [31:0] rd1, rd2);

  reg [31:0] rf[31:0];

  always @(negedge clk)
    if (we) rf[wa] <= #`mydelay wd;	
  always @(*)
	begin
	  	rd1 <= #`mydelay (ra1 != 0) ? rf[ra1] : 0;
 	 	rd2 <= #`mydelay (ra2 != 0) ? rf[ra2] : 0;
	end
endmodule

`endif

module is_equal(input  [31:0] d0, d1,
              output  reg eq);

  always @(*)
	begin
	   if (d0 == d1)  eq <= 1'b1;
	   else          eq <= 1'b0;
	end

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
	  6'b000101: controls <= #`mydelay 14'b10000100000110; // BNE
	  6'b000011: controls <= #`mydelay 14'b00100000100001; // JAL
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
		    6'b001000: alucontrol <= #`mydelay 4'b1010; // JR
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
	     jr_no_regwrite <= #`mydelay 1'b0;
	 end
	 else begin
	     jr_no_regwrite <= #`mydelay 1'b1;
	 end
  end    
endmodule

module mux4 #(parameter WIDTH = 8)
             (input  [WIDTH-1:0] d0, d1, d2, d3, 
              input  [1:0]       s, 
              output reg [WIDTH-1:0] y);

  always@(s, d0, d1, d2, d3)
    case(s)
      2'b00: y = d0;
      2'b01: y = d1;
      2'b10: y = d2;
      2'b11: y = d3;
    endcase

endmodule

module alu(input      [31:0] a, b, 
           input      [3:0]  alucont, 
           output reg [31:0] result,
           output            zero);

  wire [31:0] b2, sum, slt, sltu, real_slt;
  wire        N, Z, C, V;

  assign b2 = alucont[2] ? ~b:b; 

  adder_32bit iadder32 (.a   (a),
			               .b   (b2),
								.cin (alucont[2]),
								.sum (sum),
								.N   (N),
								.Z   (Z),
								.C   (C),
								.V   (V));

  assign slt  = N ^ V ; 

  assign sltu = ~C ;

  assign real_slt = (alucont[3] == 1) ? {31'b0, sltu[0]}:{31'b0, slt[0]};

  always@(*)
    case(alucont[1:0])
      2'b00: result <= #`mydelay a & b;
      2'b01: result <= #`mydelay a | b;
      2'b10: result <= #`mydelay sum;
      2'b11: result <= #`mydelay real_slt;
    endcase

  assign #`mydelay zero = (result == 32'b0);

endmodule

module adder_32bit (input  [31:0] a, b, 
                    input         cin,
                    output [31:0] sum,
                    output        N,Z,C,V);

	wire [31:0]  ctmp;

	assign N = sum[31];
	assign Z = (sum == 32'b0);
	assign C = ctmp[31];
	assign V = ctmp[31] ^ ctmp[30];

	adder_1bit bit31 (.a(a[31]), .b(b[31]), .cin(ctmp[30]), .sum(sum[31]), .cout(ctmp[31]));
	adder_1bit bit30 (.a(a[30]), .b(b[30]), .cin(ctmp[29]), .sum(sum[30]), .cout(ctmp[30]));
	adder_1bit bit29 (.a(a[29]), .b(b[29]), .cin(ctmp[28]), .sum(sum[29]), .cout(ctmp[29]));
	adder_1bit bit28 (.a(a[28]), .b(b[28]), .cin(ctmp[27]), .sum(sum[28]), .cout(ctmp[28]));
	adder_1bit bit27 (.a(a[27]), .b(b[27]), .cin(ctmp[26]), .sum(sum[27]), .cout(ctmp[27]));
	adder_1bit bit26 (.a(a[26]), .b(b[26]), .cin(ctmp[25]), .sum(sum[26]), .cout(ctmp[26]));
	adder_1bit bit25 (.a(a[25]), .b(b[25]), .cin(ctmp[24]), .sum(sum[25]), .cout(ctmp[25]));
	adder_1bit bit24 (.a(a[24]), .b(b[24]), .cin(ctmp[23]), .sum(sum[24]), .cout(ctmp[24]));
	adder_1bit bit23 (.a(a[23]), .b(b[23]), .cin(ctmp[22]), .sum(sum[23]), .cout(ctmp[23]));
	adder_1bit bit22 (.a(a[22]), .b(b[22]), .cin(ctmp[21]), .sum(sum[22]), .cout(ctmp[22]));
	adder_1bit bit21 (.a(a[21]), .b(b[21]), .cin(ctmp[20]), .sum(sum[21]), .cout(ctmp[21]));
	adder_1bit bit20 (.a(a[20]), .b(b[20]), .cin(ctmp[19]), .sum(sum[20]), .cout(ctmp[20]));
	adder_1bit bit19 (.a(a[19]), .b(b[19]), .cin(ctmp[18]), .sum(sum[19]), .cout(ctmp[19]));
	adder_1bit bit18 (.a(a[18]), .b(b[18]), .cin(ctmp[17]), .sum(sum[18]), .cout(ctmp[18]));
	adder_1bit bit17 (.a(a[17]), .b(b[17]), .cin(ctmp[16]), .sum(sum[17]), .cout(ctmp[17]));
	adder_1bit bit16 (.a(a[16]), .b(b[16]), .cin(ctmp[15]), .sum(sum[16]), .cout(ctmp[16]));
	adder_1bit bit15 (.a(a[15]), .b(b[15]), .cin(ctmp[14]), .sum(sum[15]), .cout(ctmp[15]));
	adder_1bit bit14 (.a(a[14]), .b(b[14]), .cin(ctmp[13]), .sum(sum[14]), .cout(ctmp[14]));
	adder_1bit bit13 (.a(a[13]), .b(b[13]), .cin(ctmp[12]), .sum(sum[13]), .cout(ctmp[13]));
	adder_1bit bit12 (.a(a[12]), .b(b[12]), .cin(ctmp[11]), .sum(sum[12]), .cout(ctmp[12]));
	adder_1bit bit11 (.a(a[11]), .b(b[11]), .cin(ctmp[10]), .sum(sum[11]), .cout(ctmp[11]));
	adder_1bit bit10 (.a(a[10]), .b(b[10]), .cin(ctmp[9]),  .sum(sum[10]), .cout(ctmp[10]));
	adder_1bit bit9  (.a(a[9]),  .b(b[9]),  .cin(ctmp[8]),  .sum(sum[9]),  .cout(ctmp[9]));
	adder_1bit bit8  (.a(a[8]),  .b(b[8]),  .cin(ctmp[7]),  .sum(sum[8]),  .cout(ctmp[8]));
	adder_1bit bit7  (.a(a[7]),  .b(b[7]),  .cin(ctmp[6]),  .sum(sum[7]),  .cout(ctmp[7]));
	adder_1bit bit6  (.a(a[6]),  .b(b[6]),  .cin(ctmp[5]),  .sum(sum[6]),  .cout(ctmp[6]));
	adder_1bit bit5  (.a(a[5]),  .b(b[5]),  .cin(ctmp[4]),  .sum(sum[5]),  .cout(ctmp[5]));
	adder_1bit bit4  (.a(a[4]),  .b(b[4]),  .cin(ctmp[3]),  .sum(sum[4]),  .cout(ctmp[4]));
	adder_1bit bit3  (.a(a[3]),  .b(b[3]),  .cin(ctmp[2]),  .sum(sum[3]),  .cout(ctmp[3]));
	adder_1bit bit2  (.a(a[2]),  .b(b[2]),  .cin(ctmp[1]),  .sum(sum[2]),  .cout(ctmp[2]));
	adder_1bit bit1  (.a(a[1]),  .b(b[1]),  .cin(ctmp[0]),  .sum(sum[1]),  .cout(ctmp[1]));
	adder_1bit bit0  (.a(a[0]),  .b(b[0]),  .cin(cin),      .sum(sum[0]),  .cout(ctmp[0]));

endmodule

module adder_1bit (input a, b, cin,
                   output sum, cout);

  assign sum  = a ^ b ^ cin;
  assign cout = (a & b) | (a & cin) | (b & cin);

endmodule

module sl2(input  [31:0] a,
           output [31:0] y);

  assign #`mydelay y = {a[29:0], 2'b00};
endmodule

module sign_zero_ext(input      [15:0] a,
                     input             signext,
                     output reg [31:0] y);
              
   always @(*)
	begin
	   if (signext)  y <= {{16{a[15]}}, a[15:0]};
	   else          y <= {16'b0, a[15:0]};
	end

endmodule

module shift_left_16(input      [31:0] a,
		               input         shiftl16,
                     output reg [31:0] y);

   always @(*)
	begin
	   if (shiftl16) y = {a[15:0],16'b0};
	   else          y = a[31:0];
	end
              
endmodule

module flopr #(parameter WIDTH = 8)
              (input                  clk, reset,
               input      [WIDTH-1:0] d, 
               output reg [WIDTH-1:0] q);

  always @(posedge clk, posedge reset)
    if (reset) q <= #`mydelay 0;
    else       q <= #`mydelay d;

endmodule

module flopenr #(parameter WIDTH = 8)
                (input                  clk, reset,
                 input                  en,
                 input      [WIDTH-1:0] d, 
                 output reg [WIDTH-1:0] q);
 
  always @(posedge clk, posedge reset)
    if      (reset) q <= #`mydelay 0;
    else if (en)    q <= #`mydelay d;

endmodule

module mux2 #(parameter WIDTH = 8)
             (input  [WIDTH-1:0] d0, d1, 
              input              s, 
              output [WIDTH-1:0] y);

  assign #`mydelay y = (s == 1) ? d1 : d0; 

endmodule

// ###### Minsoo Kim : Start ######

module jrmux (input  [31:0] d0, d1, 
              input  [3:0]  alucontrol, 
              output [31:0] y);

  assign #`mydelay y = (alucontrol[3:0] == 4'b1010) ? d1 : d0; 

endmodule

module IF_STAGE(input			clk, reset,
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

	assign #`mydelay pc_plus4 = pc + 32'b100;

endmodule

module IF_ID(input 	         clk, reset,
				   input             keep_write,
				   input      [31:0] pc_plus4_in,
				   input      [31:0] instr_in,
				   output reg [31:0] pc_plus4,
				   output reg [31:0] instr);
	
	always @(posedge clk) begin
		if (reset) begin
			pc_plus4 <= #`mydelay 1'b0;
			instr   <= #`mydelay 1'b0;
		end
		else if (keep_write) begin
			pc_plus4 <= #`mydelay pc_plus4_in;
			instr   <= #`mydelay instr_in;
		end
	end
endmodule

module ID_STAGE(input			clk,
					input  [31:0] instr,
					input  [4:0]  writereg,
					input  [31:0] result,
					input  [31:0] pc_plus4,
					input         regwrite_wb,
					output [31:0] rd1,
					output [31:0] rd2,
					output [31:0] signimm,
					output		  shiftl16,
					output		  regdst,   
					output		  alusrc,
					output        branch,
					output        branch_bne,
					output        jump,
					output        memwrite,
					output        isjal,
					output        memtoreg,
					output        regwrite,
					output [3:0]  alucontrol
					);
    wire 		 signext;
	wire        regwrite_tmp;
	wire        jr_no_regwrite;
	wire [2:0]	 aluop;
	 
    regfile rf(
		.clk     (clk),
		.we      (regwrite_wb),
		.ra1     (instr[25:21]),
		.ra2     (instr[20:16]),
		.wa      (writereg),
		.wd      (result),
		.rd1     (rd1),
		.rd2     (rd2));
		
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
		.branch_bne  (branch_bne),
		.alusrc   (alusrc),
		.regdst   (regdst),
		.regwrite (regwrite_tmp),
		.jump     (jump),
		.isjal    (isjal),
		.aluop    (aluop));
		
	aludec ad(
		.funct       (instr[5:0]),
		.aluop       (aluop), 
		.alucontrol  (alucontrol),
		.jr_no_regwrite (jr_no_regwrite));
		
		assign regwrite = jr_no_regwrite & regwrite_tmp;

endmodule

module ID_EX(input 	         clk, reset,
				   input      [31:0] instr_in,
				   input      [31:0] pc_plus4_in,
				   input      [31:0] rd1_in,
				   input      [31:0] rd2_in,
				   input      [31:0] immex_in,
				   input             shiftl16_in,
				   input             regdst_in,  
				   input      [3:0]  alucontrol_in,   
				   input             alusrc_in,    
				   input			 branch_in,	
				   input			 branch_bne_in,	
				   input			 jump_in,	
				   input             memwrite_in,  
				   input             isjal_in,
				   input             regwrite_in,
				   input             memtoreg_in,
				   output reg [31:0] pc_plus4,
				   output reg [31:0] instr,
				   output reg [31:0] rd1,
				   output reg [31:0] rd2,
				   output reg [31:0] immex,
				   output reg        shiftl16,
				   output reg        regdst,  
				   output reg [3:0]  alucontrol,   
				   output reg        alusrc,   
				   output reg		 branch,	
				   output reg		 branch_bne,	
				   output reg		 jump,	
				   output reg        memwrite,  
				   output reg        isjal,
				   output reg        regwrite,
				   output reg        memtoreg
				   );
	
	always @(posedge clk) begin
		if (reset) begin
			pc_plus4   <= #`mydelay 1'b0;
			rd1       <= #`mydelay 1'b0;
			rd2       <= #`mydelay 1'b0;
			immex     <= #`mydelay 1'b0;
			instr     <= #`mydelay 1'b0;
			shiftl16  <= #`mydelay 1'b0;
			regdst    <= #`mydelay 1'b0;
			alucontrol<= #`mydelay 1'b0;
			alusrc    <= #`mydelay 1'b0;
			branch    <= #`mydelay 1'b0;
			branch_bne   <= #`mydelay 1'b0;
			jump      <= #`mydelay 1'b0;
			memwrite  <= #`mydelay 1'b0; 
			isjal  <= #`mydelay 1'b0;
			regwrite  <= #`mydelay 1'b0;
			memtoreg  <= #`mydelay 1'b0;
		end
		else begin
			pc_plus4   <= #`mydelay pc_plus4_in;
			rd1       <= #`mydelay rd1_in;
			rd2       <= #`mydelay rd2_in;
			immex     <= #`mydelay immex_in;
			instr     <= #`mydelay instr_in;
			shiftl16  <= #`mydelay shiftl16_in;
			regdst    <= #`mydelay regdst_in;  
			alucontrol<= #`mydelay alucontrol_in;   
			alusrc    <= #`mydelay alusrc_in;    
			branch    <= #`mydelay branch_in;
			branch_bne   <= #`mydelay branch_bne_in;
			jump      <= #`mydelay jump_in;
			memwrite  <= #`mydelay memwrite_in;  
			isjal  <= #`mydelay isjal_in;
			regwrite  <= #`mydelay regwrite_in;
			memtoreg  <= #`mydelay memtoreg_in;
		end
	end
endmodule

module EX_STAGE(input	[31:0]  instr,
					input [31:0]  rd1,
					input [31:0]  rd2,
					input [31:0]  foward_mem,
					input [31:0]  foward_wd,
					input [1:0]	  foward_rs_control,
					input [1:0]	  foward_rt_control,
					input [31:0]  signimm,
					input [31:0]  pc_plus4,
					input [31:0]  compare_pc_plus4,
					input		  shiftl16,
					input		  regdst,
					input [3:0]   alucontrol,
					input         alusrc,
					input         branch,
					input         branch_bne,
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
	  wire [31:0] pc_next_jr, pc_next_tmp;
	  wire [31:0] alu_a, alu_b, alu_b_temp;
	  wire [4:0]  writereg_tmp;
	  wire        pcsrc;
	  
	  assign write_data = alu_b_temp;
	  
	  shift_left_16 sl16(
		.a         (signimm[31:0]),
		.shiftl16  (shiftl16),
		.y         (signimmsh16[31:0]));
		
	  mux4 #(32) foward_for_rs(
		.d0 (rd1),
		.d1 (foward_mem),
		.d2 (foward_wd),
		.d3 (32'b0),
		.s	 (foward_rs_control),
		.y  (alu_a));
		
	  mux4 #(32) foward_for_rt(
		.d0 (rd2),
		.d1 (foward_mem),
		.d2 (foward_wd),
		.d3 (32'b0),
		.s	 (foward_rt_control),
		.y  (alu_b_temp));
		
	  mux2 #(32) alu_b_mux(
		.d0 (alu_b_temp),
		.d1 (signimmsh16[31:0]),
		.s  (alusrc),
		.y  (alu_b));
		
	  alu alu(
		.a       (alu_a),
		.b       (alu_b),
		.alucont (alucontrol),
		.result  (aluout),
		.zero    (aluzero));
		
	  mux2 #(5) decide_dst_reg(
		.d0  (instr[20:16]),
		.d1  (instr[15:11]),
		.s   (regdst),
		.y   (writereg_tmp));
		
	assign pcsrc = branch_bne ? (branch & !aluzero) : (branch & aluzero);
	
	sl2 immshift(
		.a (signimm),
		.y (signimmsh2));

	assign #`mydelay pc_branch = signimmsh2 + pc_plus4; 
	 
	mux2 #(32) pcbrmux(
		.d0  (compare_pc_plus4),
		.d1  (pc_branch),
		.s   (pcsrc),
		.y   (pc_next_tmp));
		
	jrmux jrmux(
		.d0       (pc_next_tmp),
		.d1       (alu_a),
		.alucontrol (alucontrol),
		.y       (pc_next_jr));
		
    mux2 #(32) pcmux(
		.d0   (pc_next_jr),
		.d1   ({pc_plus4[31:28], instr[25:0], 2'b00}),
		.s    (jump),
		.y    (pc_next));
		
	mux2 #(5) is_jal_regwrite_mux(
		.d0  (writereg_tmp),
		.d1  (5'b11111),
		.s   (isjal),
		.y   (writereg));
	  
endmodule

module EX_MEM(input 	         clk, reset,
				   input      [31:0] pc_plus4_in,
				   input             aluzero_in,
				   input      [31:0] aluout_in,
				   input      [31:0] write_data_in,
				   input      [4:0]  writereg_in,
				   input             memwrite_in,
				   input             isjal_in, 
				   input             regwrite_in, 
				   input             memtoreg_in, 
				   output reg [31:0] pc_plus4,
				   output reg [31:0] aluout,
				   output reg [31:0] write_data,
				   output reg [4:0]  writereg,
				   output reg        memwrite,
				   output reg        isjal, 
				   output reg        regwrite, 
				   output reg        memtoreg 
					);
				   
	always @(posedge clk) begin
		if (reset) begin
			pc_plus4     <= #`mydelay 1'b0;
			aluout       <= #`mydelay 1'b0;
			write_data   <= #`mydelay 1'b0;
			writereg     <= #`mydelay 1'b0;
			memwrite     <= #`mydelay 1'b0;
			isjal        <= #`mydelay 1'b0;
			regwrite     <= #`mydelay 1'b0;
			memtoreg     <= #`mydelay 1'b0;
		end
		else begin
			pc_plus4     <= #`mydelay pc_plus4_in;
			aluout       <= #`mydelay aluout_in;
			write_data   <= #`mydelay write_data_in;
			writereg     <= #`mydelay writereg_in;
			memwrite     <= #`mydelay memwrite_in;
			isjal        <= #`mydelay isjal_in;
			regwrite     <= #`mydelay regwrite_in;
			memtoreg     <= #`mydelay memtoreg_in;
		end
	end
endmodule

module MEM_WB(input 	         clk, reset,
				   input      [31:0] pc_plus4_in,
				   input      [31:0] readdata_in,
				   input      [31:0] aluout_in,
				   input      [4:0]  writereg_in,
				   input             isjal_in,
				   input             regwrite_in,
				   input             memtoreg_in,
				   output reg [31:0] pc_plus4,
				   output reg [31:0] readdata,
				   output reg [31:0] aluout,
				   output reg [4:0]  writereg,
				   output reg        isjal, 
				   output reg        regwrite, 
				   output reg        memtoreg 
				   );
	
	always @(posedge clk) begin
		if (reset) begin
			pc_plus4      <= #`mydelay 1'b0;
			readdata     <= #`mydelay 1'b0;
			aluout       <= #`mydelay 1'b0;
			writereg     <= #`mydelay 1'b0;
			isjal     <= #`mydelay 1'b0;
			regwrite     <= #`mydelay 1'b0;
			memtoreg     <= #`mydelay 1'b0;
		end
		else begin
			pc_plus4      <= #`mydelay pc_plus4_in;
			readdata     <= #`mydelay readdata_in;
			aluout       <= #`mydelay aluout_in;
			writereg     <= #`mydelay writereg_in;
			isjal     <= #`mydelay isjal_in;
			regwrite     <= #`mydelay regwrite_in;
			memtoreg     <= #`mydelay memtoreg_in;
		end
	end
endmodule

module WB_STAGE(input  [31:0] pc_plus4,
					input  [31:0] aluout,
					input  [31:0] readdata,
					input         isjal,
					input         memtoreg,
					output [31:0] result);
					
    wire [31:0] result_tmp;
	 
	 mux2 #(32) resmux(
		.d0 (aluout),
		.d1 (readdata),
		.s  (memtoreg),
		.y  (result_tmp));
		
    mux2 #(32) jalresmux(
		.d0 (result_tmp),
		.d1 (pc_plus4),
		.s  (isjal),
		.y  (result));
endmodule

module control_hazard_unit (input [3:0] alucontrol,
					  input 		 branch,
					  input 		 branch_bne,
					  input 		 jump,
					  input 		 aluzero,
					  output reg nullify);
  
  always @(*)
	begin
		if (aluzero == 1 && branch == 1 && branch_bne == 0) nullify <= 1'b1;
		else if (aluzero == 0 && branch == 1 && branch_bne == 1) nullify <= 1'b1;
		else if (alucontrol == 4'b1010) nullify <= 1'b1;
		else if (jump == 1) nullify <= 1'b1;
		else nullify <= 1'b0;
	end
	
endmodule

module forwarding_unit(input regwrite_wb, regwrite_mem,
						input [4:0] rs, rt,
						input [4:0] writereg_mem, writereg_wb,
						output reg[1:0] foward_rs_control, foward_rt_control);
						
  always @(regwrite_mem, regwrite_wb, writereg_mem, writereg_wb, rt, rs)
   begin
    if       (regwrite_mem && (writereg_mem != 0) && (writereg_mem == rs)) foward_rs_control = 2'b01;
	 else if  (regwrite_wb && (writereg_wb != 0) && (writereg_wb == rs)) foward_rs_control = 2'b10;
	 else 
		foward_rs_control = 2'b00;
	 if       (regwrite_mem && (writereg_mem != 0) && (writereg_mem == rt)) foward_rt_control = 2'b01;
	 else if  (regwrite_wb && (writereg_wb != 0) && (writereg_wb == rt)) foward_rt_control = 2'b10;
	 else 
		foward_rt_control = 2'b00;
   end
	
endmodule

module hazard_detect_unit(input [5:0]	op_ex,
							input [4:0]	load_reg,
							input [4:0]	rs_id,
							input [4:0]	rt_id,
							output reg	keep_write);
							
	always @(*)
		if ((op_ex == 6'b100011) && ((load_reg == rs_id) || (load_reg == rt_id))) keep_write = 1'b0;
		else keep_write = 1'b1;
	
endmodule

// ###### Minsoo Kim : End ######