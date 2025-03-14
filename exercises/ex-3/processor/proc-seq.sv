import proc_package::*;

module proc(instrIn, instrAddr, dataIn, dataOut, dataAddr, writeEnable, clk, reset);
    input TypeInstr instrIn;
    input TypeDataWord dataIn;
    input bit clk;
    input bit reset;
    output TypeInstrAddr instrAddr;
    output TypeDataWord dataOut;
    output TypeDataAddr dataAddr;
    output bit writeEnable;

    TypeArrayDataWord REG_FILE; //Registers R0 to R7: each 8 bit wide; R0 is not used
     enum {c_IF = 1, c_ID, c_EX, c_MEM, c_WB} CONTROL_STATE;

    TypeDataAddr DADDR;
    TypeInstrAddr PC;
    TypeDataWord A, B, DIN, DOUT, TEMP;
    TypeInstr IR;
    logic DATA_WRITE;

    assign instrAddr = PC;
    assign dataOut = DOUT;
    assign dataAddr = DADDR;
    assign writeEnable = DATA_WRITE;
    
    always @(posedge clk) begin
        TypeInstrAddr immediate_branch;
        TypeInstrAddr immediate_jump;
        TypeDataWord immediate_alu;
        TypeDataWord operandB;
        DATA_WRITE <= 0;

	if(reset) begin
	    CONTROL_STATE <= c_IF;
	    PC <= '{default: '0};
	    IR <= '{default: '0};
	end
	else begin
	    case(CONTROL_STATE)
		c_IF: begin //FETCH
		    PC <= PC + 2;
		    IR <= instrIn;
		    CONTROL_STATE <= c_ID;
		end
		c_ID: begin // DECODE
		    if(op1(IR) != c_REG_NULL)
			A <= REG_FILE[int'(op1(IR))];
		    else
			A <= c_NULL_WORD;

		    if(op2(IR) != c_REG_NULL)
			B <= REG_FILE[int'(op2(IR))];
		    else
			B <= c_NULL_WORD;

		    if(op1(IR) != c_REG_NULL)
			A <= REG_FILE[int'(op1(IR))];
		    else
			A <= c_NULL_WORD;
		
		    if(~IR[8]) // sign extension
			immediate_branch = {c_NULL_BRANCH, IR[8:0]};
		    else
			immediate_branch = {c_ONE_BRANCH, IR[8:0]};

		    if(~IR[11]) // sign extension
			immediate_jump = {c_NULL_JUMP, IR[11:0]};
		    else
			immediate_jump = {c_ONE_JUMP, IR[11:0]};

		    if(opcode(IR) == c_BRANCH) begin
			if(op1(IR) == c_REG_NULL)
			    PC <= PC + immediate_branch;
			else if(REG_FILE[int'(op1(IR))] == c_NULL_WORD)
			    PC <= PC + immediate_branch;
			CONTROL_STATE <= c_IF;
		    end
		    else if(opcode(IR) == c_JUMP) begin
			PC <= PC + immediate_jump;
			CONTROL_STATE <= c_IF;
		    end
		    else
			CONTROL_STATE <= c_EX;
		end

		c_EX: begin //EX
		    if(~IR[5])
			immediate_alu = {c_NULL_ALU, IR[5:0]};
		    else
			immediate_alu = {c_ONE_ALU, IR[5:0]};

		    if(opcode(IR) == c_STORE) begin
			DOUT <= B;
			DATA_WRITE <= 1;
		    end
		    else if (opcode(IR) == c_ALU_REG)
			operandB = B;
		    else if((opcode(IR) == c_ADD_IMM) || (opcode(IR) == c_OR_IMM))
			operandB = immediate_alu;

		    if(((opcode(IR) == c_ALU_REG) && (IR[2:0] == c_ADD)) || (opcode(IR) == c_ADD_IMM))
			TEMP <= A + operandB;

		    if(((opcode(IR) == c_ALU_REG) && (IR[2:0] == c_OR)) || (opcode(IR) == c_OR_IMM))
			TEMP <= A | operandB;

		    if((opcode(IR) == c_LOAD) || (opcode(IR) == c_STORE))
			DADDR <= A + immediate_alu;

		    CONTROL_STATE <= c_MEM;
		end

		c_MEM: begin
		    if(opcode(IR) == c_LOAD)
			DIN <= dataIn;
		    CONTROL_STATE <= c_WB;
		end

		c_WB: begin
		    if((opcode(IR) == c_LOAD) && (op2(IR) != c_REG_NULL))
			REG_FILE[int'(op2(IR))] <= DIN;
		    else if((opcode(IR) == c_ALU_REG) && (op3(IR) != c_REG_NULL))
			REG_FILE[int'(op3(IR))] <= TEMP;
		    else if(((opcode(IR) == c_ADD_IMM) || (opcode(IR) == c_OR_IMM)) && (op2(IR) != c_REG_NULL))
			REG_FILE[int'(op2(IR))] <= TEMP;
		    CONTROL_STATE <= c_IF;
		end
	    endcase
	end
    end
endmodule