package proc_package;

    typedef bit [15:0] TypeInstr;
    
    typedef bit [15:0] TypeInstrAddr;
    
    typedef bit [7:0] TypeDataAddr;
    typedef bit [7:0] TypeDataWord;

    typedef bit [2:0] TypeRegAddr;
    typedef bit [8:0] TypeExInstr; //opcode and op1 not used anymore

    typedef bit [3:0] TypeOpcode;
    typedef bit [2:0] TypeAluOp;

    typedef TypeDataWord [7:0]TypeArrayDataWord; //8 Registers -- 1byte each
    
    parameter TypeOpcode c_ALU_REG = 4'b0001;
    
    parameter TypeOpcode c_ADD_IMM = 4'b0010;
    parameter TypeOpcode c_OR_IMM = 4'b0011;

    parameter TypeOpcode c_LOAD = 4'b0100;
    parameter TypeOpcode c_STORE = 4'b0101;

    parameter TypeOpcode c_JUMP = 4'b0110;
    parameter TypeOpcode c_BRANCH = 4'b0111;

    parameter TypeAluOp c_ADD = 3'b001;
    parameter TypeAluOp c_OR = 3'b010;

    parameter bit [2:0] c_REG_NULL = '{default: '0};
    parameter bit [7:0] c_NULL_WORD = '{default: '0};

    parameter bit [1:0] c_NULL_ALU = '{default: '0};
    parameter bit [1:0] c_ONE_ALU = '{default: '1};

    parameter bit [6:0] c_NULL_BRANCH = '{default: '0};
    parameter bit [6:0] c_ONE_BRANCH = '{default: '1};

    parameter bit [3:0] c_NULL_JUMP = '{default: '0};
    parameter bit [3:0] c_ONE_JUMP = '{default: '1};

    function unsigned [3:0] opcode(unsigned [15:0]ir);
        return ir[15:12];
    endfunction

    function unsigned [2:0] op1(unsigned [15:0]ir);
        return ir[11:9];
    endfunction

    function unsigned [2:0] op2(unsigned [15:0]ir);
        return ir[8:6];
    endfunction

    function unsigned [2:0] op3(unsigned [15:0]ir);
        return ir[5:3];
    endfunction
endpackage