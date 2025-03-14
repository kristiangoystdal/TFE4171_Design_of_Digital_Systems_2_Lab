//Make your struct here
typedef struct {
    bit [7:0] a;
    bit [7:0] b;
    bit [2:0] op;
} data_t;

class alu_data;
    // Initialize your struct here
    data_t data;

    function new();
        data.a = $urandom_range(seed, c1);
        data.b = $urandom_range(seed, c2);
        data.op = $urandom_range(seed, c3);
    endfunction

    // Class methods (tasks) go here
    task get(output bit [7:0] a, output bit [7:0] b, output bit [2:0] op);
        a = data.a;
        b = data.b;
        op = data.op;
    endtask

    // Constraints
    int seed = 100;
    int c1 = 127;
    int c2 = 255;
    int c3 = 6;

endclass: alu_data

