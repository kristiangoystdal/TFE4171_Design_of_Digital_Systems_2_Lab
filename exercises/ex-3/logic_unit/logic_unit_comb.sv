// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------

`default_nettype none

module logic_unit_comb #(
    parameter WIDTH = 16
)(
    input  logic [WIDTH-1:0] req_vec,
    input  logic             valid,
    output logic             out,
    output logic             done
);

    logic or_result;

    always_comb begin
        or_result = req_vec[0];
        for (int i = 1; i < WIDTH-1; i++) begin
            or_result = or_result | req_vec[i];
        end
    end

    assign out = or_result & req_vec[WIDTH-1];
    assign done = valid;    

endmodule
