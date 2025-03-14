module test_ex1_1;

   logic clk, rst, validi;
   
   logic [31:0] data_in;
   wire 	valido;
   wire [31:0]  data_out;
   
   ex1_1 dut 
     (
      clk, rst, validi,
      data_in,
      valido,
      data_out
      );
   
   bind ex1_1 ex1_1_property ex1_1_bind 
     (
      clk, rst, validi,
      data_in,
      valido,
      data_out
      );

   initial begin
      clk=1'b0;
      set_stim;
      @(posedge clk); $finish(2);
   end

   always @(posedge clk) 
     $display($stime,,,"rst=%b clk=%b validi=%b DIN=%0d valido=%b DOUT=%0d",
	      rst, clk, validi, data_in, valido, data_out);
   
   always #5 clk=!clk;

   task set_stim;
      rst=1'b0; validi=0'b1; data_in=32'b1;
      @(negedge clk) rst=1;
      @(negedge clk) rst=0;
      
      @(negedge clk); validi=1'b0; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b0; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b0; data_in+=32'b1;
      @(negedge clk); validi=1'b0; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b0; data_in+=32'b1;
      
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b0; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b0; data_in+=32'b1;
      @(negedge clk); validi=1'b0; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b1; data_in+=32'b1;
      @(negedge clk); validi=1'b0; data_in+=32'b1;
 
      @(negedge clk);
   endtask

endmodule
