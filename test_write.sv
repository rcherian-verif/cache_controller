//Author - rcheriax-verif
//This test writes a random data to a random address and then reads from the
//same address. It also checks whether the read data is the same as the data
//that was written
//For run commands please check the README file
//Regressible : Yes

module test_write;


bit [31:0] address;
bit [127:0] write_data;
bit [31:0]  write_data_block;
bit [1:0] block_offset;



initial begin
        cache_controller_tb.reset_values();
        address = $urandom();
	write_data = $urandom();
        std::randomize ( write_data ) with { write_data dist {[0:'hFFFFFFFF]:/20,['hFFFFFFFF:'hFFFFFFFFFFFFFFFF]:/20,['hFFFFFFFFFFFFFFFFF:'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF]:/20};};
	block_offset = address[3:2];
	$display("Blockoffset is %0d",block_offset);
	case ( block_offset)
		2'b00 : write_data_block = write_data[31:0];
		2'b01 : write_data_block = write_data[63:32];
		2'b10 : write_data_block = write_data[95:64];
		2'b11 : write_data_block = write_data[127:96];
		default: write_data_block = 0;
        endcase




	$display("Address and data  chosen is %0h and %0h",address,write_data);
    	cache_controller_tb.write_cpu(address,write_data);



        cache_controller_tb.read_cpu(address);
	#5ns;
        wait(cache_controller_tb.cache_ready == 1)


	$display("Data read is %0h",cache_controller_tb.cpu_req_dataout);
	$display("Write data block is %0h",write_data_block);
	if(cache_controller_tb.cpu_req_dataout == write_data_block)
		$display("Read data is correct as write data");
	 else
	 begin
		 $display("Test failed. Please deubg");
	 end
         #20ns;
	 $display("Test is over");
         $finish;



end

endmodule
