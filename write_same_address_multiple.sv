//author - rcheriax_verif
//Test to write a multiple data into the same address
//Fo run commands please refer the README doc
//PLEASE NOTE TEST IS NOT CLEAN, NEED SOME MORE WORK
//Regressible : No

module test_write_multiple;

bit [31:0] address;
bit [127:0] write_data;
bit [1:0] count;

initial begin

	cache_controller_tb.reset_values();
	std::randomize (address) with { address inside {'h19177182,'h20d2,'hc1,'h2f6991b2,'h61,'h5d8efe30,'h9043f222};};

	count =2;
	write_data = $urandom();
	$display("Count is %0d",count);
	for(int i=0; i <  count; i++)
	begin
        #10ns;
	$display("Address is %0h",address);

        write_data = write_data +5;
        $display("Data being written donw is %0h",write_data);
        cache_controller_tb.write_cpu(address,write_data);
	cache_controller_tb.read_cpu(address);
        #5ns;
        wait(cache_controller_tb.cache_ready == 1)
        //Check whether the Data we have written is the same
	//data being read out
        $display("Data read is %0h",cache_controller_tb.cpu_req_dataout);
	if(cache_controller_tb.cpu_req_dataout == write_data)
                $display("Read data is correct as write data");
         else
         begin
                 $display("Test failed. Please deubg");
		 $fatal;
         end
         end     
         $display("Test is over");
	 $finish;

	end

	endmodule
