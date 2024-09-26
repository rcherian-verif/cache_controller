module tb_cache_controller;



reg clk;

reg rst_n;

// CPU Interface

reg [31:0] cpu_req_addr;

reg [31:0] cpu_req_datain;

wire [31:0] cpu_req_dataout;

reg cpu_req_rw;       // 1=write, 0=read

reg cpu_req_valid;

wire cache_ready;

// Memory Interface

wire [31:0] mem_req_addr;

reg [127:0] mem_req_datain;

wire [127:0] mem_req_dataout;

wire mem_req_rw;

wire mem_req_valid;

reg mem_req_ready;



// Instantiate the cache controller

cache_controller uut (

    .clk(clk),

    .rst_n(rst_n),

    .cpu_req_addr(cpu_req_addr),

    .cpu_req_datain(cpu_req_datain),

    .cpu_req_dataout(cpu_req_dataout),

    .cpu_req_rw(cpu_req_rw),

    .cpu_req_valid(cpu_req_valid),

    .cache_ready(cache_ready),

    .mem_req_addr(mem_req_addr),

    .mem_req_datain(mem_req_datain),

    .mem_req_dataout(mem_req_dataout),

    .mem_req_rw(mem_req_rw),

    .mem_req_valid(mem_req_valid),

    .mem_req_ready(mem_req_ready)

);



// Clock generation

initial clk = 0;

always #5 clk = ~clk; // 100MHz clock



// Test stimulus

initial begin

    // Initialize signals

    rst_n = 0;

    cpu_req_addr = 32'd0;

    cpu_req_datain = 32'd0;

    cpu_req_rw = 1'b0;

    cpu_req_valid = 1'b0;

    mem_req_datain = 128'd0;

    mem_req_ready = 1'b0;



    // Reset the cache

    #10;

    rst_n = 1;



    // Test sequence

    // Test 1: Read miss, should allocate from memory

    #10;

    cpu_req_addr = 32'h0000_1000;

    cpu_req_rw = 1'b0; // Read

    cpu_req_valid = 1'b1;

    #10;

    cpu_req_valid = 1'b0;



    // Simulate memory ready after some cycles

    #30;

    mem_req_ready = 1'b1;

    mem_req_datain = 128'hAAAA_AAAA_BBBB_BBBB_CCCC_CCCC_DDDD_DDDD; // Data from memory

    #10;

    mem_req_ready = 1'b0;



    // Wait for cache to be ready

    #20;



    // Test 2: Write hit

    #10;

    cpu_req_addr = 32'h0000_1000;

    cpu_req_datain = 32'h1234_5678;

    cpu_req_rw = 1'b1; // Write

    cpu_req_valid = 1'b1;

    #10;

    cpu_req_valid = 1'b0;



    // Wait for cache to be ready

    #20;



    // Test 3: Read hit

    #10;

    cpu_req_addr = 32'h0000_1000;

    cpu_req_rw = 1'b0; // Read

    cpu_req_valid = 1'b1;

    #10;

    cpu_req_valid = 1'b0;



    // Wait for cache to be ready

    #20;



    // Test 4: Write miss with dirty block (should write back)

    #10;

    cpu_req_addr = 32'h0000_2000; // Different block index

    cpu_req_datain = 32'hDEAD_BEEF;

    cpu_req_rw = 1'b1; // Write

    cpu_req_valid = 1'b1;

    #10;

    cpu_req_valid = 1'b0;



    // Simulate memory ready for write-back

    #30;

    mem_req_ready = 1'b1;

    #10;

    mem_req_ready = 1'b0;



    // Simulate memory ready for allocate

    #20;

    mem_req_ready = 1'b1;

    mem_req_datain = 128'h1111_1111_2222_2222_3333_3333_4444_4444;

    #10;

    mem_req_ready = 1'b0;



    // Wait for cache to be ready

    #20;



    // Finish simulation

    #50;

    $finish;

end



endmodule


