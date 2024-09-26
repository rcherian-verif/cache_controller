module cache_controller (

    input clk,

    input rst_n,

    // CPU Interface

    input [31:0] cpu_req_addr,

    input [31:0] cpu_req_datain,

    output reg [31:0] cpu_req_dataout,

    input cpu_req_rw,       // 1=write, 0=read

    input cpu_req_valid,

    output reg cache_ready,

    // Memory Interface

    output reg [31:0] mem_req_addr,

    input [127:0] mem_req_datain,

    output reg [127:0] mem_req_dataout,

    output reg mem_req_rw,

    output reg mem_req_valid,

    input mem_req_ready

);



// Parameters

parameter IDLE        = 2'b00;

parameter COMPARE_TAG = 2'b01;

parameter WRITE_BACK  = 2'b10;

parameter ALLOCATE    = 2'b11;



// Cache Parameters

parameter CACHE_SIZE = 16 * 1024;  // 16KiB

parameter BLOCK_SIZE = 16;         // 4 words = 16 bytes

parameter NUM_BLOCKS = CACHE_SIZE / BLOCK_SIZE;  // 1024 blocks

parameter INDEX_BITS = 10;         // log2(1024) = 10 bits for index

parameter OFFSET_BITS = 4;         // 16-byte blocks, so 4 bits for offset

parameter TAG_BITS = 32 - (INDEX_BITS + OFFSET_BITS);



// FSM State

reg [1:0] state, next_state;



// Cache memories

reg [TAG_BITS-1:0] tag_mem [NUM_BLOCKS-1:0];   // Tag memory

reg [127:0] data_mem [NUM_BLOCKS-1:0];         // Data memory

reg valid_mem [NUM_BLOCKS-1:0];                // Valid bits

reg dirty_mem [NUM_BLOCKS-1:0];                // Dirty bits



// Internal signals

wire [TAG_BITS-1:0] addr_tag;

wire [INDEX_BITS-1:0] addr_index;

wire [OFFSET_BITS-1:0] addr_offset;

reg [127:0] cache_block;

reg hit;

reg [31:0] write_data;

reg [127:0] new_block;

reg write_hit;



// Address Breakdown

assign addr_tag = cpu_req_addr[31:INDEX_BITS + OFFSET_BITS];

assign addr_index = cpu_req_addr[INDEX_BITS + OFFSET_BITS - 1:OFFSET_BITS];

assign addr_offset = cpu_req_addr[OFFSET_BITS - 1:0];



// Initializing Cache (Optional)

integer i;

initial begin

    for (i = 0; i < NUM_BLOCKS; i = i + 1) begin

        valid_mem[i] = 1'b0;

        dirty_mem[i] = 1'b0;

        tag_mem[i] = {TAG_BITS{1'b0}};

        data_mem[i] = 128'd0;

    end

    state = IDLE;

end



// FSM and Cache Controller

always @(posedge clk or negedge rst_n) begin

    if (!rst_n) begin

        // Reset state

        state <= IDLE;

        cache_ready <= 1'b0;

        mem_req_valid <= 1'b0;

        mem_req_rw <= 1'b0;

        mem_req_addr <= 32'd0;

        mem_req_dataout <= 128'd0;

        cpu_req_dataout <= 32'd0;

    end else begin

        state <= next_state;



        case (state)

            IDLE: begin

                cache_ready <= 1'b0;

                if (cpu_req_valid) begin

                    next_state <= COMPARE_TAG;

                end else begin

                    next_state <= IDLE;

                end

            end



            COMPARE_TAG: begin

                // Check for hit

                hit <= valid_mem[addr_index] && (tag_mem[addr_index] == addr_tag);

                cache_block <= data_mem[addr_index];

                if (hit) begin

                    // Hit

                    if (cpu_req_rw) begin

                        // Write hit

                        write_hit <= 1'b1;

                        // Update cache block

                        case (addr_offset[3:2])

                            2'b00: data_mem[addr_index][31:0] <= cpu_req_datain;

                            2'b01: data_mem[addr_index][63:32] <= cpu_req_datain;

                            2'b10: data_mem[addr_index][95:64] <= cpu_req_datain;

                            2'b11: data_mem[addr_index][127:96] <= cpu_req_datain;

                        endcase

                        // Set dirty bit

                        dirty_mem[addr_index] <= 1'b1;

                        // Update tag and valid bit (even though they may not change)

                        tag_mem[addr_index] <= addr_tag;

                        valid_mem[addr_index] <= 1'b1;

                        cache_ready <= 1'b1;

                        next_state <= IDLE;

                    end else begin

                        // Read hit

                        case (addr_offset[3:2])

                            2'b00: cpu_req_dataout <= data_mem[addr_index][31:0];

                            2'b01: cpu_req_dataout <= data_mem[addr_index][63:32];

                            2'b10: cpu_req_dataout <= data_mem[addr_index][95:64];

                            2'b11: cpu_req_dataout <= data_mem[addr_index][127:96];

                        endcase

                        cache_ready <= 1'b1;

                        next_state <= IDLE;

                    end

                end else begin

                    // Miss

                    if (dirty_mem[addr_index]) begin

                        // Dirty block - need to write back

                        next_state <= WRITE_BACK;

                        mem_req_addr <= {tag_mem[addr_index], addr_index, {OFFSET_BITS{1'b0}}};

                        mem_req_dataout <= data_mem[addr_index];

                        mem_req_rw <= 1'b1; // Write to memory

                        mem_req_valid <= 1'b1;

                    end else begin

                        // Clean block - can allocate

                        next_state <= ALLOCATE;

                        mem_req_addr <= {addr_tag, addr_index, {OFFSET_BITS{1'b0}}};

                        mem_req_rw <= 1'b0; // Read from memory

                        mem_req_valid <= 1'b1;

                    end

                    // Update tag and valid bit

                    tag_mem[addr_index] <= addr_tag;

                    valid_mem[addr_index] <= 1'b1;

                end

            end



            WRITE_BACK: begin

                if (mem_req_ready) begin

                    mem_req_valid <= 1'b0;

                    // After write-back, proceed to allocate

                    next_state <= ALLOCATE;

                    mem_req_addr <= {addr_tag, addr_index, {OFFSET_BITS{1'b0}}};

                    mem_req_rw <= 1'b0; // Read from memory

                    mem_req_valid <= 1'b1;

                end else begin

                    next_state <= WRITE_BACK;

                end

            end



            ALLOCATE: begin

                if (mem_req_ready) begin

                    mem_req_valid <= 1'b0;

                    // Load the new block into cache

                    data_mem[addr_index] <= mem_req_datain;

                    dirty_mem[addr_index] <= 1'b0; // Freshly loaded block is clean

                    // If the request was a write, update the block

                    if (cpu_req_rw) begin

                        // Write to the appropriate word in the block

                        case (addr_offset[3:2])

                            2'b00: data_mem[addr_index][31:0] <= cpu_req_datain;

                            2'b01: data_mem[addr_index][63:32] <= cpu_req_datain;

                            2'b10: data_mem[addr_index][95:64] <= cpu_req_datain;

                            2'b11: data_mem[addr_index][127:96] <= cpu_req_datain;

                        endcase

                        dirty_mem[addr_index] <= 1'b1; // Set dirty bit

                    end else begin

                        // Read - provide data to CPU

                        case (addr_offset[3:2])

                            2'b00: cpu_req_dataout <= mem_req_datain[31:0];

                            2'b01: cpu_req_dataout <= mem_req_datain[63:32];

                            2'b10: cpu_req_dataout <= mem_req_datain[95:64];

                            2'b11: cpu_req_dataout <= mem_req_datain[127:96];

                        endcase

                    end

                    cache_ready <= 1'b1;

                    next_state <= IDLE;

                end else begin

                    next_state <= ALLOCATE;

                end

            end



            default: begin

                next_state <= IDLE;

            end

        endcase

    end

end



endmodule


