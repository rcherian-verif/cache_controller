#Cache controller
1. The design for a cache controller along with the tb is present

Specifications

1. Direct mapped cache
2. Write-back policy with Write-allocate
3. Block Size : 4 words (16 bytes)
4. Cache Size : 16 KiB
5. Valid bit and dirty bit per block


#Run command
xrun -sv cache.v cache_tb.sv
#Run command with GUI
xrun -sv -access +rwc -gui cache.v cache_tb.sv
