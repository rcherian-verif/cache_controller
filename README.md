#Cache controller - As part of the dissertation done in partial fullfillment of WILP M.Tech Microelectronics degree programme
1.Design of the Cache controller along with the TB and currently 2 tests
2. SVA and Coverage bins added as well
To run on Cadence Xcelium, please find the below run commands
#Basic Run Command
xrun -sv cache.v tb_cache.v &
#Run command with test
xrun -sv cache.v tb_cache.sv test_write.sv -access rwc &
#Run command with GUI
xrun -sv cache.v tb_cache.sv test_write.sv -access rwc -gui &i
#Run command with Coverage enabled
run -sv cache.v tb_cache.sv test_write.sv -access rwc -coverage all &
#Run command with random seed
xrun -sv cache.v tb_cache.sv test_write.sv -access rwc -seed random &
#Run command with a particular seedi
xrun -sv cache.v tb_cache.sv test_write.sv -access rwc -seed -2129151955 &
