First and foremost, run `git submodule update --init`. Then use `make` or `make all` to build both the MPC and zk-SNARK implementations. Use `make common_master_mpc` or `make common_master_zksnark`, respectively, to build either one.

To run the zk-SNARK implementation, use `./common_master`. That will print some help to get started.

To run the MPC implementation, use `./path/to/mp-spdz/Scripts/mascot.sh common_master`.

zk-SNARK example:

```
./common_master -g    # generate proving and verifying keys
./common_master -p -m 1 -i 2 -j 3 -h1 ae4b3280e56e2faf83f414a6e3dabe9d5fbe18976544c05fed121accb85b53fc -h2 b744d600fbe3853702978ec726c166d26274fe7b09b2c600ddf2d7d895667b24 # generate the proof
./common_master -v -h1 ae4b3280e56e2faf83f414a6e3dabe9d5fbe18976544c05fed121accb85b53fc -h2 b744d600fbe3853702978ec726c166d26274fe7b09b2c600ddf2d7d895667b24 # verify the proof
echo $? # prints 0 if verification successful, 1 otherwise
```

The master value is 16 bits, the indices 8 bits, so `-m 1 -i 2 -j 3` corresponds to hashing `0x000102` and `0x000103`.
