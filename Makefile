MP-SPDZ=mp-spdz-0.2.5
CURVE=CURVE_ALT_BN128

all: common_master_zksnark common_master_mpc

common_master_zksnark: common_master_zksnark.o
	g++ common_master.o -o common_master -Llibsnark/build/libsnark/ -Llibsnark/build/depends/libff/libff/ -lsnark -lff -lgmp -lgmpxx 
common_master_zksnark.o: common_master.cpp libsnark
	g++ common_master.cpp -o common_master.o -c -Ilibsnark -Ilibsnark/depends/libff -Ilibsnark/depends/libfqfft -D$(CURVE) -g

libsnark:
	cd libsnark && git submodule update --init
	if [ ! -d "libsnark/build" ]; then mkdir libsnark/build && cd libsnark/build && cmake -DWITH_PROCPS=OFF .. && make; fi

common_master_mpc: $(MP-SPDZ)/Programs/Circuits/Keccak_f.txt
	cp common_master.mpc $(MP-SPDZ)/Programs/Source && cd $(MP-SPDZ) && ./compile.py common_master

$(MP-SPDZ):
	if [ ! -d "$@" ]; then wget https://github.com/data61/MP-SPDZ/releases/download/v0.2.5/mp-spdz-0.2.5.tar.xz && tar xf mp-spdz-0.2.5.tar.xz && rm mp-spdz-0.2.5.tar.xz; fi

$(MP-SPDZ)/Programs/Circuits/Keccak_f.txt: $(MP-SPDZ)
	if [ ! -e "$@" ]; then cd $(MP-SPDZ)/Programs/Circuits && wget https://homes.esat.kuleuven.be/~nsmart/MPC/Keccak_f.txt; fi

clean:
	rm -rf libsnark/build
	rm -rf $(MP-SPDZ)
	rm -f common_master *.o

.PHONY: all libsnark clean
