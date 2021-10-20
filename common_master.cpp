/*
 * H(m || i) == h1 && H(m || j) == h2
 */

#include <iostream>
#include <string>
#include <cstdlib>
#include <cstdint>
#include <fstream>
#include <getopt.h>

#include <libff/common/utils.hpp>
#include <libff/common/serialization.hpp>
#include <libff/algebra/fields/fp.hpp>

#include <libsnark/gadgetlib1/protoboard.hpp>
#include <libsnark/gadgetlib1/gadget.hpp>
#include <libsnark/gadgetlib1/gadgets/hashes/sha256/sha256_gadget.hpp>
#include <libsnark/common/default_types/r1cs_ppzksnark_pp.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>

using FieldT = libff::Fr<libsnark::default_r1cs_ppzksnark_pp>;
using root_t = std::uint16_t;
using index_t = std::uint8_t;

#ifndef NDEBUG

std::ostream &operator<<(std::ostream &out, const libff::bit_vector &v)
{
	for (auto i : v)
		out << i;
	return out;
}

#endif

enum class task_type { none, generate, prove, verify };

template<typename FieldT>
class hash_cmp_gadget : public libsnark::gadget<FieldT> {
	libsnark::pb_variable_array<FieldT> supplied_bit_array;
	libsnark::block_variable<FieldT> block;
	libsnark::digest_variable<FieldT> computed_hash;
	libsnark::sha256_two_to_one_hash_gadget<FieldT> hash_gadget;
	libsnark::dual_variable_gadget<FieldT> computed_packer1, computed_packer2;
	libsnark::dual_variable_gadget<FieldT> supplied_packer1, supplied_packer2;
	libsnark::pb_variable<FieldT> less1, less2, less_or_eq1, less_or_eq2;
	libsnark::comparison_gadget<FieldT> cmp1, cmp2;
	libsnark::pb_variable_array<FieldT> conjunction_inputs;
	public:
	libsnark::pb_variable<FieldT> equal; // equal must be before conjunction to ensure that its index is not overwritten in conjunction's constructor
	private:
	libsnark::conjunction_gadget<FieldT> conjunction;

	public:
	hash_cmp_gadget(libsnark::protoboard<FieldT> &pb, const libsnark::pb_variable_array<FieldT>& supplied_bit_array, const libsnark::block_variable<FieldT> &block, const std::string &annotation_prefix = "") :
		libsnark::gadget<FieldT>{pb, annotation_prefix},
		supplied_bit_array{supplied_bit_array},
		block{block},
		computed_hash{this->pb, libsnark::SHA256_digest_size, FMT(annotation_prefix, "computed_hash")},
		hash_gadget{this->pb, block.block_size, block, computed_hash, FMT(annotation_prefix, "hash_gadget")},
		computed_packer1{this->pb, {computed_hash.bits.begin(), computed_hash.bits.begin() + 128}, FMT(annotation_prefix, "computed_packer1")},
		computed_packer2{this->pb, {computed_hash.bits.begin() + 128, computed_hash.bits.end()}, FMT(annotation_prefix, "computed_packer2")},
		supplied_packer1{this->pb, {supplied_bit_array.begin(), supplied_bit_array.begin() + 128}, FMT(annotation_prefix, "supplied_packer1")},
		supplied_packer2{this->pb, {supplied_bit_array.begin() + 128, supplied_bit_array.end()}, FMT(annotation_prefix, "supplied_packer2")},
		cmp1{pb, 128, computed_packer1.packed, supplied_packer1.packed,
			(less1.allocate(this->pb, FMT(annotation_prefix, "less1")), less1),
			(less_or_eq1.allocate(this->pb, FMT(annotation_prefix, "less_or_eq1")), less_or_eq1),
			FMT("", "cmp1")},
		cmp2{pb, 128, computed_packer2.packed, supplied_packer2.packed,
			(less2.allocate(this->pb, FMT(annotation_prefix, "less2")), less2),
			(less_or_eq2.allocate(this->pb, FMT(annotation_prefix, "less_or_eq2")), less_or_eq2),
			FMT("", "cmp2")},
		conjunction{pb,
			(conjunction_inputs.allocate(this->pb, 4, FMT(annotation_prefix, "conjunction_inputs")), conjunction_inputs),
			(equal.allocate(this->pb, "equal"), equal),
			FMT(annotation_prefix, "conjunction")}
	{}

	void generate_r1cs_constraints()
	{
		computed_hash.generate_r1cs_constraints();
		hash_gadget.generate_r1cs_constraints();

		computed_packer1.generate_r1cs_constraints(true);
		computed_packer2.generate_r1cs_constraints(true);

		supplied_packer1.generate_r1cs_constraints(true);
		supplied_packer2.generate_r1cs_constraints(true);

		cmp1.generate_r1cs_constraints();
		cmp2.generate_r1cs_constraints();

		this->pb.add_r1cs_constraint(libsnark::r1cs_constraint<FieldT>(1, {{less1, conjunction_inputs[0]}}, 1), ""); // ensures negation
		this->pb.add_r1cs_constraint(libsnark::r1cs_constraint<FieldT>(1, {{less2, conjunction_inputs[1]}}, 1), ""); // ensures negation
		this->pb.add_r1cs_constraint(libsnark::r1cs_constraint<FieldT>(1, {{less_or_eq1}}, {{conjunction_inputs[2]}}), ""); // ensures equality
		this->pb.add_r1cs_constraint(libsnark::r1cs_constraint<FieldT>(1, {{less_or_eq2}}, {{conjunction_inputs[3]}}), ""); // ensures equality

		conjunction.generate_r1cs_constraints();
	}

	void generate_r1cs_witness()
	{
		hash_gadget.generate_r1cs_witness();

		computed_packer1.generate_r1cs_witness_from_bits();
		computed_packer2.generate_r1cs_witness_from_bits();
		supplied_packer1.generate_r1cs_witness_from_bits();
		supplied_packer2.generate_r1cs_witness_from_bits();

		cmp1.generate_r1cs_witness();
		cmp2.generate_r1cs_witness();

#ifndef NDEBUG
		std::cout << "FIRST HALF = <:" << this->pb.val(cmp1.less) << " <=:" << this->pb.val(cmp1.less_or_eq) << '\n';
		std::cout << "SECOND HALF = <:" << this->pb.val(cmp2.less) << " <=:" << this->pb.val(cmp2.less_or_eq) << '\n';
#endif

		this->pb.val(conjunction_inputs[0]) = this->pb.val(less1) == FieldT::zero() ? FieldT::one() : FieldT::zero();
		this->pb.val(conjunction_inputs[1]) = this->pb.val(less2) == FieldT::zero() ? FieldT::one() : FieldT::zero();
		this->pb.val(conjunction_inputs[2]) = this->pb.val(less_or_eq1);
		this->pb.val(conjunction_inputs[3]) = this->pb.val(less_or_eq2);

		conjunction.generate_r1cs_witness();
	}
};

template<typename FieldT>
class common_master_gadget : public libsnark::gadget<FieldT> {
	libsnark::block_variable<FieldT> ri_block;
	libsnark::block_variable<FieldT> rj_block;
	hash_cmp_gadget<FieldT> h1_gadget, h2_gadget;
	libsnark::pb_variable_array<FieldT> conjunction_inputs;
	public:
	libsnark::pb_variable<FieldT> output; // output must be before conjunction to ensure that its index is not overwritten in conjunction's constructor
	private:
	libsnark::conjunction_gadget<FieldT> conjunction;

	public:

	common_master_gadget(libsnark::protoboard<FieldT> &pb, const libsnark::pb_variable_array<FieldT> &h1_array, const libsnark::pb_variable_array<FieldT> &h2_array, const std::string &annotation_prefix = "") :
		libsnark::gadget<FieldT>{pb, annotation_prefix},
		ri_block{this->pb, libsnark::SHA256_block_size, ""},
		rj_block{this->pb, libsnark::SHA256_block_size, ""},
		h1_gadget{pb, h1_array, ri_block},
		h2_gadget{pb, h2_array, rj_block},
		conjunction{pb, (conjunction_inputs.allocate(pb, 2, "conjunction_inputs"), conjunction_inputs), (output.allocate(pb, "output"), output), "conjunction"}
	{}

	void generate_r1cs_constraints()
	{
		// guarantee that concatenated values start with the same r
		for (std::size_t i = 0; i < sizeof(root_t) * CHAR_BIT; ++i)
			this->pb.add_r1cs_constraint(libsnark::r1cs_constraint<FieldT>{1, {{ri_block.bits[i]}}, {{rj_block.bits[i]}}});

		h1_gadget.generate_r1cs_constraints();
		h2_gadget.generate_r1cs_constraints();

		this->pb.add_r1cs_constraint(libsnark::r1cs_constraint<FieldT>(1, {{conjunction_inputs[0]}}, {{h1_gadget.equal}}), ""); // ensures equality
		this->pb.add_r1cs_constraint(libsnark::r1cs_constraint<FieldT>(1, {{conjunction_inputs[1]}}, {{h2_gadget.equal}}), ""); // ensures equality

		conjunction.generate_r1cs_constraints();

		this->pb.add_r1cs_constraint(libsnark::r1cs_constraint<FieldT>{1, {{output}}, 1});
	}

	void generate_r1cs_witness(const libff::bit_vector &ri_block_bits, const libff::bit_vector &rj_block_bits)
	{
		ri_block.generate_r1cs_witness(ri_block_bits);
		rj_block.generate_r1cs_witness(rj_block_bits);

		h1_gadget.generate_r1cs_witness();
		h2_gadget.generate_r1cs_witness();

		this->pb.val(conjunction_inputs[0]) = this->pb.val(h1_gadget.equal);
		this->pb.val(conjunction_inputs[1]) = this->pb.val(h2_gadget.equal);

		conjunction.generate_r1cs_witness();

#ifndef NDEBUG
		std::cout << "OUTPUT = " << this->pb.val(output) << '\n';
#endif
	}
};

/*
 * Print usage. Standard thing among Unix/Linux applications.
 */
void usage(const std::string &program_name)
{
	std::cout << "Usage: " << program_name << " -g [-pk PROVING_KEY_PATH] [-vk VERIFYING_KEY_PATH]\n";
	std::cout << "   or: " << program_name << " -p -h1 HASH1 -h2 HASH2 -m MASTER_KEY -i INDEX1 -j INDEX2 [-pk PROVING_KEY_PATH] [-vk VERIFYING_KEY_PATH]" \
		" [-proof PROOF_PATH]\n";
	std::cout << "   or: " << program_name << " -v -h1 HASH1 -h2 HASH2 [-vk VERIFYING_KEY_PATH] [-proof PROOF_PATH]\n";
	std::cout <<
R"(Generate a preprocessed zk-SNARK keypair or a proof or verify one for the pseudocode
    SHA256(MASTER_KEY || INDEX1) == HASH1 && SHA256(MASTER_KEY || INDEX2) == HASH2
where || is bitwise concatenation.

  -g                             generate keypair
  -p                             generate proof
  -v                             verify proof
      --h1=HASH1                 first hash
      --h2=HASH2                 second hash
  -m, --master=MASTER_KEY        master key
  -i, --index1=INDEX1            first index
  -j, --index2=INDEX2            second index
      --vk=VERIFYING_KEY_PATH    path to verifying key. If not supplied, "verifying_key" is used
      --pk=PROVING_KEY_PATH      path to proving key. If not supplied, "proving_key" is used
      --proof=PROOF_PATH         path to proof. If not supplied, "proof" is used
  -h, --help                     print help and exit
)";

}

void check_hash_str(const std::string &hash_str, int i)
{
	if (hash_str.empty()) {
		std::cerr << "HASH" << i << " missing.\n";
		std::exit(EXIT_FAILURE);
	}
	if (hash_str.length() != libsnark::SHA256_digest_size / 4) {
		std::cerr << "HASH" << i << " is not 256 bits long.\n";
		std::exit(EXIT_FAILURE);
	}
}

/*
 * Parse options with getopt facilities.
 */
void parse_options(int argc, char **argv, std::string &h1_str, std::string &h2_str, root_t &r, index_t &i, index_t &j,
	std::string &pk_path, std::string &vk_path, std::string &proof_path, task_type &task)
{
	static const struct option long_options[] = {
		{ "h1", required_argument, NULL, 0 },
		{ "h2", required_argument, NULL, 0 },
		{ "master", required_argument, NULL, 0 },
		{ "index1", required_argument, NULL, 0 },
		{ "index2", required_argument, NULL, 0 },
		{ "vk", required_argument, NULL, 0 },
		{ "proof", required_argument, NULL, 0 },
		{ "help", no_argument, NULL, 0 },
		{ "generate", no_argument, NULL, 0 },
		{ "prove", no_argument, NULL, 0 },
		{ "verify", no_argument, NULL, 0 },
		{ "pk", required_argument, NULL, 0 },
		{ NULL, 0, NULL, 0 }
	};

	bool no_master_key = true, no_index1 = true, no_index2 = true;
	task = task_type::none;

	int opt;
	int opt_index;
	while ((opt = getopt_long_only(argc, argv, "m:i:j:hgpv", long_options, &opt_index)) != -1) {
		switch (opt) {
			case 0:
				switch (opt_index) {
					case 0:
						h1_str = optarg;
						break;
					case 1:
						h2_str = optarg;
						break;
					case 2:
						r = std::atoi(optarg);
						no_master_key = false;
						break;
					case 3:
						i = std::atoi(optarg);
						no_index1 = false;
						break;
					case 4:
						j = std::atoi(optarg);
						no_index2 = false;
						break;
					case 5:
						vk_path = optarg;
						break;
					case 6:
						proof_path = optarg;
						break;
					case 7:
						usage(argv[0]);
						std::exit(EXIT_SUCCESS);
					case 8:
						task = task_type::generate;
						break;
					case 9:
						task = task_type::prove;
						break;
					case 10:
						task = task_type::verify;
						break;
					case 11:
						pk_path = optarg;
						break;
				}

				break;
			case 'm':
				r = std::atoi(optarg);
				no_master_key = false;
				break;
			case 'i':
				i = std::atoi(optarg);
				no_index1 = false;
				break;
			case 'j':
				j = std::atoi(optarg);
				no_index2 = false;
				break;
			case 'h':
				usage(argv[0]);
				std::exit(EXIT_SUCCESS);
			case 'g':
				task = task_type::generate;
				break;
			case 'p':
				task = task_type::prove;
				break;
			case 'v':
				task = task_type::verify;
				break;
			case '?':
				std::exit(EXIT_FAILURE);
#ifndef NDEBUG
			default:
				assert(false);
#endif
		}
	}

	switch (task) {
		case task_type::none:
			return;
		case task_type::generate:
			break;
		case task_type::prove:
			check_hash_str(h1_str, 1);
			check_hash_str(h2_str, 2);
			if (no_master_key) {
				std::cerr << "MASTER_KEY missing.\n";
				std::exit(EXIT_FAILURE);
			}
			if (no_index1) {
				std::cerr << "INDEX1 missing.\n";
				std::exit(EXIT_FAILURE);
			}
			if (no_index2) {
				std::cerr << "INDEX2 missing.\n";
				std::exit(EXIT_FAILURE);
			}
			break;
		case task_type::verify:
			check_hash_str(h1_str, 1);
			check_hash_str(h2_str, 2);
			if (vk_path.empty()) {
				std::cerr << "VERIFYING_KEY_PATH missing.\n";
				std::exit(EXIT_FAILURE);
			}
			if (proof_path.empty()) {
				std::cerr << "PROOF_PATH missing.\n";
				std::exit(EXIT_FAILURE);
			}
			break;
#ifndef NDEBUG
		default:
			assert(false);
#endif
	}

}

/*
 * Convert a hexadecimal string (NOT starting with '0x') to `libff::bit_vector`.
 */
libff::bit_vector hex_to_bit_vector(const std::string &str)
{
	libff::bit_vector result;
	result.reserve(str.length() * 4);

	for (char c : str) {
		unsigned char value;

		if ('0' <= c && c <= '9') {
			value = c - '0';
		} else if ('a' <= c && c <= 'f') {
			value = c - 'a' + 10;
		} else if ('A' <= c && c <= 'F') {
			value = c  - 'A' + 10;
		} else {
			std::cerr << "Invalid character in hexadecimal string " << str << ".\n";
			std::exit(EXIT_FAILURE);
		}

		result.push_back(value & 0x8);
		result.push_back(value & 0x4);
		result.push_back(value & 0x2);
		result.push_back(value & 0x1);
	}

	return result;
}

/*
 * Put the master key and index together into one SHA256-compatible block.
 *
 * NOTE (TODO): this function (and the entire program, for that matter) can
 * for the moment only deal with one block, so the input has to fit into one
 * block.
 */
libff::bit_vector to_block(const libff::bit_vector &master_bits, const libff::bit_vector &index_bits)
{
	auto result = master_bits;
	result.insert(result.end(), index_bits.begin(), index_bits.end());

	uint64_t length = result.size();

	result.push_back(true);
	while (result.size() < 448)
		result.push_back(false);

	// TODO: does endianness play a role here? should be in big endian...
	auto length_vector = libff::int_list_to_bits({length}, sizeof(length) * CHAR_BIT);
	result.insert(result.end(), length_vector.begin(), length_vector.end());

	return result;
}

int generate(const std::string &pk_path, const std::string &vk_path)
{
	libsnark::protoboard<FieldT> pb{};

	libsnark::pb_variable_array<FieldT> h1_array, h2_array;
	h1_array.allocate(pb, 256, "h1_array");
	h2_array.allocate(pb, 256, "h2_array");

	pb.set_input_sizes(2 * 256);

	common_master_gadget<FieldT> common_master_gadget{pb, h1_array, h2_array};
	common_master_gadget.generate_r1cs_constraints();

	libsnark::r1cs_ppzksnark_keypair<libsnark::default_r1cs_ppzksnark_pp> keypair =
		libsnark::r1cs_ppzksnark_generator<libsnark::default_r1cs_ppzksnark_pp>(pb.get_constraint_system());

	std::fstream proving_key_file{pk_path, std::ios_base::out};
	if (!proving_key_file) {
		std::cerr << "Opening file " << pk_path << " failed.\n";
		return EXIT_FAILURE;
	}

	std::fstream verifying_key_file{vk_path, std::ios_base::out};
	if (!verifying_key_file) {
		std::cerr << "Opening file " << vk_path << " failed.\n";
		return EXIT_FAILURE;
	}

	proving_key_file << keypair.pk;
	verifying_key_file << keypair.vk;

	return EXIT_SUCCESS;
}

int prove(const std::string &h1_str, const std::string &h2_str, root_t r, index_t i, index_t j, const std::string &pk_path, const std::string &proof_path)
{
	auto m_bits = libff::int_list_to_bits({r}, sizeof(r) * CHAR_BIT);
	auto i_bits = libff::int_list_to_bits({i}, sizeof(i) * CHAR_BIT);
	auto j_bits = libff::int_list_to_bits({j}, sizeof(j) * CHAR_BIT);

	libsnark::protoboard<FieldT> pb{};

	libsnark::pb_variable_array<FieldT> h1_array, h2_array;
	h1_array.allocate(pb, 256, "h1_array");
	h2_array.allocate(pb, 256, "h2_array");

	pb.set_input_sizes(2 * 256);

	h1_array.fill_with_bits(pb, hex_to_bit_vector(h1_str));
	h2_array.fill_with_bits(pb, hex_to_bit_vector(h2_str));

	common_master_gadget<FieldT> common_master_gadget{pb, h1_array, h2_array};
	common_master_gadget.generate_r1cs_constraints();
	common_master_gadget.generate_r1cs_witness(to_block(m_bits, i_bits), to_block(m_bits, j_bits));

#ifndef NDEBUG
	std::cout << "PROTOBOARD SATISFIED = " << pb.is_satisfied() << std::endl;
#endif

	std::fstream proving_key_file{pk_path, std::ios_base::in};
	if (!proving_key_file) {
		std::cerr << "Opening file " << pk_path << " failed.\n";
		return EXIT_FAILURE;
	}

	libsnark::r1cs_ppzksnark_proving_key<libsnark::default_r1cs_ppzksnark_pp> proving_key;
	proving_key_file >> proving_key;

	libsnark::r1cs_ppzksnark_proof<libsnark::default_r1cs_ppzksnark_pp> proof = // TODO: narrow init doesnt work here, why?
		libsnark::r1cs_ppzksnark_prover<libsnark::default_r1cs_ppzksnark_pp>(proving_key, pb.primary_input(), pb.auxiliary_input());

	std::fstream proof_file{proof_path, std::ios_base::out};
	if (!proof_file) {
		std::cerr << "Opening file " << proof_path << " failed.\n";
		return EXIT_FAILURE;
	}

	proof_file << proof;

	return EXIT_SUCCESS;
}

int verify(const std::string &h1_str, const std::string &h2_str, const std::string &vk_path, const std::string &proof_path)
{
	std::fstream verifying_key_file{vk_path, std::ios_base::in};
	if (!verifying_key_file) {
		std::cerr << "Opening file " << vk_path << " failed.\n";
		return EXIT_FAILURE;
	}

	std::fstream proof_file{proof_path, std::ios_base::in};
	if (!proof_file) {
		std::cerr << "Opening file " << proof_path << " failed.\n";
		return EXIT_FAILURE;
	}

	libsnark::r1cs_ppzksnark_proof<libsnark::default_r1cs_ppzksnark_pp> proof;
	libsnark::r1cs_ppzksnark_verification_key<libsnark::default_r1cs_ppzksnark_pp> verifying_key;
	libsnark::r1cs_primary_input<FieldT> primary_input;

	proof_file >> proof;
	verifying_key_file >> verifying_key;

	for (auto bit : hex_to_bit_vector(h1_str))
		primary_input.push_back(bit ? FieldT::one() : FieldT::zero());
	    for (auto bit : hex_to_bit_vector(h2_str))
	        primary_input.push_back(bit ? FieldT::one() : FieldT::zero());

	return !libsnark::r1cs_ppzksnark_verifier_strong_IC<libsnark::default_r1cs_ppzksnark_pp>(verifying_key, primary_input, proof);
}

int main(int argc, char **argv)
{
	std::string h1_str = "";
	std::string h2_str = "";
	uint16_t m;
	uint8_t i, j;
	std::string pk_path = "proving_key";
	std::string vk_path = "verifying_key";
	std::string proof_path = "proof";
	task_type task;

	parse_options(argc, argv, h1_str, h2_str, m, i, j, pk_path, vk_path, proof_path, task);

	libsnark::default_r1cs_ppzksnark_pp::init_public_params();

	switch (task) {
		case task_type::none:
			usage(argv[0]);
			return EXIT_SUCCESS;
		case task_type::generate:
			return generate(pk_path, vk_path);
		case task_type::prove:
			return prove(h1_str, h2_str, m, i, j, pk_path, proof_path);
		case task_type::verify:
			return verify(h1_str, h2_str, vk_path, proof_path);
#ifndef NDEBUG
		default:
			assert(false);
#endif
	}
}
