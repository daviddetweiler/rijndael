#include <array>
#include <chrono>
#include <cstdint>
#include <format>
#include <functional>
#include <iostream>
#include <memory>

#include <intrin.h>

#include <gsl/gsl>

#include "rijndael.h"

namespace rijndael {
	namespace {
		[[gsl::suppress(bounds .1)]] void print_blob(gsl::span<std::uint8_t> blob)
		{
			for (const auto& b : blob)
				std::cout << std::format("{:02X}", b);

			std::cout << '\n';
		}

		enum class mode { vectors, multiply };

		constexpr auto reps = 1ull << 24;

		template <typename callable_type>
		auto time(callable_type task) noexcept
		{
			using clock = std::chrono::high_resolution_clock;
			const auto start = clock::now();
			const auto start_c = __rdtsc();

			for (auto i = 0u; i < reps; ++i)
				task();

			const auto stop_c = __rdtsc();
			const auto stop = clock::now();
			const auto elapsed_time = std::chrono::duration_cast<std::chrono::duration<double>>(stop - start);
			const auto elapsed_cycles = static_cast<double>(stop_c - start_c);

			return std::make_pair(elapsed_time, elapsed_cycles);
		};

		template <typename cipher_type>
		[[gsl::suppress(gsl.view)]] void print_vectors(const constant_table& constants)
		{
			const std::array<std::uint8_t, cipher_type::key_size> key {};
			const cipher_type cipher {constants, key};
			std::array<std::uint8_t, cipher_type::block_size> block {};

			cipher.encrypt(constants, block);
			print_blob(block);
			cipher.encrypt(constants, block);
			print_blob(block);
			cipher.decrypt(constants, block);
			cipher.decrypt(constants, block);

			for (const auto& b : block) {
				if (b)
					std::cout << "bad decrypt\n";
			}

			std::cout << '\n';
		}

		template <typename cipher_type>
		[[gsl::suppress(gsl.view)]] void do_benchmark(const constant_table& constants)
		{
			static constexpr auto format_string
				= "b{}-k{}: {:.1f} K/s ({:01.02f}), {:.1f} MiB/s E ({:01.02f}), {:.1f} MiB/s D ({:01.02f})\n";

			const std::array<std::uint8_t, cipher_type::key_size> key {};
			std::array<std::uint8_t, cipher_type::block_size> block {};
			cipher_type cipher {constants, key};

			const auto [apply_key, rk_c] = time(std::bind(&cipher_type::apply_key, cipher, constants, key));
			const auto [encrypt, e_c] = time(std::bind(&cipher_type::encrypt, cipher, constants, block));
			const auto [decrypt, d_c] = time(std::bind(&cipher_type::decrypt, cipher, constants, block));

			const auto rkps = reps / apply_key.count();
			const auto embps = reps * block.size() / (encrypt.count() * 1024 * 1024);
			const auto dmbps = reps * block.size() / (decrypt.count() * 1024 * 1024);
			static constexpr auto div = reps * cipher.block_size;
			static constexpr auto div_k = reps * cipher.key_size;

			std::cout << std::format(
				format_string,
				block.size() * 8,
				key.size() * 8,
				rkps,
				rk_c / div_k,
				embps,
				e_c / div,
				dmbps,
				d_c / div);
		}

		template <typename cipher_type>
		void test(const constant_table& constants, mode m)
		{
			if (m == mode::vectors)
				print_vectors<cipher_type>(constants);
			else if (m == mode::multiply)
				do_benchmark<cipher_type>(constants);
		}

		using blocks = std::make_integer_sequence<unsigned int, 5>;

		template <unsigned int k, unsigned int b, unsigned int... s>
		void iter_blocks(const constant_table& table, mode m)
		{
			test<transcoder<k + 4, b + 4>>(table, m);
			if constexpr (sizeof...(s) != 0)
				iter_blocks<k, s...>(table, m);
		}

		template <unsigned int k, typename type, type... s>
		void all_blocks(const constant_table& table, mode m, std::integer_sequence<type, s...>)
		{
			iter_blocks<k, s...>(table, m);
		}

		template <unsigned int k, unsigned int... s>
		void iter_keys(const constant_table& table, mode m)
		{
			all_blocks<k>(table, m, blocks {});
			if constexpr (sizeof...(s) != 0)
				iter_keys<s...>(table, m);
		}

		template <typename type, type... s>
		void all_keys(const constant_table& table, mode m, std::integer_sequence<type, s...>)
		{
			iter_keys<s...>(table, m);
		}

		void run_benchmarks(const constant_table& table, mode m) { all_keys(table, m, blocks {}); }

		void benchmark_aes(const constant_table& table)
		{
			test<aes128>(table, mode::multiply);
			test<aes128>(table, mode::vectors);
			test<aes192>(table, mode::multiply);
			test<aes192>(table, mode::vectors);
			test<aes256>(table, mode::multiply);
			test<aes256>(table, mode::vectors);
		}
	}
}

int main(int argc, char** argv)
{
	using namespace rijndael;

	const gsl::span arguments {argv, gsl::narrow_cast<std::size_t>(argc)};
	if (argc != 2)
		return 1;

	const std::string_view mode {arguments[1]};
	constexpr auto make = [] { return std::make_unique<constant_table>(); };
	if (mode == "vectors")
		run_benchmarks(*make(), mode::vectors);
	else if (mode == "times")
		run_benchmarks(*make(), mode::multiply);
	else if (mode == "aes")
		benchmark_aes(*make());
	else
		return 1;
}
