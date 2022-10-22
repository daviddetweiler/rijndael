#include <array>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <format>
#include <iostream>
#include <memory>
#include <string_view>
#include <tuple>
#include <utility>
#include <vector>

#include <intrin.h>

#include <gsl/gsl>

namespace rijndael {
	namespace {
		using t_table = std::array<std::uint32_t, 256>;
		using u_op = std::array<std::uint8_t, 256>;
		using b_op = std::array<u_op, 256>;
		static_assert(sizeof(b_op) == sizeof(u_op) * 256);

		struct t_tables {
			t_table t0;
			t_table t1;
			t_table t2;
			t_table t3;
		};

		constexpr auto pack(std::uint8_t a, std::uint8_t b, std::uint8_t c, std::uint8_t d)
		{
			return gsl::narrow_cast<std::uint32_t>(a | b << 8 | c << 16 | d << 24);
		};

		class constant_table {
		public:
			std::array<std::uint8_t, (14 + 1) * 8 / 4> rc;
			u_op sbox;
			u_op isbox;
			t_tables round;
			t_tables iround;

			static auto make() { return std::make_unique<const constant_table>(); }

		private:
			friend std::unique_ptr<const constant_table> std::make_unique<const constant_table>();

			[[gsl::suppress(bounds)]] [[gsl::suppress(f .6)]] constant_table() :
				rc {},
				sbox {},
				isbox {},
				round {},
				iround {}
			{
				auto mul_table = std::make_unique<b_op>();
				auto inv_table = std::make_unique<u_op>();
				auto& mul = *mul_table;
				auto& inv = *inv_table;
				for (auto i = 0u; i < 256u; ++i) {
					for (auto j = i; j < 256u; ++j) {
						const auto a = gsl::narrow_cast<std::uint8_t>(i);
						const auto b = gsl::narrow_cast<std::uint8_t>(j);
						const auto c = times(a, b);
						mul[a][b] = mul[b][a] = c;
						if (c == 0x01u) {
							inv[a] = b;
							inv[b] = a;
						}
					}
				}

				rc[1] = 0x01;
				for (auto i = 2u; i < rc.size(); ++i)
					rc[i] = mul[rc[i - 1]][0x02];

				for (auto i = 0u; i < 256u; ++i) {
					const auto b = gsl::narrow_cast<std::uint8_t>(i);
					const auto ib = inv[b];
					const auto sb = gsl::narrow_cast<std::uint8_t>(
						rotate<4>(ib) ^ rotate<3>(ib) ^ rotate<2>(ib) ^ rotate<1>(ib) ^ ib ^ 0x63u);

					sbox[b] = sb;
					isbox[sb] = b;

					const auto sb2 = mul[sb][0x02];
					const auto sb3 = mul[sb][0x03];
					round.t0[b] = pack(sb2, sb, sb, sb3);
					round.t1[b] = pack(sb3, sb2, sb, sb);
					round.t2[b] = pack(sb, sb3, sb2, sb);
					round.t3[b] = pack(sb, sb, sb3, sb2);

					const auto b9 = mul[b][0x09];
					const auto bb = mul[b][0x0b];
					const auto bd = mul[b][0x0d];
					const auto be = mul[b][0x0e];
					iround.t0[sb] = pack(be, b9, bd, bb);
					iround.t1[sb] = pack(bb, be, b9, bd);
					iround.t2[sb] = pack(bd, bb, be, b9);
					iround.t3[sb] = pack(b9, bd, bb, be);
				}

				mul_table.reset();
				inv_table.reset();
			}

			template <unsigned int i>
			static constexpr std::uint8_t rotate(std::uint8_t b)
			{
				return (b << i) | (b >> (7 & (0u - i)));
			}

			static constexpr std::uint8_t xtimes(std::uint8_t n)
			{
				const auto t = gsl::narrow_cast<std::uint8_t>(n << 1);
				return (n & 0x80) ? t ^ 0x1b : t;
			}

			static constexpr std::uint8_t times(std::uint8_t a, std::uint8_t b)
			{
				std::uint8_t c {};
				for (; a; a >>= 1, b = xtimes(b))
					c ^= (a & 0x01) ? b : 0x0u;

				return c;
			}
		};

		static constexpr std::array shifts {
			std::array {0ull, 1ull, 2ull, 3ull},
			std::array {0ull, 1ull, 2ull, 3ull},
			std::array {0ull, 1ull, 2ull, 3ull},
			std::array {0ull, 1ull, 2ull, 4ull},
			std::array {0ull, 1ull, 3ull, 4ull},
		};

		template <unsigned int nk, unsigned int nb>
		class [[gsl::suppress(bounds)]] rijndael
		{
			static_assert(nk >= 4 && nb >= 4 && nk <= 8 && nb <= 8, "not a valid Rijndael cipher");

		public:
			constexpr static auto key_size = nk * 4;
			constexpr static auto block_size = nb * 4;
			constexpr static auto nr = std::max(10u + nk - 4u, 10u + nb - 4u);
			constexpr static auto nek = (nr + 1) * nb;
			using key_view = std::span<const std::uint8_t, key_size>;
			using block_view = std::span<std::uint8_t, block_size>;

			[[gsl::suppress(gsl.view)]] rijndael(const constant_table& c, key_view k) noexcept : rijndael {}
			{
				rekey(c, k);
			}

			[[gsl::suppress(gsl.view)]] void rekey(const constant_table& tbl, key_view k) noexcept
			{
				std::memcpy(ekey.data(), k.data(), k.size_bytes());
				apply_key_schedule(tbl);
				std::memcpy(iekey.data(), ekey.data(), ekey.size());
				const std::span view {iekey};
				for (auto r = 1ull; r < nr; ++r) {
					for (auto c = 0ull; c < nb; ++c)
						imix_column(tbl, column {view.subspan(((r * nb) + c) * 4, 4)});
				}
			}

			void encrypt(const constant_table& tbl, block_view p) const noexcept { apply_rounds<false>(tbl, p); }
			void decrypt(const constant_table& tbl, block_view c) const noexcept { apply_rounds<true>(tbl, c); }

		private:
			using rkey_view = std::span<const std::uint8_t, block_size>;
			using round_keys = std::array<std::uint8_t, nek * 4>;
			using column = std::span<std::uint8_t, 4>;

			round_keys ekey {};
			round_keys iekey {};

			rijndael() = default;

			[[gsl::suppress(bounds)]] [[gsl::suppress(gsl.view)]] static void imix_column(
				const constant_table& tbl,
				column c) noexcept
			{
				const auto x = tbl.iround.t0[tbl.sbox[c[0]]];
				const auto y = tbl.iround.t1[tbl.sbox[c[1]]];
				const auto z = tbl.iround.t2[tbl.sbox[c[2]]];
				const auto w = tbl.iround.t3[tbl.sbox[c[3]]];
				const auto nc = x ^ y ^ z ^ w;
				std::memcpy(c.data(), &nc, 4);
			}

			static constexpr auto rot_word(std::uint32_t c) { return c >> 8 | c << 24; }

			[[gsl::suppress(bounds)]] static constexpr auto sub_word(const constant_table& tbl, std::uint32_t c)
			{
				const auto x = tbl.sbox[c & 0xff];
				const auto y = tbl.sbox[(c >> 8) & 0xff];
				const auto z = tbl.sbox[(c >> 16) & 0xff];
				const auto w = tbl.sbox[(c >> 24) & 0xff];
				return pack(x, y, z, w);
			}

			[[gsl::suppress(bounds)]] [[gsl::suppress(gsl.view)]] void apply_key_schedule(
				const constant_table& tbl) noexcept
			{
				const std::span key_view {ekey};
				for (auto c_idx = nk; c_idx < nek; ++c_idx) {
					const column a {key_view.subspan((c_idx - 1) * 4ull, 4)};
					const column b {key_view.subspan((c_idx - nk) * 4ull, 4)};
					const column c {key_view.subspan(c_idx * 4ull, 4)};

					std::uint32_t x, y;
					std::memcpy(&x, a.data(), 4);
					std::memcpy(&y, b.data(), 4);
					if (c_idx % nk == 0) {
						x = sub_word(tbl, rot_word(x)) ^ tbl.rc[c_idx / nk];
					}
					else if constexpr (nk > 6) {
						if (c_idx % nk == 4)
							x = sub_word(tbl, x);
					}

					x ^= y;
					std::memcpy(c.data(), &x, c.size_bytes());
				}
			}

			template <bool inverted>
			[[gsl::suppress(bounds)]] [[gsl::suppress(gsl.view)]] void apply_rounds(
				const constant_table& tbl,
				block_view state) const noexcept
			{
				const std::span key_view {inverted ? iekey : ekey};
				const auto offset = [](unsigned int r) { return (inverted ? nr - r : r) * block_size; };
				const auto rkey = [&offset, key_view](unsigned int r) {
					return rkey_view {key_view.subspan(offset(r), block_size)};
				};

				const auto first_key = rkey(0);
				for (auto i = 0ull; i < nb; ++i) {
					std::uint32_t a, b;
					std::memcpy(&a, &state[i * 4], 4);
					std::memcpy(&b, &first_key[i * 4], 4);
					a ^= b;
					std::memcpy(&state[i * 4], &a, 4);
				}

				std::array<std::uint8_t, block_size> nstate {};
				for (auto i = 1u; i < nr; ++i)
					apply_round<inverted, false>(tbl, (i % 2) ? state : nstate, rkey(i), (i % 2) ? nstate : state);

				apply_round<inverted, true>(tbl, (nr % 2) ? state : nstate, rkey(nr), (nr % 2) ? nstate : state);
				if constexpr (nr % 2)
					std::memcpy(state.data(), nstate.data(), block_size);
			}

			template <bool inverted>
			[[gsl::suppress(bounds)]] [[gsl::suppress(gsl.view)]] static constexpr auto get_byte(
				block_view st,
				std::uint64_t r,
				std::uint64_t c)
			{
				static constexpr std::span row_shifts = shifts[nb - 4];
				const auto o = row_shifts[r];
				const auto nc = (inverted ? c + (nb - o) : c + o) % nb;
				const auto b = st[nc * 4 + r];
				return b;
			};

			template <bool inverted, bool skip_mix>
			[[gsl::suppress(bounds)]] [[gsl::suppress(gsl.view)]] static void apply_round(
				const constant_table& tbl,
				block_view state,
				rkey_view round_key,
				block_view nstate) noexcept
			{
				auto& sbox = inverted ? tbl.isbox : tbl.sbox;
				static constexpr auto get = [](auto&&... args) { return get_byte<inverted>(args...); };
				for (auto j = 0ull; j < nb; ++j) {
					std::uint32_t kc;
					std::memcpy(&kc, &round_key[j * 4], 4);
					if constexpr (!skip_mix) {
						auto& [t0, t1, t2, t3] = inverted ? tbl.iround : tbl.round;
						const auto x = t0[get(state, 0, j)];
						const auto y = t1[get(state, 1, j)];
						const auto z = t2[get(state, 2, j)];
						const auto w = t3[get(state, 3, j)];
						const auto nc = x ^ y ^ z ^ w ^ kc;
						std::memcpy(&nstate[j * 4], &nc, 4);
					}
					else {
						const auto subbed = pack(
							sbox[get(state, 0, j)],
							sbox[get(state, 1, j)],
							sbox[get(state, 2, j)],
							sbox[get(state, 3, j)]);

						const auto nc = subbed ^ kc;
						std::memcpy(&nstate[j * 4], &nc, 4);
					}
				}
			}
		};

		using aes128 = rijndael<4, 4>;
		using aes192 = rijndael<6, 4>;
		using aes256 = rijndael<8, 4>;

		[[gsl::suppress(bounds .1)]] void print_blob(gsl::span<std::uint8_t> blob)
		{
			for (const auto& b : blob)
				std::cout << std::format("{:02X}", b);

			std::cout << '\n';
		}

		enum class mode { vectors, times };

		template <typename cipher_type>
		[[gsl::suppress(gsl.view)]] [[gsl::suppress(bounds .1)]] void test(const constant_table& constants, mode m)
		{
			std::array<std::uint8_t, cipher_type::key_size> key {};
			std::array<std::uint8_t, cipher_type::block_size> block {};
			cipher_type cipher {constants, key};
			if (m == mode::vectors) {
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
			else if (m == mode::times) {
				const auto time = [](auto&& task) {
					using clock = std::chrono::high_resolution_clock;
					const auto start = clock::now();
					const auto start_c = __rdtsc();
					task();
					const auto stop_c = __rdtsc();
					const auto stop = clock::now();
					return std::make_tuple(
						std::chrono::duration_cast<std::chrono::duration<double>>(stop - start),
						static_cast<double>(stop_c - start_c));
				};

				static constexpr auto reps = 1ull << 24;
				const auto [rekey, rk_c] = time([&] {
					for (auto i = 0u; i < reps; ++i)
						cipher.rekey(constants, key);
				});

				const auto [encrypt, e_c] = time([&] {
					for (auto i = 0u; i < reps; ++i)
						cipher.encrypt(constants, block);
				});

				const auto [decrypt, d_c] = time([&] {
					for (auto i = 0u; i < reps; ++i)
						cipher.decrypt(constants, block);
				});

				const auto rkps = reps / rekey.count();
				const auto embps = reps * block.size() / (encrypt.count() * 1024 * 1024);
				const auto dmbps = reps * block.size() / (decrypt.count() * 1024 * 1024);
				static constexpr auto div = reps * cipher.block_size * cipher.nr;
				static constexpr auto div_k = reps * 4 * cipher.nek;
				std::cout << std::format(
					"b{}-k{}: {:.1f} K/s ({:.1f}), {:.1f} MiB/s E ({:01.02f}), {:.1f} MiB/s D ({:01.02f})\n",
					block.size() * 8,
					key.size() * 8,
					rkps,
					rk_c / div_k,
					embps,
					e_c / div,
					dmbps,
					d_c / div);
			}
		}

		using blocks = std::make_integer_sequence<unsigned int, 5>;

		template <unsigned int k, unsigned int b, unsigned int... s>
		void iter_blocks(const constant_table& table, mode m)
		{
			test<rijndael<k + 4, b + 4>>(table, m);
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
			test<aes128>(table, mode::times);
			test<aes128>(table, mode::vectors);
			test<aes192>(table, mode::times);
			test<aes192>(table, mode::vectors);
			test<aes256>(table, mode::times);
			test<aes256>(table, mode::vectors);
		}
	}
}

int main(int argc, char** argv)
{
	const gsl::span arguments {argv, gsl::narrow_cast<std::size_t>(argc)};
	if (argc != 2)
		return 1;

	const std::string_view mode {arguments[1]};
	if (mode == "vectors")
		rijndael::run_benchmarks(*rijndael::constant_table::make(), rijndael::mode::vectors);
	else if (mode == "times")
		rijndael::run_benchmarks(*rijndael::constant_table::make(), rijndael::mode::times);
	else if (mode == "aes")
		rijndael::benchmark_aes(*rijndael::constant_table::make());
	else
		return 1;
}
