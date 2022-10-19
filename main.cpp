#include <array>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
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
			std::array<std::uint8_t, 15> rc;
			u_op sbox;
			u_op isbox;
			t_tables round;
			t_tables iround;

			static auto make() { return std::make_unique<const constant_table>(); }

		private:
			friend std::unique_ptr<const constant_table> std::make_unique<const constant_table>();

			constant_table() : rc {}, sbox {}, isbox {}, round {}, iround {}
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

				const auto rotate = [](std::uint8_t b, unsigned int i) { return (b << i) | (b >> (7 & (0u - i))); };
				for (auto i = 0u; i < 256u; ++i) {
					const auto b = gsl::narrow_cast<std::uint8_t>(i);
					const auto ib = inv[b];
					const auto sb = gsl::narrow_cast<std::uint8_t>(
						rotate(ib, 4) ^ rotate(ib, 3) ^ rotate(ib, 2) ^ rotate(ib, 1) ^ ib ^ 0x63u);

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

			static constexpr std::uint8_t rotate(std::uint8_t b, unsigned int i)
			{
				return (b << i) | (b >> (7 & (0u - i)));
			}

			static constexpr std::uint8_t xtimes(std::uint8_t n)
			{
				const auto t = static_cast<std::uint16_t>(n) << 1;
				return gsl::narrow_cast<std::uint8_t>((n & (1u << 7)) ? t ^ 0x11b : t);
			}

			static constexpr std::uint8_t times(std::uint8_t a, std::uint8_t b)
			{
				std::uint8_t c {};
				for (auto i = 0u; i < 8u; ++i) {
					c ^= (a & (1u << i)) ? b : 0x0u;
					b = xtimes(b);
				}

				return c;
			}
		};

		static constexpr std::array shifts {
			std::array {0, 1, 2, 3},
			std::array {0, 1, 2, 3},
			std::array {0, 1, 2, 3},
			std::array {0, 1, 2, 4},
			std::array {0, 1, 3, 4},
		};

		template <unsigned int nk, unsigned int nb>
		class rijndael {
			static_assert(nk >= 4 && nb >= 4 && nk <= 8 && nb <= 8, "not a valid Rijndael cipher");

		public:
			constexpr static auto key_size = nk * 4;
			constexpr static auto block_size = nb * 4;
			using key_view = gsl::span<const std::uint8_t, key_size>;
			using block_view = gsl::span<std::uint8_t, block_size>;

			rijndael(const constant_table& c, key_view k) noexcept : rijndael {} { rekey(c, k); }

			void rekey(const constant_table& tbl, key_view k) noexcept
			{
				std::memcpy(ekey.data(), k.data(), k.size_bytes());
				apply_key_schedule(tbl);
				std::memcpy(iekey.data(), ekey.data(), ekey.size());
				const gsl::span view {iekey};
				for (auto r = 1u; r < nr; ++r) {
					for (auto c = 0u; c < nb; ++c)
						imix_column(tbl, column {view.subspan(((r * nb) + c) * 4, 4)});
				}
			}

			void encrypt(const constant_table& tbl, block_view p) const noexcept { apply_rounds<false>(tbl, p); }
			void decrypt(const constant_table& tbl, block_view c) const noexcept { apply_rounds<true>(tbl, c); }

		private:
			constexpr static auto nr = std::max(10u + nk - 4u, 10u + nb - 4u);
			constexpr static auto round_keys_size = 4 * nb * (nr + 1);

			using rkey_view = gsl::span<const std::uint8_t, block_size>;
			using round_keys = std::array<std::uint8_t, round_keys_size>;
			using column = gsl::span<std::uint8_t, 4>;

			round_keys ekey {};
			round_keys iekey {};

			rijndael() = default;

			static void imix_column(const constant_table& tbl, column c) noexcept
			{
				const auto x = tbl.iround.t0[tbl.sbox[c[0]]];
				const auto y = tbl.iround.t1[tbl.sbox[c[1]]];
				const auto z = tbl.iround.t2[tbl.sbox[c[2]]];
				const auto w = tbl.iround.t3[tbl.sbox[c[3]]];
				const auto nc = x ^ y ^ z ^ w;
				std::memcpy(c.data(), &nc, 4);
			}

			static constexpr void rot_word(column c)
			{
				const auto t = c[0];
				c[0] = c[1];
				c[1] = c[2];
				c[2] = c[3];
				c[3] = t;
			}

			static constexpr void sub_word(const constant_table& tbl, column c)
			{
				c[0] = tbl.sbox[c[0]];
				c[1] = tbl.sbox[c[1]];
				c[2] = tbl.sbox[c[2]];
				c[3] = tbl.sbox[c[3]];
			}

			void apply_key_schedule(const constant_table& tbl) noexcept
			{
				const gsl::span key_view {ekey};
				for (auto c_idx = nk; c_idx < (nr + 1) * nb; ++c_idx) {
					const column a {key_view.subspan((c_idx - 1) * 4, 4)};
					const column b {key_view.subspan((c_idx - nk) * 4, 4)};
					const column c {key_view.subspan(c_idx * 4, 4)};
					std::memcpy(c.data(), a.data(), c.size_bytes());
					if (c_idx % nk == 0) {
						rot_word(c);
						sub_word(tbl, c);
						c[0] ^= tbl.rc[c_idx / nk];
					}
					else if constexpr (nk > 6) {
						if (c_idx % 4 == 0)
							sub_word(tbl, c);
					}

					std::uint32_t x, y;
					std::memcpy(&x, c.data(), c.size_bytes());
					std::memcpy(&y, b.data(), b.size_bytes());
					x ^= y;
					std::memcpy(c.data(), &x, c.size_bytes());
				}
			}

			template <bool inverted>
			void apply_rounds(const constant_table& tbl, block_view state) const noexcept
			{
				const gsl::span key_view {inverted ? iekey : ekey};
				const auto offset = [](unsigned int r) { return (inverted ? nr - r : r) * block_size; };
				const auto rkey = [&offset, key_view](unsigned int r) {
					return rkey_view {key_view.subspan(offset(r), block_size)};
				};

				const auto first_key = rkey(0);
				for (auto i = 0u; i < block_size; ++i)
					state[i] ^= first_key[i];

				for (auto i = 1u; i < nr; ++i)
					apply_round<inverted, false>(tbl, state, rkey(i));

				apply_round<inverted, true>(tbl, state, rkey(nr));
			}

			template <bool inverted, bool skip_mix>
			static void apply_round(const constant_table& tbl, block_view state, rkey_view round_key) noexcept
			{
				static constexpr gsl::span row_shifts = shifts.at(nb - 4);
				auto& sbox = inverted ? tbl.isbox : tbl.sbox;
				const auto get = [](block_view st, unsigned int r, unsigned int c) {
					const auto o = row_shifts[r];
					const auto nc = (inverted ? c + (nb - o) : c + o) % nb;
					const auto b = st[nc * 4 + r];
					return b;
				};

				std::array<std::uint8_t, block_size> nstate {};
				for (auto j = 0u; j < nb; ++j) {
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

				std::memcpy(state.data(), nstate.data(), nstate.size());
			}
		};

		template class rijndael<4, 4>;
		template class rijndael<6, 4>;
		template class rijndael<8, 4>;

		using aes128 = rijndael<4, 4>;
		using aes192 = rijndael<6, 4>;
		using aes256 = rijndael<8, 4>;

		template <typename cipher_type>
		void benchmark(const constant_table& constants)
		{
			std::array<std::uint8_t, cipher_type::key_size> key {};
			std::array<std::uint8_t, cipher_type::block_size> block {};
			cipher_type cipher {constants, key};

			constexpr auto reps = 1 << 16;
			const auto start_k = __rdtsc();
			for (auto i = 0u; i < reps; ++i)
				cipher.rekey(constants, key);

			const auto stop_k = __rdtsc();
			const auto cycles_per_k = static_cast<float>(stop_k - start_k) / reps;

			const auto start_e = __rdtsc();
			for (auto i = 0u; i < reps; ++i)
				cipher.encrypt(constants, block);

			const auto stop_e = __rdtsc();
			const auto cycles_per_e = static_cast<float>(stop_e - start_e) / reps;

			const auto start_d = __rdtsc();
			for (auto i = 0u; i < reps; ++i)
				cipher.decrypt(constants, block);

			const auto stop_d = __rdtsc();
			const auto cycles_per_d = static_cast<float>(stop_d - start_d) / reps;

			std::cout << cycles_per_k / cipher_type::key_size << ' ' << cycles_per_e / cipher_type::block_size << ' '
					  << cycles_per_d / cipher_type::block_size << '\n';
		}
	}
}

int main()
{
	const auto constants = rijndael::constant_table::make();
	rijndael::benchmark<rijndael::aes128>(*constants);
	rijndael::benchmark<rijndael::aes192>(*constants);
	rijndael::benchmark<rijndael::aes256>(*constants);
}
