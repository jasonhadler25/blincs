# BLINCS (`BLINCS-48-X`)

> **Pre-1.0 — Experimental & Unsupported.** This repository is under active development (draft `0.5.0`); wire formats, parameters, and context strings may still change incompatibly before 1.0. Written primarily by an AI assistant at the direction of this repository's owner; **no independent human cryptographic review or security audit has been performed**. Do not rely on BLINCS to protect production assets.

**BLINCS** is a stateless hash-based signature algorithm based on BLAKE3 and SPHINCS. This repository is the **specification, teaching reference implementation, exhaustive deterministic certifier, Lean 4 formalization, and cryptography paper** for **`BLINCS-48-X`** (`13+7×5` packed `WOTS+C` hypertree + single height-11 chained `U-PORS` Octopus tree, **`3,990`-byte** imprints, lifetime budget $q_s \le 2^{48}$).

- For the **production Rust crate** (`19,584`-chain single-threaded SIMD super-wave signing, `#![no_std]` zero-alloc verifier + `27.1 KiB` zero-import WASM target, lock-free local randomness state), see [`jasonhadler25/signet`](https://github.com/jasonhadler25/signet).
- For **Git commit/tag imprinting** built on `signet`, see [`jasonhadler25/git-signet`](https://github.com/jasonhadler25/git-signet).

---

## Key Properties of `BLINCS-48-X`

- **Size:** **`3,990`-byte `Imprint`** (`5,320` B Base64 — **49.2% smaller than `SLH-DSA-128s`** [`7,856 B`] and **4.28× smaller than `SLH-DSA-128f`** [`17,088 B`]), `32`-byte `SignetId`, `32`-byte seed, and an optional `256 KiB` cached top tree (`h_top = 13`, `8,192` leaves; or `16 KiB` depth-10 partial cut at `+1.08%` ideal fixed compressions with byte-for-byte identical signatures). For fair size comparison at $q_s = 2^{64}$, [`paper/blincs.pdf`](paper/blincs.pdf) (§8.1) also lists wire-byte-only projections (`BLINCS-64-EQ` `4,924 B`, `-37.3%`; `BLINCS-64-S` `4,585 B`, `-41.6%`), while all specifications, proofs, formalization, and implementations focus strictly on flagship `BLINCS-48-X`.
- **100% pure stateless ($q_s \le 2^{48}$):** zero synchronized one-time signing state; signing keys can be copied across machines, restored from backups, or run in short-lived processes without XMSS/LMS state-reuse hazards. **Do not imprint more than `2^48` things with one signet.**
- **Zero-coding-table packed `WOTS+C` hypertree (`13 + 7×5 = 48`, `d = 6`):** one uniform OTS primitive across all six layers — `n = 21` chains of length `w - 1 = 59`, `z = 2` zero bits, shifted upper-half constant sum `S = 679` (`|L_679(21, 60)| = 83,261,328,062,314,682,436,358,950,675,433,803 > 2^{116}`), direct 6-bit unpacking (`2 + 21 × 6 = 128` bits exact, zero division, zero dynamic programming, zero coding lookup tables), `3`-byte `u24` LE counter (`u24` overflow `< 2^{-5,923}` per key, `< 2^{-5,874}` globally across all `< 2^{49}` physical keys), and exact constant `560` verification steps per layer.
- **Zero-coding-table chained `U-PORS` Octopus few-time signature (`A = 11, k = 9, m_max = 45`):** one height-11 binary Merkle tree (`2,048` leaves) whose leaves use `n = 3` equal-length chains of length `23` (`a + b + c = 42`, `C = 376` codewords with 24-row arithmetic scan — `0 B` coding tables), exact `64`-byte single-block BLAKE3 leaf hashing (`16 + 3 × 16 = 64 B`), Octopus path merging capped at `45` authentication nodes with canonical trailing zero-padding, and `FEW_CODE` (`48 B`) chained directly from the `32`-byte `FEW_SELECT` digest `H_sel` (zero BLAKE3 XOF mode required; prevents code-first pre-filtering on a fixed selection input).
- **Zero-Monte-Carlo, exact-`BigInt` all-orbits `U-PORS` certification (`tools/upors_cert.rs`):** conditioning honest signatures on `sibs(S) <= 45` breaks negative association and induces `30.35×` adjacent-sibling clustering. Our standalone certifier proves an all-integer 3-term upper envelope `u_3(t) >= q_C(t)` for all $t \ge 0$, enumerates **all `1,614,132` `Aut(T_11)`-orbits** (partitioning all `|F| = 180,700,154,447,569,471,488` subsets), evaluates exact binomial moments (`K = 44`) across every orbit in `256`-bit fractional arithmetic, and certifies the final outward-rounded table in exact arbitrary-precision `BigInt` rational interval arithmetic (zero `f64` reliance in final bounds), proving single-raw-candidate upper-envelope bound `>= 131.7076` bits (`P <= 2.2493e-40`) at $(h, q_s) = (48, 2^{48})$ and at $(64, 2^{64})$. Classical single-user target (`128`-bit); physical CRQC hash-collision costs follow Bernstein (SHARCS 2009), with QROM and multi-user proofs noted as open problems.
- **Fast constant-work verification & cross-architecture co-design:** **`3,715 + m + b` short-message compressions** to verify (**`3,761`** at `m = 45, b = 1`; `62.7 µs` at `7.44 IPC` on 1 Apple M6 core, zero heap allocations; `8.45 ms` warm signing); bare-metal QEMU ARM Cortex-M33 emulation measures `3,577` Thumb-2 instructions for 6-layer `WOTS+C` decode (`1,816×` fewer than zero-table Sperner DP), `988 B` verification stack watermark, and `653.2` Thumb-2 instructions/compression for a hand-written Thumb-2+FPU `CHAIN` kernel (modeled at `~4.44 s` mean / `~4.82 s` `p99` warm sign with `16 KiB` partial cache and `~16.2 ms` verify at `160 MHz` TRM 0-wait cycles; physical Cortex-M33 silicon has not been measured).
- **Single-pass salted content hashing:** streams arbitrarily large messages in a single pass under a fresh per-imprint salt `e` drawn before `(ctx, M)` is committed, while keeping hedged post-hash randomizer `R = Keyed(K_R, e || h_msg || framed_ctx)[..16]` resilient if the salt draw repeats.

---

## Repository Contents

| Path | Description |
|---|---|
| [`SPEC.md`](SPEC.md) | Normative byte-level specification of `BLINCS-48-X` (draft `0.5.0`), including fail-closed exhaustion rules, salt-commitment rule (§7), and §13 startup self-test guidance |
| [`DESIGN.md`](DESIGN.md) | Design-space rationale, all-orbits rational-interval `U-PORS` bounds, cross-architecture co-design (Apple M6 + QEMU Cortex-M33), and adopted vs. declined techniques |
| [`paper/blincs.pdf`](paper/blincs.pdf) | Cryptography technical report (`paper/blincs.tex`, `blincs.bib`): failure of negative association under Octopus capping, exact-`BigInt` all-`1,614,132`-orbits certification, 4-game single-user classical ROM+PRF EUF-CMA proof with adaptive marked-history coupling, Lean 4 formalization boundary, Apple M6 + QEMU Cortex-M33 co-design, and physical CRQC collision-cost analysis (Bernstein, SHARCS 2009) |
| [`tools/upors_cert.rs`](tools/upors_cert.rs) | Standalone zero-dependency Rust certifier: exact 256-bit integer proof of `u_3(t) >= q_C(t)` ($\forall t \ge 0$), small-tree brute-force & trinomial $r=2$ checks, exhaustive enumeration of all `1,614,132` `Aut(T_11)`-orbits, and zero-`f64` exact `BigInt` rational-interval certification (`--fast` mode runs in `< 1 s` in CI) |
| [`reference/`](reference/) | Teaching-clarity Rust reference implementation (`#![forbid(unsafe_code)]`, strictly single-threaded `blake3-servil-core = "=0.11.0"`, `self_test()`, matching all 5 canonical `3,990 B` vectors byte-for-byte) |
| [`formal/`](formal/) | Spec-exact declarative **Lean 4.36.0** formalization (`Blincs/{Params,Tweaks,Wots,Merkle,Scheme,Reduction}.lean`) — **37 theorems verified against a strict CI allowlist (`propext`, `Classical.choice`, `Quot.sound` only; zero `sorry`, zero `native_decide`)**, proving `encodeTweak_injective`, `tweak_fields_no_wrap`, full `WOTS+C` bijection, `sliceCount_eq_spernerIE`, `octopusClimbAux_sibs_consumed`, `decodeImprint_encodeImprint`, `signNormative_sound` (all 6 layer minimalities + `ctr_ft` minimality), `blincs_forgery_dichotomy` (with explicit `exactOctopusSibs <= 45` & chained `FEW_CODE`), and `rng_failure_hedged_fallback` |
| [`test_vectors/`](test_vectors/) | Canonical `3,990`-byte reference imprint + 4 boundary vectors (with SHA-256 & BLAKE3 digests), independently cross-verified in pure Python & TypeScript |
| [`docs/history/manifesto.md`](docs/history/manifesto.md) | Original strategy note that launched the BLINCS project |

---

## Verification Commands

### Rust Teaching Reference Implementation & Fast Certifier Check
```sh
cd reference
cargo fmt -- --check
cargo clippy --all-targets --locked -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --locked
cargo test --release --locked

cd ..
rustc --edition 2024 -O -D warnings tools/upors_cert.rs -o /tmp/upors_cert
/tmp/upors_cert --fast   # < 1s exact rational certification on archived all-orbits sums
/tmp/upors_cert          # ~11 min full recomputation over all 1,614,132 Aut(T_11)-orbits
```

### Lean 4 Formalization (Pinned `leanprover/lean4:v4.36.0`)
```sh
cd formal
lake build
```

### LaTeX Paper (Tectonic)
```sh
cd paper
tectonic -X compile blincs.tex
```

---

## Credits and Thanks

Builds on **BLAKE3** (O'Connor, Aumasson, Neves, Wilcox-O'Hearn) and **SPHINCS / SPHINCS+ / FIPS 205 SLH-DSA** (Bernstein, Hopwood, Hülsing, Kölbl, Lange, Niederhagen, Papachristodoulou, Rijneveld, Schneider, Schwabe, Wilcox-O'Hearn, Kudinov, and the NIST SLH-DSA team), as well as the constant-sum, upper-hypercube, Octopus, and few-time signature literature cited in [`paper/blincs.pdf`](paper/blincs.pdf) and [`DESIGN.md`](DESIGN.md). Thanks to [Project 11](https://research.projecteleven.com/) — especially **Conor Deegan**, **Alessandro Baiocchi**, **Matteo Vena**, and **Matteo Vicari** — for early specification feedback and constrained-device design inspiration.

---

## License

Dual-licensed at your option under any of **MIT**, **Apache-2.0**, or **TGPPL-1.0** (`LICENSE-MIT`, `LICENSE-APACHE`, `LICENSE-TGPPL`), plus **`BOSL-1.0`** (`LICENSE-BOSL.txt`) for any non-code / documentation material as applicable.
