# BLINCS (`BLINCS-128-A2`)

> **Pre-1.0 — Experimental & Unsupported.** This repository is under active development (draft `0.3.0`); wire formats, parameters, and context strings may still change incompatibly before 1.0. Written primarily by an AI assistant at the direction of this repository's owner; **no independent human cryptographic review or security audit has been performed**. Do not rely on BLINCS to protect production assets.

**BLINCS** is a stateless hash-based signature algorithm based on BLAKE3 and SPHINCS. This repository is the **specification, teaching reference implementation, Lean 4 formalization, and security-analysis paper** for **`BLINCS-128-A2`** (`12+7+7+7` `S-WOTS+Z` hypertree + single height-10 `U-PORS` Octopus tree, **`3,292`-byte** imprints).

- For the **production Rust crate** (12,288-chain single-threaded SIMD super-wave signing, `#![no_std]` zero-alloc verifier + WASM target, lock-free local randomness state), see [`jasonhadler25/signet`](https://github.com/jasonhadler25/signet).
- For **Git commit/tag imprinting** built on `signet`, see [`jasonhadler25/git-signet`](https://github.com/jasonhadler25/git-signet).

---

## Key Properties of `BLINCS-128-A2`

- **Size:** **`3,292`-byte `Imprint`** (`4,392` B Base64 — **2.39× smaller than `SLH-DSA-128s`** [`7,856 B`] and **5.19× smaller than `SLH-DSA-128f`** [`17,088 B`]), `32`-byte `SignetId`, `32`-byte seed, and a `128 KiB` cached top tree (`h_top = 12`, `4,096` leaves).
- **100% pure stateless (`q = 2^{32}`):** zero synchronized one-time signing state; signing keys can be copied across machines, restored from backups, or run in short-lived processes without XMSS/LMS state-reuse hazards. Do not imprint more than `2^32` things with one signet.
- **`S-WOTS+Z` hypertree (`12 + 7 + 7 + 7 = 33`, `d = 4`):** one uniform OTS primitive across all four layers — `n = 24` chains of length `w - 1 = 39`, constant sum `S = 468` (`|L_468(24, 40)| = 1,973,221,677,906,098,493,567,206,234,001,571,000 > 2^{120}`), `z = 8` leading zero-bit counter grinding (`2`-byte `u16` counter, `~256` hashes/layer), exact constant `468` verification steps per layer, and `0 B` required ROM via `O(S)` boxcar deconvolution unranking.
- **Zero-ROM `U-PORS` Octopus few-time signature (`A = 10, k = 10, m_max = 44`):** one height-10 binary Merkle tree (`1,024` leaves) whose leaves use `n = 3` equal-length chains of length `23` (`a + b + c = 42`, `C = 376` codewords with closed-form arithmetic hexagon unranking — `0 B` ROM), exact `64`-byte single-block BLAKE3 leaf hashing (`16 + 3 × 16 = 64 B`), Octopus path merging capped at `44` authentication nodes with canonical trailing zero-padding, indexed `32`-byte `Keyed` codeword derivation (zero BLAKE3 XOF mode required), and `u32` selection grinding (`mean ≈ 1,365`, `p99 ≈ 6,287`).
- **Elementary zero-cap-credit security margin:** **`128.58` bits** at $q = 2^{32}$ purely from elementary without-replacement hypergeometric dynamic programming (zero cap credit needed in the proof!), rising to **`135.37` bits** true at $q = 2^{32}$ and remaining **`128.91` bits** (`> 128` bits) even at $2\times$ overuse ($q = 2^{33}$).
- **Fast constant-work verification & SIMD-aligned signing:** **`2,263` exact constant compressions** to verify (`~39 µs` single-core Apple M6, zero heap allocations); `100%` 32-lane SIMD alignment across all trees (`128`, `1,024`, `4,096` leaves; `3,072` chains/tree); modeled at `~4.29 s` `p99` warm signing on a `160 MHz` Cortex-M33 (e.g., Nitrokey 3 / Trezor Safe 5 — modeled only, no Cortex-M hardware has been measured).
- **Single-pass salted content hashing:** streams arbitrarily large messages in a single pass under a fresh per-imprint salt `e` drawn upfront, while keeping hedged post-hash randomizer `R = Keyed(K_R, e || h_msg || framed_ctx)[..16]` resilient even if the salt source repeats.

---

## Repository Contents

| Path | Description |
|---|---|
| [`SPEC.md`](SPEC.md) | Normative byte-level specification of `BLINCS-128-A2` (draft `0.3.0`), including §13 startup self-test guidance |
| [`DESIGN.md`](DESIGN.md) | Parameter-search rationale, black-box bounds, coding-theory trade-offs, and adopted vs. declined techniques |
| [`paper/blincs.pdf`](paper/blincs.pdf) | Cryptography technical report (`paper/blincs.tex`, `blincs.bib`): black-box bounds, `S-WOTS+Z` + `U-PORS` Lattice-Meet Asymmetry & Octopus analysis, concrete $\mathrm{EUF\text{-}CMA}$ & attacker-generous BLAKE3 2nd-preimage reductions, salt-failure fallback, and bidirectional SPHINCS+ / FIPS 205 lifting matrix |
| [`paper/RESEARCH_NOTES.md`](paper/RESEARCH_NOTES.md) | Complete traceable research ledger (§§1–10): exact DP tables, 2M-trial Octopus distributions, importance-sampling cap verification, and SOTA comparisons |
| [`reference/`](reference/) | Teaching-clarity Rust reference implementation (`#![forbid(unsafe_code)]`, strictly single-threaded `blake3-servil-core = "=0.11.0"`, `self_test()`, matching all 5 canonical `3,292 B` vectors byte-for-byte) |
| [`formal/`](formal/) | Complete declarative **Lean 4.36.0** formalization (`Blincs/{Params,Tweaks,Wots,Merkle,Scheme,Reduction}.lean`) — **zero `sorry`, zero custom axioms**, proving completeness, tweak/context injectivity, exact `S-WOTS+Z` Sperner cardinality (`> 2^120`), `U-PORS` & `S-WOTS+Z` constant-sum antichain dominance, Octopus completeness & collision extraction, wire bijection (`3,292 B`), exhaustive 13-witness `blincs_forgery_dichotomy`, and `rng_failure_hedged_fallback` |
| [`test_vectors/`](test_vectors/) | Canonical `3,292`-byte reference imprint + 4 boundary vectors (with SHA-256 & BLAKE3 digests), independently cross-verified in pure Python |
| [`docs/history/manifesto.md`](docs/history/manifesto.md) | Original strategy note that launched the BLINCS project |

---

## Verification Commands

### Rust Teaching Reference Implementation
```sh
cd reference
cargo fmt -- --check
cargo clippy --all-targets --locked -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --locked
cargo test --release --locked
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

Builds on **BLAKE3** (O'Connor, Aumasson, Neves, Wilcox-O'Hearn) and **SPHINCS / SPHINCS+ / FIPS 205 SLH-DSA** (Bernstein, Hopwood, Hülsing, Kölbl, Lange, Niederhagen, Papachristodoulou, Rijneveld, Schneider, Schwabe, Wilcox-O'Hearn, Kudinov, and the NIST SLH-DSA team), as well as the constant-sum, upper-hypercube, Octopus, and few-time signature literature cited in [`paper/blincs.pdf`](paper/blincs.pdf) and [`DESIGN.md`](DESIGN.md). Thanks to [Project 11](https://research.projecteleven.com/) — especially **Conor Deegan**, **Alessandro Baiocchi**, **Matteo Vena**, and **Matteo Vicari** — for direct review feedback, benchmarks, and constrained-device design insights.

---

## License

Dual-licensed at your option under any of **MIT**, **Apache-2.0**, or **TGPPL-1.0** (`LICENSE-MIT`, `LICENSE-APACHE`, `LICENSE-TGPPL`), plus **`BOSL-1.0`** (`LICENSE-BOSL.txt`) for any non-code / documentation material as applicable.
