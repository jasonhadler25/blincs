# BLINCS (`BLINCS-128-A2`)

> **Pre-1.0 — Experimental & Unsupported.** This repository is under active development (draft `0.4.0`); wire formats, parameters, and context strings may still change incompatibly before 1.0. Written primarily by an AI assistant at the direction of this repository's owner; **no independent human cryptographic review or security audit has been performed**. Do not rely on BLINCS to protect production assets.

**BLINCS** is a stateless hash-based signature algorithm based on BLAKE3 and SPHINCS. This repository is the **specification, teaching reference implementation, Lean 4 formalization, and security-analysis paper** for **`BLINCS-128-A2`** (`12+7+7+7` `S-WOTS+Z` hypertree + single height-10 `U-PORS` Octopus tree, **`3,292`-byte** imprints).

- For the **production Rust crate** (12,288-chain single-threaded SIMD super-wave signing, `#![no_std]` zero-alloc verifier + WASM target, lock-free local randomness state), see [`jasonhadler25/signet`](https://github.com/jasonhadler25/signet).
- For **Git commit/tag imprinting** built on `signet`, see [`jasonhadler25/git-signet`](https://github.com/jasonhadler25/git-signet).

---

## Key Properties of `BLINCS-128-A2`

- **Size:** **`3,292`-byte `Imprint`** (`4,392` B Base64 — **2.39× smaller than `SLH-DSA-128s`** [`7,856 B`] and **5.19× smaller than `SLH-DSA-128f`** [`17,088 B`]), `32`-byte `SignetId`, `32`-byte seed, and a `128 KiB` cached top tree (`h_top = 12`, `4,096` leaves). For fair scientific comparison at identical `q = 2^{64}` budget against `SLH-DSA-128s`, [`paper/blincs.pdf`](paper/blincs.pdf) (§7.1) also specifies equal-budget comparison parameterizations (`BLINCS-128-64` at `5,348 B` with identical `16 KiB` top cache, `-31.9%`; `BLINCS-128-64s` at `4,962 B`, `-36.8%`), while all engineering, hardening, formalization, and implementations focus strictly on flagship `BLINCS-128-A2` (`q <= 2^{32}`).
- **100% pure stateless (`q <= 2^{32}`):** zero synchronized one-time signing state; signing keys can be copied across machines, restored from backups, or run in short-lived processes without XMSS/LMS state-reuse hazards. Do not imprint more than `2^32` things with one signet.
- **`S-WOTS+Z` hypertree (`12 + 7 + 7 + 7 = 33`, `d = 4`):** one uniform OTS primitive across all four layers — `n = 24` chains of length `w - 1 = 39`, constant sum `S = 468` (`|L_468(24, 40)| = 1,973,221,677,906,098,493,567,206,234,001,571,000 > 2^{120}`), `z = 8` leading zero-bit counter grinding (`2`-byte `u16` counter, `~256` hashes/layer, effective `2^{128}` domain), exact constant `468` verification steps per layer, and `0 B` of static lookup tables via `O(S)` boxcar deconvolution unranking.
- **Zero-table `U-PORS` Octopus few-time signature (`A = 10, k = 10, m_max = 44`):** one height-10 binary Merkle tree (`1,024` leaves) whose leaves use `n = 3` equal-length chains of length `23` (`a + b + c = 42`, `C = 376` codewords with closed-form arithmetic hexagon unranking — `0 B` static tables), exact `64`-byte single-block BLAKE3 leaf hashing (`16 + 3 × 16 = 64 B`), Octopus path merging capped at `44` authentication nodes with canonical trailing zero-padding, indexed `32`-byte `Keyed` codeword derivation (zero BLAKE3 XOF mode required; `2^{-61}` 2-block failure), and `u32` selection grinding (exact `p_cap = 7.6637e-4`, mean `1,304.8`, `p99 ≈ 6,009`).
- **Certified capped-history `U-PORS` security (`tools/upors_cert.rs`):** accounting for the `16.01×` sibling clustering induced by conditioning honest signatures on `sibs(S) <= 44` (which breaks negative association), our 320-bit Kronecker-transform + all-37-strata verifier certifies **`132.13` bits (`99%` LCB)** raw-query security at $q = 2^{32}$ (`+2.54 b` net cap gain over `129.63 b` zero-MC uncapped; `125.48 b` at `2×` overuse $q = 2^{33}$). Classical single-user target (`128`-bit); physical CRQC hash-collision costs follow Bernstein (SHARCS 2009), with QROM and multi-user proofs noted as open problems.
- **Fast constant-work verification & SIMD-aligned signing:** **`2,231 + m + b` short-message compressions** to verify (**`2,276`** at `m = 44, b = 1`; `~39.1 µs` single-core Apple M6, zero heap allocations); `100%` 32-lane SIMD alignment across all trees (`128`, `1,024`, `4,096` leaves; `3,072` chains/tree); modeled at `~4.27 s` `p99` warm signing on a `160 MHz` Cortex-M33 (e.g., Nitrokey 3 / Trezor Safe 5 — modeled only, no Cortex-M hardware has been measured).
- **Single-pass salted content hashing:** streams arbitrarily large messages in a single pass under a fresh per-imprint salt `e` drawn before `M` is committed, while keeping hedged post-hash randomizer `R = Keyed(K_R, e || h_msg || framed_ctx)[..16]` resilient if the salt draw repeats.

---

## Repository Contents

| Path | Description |
|---|---|
| [`SPEC.md`](SPEC.md) | Normative byte-level specification of `BLINCS-128-A2` (draft `0.4.0`), including fail-closed exhaustion rules and §13 startup self-test guidance |
| [`DESIGN.md`](DESIGN.md) | Design-space rationale, certified capped-history `U-PORS` bounds, `q = 2^{64}` comparison ablation, and adopted vs. declined techniques |
| [`paper/blincs.pdf`](paper/blincs.pdf) | Cryptography technical report (`paper/blincs.tex`, `blincs.bib`): exact capped-history `U-PORS` clustering proof & 320-bit certified bounds, single-user classical ROM+PRF EUF-CMA reduction, Lean 4 formalization boundary, equal-budget `q = 2^{64}` scientific comparison variants (`BLINCS-128-64` / `BLINCS-128-64s`), and physical CRQC collision-cost analysis (Bernstein, SHARCS 2009) |
| [`tools/upors_cert.rs`](tools/upors_cert.rs) | Standalone zero-dependency Rust verifier computing exact `|F|`, `p_cap`, pairwise clustering, 3-term exponential upper envelope `u_3(t) >= q_C(t)`, 320-bit Kronecker transforms, and all-37-strata 99% LCB bounds |
| [`paper/RESEARCH_NOTES.md`](paper/RESEARCH_NOTES.md) | Exploratory design-search ledger (§§1–10) from the parameter-search phase (superseded on capped-history `U-PORS` bounds by `tools/upors_cert.rs` and `paper/blincs.pdf` §4) |
| [`reference/`](reference/) | Teaching-clarity Rust reference implementation (`#![forbid(unsafe_code)]`, strictly single-threaded `blake3-servil-core = "=0.11.0"`, `self_test()`, matching all 5 canonical `3,292 B` vectors byte-for-byte) |
| [`formal/`](formal/) | Spec-exact declarative **Lean 4.36.0** formalization (`Blincs/{Params,Tweaks,Wots,Merkle,Scheme,Reduction}.lean`) — **26 kernel-checked theorems, zero `sorry`, zero `native_decide`, zero custom axioms**, aligned byte-for-byte with `SPEC.md`, proving direct `sliceCount_eq_spernerIE` & `wots_sperner_cardinality`, wire parser round-trip bijectivity (`decodeImprint_encodeImprint`), `extractUporsLeaves_spec`, conditional `blincs_completeness`, provenance- and target-bound 13-witness `blincs_forgery_dichotomy`, and `rng_failure_hedged_fallback` |
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
