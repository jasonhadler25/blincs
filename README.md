# BLINCS (`BLINCS-128-7x5`)

> **Pre-1.0 — Experimental & Unsupported.** This repository is under active development (draft `0.2.0`); wire formats, parameters, and context strings may still change incompatibly before 1.0. Written primarily by an AI assistant at the direction of this repository's owner; **no independent human cryptographic review or security audit has been performed**. Do not rely on BLINCS to protect production assets.

**BLINCS** is a stateless hash-based signature algorithm based on BLAKE3 and SPHINCS. This repository is the **specification, teaching reference implementation, Lean 4 formalization, and security-analysis paper** for **`BLINCS-128-7x5`** (`U-FORS` unified height-5 architecture).

- For the **production Rust crate** (batched SIMD signing, `#![no_std]` verifier + WASM target, lock-free local randomness state), see [`jasonhadler25/signet`](https://github.com/jasonhadler25/signet).
- For **Git commit/tag imprinting** built on `signet`, see [`jasonhadler25/git-signet`](https://github.com/jasonhadler25/git-signet).

---

## Key Properties of `BLINCS-128-7x5` (`U-FORS`)

- **Size:** `6,432`-byte `Imprint` (`8,576` B Base64 — `1,424` B smaller than `SLH-DSA-128s`), `32`-byte `SignetId`, `32`-byte seed, `1 KiB` top tree.
- **Unified structure:** **one** Merkle tree height (`5`, `32` leaves per tree) across all `7` hypertree layers and all `15` `U-FORS` trees, **one** hash-chain leaf primitive (`35` chains of length `15` in the hypertree, `3` equal-length chains of length `9` in `U-FORS` fitting in **one single 64-byte BLAKE3 compression**), and only **`6`** tweak kinds.
- **Upper-Layer Constant-Sum Lattice Forest (`U-FORS`):** replaces raw-secret FORS leaves with a canonical 64-element constant-sum antichain in `{0..=9}^3` (`a + b + c = 16`, `192`-byte lookup table), giving **138.48 bits** exact dynamic-programming `ITSR` security at $q = 2^{32}$ (`132.13` bits at $2^{33}$, `124.73` bits at $2^{34}$, `116.05` bits at $2^{35}$), constant `11` verification chain steps per tree, and `1,440 = 45 × 32` equal-length SIMD chains. Do not imprint more than $2^{32}$ things with one signet.
- **Zero counter grinding:** constant compression count (`143,022` cold / `125,343` max warm; `p99 = mean = max`), modeled below `5 s` on a 60 MHz Ledger `ST33` Secure Element (no Cortex-M hardware has been measured).
- **Single-pass salted content hashing:** streams arbitrarily large messages in a single pass under a fresh per-imprint salt `e` drawn upfront, while keeping hedged post-hash randomizer `R = Keyed(K_R, e || h_msg || framed_ctx)[..16]` resilient even if the salt source repeats.

---

## Repository Contents

| Path | Description |
|---|---|
| [`SPEC.md`](SPEC.md) | Normative byte-level specification of `BLINCS-128-7x5`, including §12 startup self-test guidance |
| [`DESIGN.md`](DESIGN.md) | Parameter-search rationale, coding-theory trade-offs, and adopted vs. declined techniques |
| [`paper/blincs.pdf`](paper/blincs.pdf) | Cryptography technical report (`paper/blincs.tex`, `blincs.bib`): `U-FORS` coding-theory analysis, concrete $\mathrm{EUF\text{-}CMA}$ & attacker-generous BLAKE3 2nd-preimage reductions, salt-failure fallback, and bidirectional SPHINCS+ / FIPS 205 lifting matrix |
| [`paper/RESEARCH_NOTES.md`](paper/RESEARCH_NOTES.md) | Detailed research notes, exact DP tables across BLINCS & FIPS 205 `SLH-DSA-128s/f`, tested coding families, and 2023–2026 literature notes |
| [`reference/`](reference/) | Teaching-clarity Rust reference implementation (`#![forbid(unsafe_code)]`, strictly single-threaded `blake3-servil-core = "=0.11.0"`, `self_test()`, matching all 5 canonical vectors byte-for-byte) |
| [`formal/`](formal/) | Complete declarative **Lean 4.36.0** formalization (`Blincs/{Params,Tweaks,Wots,Merkle,Scheme,Reduction}.lean`) — **zero `sorry`, zero custom axioms**, proving completeness, tweak/context injectivity, `UFORS_CODE` antichain/sum, WOTS+ dominance, wire bijection (`6,432 B`), exhaustive 12-witness `blincs_forgery_dichotomy`, and `rng_failure_hedged_fallback` |
| [`test_vectors/`](test_vectors/) | Canonical `6,432`-byte reference imprint + 4 boundary vectors (with SHA-256 & BLAKE3 digests), independently generated from scratch in Python |
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

Builds on **BLAKE3** (O'Connor, Aumasson, Neves, Wilcox-O'Hearn) and **SPHINCS / SPHINCS+ / FIPS 205 SLH-DSA** (Bernstein, Hopwood, Hülsing, Kölbl, Lange, Niederhagen, Papachristodoulou, Rijneveld, Schneider, Schwabe, Wilcox-O'Hearn, Kudinov, and the NIST SLH-DSA team), as well as the constant-sum, upper-hypercube, and few-time signature literature cited in [`paper/blincs.pdf`](paper/blincs.pdf) and [`DESIGN.md`](DESIGN.md). Thanks to [Project 11](https://research.projecteleven.com/) — especially **Conor Deegan**, **Alessandro Baiocchi**, **Matteo Vena**, and **Matteo Vicari** — for direct review feedback, benchmarks, and constrained-device design insights.

---

## License

Dual-licensed at your option under any of **MIT**, **Apache-2.0**, or **TGPPL-1.0** (`LICENSE-MIT`, `LICENSE-APACHE`, `LICENSE-TGPPL`), plus **`BOSL-1.0`** (`LICENSE-BOSL.txt`) for any non-code / documentation material as applicable.
