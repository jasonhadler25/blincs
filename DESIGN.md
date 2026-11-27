# BLINCS (`BLINCS-128-A2`) and Signet design rationale

*Thanks to the [Project 11](https://research.projecteleven.com/) research team — **Conor Deegan** (direct review of `SPEC.md`, constrained-device-first parameter search inspiration, SLH-DSA-B with **julienif**, THINCS, CUTS, and the SHRINCS review with **Alex Pruden**), **Alessandro Baiocchi, Matteo Vena, and Matteo Vicari** ([SPHINCS+ Parameter Explorer](https://research.projecteleven.com/tools/sphincs-parameter), [SPHINCS-G benchmarks](https://research.projecteleven.com/articles/sphincs-g-benchmarks), and [taller cached top-tree work](https://research.projecteleven.com/articles/raising-sphincs-lifetime-budgets)), and **Jamie Judd, Louis Tajan, and Furkan Akal** (CUTS) — as well as the authors of BLAKE3, `blake3-servil-core`, SPHINCS/SPHINCS+/FIPS 205, WOTS+C, PORS+FP, Gravity-SPHINCS, and the randomness papers credited in [`README.md`](README.md#credits-and-thanks) and Section 4 below.*

This document records **why** the **BLINCS** (`BLINCS-128-A2`) signature algorithm and **Signet** (`jasonhadler25/signet`, the production Rust implementation of `BLINCS-128-A2`) are shaped the way they are: the threat model, the $2^{32}$ signature budget, the design-space bounds on stateless BLAKE3 signatures, the two-pillar redesign (**`S-WOTS+Z`** constant-sum Sperner hypertree with a `128 KiB` cached top tree + zero-table **`U-PORS`** single-tree Octopus few-time signature) targeting **`≤ 5.0 s` `p99` warm signing on a `160 MHz` Cortex-M33** (e.g., Nitrokey 3 / Trezor Safe 5 — modeled, not measured on Cortex-M hardware) while hitting **`3,292` bytes** (`4,392` B Base64, **2.39× smaller than `SLH-DSA-128s`**), the exact capped-history `U-PORS` certification (`tools/upors_cert.rs`), the equal-budget `q = 2^{64}` scientific comparison baselines (`BLINCS-128-64` / `BLINCS-128-64s`), every candidate technique we evaluated and why each was adopted or declined, the single-pass salted content hash, the lock-free state file, and the crash-only engineering choices. For the normative byte-level definition, see [`SPEC.md`](SPEC.md); for the companion security proof and full tables, see [`paper/blincs.pdf`](paper/blincs.pdf); for the original strategy note that launched the project, see [`docs/history/manifesto.md`](docs/history/manifesto.md).

---

## 1. Goals and threat model

BLINCS is designed for a dishonest submitter who does **not** hold the signing key, interacting with an honest signer and honest verifiers. The attacker may:

- observe up to $2^{32}$ signatures and trigger the honest signer to sign messages the signer approves,
- possess a structural weakness in BLAKE3 that produces **collisions** cheaply without yielding **second preimages**, and
- spend enormous classical compute (a 128-bit security target; BLAKE3 itself claims 128-bit security).

Security-analysis priorities:
1. **Primary:** correct use — unique unpredictable salt per imprint, `< 2^{32}` imprints per signet, secret `seed` (classical single-user 128-bit target; physical CRQC hash-collision costs per Bernstein SHARCS 2009; QROM and multi-user proofs noted as open work).
2. **Secondary:** cheap mitigations for stuck or leaked salt randomness (`saltseed`) or modest overuse (`2^{33}` imprints: `125.48 b` 99% LCB).
3. **Out of scope:** predictable or leaked `seed`.

The design goals that follow:

- **Post-quantum, pure-BLAKE3 assumptions:** security rests solely on symmetric hash properties of BLAKE3 (`KEYED_HASH` and `DERIVE_KEY`, zero XOF mode required) and this SPHINCS-family construction — no lattices, pairings, AES, or factoring.
- **100% pure stateless (no synchronized one-time signing state):** a signing key can be copied across machines, restored from backups, or run in short-lived processes (such as `git commit`) without XMSS/LMS or hybrid stateful rollback hazards.
- **Short verifying key (`32` bytes):** small enough to embed directly in a name or identifier a user already acquires (for example, a repository or branch name).
- **Compact fixed-size signatures (`3,292` bytes / `4,392` bytes Base64):** **2.39× smaller** than `SLH-DSA-128s` (`7,856 B`) and **5.19× smaller** than `SLH-DSA-128f` (`17,088 B`), regardless of whether the signed message is 0 bytes or 100 GiB.
- **Two-pillar `12+7+7+7` `S-WOTS+Z` + `U-PORS` architecture (`8` tweak kinds, `0 B` static lookup tables):**
  - **Hypertree:** `d = 4` layers (`h = 33`), one `128 KiB` cached top tree (`h_top = 12`, `4,096` leaves) + three uniform height-`7` lower trees (`128` leaves each), using ONE uniform OTS primitive (`S-WOTS+Z`: `n = 24, w = 40, S = 468, z = 8`, `2`-byte `u16` counter).
  - **Few-time signature:** ONE height-`10` binary Merkle tree (`1,024` leaves) using `U-PORS(n = 3, w = 24, S = 42, C = 376, k = 10, m_max = 44)` with closed-form hexagon unranking (`0 B` static tables), exact `64`-byte single-block BLAKE3 leaf hashing (`16 + 3 × 16 = 64 B`), Octopus path merging with canonical trailing zero-padding, and indexed `32`-byte `Keyed` codeword derivation (zero XOF).
- **Fast constant-work verification & 100% SIMD-aligned single-threaded signing:** short-message verification executes **`2,231 + m + b` BLAKE3 compressions** (**`2,276`** at `m = 44, b = 1`; exact constant chain work: `468` steps/hypertree layer, `27` steps/opened `U-PORS` leaf) and zero heap allocations; every tree size (`128`, `1,024`, `4,096` leaves -> `3,072` / `98,304` chains) is an exact multiple of `32` SIMD lanes, enabling a single-threaded `12,288`-chain SIMD super-wave via `blake3-servil-core = "=0.11.0"`.
- **Suite-separated key schedule, framed application `Context`, and fail-closed verification:** every algorithm key-derivation context binds `BLINCS-128-A2`, every imprint binds a typed `Context` (`0..=255` bytes, framed as `u8(len(ctx)) || ctx`) into `K_msg`, `R`, and `D_seed`, and verification fails closed.

---

## 2. Why $2^{32}$ signatures, certified capped-history `U-PORS`, and `q = 2^{64}` comparison baselines

The sizing target is one full `u32` of signatures per signing key: **$2^{32} = 4{,}294{,}967{,}296$** (10 signatures every second nonstop for **13.6 years**). Do not imprint more than `2^32` things with one signet.

### Certified capped-history `U-PORS` security (`tools/upors_cert.rs`)

Enforcing the Octopus cap `sibs(S) <= 44` on honest signatures conditions the signer's leaf sets onto `F = {S subset [1024] : |S| = 10, sibs(S) <= 44}` (exact `|F| = 256,172,225,164,499,838,464`, exact `p_cap = 7.6637e-4`, mean `1,304.8` trials). Because `sibs(S) <= 44` forces `sum_{j=1}^9 n_j <= 52`, conditioning on `F` **breaks negative association** and creates `16.01×` sibling clustering (`d = 1`), absorbing `~4.2 b` of the naive uncapped-signer cap credit!

Our zero-dependency 320-bit fixed-point Kronecker-transform + all-37-strata verifier (`tools/upors_cert.rs`, using the certified 3-term exponential upper envelope `u_3(t) = 1 - (8905/7144)(0.81)^t + (1761/7144)(0.05)^t >= q_C(t)` with zero NA/factorization assumptions) certifies:

| Signatures signed by one key (`h = 33`) | Exact Uncapped (`Unc+Unc`, 0 MC) | Certified True `BLINCS-128-A2` (`Cap+Cap`, 99% LCB) | True Net Cap Effect |
|---:|---:|---:|---:|
| $2^{30}$ (1.07B) | `141.17` bits | **`142.83` bits** | `+1.70 b` |
| $2^{31}$ (2.15B) | `135.83` bits | **`137.85` bits** | `+2.06 b` |
| **$2^{32}$ (budget, 4.29B)** | **`129.63` bits** | **`132.13` bits** | **`+2.54 b`** |
| $2^{33}$ ($2\times$, 8.59B) | `122.36` bits | `125.48` bits | `+3.16 b` |
| $2^{34}$ ($4\times$, 17.2B) | `113.83` bits | `117.72` bits | `+3.93 b` |
| $2^{35}$ ($8\times$, 34.4B) | `103.81` bits | `108.63` bits | `+4.85 b` |

### Equal-budget `q = 2^{64}` scientific comparison baselines (exposition only)

To separate the byte savings of `S-WOTS+Z` + `U-PORS` from the `q = 2^{32}` vs. `q = 2^{64}` budget and `128 KiB` cache differences when comparing against `SLH-DSA-128s` (`7,856 B`), [`paper/blincs.pdf`](paper/blincs.pdf) (§7.1) specifies two `h = 65` (`lambda = 0.5`, identical `132.13 b` `U-PORS` bound) scientific comparison baselines:

- **`BLINCS-128-64`** (`d = 8`, `9 + 7×8`, identical `16 KiB` top cache to `SLH-DSA-128s`): **`5,348 B`** (`-31.9%` vs. `SLH-DSA-128s`, est. `~16.7 ms` 1-core M6 sign, `4,212` verify compressions).
- **`BLINCS-128-64s`** (`d = 7`, `11 + 6×9` [`64 KiB`] or `12 + 8 + 5×9` [`128 KiB`]): **`4,962 B`** (`-36.8%` vs. `SLH-DSA-128s`, est. `~25.9–28.1 ms` 1-core M6 sign, `3,736` verify compressions).

All practical engineering, product design, optimization, security hardening, Lean 4 formalization, and shipped implementations (`signet`, `git-signet`) remain focused strictly on flagship **`BLINCS-128-A2`** (`q <= 2^{32}`, `3,292 B`).

---

## 3. Parameter choices & hardware modeling

### Target constrained device: `160 MHz` Cortex-M33 (modeled, not measured)

Our prior `BLINCS-128-7x5` draft targeted zero-cache `60 MHz` Ledger `ST33` (`≤ 5.0 s`), which capped total signing work at `~200k` compressions and forced `d = 7` layers (`6,432 B`–`7,392 B`). Switching the target constrained signer to modern `160 MHz` ARM Cortex-M33 hardware wallets — such as **Nitrokey 3** (`LPC55S69`, 150 MHz, 320 KB RAM) and **Trezor Safe 3 / Safe 5** (`STM32U585`, 160 MHz, 786 KB RAM, 2 MB Flash) — and allowing a **`128 KiB` cached top tree** (`h_top = 12`, stored once in Flash or RAM) unlocks `d = 4` (`12+7+7+7`) and cuts signature size in half to **`3,292 B`**!

*(No Cortex-M hardware has been measured; Cortex-M33 times below are modeled from ~1,500 cycles per Thumb-2 scalar BLAKE3 compression = `9.375 µs/comp` @ 160 MHz with streaming `O(h)` TreeHash.)*

| Operation | Exact BLAKE3 compressions | Modeled `160 MHz` Cortex-M33 | Measured `1-core` Apple M6 (`signet`, `blake3-servil-core 0.11.0`) |
|---|---:|---:|---:|
| `from_seed` (`128 KiB` top tree, `h_top = 12`) | `3,964,927` | ~37.2 s (once at keygen, cached in Flash) | **31.97 ms** |
| Warm sign (`3×` height-7 + `1×` height-10 `U-PORS` + grind) | `447,976` fixed + `2,329` mean / `~8,000` `p99` | **~4.22 s mean / ~4.27 s `p99`** (`1.013×` tail!) | **4.15 ms** (12,288-chain super-wave + self-verify) |
| Verify (short message, `m = 44, b = 1`) | **`2,276`** (`2,231 + m + b`) | **~21.3 ms** | **39.1 µs** (`25,600/s`, zero heap alloc) |

### Why every parameter has its exact value

- **`S-WOTS+Z(n = 24, w = 40, S = 468, z = 8, u16 ctr)`:**
  - `w = 40` is the **minimal** Winternitz base for `n = 24` whose middle-slice Sperner cardinality exceeds $2^{120}$:
    - `w = 39`: $|L_{456}(24, 39)| = 2^{119.730} < 2^{120}$ (mechanically verified directly on `sliceCount` in Lean 4: `wots_w39_lt_pow120`).
    - `w = 40`: $|L_{468}(24, 40)| = 1{,}973{,}221{,}677{,}906{,}098{,}493{,}567{,}206{,}234{,}001{,}571{,}000 = 2^{120.570} > 2^{120}$ (mechanically verified directly on `sliceCount` in Lean 4: `wots_sperner_gt_pow120`).
  - `z = 8` (leading zero byte `h[0] == 0`) paired with the first `2^{120}` ranks gives an exact effective `2^{128}` domain while keeping the `u16` counter (`65,536` slots) safe from exhaustion: $(1 - 2^{-8})^{65536} \approx 2^{-370}$. By contrast, `z = 10` (`1/1024`) would have a `2^{-92.4}` `u16` overflow hazard (`< 128` bits!), so `z = 8` was chosen over `z = 10`.
  - Constant sum `S = 468` makes every layer's verification work **exact constant `468` chain steps** (zero timing/work variance) and requires `0 B` of static lookup tables via `O(S)` boxcar deconvolution (`7.5 KiB` stack RAM; optional `7.5 KiB` precomputed `u128` row cache for `~206 ns` desktop unranking).
- **`U-PORS(n = 3, w = 24, S = 42, C = 376, A = 10, k = 10, m_max = 44, u32 ctr)`:**
  - `n = 3` chains keep `ONE_TIME_KEY` leaf input to `16 + 3 × 16 = 64` bytes (**exact 1 BLAKE3 block**).
  - `S = 42` in `{0..=23}^3` is an **upper-layer constant-sum slice** (above midpoint `34.5`), exploiting **Lattice-Meet Asymmetry** (`q_C(1) = 1/376`, `q_C(2) = 0.17000`, `q_C(3) = 0.33624`) while cutting verification steps to a constant `3 × 23 - 42 = 27` per opened leaf (`270` total) and admitting a **10-line exact closed-form hexagon unranker (`0 B` static lookup tables)**.
  - `m_max = 44` (exact `p_cap = 7.6637e-4`, mean `1,304.8`, `p99 ≈ 6,009` trials) keeps grinding to `< 1.8%` of total `p99` work (`p99/mean = 1.013×`!), eliminates variable-length wire formats via canonical zero-padding (`sibs < 44`), and makes `u32` counter exhaustion impossible ($2^{-4.75 \times 10^6}$).
  - Indexed `32`-byte `Keyed` blocks (`FEW_CODE`, 28 9-bit draws/block, `99.9994%` single block, `2^{-61}` 2-block failure) replace BLAKE3 XOF so Python, TypeScript, Lean 4, and `#![no_std]` verifiers never need XOF mode.

---

## 4. Candidate techniques evaluated: adopted and declined

### Adopted in `BLINCS-128-A2`

1. **BLAKE3 (`Keyed` + `DeriveKey`, zero XOF) as the sole primitive** (`blake3-servil-core = "=0.11.0"`, strictly single-threaded).
2. **`128 KiB` cached top tree (`h_top = 12`, `d = 4`: `12+7+7+7`)** (inspired by Project 11's taller cached top-tree analysis).
3. **`S-WOTS+Z` (`n = 24, w = 40, S = 468, z = 8, u16 ctr`)**: combines Sperner middle-layer constant-sum coding (de Bruijn–Tengbergen–Kruyswijk 1951; Zhang–Cui–Yu [ePrint 2023/850](https://eprint.iacr.org/2023/850); Khovratovich–Kudinov–Wagner [ePrint 2025/889](https://eprint.iacr.org/2025/889)) with zero-bit counter grinding (`WOTS+C` / [ePrint 2022/778](https://eprint.iacr.org/2022/778)) while spending `0%` of grinding budget on sum rejection.
4. **Zero-table `U-PORS` + Octopus merging** (building on `PORS+FP`, Abri & Katz [ePrint 2025/2069](https://eprint.iacr.org/2025/2069), and Octopus, Aumasson & Endignoux [ePrint 2017/933](https://eprint.iacr.org/2017/933), upgraded with 3-chain upper-layer Lattice-Meet Asymmetry, closed-form hexagon unranking, canonical zero-padding, and certified capped-history 320-bit Kronecker bounds in `tools/upors_cert.rs`).
5. **Single-pass salted content hashing (`K_content -> K_msg -> h_msg`)** + hedged post-hash randomizer `R = Keyed(K_R, short || framed_ctx)[..16]` + `D_seed` binding `root`, `R`, `short`, and `framed_ctx`.
6. **Lock-free single-file atomic-rename `Randomness` state** + `Signet::generate(&rng)`.

### Declined (and why)

7. **Crash-Safe `U-PORS` Hybrid / `SHRINCS` ([ePrint 2025/2203](https://eprint.iacr.org/2025/2203)):** keeping BLINCS 100% pure stateless avoids read-only-filesystem degradation, dual-branch format/code complexity, and Feistel/privacy trade-offs once pure stateless size dropped to **`3,292 B`**. (Documented as a research remark in `paper/RESEARCH_NOTES.md §9`.)
8. **Zero-cache `60 MHz` Ledger `ST33` floor (`4,834 B`–`6,432 B`):** `ST33` (`~25 µs/comp`, zero Flash cache) hits a hard black-box floor around `4,690 B`–`4,834 B`; targeting modern `160 MHz` Cortex-M33 + `128 KiB` cached top tree saves **`1,542 B`–`3,140 B`**.
9. **BLAKE3 XOF mode for `U-PORS` codeword sampling:** replaced by indexed `32`-byte `Keyed` hashes (`FEW_CODE`, `99.9994%` single compression, `2^{-61}` 2-block failure) for minimal primitive surface across Rust, Python, TypeScript, and Lean 4.
10. **`z = 10` `S-WOTS+Z` with `u16` counter:** `2^{-92.4}` counter-overflow risk; `z = 8` (`2^{-370}`) eliminates the hazard cleanly.
11. **Classical MDS / Reed–Solomon / $r$-CFF / Golay / Steiner / `CUTS` 2-use WOTS / BLAKE3 VOLEitH / Haraka / AES-NI:** all rigorously bounded in `paper/RESEARCH_NOTES.md §§4, 7` and proven strictly dominated under BLINCS's pure-BLAKE3 stateless constraints.
12. **Library-internal multithreading:** kept strictly single-threaded via `blake3-servil-core = "=0.11.0"` so a signature library never spawns background threads or contends with a host application's scheduler.

---

## 5. Single-pass salted content hashing

| Mode | How the message `M` is hashed | Passes over `M` | Hash assumption on `M` | Examples |
|---|---|---:|---|---|
| **1. Unsalted pre-hash** | Hash `M` first with a fixed hash `H(M)`, then sign the digest | 1 | Unsalted collision resistance | HashSLH-DSA, Ed25519ph |
| **2. Two-pass message-dependent randomization** | Pass 1 derives randomizer `R` from `(key, M)`; Pass 2 hashes `(R, pk, M)` | 2 *(must buffer or rewind `M`)* | Randomized target-collision resistance | Pure SLH-DSA (FIPS 205), Ed25519 |
| **3. Single-pass salted streaming** *(BLINCS)* | Derive fresh salt `e` from `(K_salt, draw)` **before** reading `M`; hash `Keyed(Keyed(K_content, e || framed_ctx), M)` | 1 *(constant-RAM streaming)* | Randomized target-collision resistance *(falls back to 128-bit known-key collision resistance if `e` repeats predictably)* | **BLINCS** |

```text
framed_ctx = u8(len(ctx)) || ctx                   # 1..=256 bytes (bounded application context)
e          = Keyed(K_salt, draw)[..16]             # 16-byte per-signature salt, carried in the signature
K_msg      = Keyed(K_content, e || framed_ctx)     # 32-byte per-signature, per-context message key
h_msg      = Keyed(K_msg, M)                       # 32-byte single-pass keyed BLAKE3 hash of M
short      = e || h_msg                            # 48 bytes
```

When `e` is unpredictable to the submitter until after `M` is committed, `Keyed(K_msg, M)` rests on randomized target-collision resistance. If a salt repeats predictably, content hashing falls back to the 128-bit known-key collision scale of 256-bit keyed BLAKE3 — while signing-key secrecy remains unaffected and `R = Keyed(K_R, short || framed_ctx)[..16]` still hedges distinct messages against advance steering.

---

## 6. Signer randomness: lock-free atomic state file

Signet uses a single private `0600` 32-byte state file rotated via sibling temp file + POSIX atomic `rename` (zero `flock`, zero blocking/deadlocks, forward secrecy on disk by splitting `next_seed`, `run_key`, and `keygen_key` from `prior || getrandom(32) || pid(4) || monotonic_clock`). `Signet::generate(&rng)` combines a domain-separated `keygen_key` draw with fresh 32-byte OS `getrandom(2)` entropy (`Derive(CTX_GENERATE_SIGNET, keygen_draw || os_bytes)`).

---

## 7. Crash-only design and single-threaded SIMD performance engineering

- **Pure crash-only lifecycle (zero `Drop`, zero background threads, zero `thread_local!`):** `Signet` caches its `128 KiB` top tree in memory once on construction. Verification (`SignetId::verify` / `verify_with`) executes `2,276` short-message compressions (`2,231 + m + b` at `m = 44, b = 1`) with **zero heap allocations** via `TreeHasher::on_this_core()`. Signing uses a **merged 12,288-chain single-threaded SIMD super-wave** (`3` height-7 trees × `128 × 24 = 9,216` chains + `1` height-10 `U-PORS` tree × `1,024 × 3 = 3,072` chains stepped together in lockstep!) and `TreeHasher::hash_counter_range` for register-only `ChainSecret`/`OneTimeMsg`/`FewSelect` sweeps.
- **Types carry their rules & fail-stop contracts:** `#![forbid(unsafe_code)]`; `Signet::imprint` / `imprint_with` self-verify every produced imprint (~`39 µs`) before returning and panic on mismatch.

---

## 8. Terminology: `Signet`, `SignetId`, and `Imprint`

Following Mark S. Miller (*Robust Composition*) and Ka-Ping Yee & Mark S. Miller (*Capability Myths Demolished*), a cryptographic signing secret is a transferable **bearer** capability rather than a human identity:

- **`Signet`**: the secret bearer object (derived from a 32-byte seed) that exercises authority by making an imprint.
- **`Imprint`**: the `3,292`-byte mark pressed by a `Signet` onto a message or stream (transparent authenticity only — the message stays in the clear).
- **`SignetId`**: a publisher's self-certifying `32`-byte identifier and complete BLINCS verifying key (`expected_publisher.verify(...)`).
