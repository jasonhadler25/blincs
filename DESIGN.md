# BLINCS (`BLINCS-128-A2`) and Signet design rationale

*Thanks to the [Project 11](https://research.projecteleven.com/) research team — **Conor Deegan** (direct review of `SPEC.md`, constrained-device-first parameter search inspiration, SLH-DSA-B with **julienif**, THINCS, CUTS, and the SHRINCS review with **Alex Pruden**), **Alessandro Baiocchi, Matteo Vena, and Matteo Vicari** ([SPHINCS+ Parameter Explorer](https://research.projecteleven.com/tools/sphincs-parameter), [SPHINCS-G benchmarks](https://research.projecteleven.com/articles/sphincs-g-benchmarks), and [taller cached top-tree work](https://research.projecteleven.com/articles/raising-sphincs-lifetime-budgets)), and **Jamie Judd, Louis Tajan, and Furkan Akal** (CUTS) — as well as the authors of BLAKE3, `blake3-servil-core`, SPHINCS/SPHINCS+/FIPS 205, WOTS+C, PORS+FP, Gravity-SPHINCS, and the randomness papers credited in [`README.md`](README.md#credits-and-thanks) and Section 4 below.*

This document records **why** the **BLINCS** (`BLINCS-128-A2`) signature algorithm and **Signet** (`jasonhadler25/signet`, the production Rust implementation of `BLINCS-128-A2`) are shaped the way they are: the threat model, the $2^{32}$ signature budget, the hard black-box bounds we proved on stateless BLAKE3 signatures, the two-pillar redesign (**`S-WOTS+Z`** constant-sum Sperner hypertree with a `128 KiB` cached top tree + zero-ROM **`U-PORS`** single-tree Octopus few-time signature) targeting **`≤ 5.0 s` `p99` warm signing on a `160 MHz` Cortex-M33** (e.g., Nitrokey 3 / Trezor Safe 5 — modeled, not measured on Cortex-M hardware) while hitting **`3,292` bytes** (`4,392` B Base64, **2.39× smaller than `SLH-DSA-128s`**), every candidate technique we evaluated and why each was adopted or declined, the single-pass salted content hash, the lock-free state file, and the crash-only engineering choices. For the normative byte-level definition, see [`SPEC.md`](SPEC.md); for the full combinatorial ledger, see [`paper/RESEARCH_NOTES.md`](paper/RESEARCH_NOTES.md); for the companion security proof, see [`paper/blincs.pdf`](paper/blincs.pdf); for the original strategy note that launched the project, see [`docs/history/manifesto.md`](docs/history/manifesto.md).

---

## 1. Goals and threat model

BLINCS is designed for a dishonest submitter who does **not** hold the signing key, interacting with an honest signer and honest verifiers. The attacker may:

- observe up to $2^{32}$ signatures and trigger the honest signer to sign messages the signer approves,
- possess a structural weakness in BLAKE3 that produces **collisions** cheaply without yielding **second preimages**, and
- spend enormous classical compute (a 128-bit security target; BLAKE3 itself claims 128-bit security).

Security-analysis priorities:
1. **Primary:** correct use — unique unpredictable salt per imprint, $< 2^{32}$ imprints per signet, secret `seed`.
2. **Secondary:** cheap mitigations for stuck or leaked salt randomness (`saltseed`) or modest overuse (`2^{33}` imprints).
3. **Out of scope:** predictable or leaked `seed`.

The design goals that follow:

- **Post-quantum, pure-BLAKE3 assumptions:** security rests solely on symmetric hash properties of BLAKE3 (`KEYED_HASH` and `DERIVE_KEY`, zero XOF mode required) and this SPHINCS-family construction — no lattices, pairings, AES, or factoring.
- **100% pure stateless (no synchronized one-time signing state):** a signing key can be copied across machines, restored from backups, or run in short-lived processes (such as `git commit`) without XMSS/LMS or hybrid stateful rollback hazards.
- **Short verifying key (`32` bytes):** small enough to embed directly in a name or identifier a user already acquires (for example, a repository or branch name).
- **Compact fixed-size signatures (`3,292` bytes / `4,392` bytes Base64):** **2.39× smaller** than `SLH-DSA-128s` (`7,856 B`) and **5.19× smaller** than `SLH-DSA-128f` (`17,088 B`), regardless of whether the signed message is 0 bytes or 100 GiB.
- **Two-pillar `12+7+7+7` `S-WOTS+Z` + `U-PORS` architecture (`8` tweak kinds, `0 B` required ROM):**
  - **Hypertree:** `d = 4` layers (`h = 33`), one `128 KiB` cached top tree (`h_top = 12`, `4,096` leaves) + three uniform height-`7` lower trees (`128` leaves each), using ONE uniform OTS primitive (`S-WOTS+Z`: `n = 24, w = 40, S = 468, z = 8`, `2`-byte `u16` counter).
  - **Few-time signature:** ONE height-`10` binary Merkle tree (`1,024` leaves) using `U-PORS(n = 3, w = 24, S = 42, C = 376, k = 10, m_max = 44)` with closed-form hexagon unranking (`0 B` ROM), exact `64`-byte single-block BLAKE3 leaf hashing (`16 + 3 × 16 = 64 B`), Octopus path merging with canonical trailing zero-padding, and indexed `32`-byte `Keyed` codeword derivation (zero XOF).
- **Fast constant-work verification & 100% SIMD-aligned single-threaded signing:** verification executes **`2,263` exact constant BLAKE3 compressions** (no data-dependent chain-length variance!) and zero heap allocations; every tree size (`128`, `1,024`, `4,096` leaves -> `3,072` / `98,304` chains) is an exact multiple of `32` SIMD lanes, enabling a single-threaded `12,288`-chain SIMD super-wave via `blake3-servil-core = "=0.11.0"`.
- **Suite-separated key schedule, framed application `Context`, and fail-closed verification:** every algorithm key-derivation context binds `BLINCS-128-A2`, every imprint binds a typed `Context` (`0..=255` bytes, framed as `u8(len(ctx)) || ctx`) into `K_msg`, `R`, and `D_seed`, and verification fails closed.

---

## 2. Why $2^{32}$ signatures and why `3,292` bytes is near the black-box BLAKE3 floor

The sizing target is one full `u32` of signatures per signing key: **$2^{32} = 4{,}294{,}967{,}296$** (10 signatures every second nonstop for **13.6 years**). Do not imprint more than `2^32` things with one signet.

### Black-box walls we proved before picking parameters

Before finalizing `BLINCS-128-A2`, we analyzed the hard information-theoretic walls for any black-box BLAKE3 stateless signature at $q = 2^{32}$ and 128-bit security (`paper/RESEARCH_NOTES.md §7`):

1. **Bleichenbacher–Maurer OTS DAG bound (1996):** any black-box 1-time signature with `128`-bit resistance needs $\ge n \cdot 2^{128/n}$ hashes for `n` chains (`16n` bytes) and $\ge 241$ hashes/leaf unconditionally.
2. **2-use WOTS (`CUTS`) 3-way symmetry bound:** for any marginal on $\{0,\dots,w-1\}$, three i.i.d. draws satisfy $\Pr[Y \ge \min(X_1, X_2)] \ge 2/3$, capping 2-use chains at $\le 0.585$ bits/chain ($\ge 219$ chains = `3,504 B`), strictly worse than 1-use WOTS + 1 Merkle level.
3. **BLAKE3 VOLE-in-the-Head (`FAEST`-style):** BLAKE3's 32-bit ARX additions take `~10,752` non-linear AND gates per compression (`8.4×` AES-128), yielding `~12–18 KiB` proofs.
4. **16-byte hash width:** every chain value and Merkle node must stay `16 B` (`128` bits) against 2nd-preimage and chain-inversion attacks.

With a `128 KiB` cached top tree (`h_top = 12`) and a `≤ 5.0 s` `p99` warm signing budget on a `160 MHz` Cortex-M33 (`~530k` compressions), **`BLINCS-128-A2` (`3,292 B`)** sits right at the Pareto knee of pure black-box stateless BLAKE3 signatures — slashing size by **48.8%** vs. our prior zero-cache `U-FORS` (`6,432 B`), **55.5%** vs. original `FORS(8,20)` (`7,392 B`), and **58.1%** vs. NIST FIPS 205 `SLH-DSA-128s` (`7,856 B`).

### Exact `U-PORS` security table (elementary zero-cap-credit AND true importance-sampled)

| Signatures signed by one key | Elementary zero-cap-credit DP (`BLINCS-128-A2`) | True security incl. Octopus cap (`m_max = 44`, IS `6000×32`) |
|---:|---:|---:|
| $2^{32}$ (budget, 4.29B) | **128.58 bits** | **135.37 bits** |
| $2^{33}$ ($2\times$, 8.59B) | 121.56 bits | **128.91 bits** |
| $2^{34}$ ($4\times$, 17.2B) | 113.71 bits | 121.48 bits |
| $2^{35}$ ($8\times$, 34.4B) | 104.88 bits | 112.88 bits |

Crucially, `BLINCS-128-A2` clears **128.58 bits at $q = 2^{32}$ purely from the elementary without-replacement hypergeometric DP with ZERO cap credit** — so neither the paper proof nor the Lean 4 formalization depends on Monte Carlo estimation — while the verifier-enforced Octopus cap (`m_max = 44`, `p_cap ≈ 0.0007325`) contributes `+6.79` additional true bits at $2^{32}$ and keeps true security above `128` bits even at $2\times$ overuse ($2^{33}$).

---

## 3. Parameter choices & hardware modeling

### Target constrained device: `160 MHz` Cortex-M33 (modeled, not measured)

Our prior `BLINCS-128-7x5` draft targeted zero-cache `60 MHz` Ledger `ST33` (`≤ 5.0 s`), which capped total signing work at `~200k` compressions and forced `d = 7` layers (`6,432 B`–`7,392 B`). Switching the target constrained signer to modern `160 MHz` ARM Cortex-M33 hardware wallets — such as **Nitrokey 3** (`LPC55S69`, 150 MHz, 320 KB RAM) and **Trezor Safe 3 / Safe 5** (`STM32U585`, 160 MHz, 786 KB RAM, 2 MB Flash) — and allowing a **`128 KiB` cached top tree** (`h_top = 12`, stored once in Flash or RAM) unlocks `d = 4` (`12+7+7+7`) and cuts signature size in half to **`3,292 B`**!

*(No Cortex-M hardware has been measured; Cortex-M33 times below are modeled from ~1,500 cycles per Thumb-2 scalar BLAKE3 compression = `9.375 µs/comp` @ 160 MHz with streaming `O(h)` TreeHash.)*

| Operation | Exact BLAKE3 compressions | Modeled `160 MHz` Cortex-M33 | Modeled `1-core` Apple M6 (`blake3-servil-core 0.11.0`) |
|---|---:|---:|---:|
| `from_seed` (`128 KiB` top tree, `h_top = 12`) | `3,964,927` | ~37.2 s (once at keygen, cached in Flash) | ~31.6–32.0 ms |
| Warm sign (`3×` height-7 + `1×` height-10 `U-PORS` + grind) | `447,976` fixed + `2,389` mean / `~8,000` `p99` | **~4.22 s mean / ~4.29 s `p99`** (`1.013×` tail!) | **~3.80 ms** (12,288-chain super-wave) |
| Verify (`2,263` exact constant) | **`2,263`** | **~21.2 ms** | **~39.1 µs** (`25,600/s`, zero heap alloc) |

### Why every parameter has its exact value

- **`S-WOTS+Z(n = 24, w = 40, S = 468, z = 8, u16 ctr)`:**
  - `w = 40` is the **minimal** Winternitz base for `n = 24` whose middle-slice Sperner cardinality exceeds $2^{120}$:
    - `w = 39`: $|L_{456}(24, 39)| = 2^{119.730} < 2^{120}$ (mechanically verified in Lean 4: `wots_w39_lt_pow120`).
    - `w = 40`: $|L_{468}(24, 40)| = 1{,}973{,}221{,}677{,}906{,}098{,}493{,}567{,}206{,}234{,}001{,}571{,}000 = 2^{120.570} > 2^{120}$ (mechanically verified in Lean 4: `wots_sperner_gt_pow120`).
  - `z = 8` (leading zero byte `h[0] == 0`) lifts `120.57` bits to **`128.57` bits** while keeping the `u16` counter (`65,536` slots) utterly safe from overflow: $(1 - 2^{-8})^{65536} \approx 2^{-370}$. By contrast, `z = 10` (`1/1024`) would have a `2^{-92.4}` `u16` overflow hazard (`< 128` bits!), so `z = 8` was chosen over `z = 10`.
  - Constant sum `S = 468` makes every layer's verification work **exact constant `468` chain steps** (zero timing/work variance) and requires `0 B` of ROM via `O(S)` boxcar deconvolution (`7.5 KiB` precomputed `u128` row table optional for ~`206 ns` desktop unranking).
- **`U-PORS(n = 3, w = 24, S = 42, C = 376, A = 10, k = 10, m_max = 44, u32 ctr)`:**
  - `n = 3` chains keep `ONE_TIME_KEY` leaf input to `16 + 3 × 16 = 64` bytes (**exact 1 BLAKE3 block**).
  - `S = 42` in `{0..=23}^3` is an **upper-layer constant-sum slice** (above midpoint `34.5`), exploiting **Lattice-Meet Asymmetry** (`lc[1] = 1/376`, `lc[2] = 0.1462`, `lc[3] = 0.3056`) while cutting verification steps to a constant `3 × 23 - 42 = 27` per opened leaf (`270` total) and admitting a **12-line exact closed-form hexagon unranker (`0 B` ROM!)**.
  - `m_max = 44` (`p_cap = 0.0007325`, `mean = 1,365`, `p99 = 6,287` trials on 2M trials) keeps grinding to `< 1.8%` of total `p99` work (`p99/mean = 1.013×`!), eliminates variable-length wire formats via canonical zero-padding (`sibs < 44`), and makes `u32` counter exhaustion impossible ($2^{-4.54 \times 10^6}$).
  - Indexed `32`-byte `Keyed` blocks (`FEW_CODE`, 28 9-bit draws/block, `99.9996%` single block) replace BLAKE3 XOF so Python, TypeScript, Lean 4, and `#![no_std]` verifiers never need XOF mode.

---

## 4. Candidate techniques evaluated: adopted and declined

### Adopted in `BLINCS-128-A2`

1. **BLAKE3 (`Keyed` + `DeriveKey`, zero XOF) as the sole primitive** (`blake3-servil-core = "=0.11.0"`, strictly single-threaded).
2. **`128 KiB` cached top tree (`h_top = 12`, `d = 4`: `12+7+7+7`)** (inspired by Project 11's taller cached top-tree analysis).
3. **`S-WOTS+Z` (`n = 24, w = 40, S = 468, z = 8, u16 ctr`)**: combines Sperner middle-layer constant-sum coding (de Bruijn–Tengbergen–Kruyswijk 1951; Zhang–Cui–Yu [ePrint 2023/850](https://eprint.iacr.org/2023/850); Khovratovich–Kudinov–Wagner [ePrint 2025/889](https://eprint.iacr.org/2025/889)) with zero-bit counter grinding (`WOTS+C` / [ePrint 2022/778](https://eprint.iacr.org/2022/778)) while spending `0%` of grinding budget on sum rejection.
4. **Zero-ROM `U-PORS` + Octopus merging** (building on `PORS+FP`, Abri & Katz [ePrint 2025/2069](https://eprint.iacr.org/2025/2069), and Octopus, Aumasson & Endignoux [ePrint 2017/933](https://eprint.iacr.org/2017/933), upgraded with 3-chain upper-layer Lattice-Meet Asymmetry, closed-form hexagon unranking, without-replacement hypergeometric DP, and canonical zero-padding).
5. **Single-pass salted content hashing (`K_content -> K_msg -> h_msg`)** + hedged post-hash randomizer `R = Keyed(K_R, short || framed_ctx)[..16]` + `D_seed` binding `root`, `R`, `short`, and `framed_ctx`.
6. **Lock-free single-file atomic-rename `Randomness` state** + `Signet::generate(&rng)`.

### Declined (and why)

7. **Crash-Safe `U-PORS` Hybrid / `SHRINCS` ([ePrint 2025/2203](https://eprint.iacr.org/2025/2203)):** keeping BLINCS 100% pure stateless avoids read-only-filesystem degradation, dual-branch format/code complexity, and Feistel/privacy trade-offs once pure stateless size dropped to **`3,292 B`**. (Documented as a research remark in `paper/RESEARCH_NOTES.md §9`.)
8. **Zero-cache `60 MHz` Ledger `ST33` floor (`4,834 B`–`6,432 B`):** `ST33` (`~25 µs/comp`, zero Flash cache) hits a hard black-box floor around `4,690 B`–`4,834 B`; targeting modern `160 MHz` Cortex-M33 + `128 KiB` cached top tree saves **`1,542 B`–`3,140 B`**.
9. **BLAKE3 XOF mode for `U-PORS` codeword sampling:** replaced by indexed `32`-byte `Keyed` hashes (`FEW_CODE`, `99.9996%` single compression) for minimal primitive surface across Rust, Python, TypeScript, and Lean 4.
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

- **Pure crash-only lifecycle (zero `Drop`, zero background threads, zero `thread_local!`):** `Signet` caches its `128 KiB` top tree in memory once on construction. Verification (`SignetId::verify` / `verify_with`) executes `2,263` constant compressions with **zero heap allocations** via `TreeHasher::on_this_core()`. Signing uses a **merged 12,288-chain single-threaded SIMD super-wave** (`3` height-7 trees × `128 × 24 = 9,216` chains + `1` height-10 `U-PORS` tree × `1,024 × 3 = 3,072` chains stepped together in lockstep!), `TreeHasher::hash_counter_range` for register-only `ChainSecret`/`OneTimeMsg`/`FewSelect` sweeps, and `u128`+`u64` level-4 Octopus early-out during `U-PORS` grinding.
- **Types carry their rules & fail-stop contracts:** `#![forbid(unsafe_code)]`; `Signet::imprint` / `imprint_with` self-verify every produced imprint (~`39 µs`) before returning and panic on mismatch.

---

## 8. Terminology: `Signet`, `SignetId`, and `Imprint`

Following Mark S. Miller (*Robust Composition*) and Ka-Ping Yee & Mark S. Miller (*Capability Myths Demolished*), a cryptographic signing secret is a transferable **bearer** capability rather than a human identity:

- **`Signet`**: the secret bearer object (derived from a 32-byte seed) that exercises authority by making an imprint.
- **`Imprint`**: the `3,292`-byte mark pressed by a `Signet` onto a message or stream (transparent authenticity only — the message stays in the clear).
- **`SignetId`**: a publisher's self-certifying `32`-byte identifier and complete BLINCS verifying key (`expected_publisher.verify(...)`).
