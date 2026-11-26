# BLINCS Specification (`BLINCS-128-7x5`, draft)

> **Pre-1.0 — Experimental & Unsupported.** This specification is under active development (draft `0.2.0`); wire formats, parameters, and context strings may still change incompatibly before 1.0. Written primarily by an AI assistant at the direction of this repository's owner; **no independent human cryptographic review or security audit has been performed**. Do not rely on BLINCS to protect production assets.

*Builds on BLAKE3 (O'Connor, Aumasson, Neves, Wilcox-O'Hearn) and SPHINCS / SPHINCS+ / FIPS 205 SLH-DSA (Bernstein, Hopwood, Hülsing, Kölbl, Lange, Niederhagen, Papachristodoulou, Rijneveld, Schneider, Schwabe, Wilcox-O'Hearn, and the NIST SLH-DSA team). Thanks to [Project 11](https://research.projecteleven.com/) — especially **Conor Deegan**, **Alessandro Baiocchi**, **Matteo Vena**, and **Matteo Vicari** — for direct review feedback, benchmarks, and constrained-device design insights.*

---

## 1. Overview

**BLINCS** is a stateless hash-based signature algorithm based on BLAKE3 and SPHINCS. This specification defines the **`BLINCS-128-7x5`** suite, which unifies the entire scheme onto a single Merkle tree height (`5`, `32` leaves) and a single hash-chain leaf primitive:

- **One-time signature (hypertree):** WOTS+ over 4-bit nibbles (`w = 16`, 32 message nibbles + 3 checksum nibbles = 35 chains of 15 steps).
- **Few-time signature (`U-FORS` — Upper-Layer Constant-Sum Lattice Forest):** `k = 15` independent height-`5` binary Merkle trees (`32` leaves per tree — identical to every hypertree layer!), where each leaf is a tiny 3-chain hash-chain key (`n = 3` equal-length chains of `9` steps, `w = 10`, fitting in **one single 64-byte BLAKE3 compression**), encoded by an upper-layer constant-sum extreme-variance code of `64` codewords (`a + b + c = 16`).
- **Hypertree:** uniform 7-layer binary Merkle hypertree (`d = 7`, layer height `5`, total height `h = 35`, `32` leaves per tree, 1 KiB top tree).
- **Zero counter grinding:** signing performs a constant number of BLAKE3 compressions (`p99 = mean = max`, `143,022` cold / `125,343` max warm), and every `U-FORS` tree performs an exact constant `11` verification chain steps.
- **SIMD-aligned equal-length chains:** all `15 × 32 × 3 = 1,440 = 45 × 32` `U-FORS` chains have identical length `9` (100% lane occupancy on 4/8/16/32-wide single-threaded SIMD vectors).
- **Single-pass salted content hashing:** every imprint binds a caller-chosen bounded application context (`0..=255` bytes) and hashes an arbitrary-length message in one streaming pass under a fresh per-imprint salt drawn before reading the message.
- **Terminology:** This specification uses **`Signet`** (private signing capability), **`SignetId`** (32-byte verifying identifier), and **`Imprint`** (6,432-byte signature). These correspond directly to conventional `(SK, VK, \sigma)` notation; the companion security paper (`paper/blincs.pdf`) states all theorems in standard cryptographic notation alongside this mapping.

An `Imprint` is **6,432 bytes** (`8,576` bytes Base64), a `SignetId` is **32 bytes**, and a `Signet` derives from a **32-byte seed**. The design target is **128-bit classical security** at up to **$2^{32}$ imprints** per signet (4,294,967,296), with an exact dynamic-programming `U-FORS` Interleaved Target Subset Resilience (`ITSR`) exponent of **138.48 bits** at $q = 2^{32}$ (`132.13` bits at $2^{33}$, `124.73` bits at $2^{34}$, `116.05` bits at $2^{35}$, `105.83` bits at $2^{36}$). Do not imprint more than $2^{32}$ things with one signet.

### Notation

All fixed-width integers are unsigned and encoded in **little-endian** byte order. Ranges written `a..b` are half-open `[a, b)` and `a..=b` are closed `[a, b]`. Concatenation is written `||`, byte slicing `x[a..b]` takes bytes `a` through `b - 1`, and `x[..n]` takes the first `n` bytes. Maximum message length is $2^{64} - 1$ bytes; maximum application context length is `255` bytes.

---

## 2. Hash Primitive

BLINCS uses two 32-byte modes of **BLAKE3**:

- `Keyed(K, M)`: BLAKE3 keyed hash (`KEYED_HASH` mode) with 32-byte key `K` over byte string `M`, returning 32 bytes.
- `Derive(ctx, M)`: BLAKE3 key derivation (`DERIVE_KEY` mode) with UTF-8 context string `ctx` over input byte string `M`, returning 32 bytes.

---

## 3. Suite Identity and Parameters

Suite identifier: **`BLINCS-128-7x5`**.

| Symbol | Value | Meaning |
|---|---:|---|
| `N` | 16 | Byte length of truncated tree, chain, salt, and randomizer values (`h_msg`, `D`, and derived keys are 32 bytes) |
| `LAYERS` | 7 | Uniform layers of the hypertree (`d`) |
| `TREE_HEIGHT` | 5 | Height of **every** Merkle tree in the scheme — all 7 hypertree layers AND all 15 `U-FORS` trees ($2^5 = 32$ leaves per tree; `HYPER_BITS = 7 * 5 = 35`) |
| `W` | 16 | Hypertree WOTS+ Winternitz parameter (`CHAIN_STEPS = 15`, 4-bit nibbles in `0..=15`) |
| `MSG_CHAINS` | 32 | WOTS+ message chains (`128 / 4 = 32` nibbles) |
| `CSUM_CHAINS` | 3 | WOTS+ checksum chains (`max checksum = 32 * 15 = 480 < 16^3`) |
| `CHAINS` | 35 | Total WOTS+ chains per hypertree leaf (`32 + 3`) |
| `UFORS_TREES` | 15 | Number of independent `U-FORS` trees (`k`) |
| `UFORS_CHAINS` | 3 | Equal-length hash chains per `U-FORS` leaf (`n = 3`; `3 * 16 + 16 = 64` B = 1 BLAKE3 block) |
| `UFORS_W` | 10 | `U-FORS` chain cardinality (`UFORS_STEPS = 9`, digits in `0..=9`) |
| `UFORS_SUM` | 16 | Constant sum `c_0 + c_1 + c_2 = 16` for every `U-FORS` codeword (`27 - 16 = 11` verify steps/tree) |
| `UFORS_CODE_BITS` | 6 | Codeword index width (`2^6 = 64` codewords in `UFORS_CODE`) |
| `UFORS_LAYER_BASE` | 128 | Tweak layer offset `0x80` separating `U-FORS` trees (`128..143`) from hypertree layers (`0..7`) |
| `MAX_CONTEXT_LEN` | 255 | Maximum byte length of the framed application context `ctx` |

Derived lengths:

- `UFORS_TREE_LEN = (UFORS_CHAINS + TREE_HEIGHT) * N = 128` bytes.
- `UFORS_LEN = UFORS_TREES * UFORS_TREE_LEN = 1,920` bytes.
- `LAYER_LEN = (CHAINS + TREE_HEIGHT) * N = 640` bytes (identical on all 7 layers).
- `IMPRINT_LEN = 2 * N + UFORS_LEN + LAYERS * LAYER_LEN = 6,432` bytes.

---

## 4. Key-Derivation Contexts

Every derived 32-byte key uses a distinct UTF-8 context string binding the suite name `BLINCS-128-7x5`, ensuring separate suites never share derived keys:

| Name | Context string |
|---|---|
| `SECRET_VALUES` | `"BLINCS-128-7x5 2026-11-26 secret values"` |
| `CONTENT_SALT` | `"BLINCS-128-7x5 2026-11-26 content salt"` |
| `RANDOMIZER` | `"BLINCS-128-7x5 2026-11-26 randomizer"` |
| `PUBLIC_SEED` | `"BLINCS-128-7x5 2026-11-26 public seed"` |
| `PUBLIC_HASH` | `"BLINCS-128-7x5 2026-11-26 public hash"` |
| `CONTENT` | `"BLINCS-128-7x5 2026-11-26 content"` |

---

## 5. Tweaks

Every tree, chain, and message-binding hash is domain-separated by a 16-byte tweak:

```text
tweak(kind, layer, tree, leaf, a, b) =
    kind  (u8,  1 byte)
 || layer (u8,  1 byte)
 || tree  (u48, 6 bytes LE)
 || leaf  (u16, 2 bytes LE)
 || a     (u16, 2 bytes LE)
 || b     (u32, 4 bytes LE)
```

Unused fields MUST be zero. Because `U-FORS` trees share the exact same chain-and-Merkle primitive as the hypertree with disjoint `layer` values (`0..7` for hypertree layers, `128 + t` in `128..143` for `U-FORS` tree `t in 0..15`), the entire algorithm needs only **six** tweak kinds:

| Value | Name | Key | Data appended after tweak | Output bytes used |
|---:|---|---|---|---|
| 1 | `CHAIN_SECRET` | `K_sec` | *(empty)* | 16 |
| 2 | `CHAIN` | `K_pub` | current 16-byte chain value | 16 |
| 3 | `ONE_TIME_KEY` | `K_pub` | `35` chain ends (`560` B, hypertree) or `3` chain ends (`48` B, `U-FORS`) | 16 |
| 4 | `NODE` | `K_pub` | `left (16) \|\| right (16)` | 16 |
| 5 | `FEW_ROOT` | `K_pub` | `15` `U-FORS` tree roots (`240` bytes) | 16 |
| 6 | `MESSAGE` | `K_pub` | `R (16) \|\| root (16) \|\| short (48) \|\| u8(len(ctx)) \|\| ctx` | 32 |

Define `ShortHash(K, T, data) = Keyed(K, T || data)[..16]`.

Notice that every 1-input or 2-input tree/chain hash (`CHAIN_SECRET`, `CHAIN`, `NODE`, and `U-FORS` `ONE_TIME_KEY`) feeds `16`, `32`, `48`, or **exact `64`** bytes into `Keyed(K, ...)`. Because BLAKE3 absorbs up to 64 bytes per single compression block and binds the 32-byte key directly into the initial chaining value (`IV`), every single one of those calls costs **one** BLAKE3 compression.

---

## 6. Signet and SignetId

A `Signet` derives deterministically from a 32-byte `seed`:

```text
K_sec   = Derive(SECRET_VALUES, seed)
K_salt  = Derive(CONTENT_SALT,  seed)
K_R     = Derive(RANDOMIZER,    seed)
pk_seed = Derive(PUBLIC_SEED,   seed)[..16]
K_pub   = Derive(PUBLIC_HASH,   pk_seed)
root    = top hypertree root at layer = 6, tree = 0 (height 5, 32 leaves)
```

The 32-byte `SignetId` is `id = pk_seed || root`. A verifier derives from `id`:

```text
K_pub     = Derive(PUBLIC_HASH, id[..16])
root      = id[16..32]
K_content = Derive(CONTENT,     id)
```

---

## 7. Framed Application Context and Single-Pass Salted Content Hashing

Every imprint binds a caller-chosen application context `ctx` of `0..=255` bytes, framed unambiguously as:

```text
framed_ctx = u8(len(ctx)) || ctx                  # 1..=256 bytes
```

When imprinting with a fresh 32-byte per-imprint random draw `draw`:

```text
e = Keyed(K_salt, draw)[..16]                     # 16-byte per-imprint content salt
```

Given the 16-byte content salt `e`, application context `ctx`, and message `M` (any length in `0..2^64`):

```text
K_msg = Keyed(K_content, e || framed_ctx)         # 32-byte per-imprint, per-context message key
h_msg = Keyed(K_msg, M)                           # 32-byte keyed BLAKE3 hash of M (single pass)
short = e || h_msg                                # 48 bytes
```

Because `e` is derived before reading `M`, signers stream arbitrarily large messages through `Keyed(K_msg, M)` in a single pass. Verifiers read `e` from the first 16 bytes of the imprint and stream `M` in a single pass as well.

---

## 8. Message Digest and Index Extraction

The signer computes the deterministic per-imprint randomizer `R` and 32-byte digest `D`:

```text
R = Keyed(K_R, short || framed_ctx)[..16]
D = Keyed(K_pub, tweak(MESSAGE, 0, 0, 0, 0, 0) || R || root || short || framed_ctx)
```

Note the two-stage role of `e` and `R`: `e` salts the streaming message hash `h_msg` before reading `M`, while `R` depends deterministically on `(K_R, e, h_msg, framed_ctx)`. Even if the salt source fails or repeats `draw` (and hence `e`) across two distinct messages `M_1 != M_2` while `seed` remains secret, `h_msg` still differs (under 256-bit BLAKE3 collision resistance), so `R` and `D` remain fresh and unpredictable — preserving hedged `U-FORS`/hypertree index selection without requiring a second pass over `M`.

Treat `D` (32 bytes) as an LSB-first little-endian 256-bit bitstream, where `read_bits(D, off, width)` returns `(nat_le(D) >> off) & ((1 << width) - 1)`:

- **`U-FORS` leaf and codeword indices** (`15 × 11 = 165` bits, `D` bits `0..165`):
  - For `t in 0..15`:
    - `ufors_leaf[t] = read_bits(D, 11 * t,     5)` (in `0..32`)
    - `ufors_code[t] = read_bits(D, 11 * t + 5, 6)` (in `0..64`)
- **Hypertree leaf address** (`35` bits, `D` bits `165..200`):
  - `leaf_addr = read_bits(D, 165, 35)` (in `0..2^35`).

Total bits consumed: `165 + 35 = 200` bits (`D[0..25]`; bits `200..256` are unused).

---

## 9. Unified Chain-and-Merkle Primitive

Both `U-FORS` (`layer = 128 + t`, `n_chains = 3`, `steps = 9`) and the hypertree (`layer = l in 0..7`, `n_chains = 35`, `steps = 15`) use the **exact same** hash-chain and height-5 binary Merkle tree construction:

- **Chain `c in 0..n_chains` at `(layer, tree, leaf)`:**
  - Start value: `x_0 = ShortHash(K_sec, tweak(CHAIN_SECRET, layer, tree, leaf, c, 0), empty)`.
  - Step `s -> s + 1` (`s in 0..steps`): `x_{s+1} = ShortHash(K_pub, tweak(CHAIN, layer, tree, leaf, c, s), x_s)`.
  - Signature value for digit `d[c] in 0..=steps`: `x_{d[c]}`. Verifier completes steps `s = d[c]..steps` to recover `x_{steps}`.
- **Merkle leaf hash (`ONE_TIME_KEY`):**
  - `leaf_hash = ShortHash(K_pub, tweak(ONE_TIME_KEY, layer, tree, leaf, 0, 0), x_{steps}[0] || ... || x_{steps}[n_chains - 1])`.
- **Height-5 binary Merkle tree (`32` leaves, `level in 1..=5`, `p in 0..(32 >> level)`):**
  - `node = ShortHash(K_pub, tweak(NODE, layer, tree, 0, level, p), left || right)`.
  - Authentication path for `leaf in 0..32`: the `5` sibling nodes from leaf level `0` up to level `4` (`80` bytes).
  - On verification, starting from `cur = leaf_hash`, for `level in 1..=5`: if bit `level - 1` of `leaf` is `0`, `cur` is left and `auth[level - 1]` is right; otherwise `auth[level - 1]` is left and `cur` is right, hashed with `tweak(NODE, layer, tree, 0, level, leaf >> level)`.

---

## 10. Few-Time Signatures (`U-FORS`)

### 10.1 The Canonical Upper-Layer Constant-Sum Code (`UFORS_CODE`)

`UFORS_CODE` is the 64-element constant-sum antichain in $\{0,\dots,9\}^3$ defined by the following zero-magic-number rule:

> Take all 69 triples $(a, b, c) \in \{0,\dots,9\}^3$ with $a + b + c = 16$, exclude the 5 triples with smallest $(a^2 + b^2 + c^2,\; (a, b, c))$ — namely $(5,5,6)$, $(5,6,5)$, $(6,5,5)$, $(4,6,6)$, and $(6,4,6)$ — and sort the remaining 64 triples lexicographically.

Because every triple satisfies $a + b + c = 16$, `UFORS_CODE` is a strict antichain in $\{0,\dots,9\}^3$ (no two distinct triples satisfy $u \preceq v$), and verification always performs an exact constant `(9 - a) + (9 - b) + (9 - c) = 11` chain steps per tree. Pushing the sum above the middle rank (`16 > 13.5`) and keeping the 64 highest-variance boundary triples exploits Lattice-Meet Asymmetry on $\{0,\dots,9\}^3$, minimizing multi-reveal cover probability `q(m)` while cutting verification work.

```text
Index  0.. 7: [0,7,9] [0,8,8] [0,9,7] [1,6,9] [1,7,8] [1,8,7] [1,9,6] [2,5,9]
Index  8..15: [2,6,8] [2,7,7] [2,8,6] [2,9,5] [3,4,9] [3,5,8] [3,6,7] [3,7,6]
Index 16..23: [3,8,5] [3,9,4] [4,3,9] [4,4,8] [4,5,7] [4,7,5] [4,8,4] [4,9,3]
Index 24..31: [5,2,9] [5,3,8] [5,4,7] [5,7,4] [5,8,3] [5,9,2] [6,1,9] [6,2,8]
Index 32..39: [6,3,7] [6,6,4] [6,7,3] [6,8,2] [6,9,1] [7,0,9] [7,1,8] [7,2,7]
Index 40..47: [7,3,6] [7,4,5] [7,5,4] [7,6,3] [7,7,2] [7,8,1] [7,9,0] [8,0,8]
Index 48..55: [8,1,7] [8,2,6] [8,3,5] [8,4,4] [8,5,3] [8,6,2] [8,7,1] [8,8,0]
Index 56..63: [9,0,7] [9,1,6] [9,2,5] [9,3,4] [9,4,3] [9,5,2] [9,6,1] [9,7,0]
```

### 10.2 `U-FORS` Signing and Verification

At hypertree address `leaf_addr` (`0..2^35`), `U-FORS` consists of `UFORS_TREES = 15` independent height-`5` Merkle trees (`t in 0..15`), each instantiated via §9 with `layer = 128 + t`, `tree = leaf_addr`, `n_chains = 3`, and `steps = 9`:

- For each tree `t in 0..15`:
  - Let `leaf = ufors_leaf[t]` (in `0..32`) and `[d_0, d_1, d_2] = UFORS_CODE[ufors_code[t]]`.
  - Sign leaf `leaf` with the 3 chain values `(x_{d_0}, x_{d_1}, x_{d_2})` (`48` bytes) and append the `5`-node Merkle authentication path (`80` bytes) to the tree root `root[t]`.
- Compress all `15` tree roots into the 16-byte `U-FORS` root:
  - `ufors_root = ShortHash(K_pub, tweak(FEW_ROOT, 0, leaf_addr, 0, 0, 0), root[0] || ... || root[14])`.

The `U-FORS` section is `15 × 128 = 1,920` bytes.

---

## 11. Hypertree (WOTS+) and Imprint Wire Format

Given a 16-byte message `node` to sign at hypertree `(layer, tree, leaf)` (`layer in 0..7`):

- **WOTS+ digits `wots_digits(node)`** (`35` nibbles in `0..=15`):
  - For `i in 0..16`: `d[2*i] = node[i] & 0x0f`, `d[2*i + 1] = node[i] >> 4`.
  - Checksum `csum = sum_{j=0..32} (15 - d[j])` (in `0..=480`).
  - `d[32] = csum & 0x0f`, `d[33] = (csum >> 4) & 0x0f`, `d[34] = (csum >> 8) & 0x0f`.
- Instantiate §9 with `layer`, `tree`, `n_chains = 35`, and `steps = 15`:
  - Starting with `addr = leaf_addr` and `node = ufors_root`:
    - For `layer = 0..7`:
      - `leaf = addr & 0x1f` (`5` low bits)
      - `tree = addr >> 5` (at `layer = 6`, `tree == 0`)
      - Sign `node` using `wots_digits(node)` at `(layer, tree, leaf)` (`560` bytes) and append its `5`-node Merkle authentication path (`80` bytes).
      - Set `node = tree_root` and `addr = tree`.
- Verification succeeds iff the reconstructed layer-6 root equals `id[16..32]` in constant time.

Wire layout of an `Imprint` (`6,432` bytes):

```text
0..16        salt e (16 B)
16..32       randomizer R (16 B)
32..1952     U-FORS: 15 trees x (3 x 16 B chains + 5 x 16 B auth path) = 1,920 B
1952..2592   Layer 0: 35 x 16 B WOTS+ + 5 x 16 B auth path = 640 B
2592..3232   Layer 1: 35 x 16 B WOTS+ + 5 x 16 B auth path = 640 B
3232..3872   Layer 2: 35 x 16 B WOTS+ + 5 x 16 B auth path = 640 B
3872..4512   Layer 3: 35 x 16 B WOTS+ + 5 x 16 B auth path = 640 B
4512..5152   Layer 4: 35 x 16 B WOTS+ + 5 x 16 B auth path = 640 B
5152..5792   Layer 5: 35 x 16 B WOTS+ + 5 x 16 B auth path = 640 B
5792..6432   Layer 6: 35 x 16 B WOTS+ + 5 x 16 B auth path = 640 B
```

---

## 12. Startup Self-Test (Recommended for Every Implementation)

Every production or library implementation of BLINCS — especially implementations using optimized assembly, SIMD/vector hashing, custom compilers, or cross-compiled targets — is **strongly recommended** to execute a **quick, fail-closed startup self-test** once per process before accepting or generating imprints.

This practice follows a long tradition in high-assurance cryptographic engineering — notably **Niels Ferguson, Bruce Schneier, and Tadayoshi Kohno** (*Cryptography Engineering*, §16.4 / *Practical Cryptography*), **`pycryptopp`** (which ran fast startup known-answer checks on load), and **`blake3-servil-core`** (whose `initialize()` executes every compiled CPU kernel against fixed known answers in under a millisecond and aborts uncatchably on any mismatch). A fast startup check catches compiler miscompilations, wrong-endianness builds, bad CPU feature dispatch, broken SIMD lanes, and silent linkage/ABI mismatches on the exact machine running the code — faults that unit tests run on the developer's build host can never see.

### Recommended minimal startup check (~50–200 µs on a modern CPU)

1. **Initialize the underlying BLAKE3 implementation's own self-test** (for example `blake3_servil_core::initialize()`).
2. **Positive verification KAT (~35 µs):** Verify the canonical `test_vectors/reference-imprint-1.bin` (`ctx = b"BLINCS-128-7x5 reference vector v1"`, `M = b"hello, BLINCS"`). A single BLINCS verification exercises `Derive`, `Keyed`, context framing, message digest bit extraction, `UFORS_CODE` lookup, all 15 `U-FORS` trees, all 7 hypertree layers, every WOTS+ nibble/checksum path, and constant-time root comparison.
3. **Negative verification KATs (~70 µs):**
   - Flip one bit in the imprint (or message) and confirm verification **rejects**.
   - Pass a different context (for example empty context `b""`) and confirm verification **rejects**.
4. **Optional signing KAT (for signing-capable builds, ~1–2 ms):** If startup latency allows (for instance in a daemon or key-generation tool), derive `Signet` from `0x00..0x1f`, imprint `b"hello, BLINCS"` under `ctx = b"BLINCS-128-7x5 reference vector v1"` with `draw = [0x07; 32]`, and check that the 32-byte `BLAKE3` digest of the resulting `6,432`-byte imprint matches the published canonical digest in `test_vectors/README.md`.
5. **Fail closed:** If any check fails, refuse to proceed (abort or panic without returning a usable handle).

See [`reference/src/lib.rs`](reference/src/lib.rs) for a concrete implementation of `self_test()`.
