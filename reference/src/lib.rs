//! Teaching-clarity reference implementation of **`BLINCS-48-X`** (`3,990` bytes, `q = 2^48`).
//!
//! Written for legibility and 1-to-1 correspondence with [`SPEC.md`](../../SPEC.md).
//! For the production implementation with super-wave SIMD batching, `#![no_std]` verifier,
//! and lock-free local randomness management, see
//! [`jasonhadler25/signet`](https://github.com/jasonhadler25/signet).
//!
//! Uses strictly single-threaded [`blake3_servil_core`] and forbids `unsafe` code.

#![forbid(unsafe_code)]

use blake3_servil_core::Mode;
use blake3_servil_core::convenience::{Hasher, hash_with};
use blake3_servil_core::throughput::{Batch, Block, Packed, Prepared, TreeHasher};

// ---------------------------------------------------------------------------
// 1. Suite parameters (SPEC.md §3)
// ---------------------------------------------------------------------------

/// Permanent suite identifier.
pub const SUITE_NAME: &str = "BLINCS-48-X";
/// Byte length of truncated nodes, chain values, salt `e`, and randomizer `R`.
pub const N: usize = 16;
/// Number of hypertree layers (`d = 6`: five height-7 lower layers + one height-13 top layer).
pub const LAYERS: usize = 6;
/// Height of each lower hypertree layer (`2^7 = 128` leaves).
pub const LOW_HEIGHT: usize = 7;
/// Leaves per lower hypertree tree (`128`).
pub const LOW_LEAVES: usize = 1 << LOW_HEIGHT;
/// Height of the top hypertree layer (`2^{13} = 8,192` leaves).
pub const TOP_HEIGHT: usize = 13;
/// Leaves in the top hypertree tree (`8,192`).
pub const TOP_LEAVES: usize = 1 << TOP_HEIGHT;
/// Total hypertree height (`5 * 7 + 13 = 48`).
pub const HYPER_BITS: usize = 5 * LOW_HEIGHT + TOP_HEIGHT;

/// `WOTS+C` chains per hypertree leaf (`n = 21`).
pub const WOTS_N: usize = 21;
/// `WOTS+C` chain cardinality (`w = 60`, 6-bit digits in `0..=59`).
pub const WOTS_W: usize = 60;
/// Maximum `WOTS+C` chain steps (`w - 1 = 59`).
pub const WOTS_STEPS: usize = WOTS_W - 1;
/// Constant upper-half digit sum (`2^{128} / |L_679(21, 60)| = 4,086.9` mean trials; exact `560` verify steps/layer).
pub const WOTS_SUM: usize = 679;
/// Required LSB-first zero bits on `ONE_TIME_MSG` (`2 + 21 * 6 = 128` bits exact).
pub const WOTS_Z: usize = 2;
/// Byte length of the deterministic `u24` LE `WOTS+C` layer counter.
pub const WOTS_CTR_LEN: usize = 3;

/// Height of the single `U-PORS` binary Merkle tree (`2^{11} = 2,048` leaves).
pub const UPORS_HEIGHT: usize = 11;
/// Leaves in the `U-PORS` tree (`2,048`).
pub const UPORS_LEAVES: usize = 1 << UPORS_HEIGHT;
/// Equal-length chains per `U-PORS` leaf (`n = 3`; `16 + 3 * 16 = 64` B = 1 BLAKE3 block).
pub const UPORS_N: usize = 3;
/// `U-PORS` chain cardinality (`w = 24`, digits in `0..=23`).
pub const UPORS_W: usize = 24;
/// Maximum `U-PORS` chain steps (`23`).
pub const UPORS_STEPS: usize = UPORS_W - 1;
/// Constant sum `a + b + c = 42` for every `U-PORS` codeword (`27` verify steps/leaf).
pub const UPORS_SUM: usize = 42;
/// Cardinality of the full upper slice `L_42(3, 24)` (`376` codewords).
pub const UPORS_C: usize = 376;
/// Number of distinct `U-PORS` leaves opened per imprint (`k = 9`).
pub const UPORS_K: usize = 9;
/// Verifier-enforced maximum Octopus authentication siblings (`45`).
pub const UPORS_M_MAX: usize = 45;
/// Byte length of the `u32` `U-PORS` selection counter (`4`).
pub const UPORS_CTR_LEN: usize = 4;
/// Maximum `11`-bit chunks scanned inside one `FEW_SELECT` digest (`18 * 11 + 48 = 246 <= 256`).
pub const UPORS_SELECT_MAX_DRAWS: usize = 18;
/// Tweak layer byte `0x80` separating `U-PORS` from hypertree layers `0..6`.
pub const UPORS_LAYER: u8 = 0x80;
/// Maximum length of the framed application context in bytes.
pub const MAX_CONTEXT_LEN: usize = 255;

/// Encoded byte length of the `U-PORS` section (`4 + (27 + 45) * 16 = 1,156`).
pub const UPORS_LEN: usize = UPORS_CTR_LEN + (UPORS_K * UPORS_N + UPORS_M_MAX) * N;
/// Encoded byte length of one lower hypertree layer (`3 + (21 + 7) * 16 = 451`).
pub const LOW_LAYER_LEN: usize = WOTS_CTR_LEN + (WOTS_N + LOW_HEIGHT) * N;
/// Encoded byte length of the top hypertree layer (`3 + (21 + 13) * 16 = 547`).
pub const TOP_LAYER_LEN: usize = WOTS_CTR_LEN + (WOTS_N + TOP_HEIGHT) * N;
/// Encoded byte length of a complete `BLINCS-48-X` imprint (`3,990`).
pub const IMPRINT_LEN: usize = 2 * N + UPORS_LEN + 5 * LOW_LAYER_LEN + TOP_LAYER_LEN;

const _: () = {
    assert!(HYPER_BITS == 48);
    assert!(UPORS_SELECT_MAX_DRAWS * UPORS_HEIGHT + HYPER_BITS == 246);
    assert!(16 + UPORS_N * N == 64);
    assert!(UPORS_LEN == 1156 && LOW_LAYER_LEN == 451 && TOP_LAYER_LEN == 547);
    assert!(IMPRINT_LEN == 3990);
};

// ---------------------------------------------------------------------------
// 2. Key-derivation contexts and tweaks (SPEC.md §§4–5)
// ---------------------------------------------------------------------------

/// Secret-values KDF context (`K_sec`).
pub const CTX_SECRET_VALUES: &str = "BLINCS-48-X 2026-11-26 secret values";
/// Content-salt KDF context (`K_salt`).
pub const CTX_CONTENT_SALT: &str = "BLINCS-48-X 2026-11-26 content salt";
/// Randomizer KDF context (`K_R`).
pub const CTX_RANDOMIZER: &str = "BLINCS-48-X 2026-11-26 randomizer";
/// Public-seed KDF context (`pk_seed`).
pub const CTX_PUBLIC_SEED: &str = "BLINCS-48-X 2026-11-26 public seed";
/// Public-hash KDF context (`K_pub`).
pub const CTX_PUBLIC_HASH: &str = "BLINCS-48-X 2026-11-26 public hash";
/// Content-key KDF context (`K_content`).
pub const CTX_CONTENT: &str = "BLINCS-48-X 2026-11-26 content";

/// Tweak kind for secret chain start values (`K_sec`).
pub const KIND_CHAIN_SECRET: u8 = 1;
/// Tweak kind for public chain steps (`K_pub`).
pub const KIND_CHAIN: u8 = 2;
/// Tweak kind for Merkle leaf compression (`K_pub`).
pub const KIND_ONE_TIME_KEY: u8 = 3;
/// Tweak kind for Merkle internal node compression (`K_pub`).
pub const KIND_NODE: u8 = 4;
/// Tweak kind for `WOTS+C` counter-grinding (`K_pub`).
pub const KIND_ONE_TIME_MSG: u8 = 5;
/// Tweak kind for message digest seed `D_seed` (`K_pub`).
pub const KIND_MESSAGE: u8 = 6;
/// Tweak kind for `U-PORS` leaf selection and Octopus cap grinding (`K_pub`).
pub const KIND_FEW_SELECT: u8 = 7;
/// Tweak kind for indexed `U-PORS` codeword extraction (`K_pub`).
pub const KIND_FEW_CODE: u8 = 8;

/// Construct a 16-byte domain-separation tweak (`SPEC.md §5`).
pub fn tweak(kind: u8, layer: u8, tree: u64, leaf: u16, a: u16, b: u32) -> [u8; 16] {
    assert!(tree < (1u64 << 48), "tree exceeds 48 bits");
    let mut out = [0u8; 16];
    out[0] = kind;
    out[1] = layer;
    out[2..8].copy_from_slice(&tree.to_le_bytes()[..6]);
    out[8..10].copy_from_slice(&leaf.to_le_bytes());
    out[10..12].copy_from_slice(&a.to_le_bytes());
    out[12..16].copy_from_slice(&b.to_le_bytes());
    out
}

fn derive_key(ctx: &str, data: &[u8]) -> [u8; 32] {
    *hash_with(Mode::DeriveKey(ctx), data).as_bytes()
}

fn keyed(key: &[u8; 32], data: &[u8]) -> [u8; 32] {
    *hash_with(Mode::Keyed(key), data).as_bytes()
}

fn first_n(h: &[u8; 32]) -> [u8; N] {
    h[..N].try_into().unwrap()
}

fn short_hash(key: &[u8; 32], tw: [u8; 16], data: &[u8]) -> [u8; N] {
    let mut h = Hasher::new(Mode::Keyed(key), Some((16 + data.len()) as u64));
    h.update(&tw);
    h.update(data);
    first_n(h.finalize().as_bytes())
}

fn read_bits(d: &[u8; 32], bit_off: usize, width: usize) -> u64 {
    assert!((1..=57).contains(&width) && bit_off + width <= 256);
    let byte_off = bit_off / 8;
    let shift = bit_off % 8;
    let mut raw = [0u8; 8];
    let avail = (32 - byte_off).min(8);
    raw[..avail].copy_from_slice(&d[byte_off..byte_off + avail]);
    (u64::from_le_bytes(raw) >> shift) & ((1u64 << width) - 1)
}

fn frame_context(ctx: &[u8]) -> Vec<u8> {
    assert!(ctx.len() <= MAX_CONTEXT_LEN, "context exceeds 255 bytes");
    let mut out = Vec::with_capacity(1 + ctx.len());
    out.push(u8::try_from(ctx.len()).unwrap());
    out.extend_from_slice(ctx);
    out
}

// ---------------------------------------------------------------------------
// 3. Zero-table coding primitives: hexagon unranking & WOTS+C 6-bit decoding
// ---------------------------------------------------------------------------

/// Map `idx in 0..376` bijectively to `(a, b, c)` in `{0..23}^3` with `a + b + c = 42`
/// (`SPEC.md §10.1`, zero static lookup tables).
pub fn hex_unrank(mut idx: usize) -> [usize; UPORS_N] {
    assert!(idx < UPORS_C, "hex_unrank index out of range");
    for a in 0..=UPORS_STEPS {
        if a > UPORS_SUM {
            break;
        }
        let rem = UPORS_SUM - a;
        let b_lo = rem.saturating_sub(UPORS_STEPS);
        let b_hi = rem.min(UPORS_STEPS);
        if b_hi < b_lo {
            continue;
        }
        let len = b_hi - b_lo + 1;
        if idx < len {
            let b = b_lo + idx;
            return [a, b, rem - b];
        }
        idx -= len;
    }
    unreachable!("hex_unrank exhausted")
}

/// Decode `WOTS+C(n = 21, w = 60, z = 2, S = 679)` directly from `H_l[0..16]` (`SPEC.md §11.1`):
/// requires `(lo & 3) == 0`, all 21 packed 6-bit fields `d_i < 60`, and `sum(d_i) == 679`.
/// Zero division, zero Sperner DP, zero static lookup tables.
pub fn decode_wots_c(digest: &[u8; 32]) -> Option<[usize; WOTS_N]> {
    let lo = u128::from_le_bytes(digest[..16].try_into().unwrap());
    if (lo & 3) != 0 {
        return None;
    }
    let mut digits = [0usize; WOTS_N];
    let mut sum = 0usize;
    for (i, slot) in digits.iter_mut().enumerate() {
        let d = usize::try_from((lo >> (WOTS_Z + 6 * i)) & 63).unwrap();
        if d >= WOTS_W {
            return None;
        }
        *slot = d;
        sum += d;
    }
    if sum == WOTS_SUM { Some(digits) } else { None }
}

// ---------------------------------------------------------------------------
// 4. Signet & SignetId public API (SPEC.md §§6–11)
// ---------------------------------------------------------------------------

/// 32-byte verifying identifier (`pk_seed || top_root`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignetId(pub [u8; 32]);

/// Private signing capability derived from a 32-byte seed, caching the `256 KiB` top height-13 tree.
pub struct Signet {
    k_sec: [u8; 32],
    k_salt: [u8; 32],
    k_r: [u8; 32],
    k_pub: [u8; 32],
    k_content: [u8; 32],
    id: SignetId,
    top_tree: Vec<[u8; N]>,
}

impl Signet {
    /// Derive a `Signet` and its cached `256 KiB` height-13 top tree from a 32-byte seed (`SPEC.md §6`).
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        blake3_servil_core::initialize();
        let k_sec = derive_key(CTX_SECRET_VALUES, seed);
        let k_salt = derive_key(CTX_CONTENT_SALT, seed);
        let k_r = derive_key(CTX_RANDOMIZER, seed);
        let pk_seed = first_n(&derive_key(CTX_PUBLIC_SEED, seed));
        let k_pub = derive_key(CTX_PUBLIC_HASH, &pk_seed);

        let top_tree = build_wots_merkle_heap(&k_sec, &k_pub, 5, 0, TOP_HEIGHT);
        let mut id_bytes = [0u8; 32];
        id_bytes[..N].copy_from_slice(&pk_seed);
        id_bytes[N..].copy_from_slice(&top_tree[1]);
        let k_content = derive_key(CTX_CONTENT, &id_bytes);
        Self {
            k_sec,
            k_salt,
            k_r,
            k_pub,
            k_content,
            id: SignetId(id_bytes),
            top_tree,
        }
    }

    /// Return the 32-byte verifying identifier `SignetId`.
    pub fn id(&self) -> SignetId {
        self.id
    }

    /// Create a deterministic `3,990`-byte `Imprint` given a 32-byte random draw `draw`,
    /// bounded application context `ctx` (`0..=255` B), and arbitrary message `msg`.
    pub fn imprint_deterministic(
        &self,
        draw: &[u8; 32],
        ctx: &[u8],
        msg: &[u8],
    ) -> [u8; IMPRINT_LEN] {
        let fctx = frame_context(ctx);
        let e = first_n(&keyed(&self.k_salt, draw));
        let h_msg = content_hash(&self.k_content, &e, &fctx, msg);

        let mut short = [0u8; N + 32];
        short[..N].copy_from_slice(&e);
        short[N..].copy_from_slice(&h_msg);

        let mut r_in = Vec::with_capacity(short.len() + fctx.len());
        r_in.extend_from_slice(&short);
        r_in.extend_from_slice(&fctx);
        let r = first_n(&keyed(&self.k_r, &r_in));

        let d_seed = compute_d_seed(&self.k_pub, &r, &self.top_tree[1], &short, &fctx);
        let sel = grind_upors_selection(&self.k_pub, &d_seed);
        let codewords =
            extract_upors_codewords(&self.k_pub, &sel.h_sel).expect("FEW_CODE block_idx overflow");

        let mut out = [0u8; IMPRINT_LEN];
        out[..N].copy_from_slice(&e);
        out[N..2 * N].copy_from_slice(&r);

        let (upors_root, upors_bytes) = upors_sign(&self.k_sec, &self.k_pub, &sel, &codewords);
        out[2 * N..2 * N + UPORS_LEN].copy_from_slice(&upors_bytes);

        let mut node = upors_root;
        let mut addr = sel.leaf_addr;
        let mut off = 2 * N + UPORS_LEN;
        for layer in 0..LAYERS {
            let layer_u8 = u8::try_from(layer).unwrap();
            let h_l = if layer == LAYERS - 1 {
                TOP_HEIGHT
            } else {
                LOW_HEIGHT
            };
            let leaf = u16::try_from(addr & ((1u64 << h_l) - 1)).unwrap();
            let tree = addr >> h_l;
            addr = tree;

            let (ctr_l, digits) = grind_wots_msg(&self.k_pub, layer_u8, tree, leaf, &node);

            out[off..off + WOTS_CTR_LEN].copy_from_slice(&ctr_l.to_le_bytes()[..WOTS_CTR_LEN]);
            off += WOTS_CTR_LEN;

            for (c, &d) in digits.iter().enumerate() {
                let c_u16 = u16::try_from(c).unwrap();
                let mut v = chain_start(&self.k_sec, layer_u8, tree, leaf, WOTS_N, c);
                for s in 0..d {
                    v = short_hash(
                        &self.k_pub,
                        tweak(
                            KIND_CHAIN,
                            layer_u8,
                            tree,
                            leaf,
                            c_u16,
                            u32::try_from(s).unwrap(),
                        ),
                        &v,
                    );
                }
                out[off..off + N].copy_from_slice(&v);
                off += N;
            }

            let (layer_root, auth) = if layer == LAYERS - 1 {
                (
                    self.top_tree[1],
                    extract_auth(&self.top_tree, TOP_HEIGHT, usize::from(leaf)),
                )
            } else {
                let heap =
                    build_wots_merkle_heap(&self.k_sec, &self.k_pub, layer_u8, tree, LOW_HEIGHT);
                (heap[1], extract_auth(&heap, LOW_HEIGHT, usize::from(leaf)))
            };
            for sib in auth {
                out[off..off + N].copy_from_slice(&sib);
                off += N;
            }
            node = layer_root;
        }
        assert_eq!(off, IMPRINT_LEN);
        out
    }
}

impl SignetId {
    /// Verify a `3,990`-byte `BLINCS-48-X` imprint (`SPEC.md §§7–11`).
    pub fn verify(&self, ctx: &[u8], msg: &[u8], imprint: &[u8; IMPRINT_LEN]) -> bool {
        if ctx.len() > MAX_CONTEXT_LEN {
            return false;
        }
        blake3_servil_core::initialize();
        let pk_seed = &self.0[..N];
        let top_root: [u8; N] = self.0[N..].try_into().unwrap();
        let k_pub = derive_key(CTX_PUBLIC_HASH, pk_seed);
        let k_content = derive_key(CTX_CONTENT, &self.0);

        let fctx = frame_context(ctx);
        let e: [u8; N] = imprint[..N].try_into().unwrap();
        let r: [u8; N] = imprint[N..2 * N].try_into().unwrap();
        let h_msg = content_hash(&k_content, &e, &fctx, msg);

        let mut short = [0u8; N + 32];
        short[..N].copy_from_slice(&e);
        short[N..].copy_from_slice(&h_msg);

        let d_seed = compute_d_seed(&k_pub, &r, &top_root, &short, &fctx);
        let upors_slice = &imprint[2 * N..2 * N + UPORS_LEN];
        let ctr_ft = u32::from_le_bytes(upors_slice[..UPORS_CTR_LEN].try_into().unwrap());
        let Some(sel) = verify_upors_selection(&k_pub, &d_seed, ctr_ft) else {
            return false;
        };
        let Some(codewords) = extract_upors_codewords(&k_pub, &sel.h_sel) else {
            return false;
        };
        let Some(mut node) = upors_verify(&k_pub, &sel, &codewords, upors_slice) else {
            return false;
        };

        let mut addr = sel.leaf_addr;
        let mut off = 2 * N + UPORS_LEN;
        for layer in 0..LAYERS {
            let layer_u8 = u8::try_from(layer).unwrap();
            let h_l = if layer == LAYERS - 1 {
                TOP_HEIGHT
            } else {
                LOW_HEIGHT
            };
            let leaf = u16::try_from(addr & ((1u64 << h_l) - 1)).unwrap();
            let tree = addr >> h_l;
            addr = tree;

            let ctr_l = u32::from_le_bytes([imprint[off], imprint[off + 1], imprint[off + 2], 0]);
            off += WOTS_CTR_LEN;
            let Some(digits) = verify_wots_msg(&k_pub, layer_u8, tree, leaf, &node, ctr_l) else {
                return false;
            };

            let mut pk_data = [0u8; WOTS_N * N];
            for (c, &d) in digits.iter().enumerate() {
                let c_u16 = u16::try_from(c).unwrap();
                let mut v: [u8; N] = imprint[off..off + N].try_into().unwrap();
                off += N;
                for s in d..WOTS_STEPS {
                    v = short_hash(
                        &k_pub,
                        tweak(
                            KIND_CHAIN,
                            layer_u8,
                            tree,
                            leaf,
                            c_u16,
                            u32::try_from(s).unwrap(),
                        ),
                        &v,
                    );
                }
                pk_data[c * N..(c + 1) * N].copy_from_slice(&v);
            }
            let leaf_pk = short_hash(
                &k_pub,
                tweak(KIND_ONE_TIME_KEY, layer_u8, tree, leaf, 0, 0),
                &pk_data,
            );
            let auth = &imprint[off..off + h_l * N];
            off += h_l * N;
            node = merkle_reconstruct(&k_pub, layer_u8, tree, usize::from(leaf), leaf_pk, auth);
        }
        assert_eq!(off, IMPRINT_LEN);
        ct_eq(&node, &top_root)
    }
}

fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (&x, &y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

// ---------------------------------------------------------------------------
// 5. Content hashing & message digest seed (SPEC.md §§7–8)
// ---------------------------------------------------------------------------

fn content_hash(k_content: &[u8; 32], e: &[u8; N], fctx: &[u8], msg: &[u8]) -> [u8; 32] {
    let mut k_in = Vec::with_capacity(N + fctx.len());
    k_in.extend_from_slice(e);
    k_in.extend_from_slice(fctx);
    let k_msg = keyed(k_content, &k_in);
    keyed(&k_msg, msg)
}

fn compute_d_seed(
    k_pub: &[u8; 32],
    r: &[u8; N],
    root: &[u8; N],
    short: &[u8; N + 32],
    fctx: &[u8],
) -> [u8; 32] {
    let mut h = Hasher::new(
        Mode::Keyed(k_pub),
        Some((16 + N + N + short.len() + fctx.len()) as u64),
    );
    h.update(&tweak(KIND_MESSAGE, 0, 0, 0, 0, 0));
    h.update(r);
    h.update(root);
    h.update(short);
    h.update(fctx);
    *h.finalize().as_bytes()
}

// ---------------------------------------------------------------------------
// 6. U-PORS selection, codewords, Octopus sign & verify (SPEC.md §§8, 10)
// ---------------------------------------------------------------------------

struct UporsSel {
    ctr: u32,
    h_sel: [u8; 32],
    leaf_addr: u64,
    leaves: [u16; UPORS_K],
    sibs: usize,
}

fn count_octopus_sibs(sorted_leaves: &[u16; UPORS_K]) -> usize {
    let mut cur = *sorted_leaves;
    let mut len = UPORS_K;
    let mut sibs = 0usize;
    for _ in 0..UPORS_HEIGHT {
        let mut next = 0usize;
        let mut i = 0usize;
        while i < len {
            let x = cur[i];
            if i + 1 < len && (x ^ 1) == cur[i + 1] {
                cur[next] = x >> 1;
                next += 1;
                i += 2;
            } else {
                sibs += 1;
                cur[next] = x >> 1;
                next += 1;
                i += 1;
            }
        }
        len = next;
    }
    sibs
}

fn parse_select_digest(d: &[u8; 32]) -> Option<(u64, [u16; UPORS_K], usize)> {
    let mut leaves = [0u16; UPORS_K];
    let mut found = 0usize;
    for i in 0..UPORS_SELECT_MAX_DRAWS {
        let x = u16::try_from(read_bits(d, i * UPORS_HEIGHT, UPORS_HEIGHT)).unwrap();
        if !leaves[..found].contains(&x) {
            leaves[found] = x;
            found += 1;
            if found == UPORS_K {
                break;
            }
        }
    }
    if found < UPORS_K {
        return None;
    }
    leaves.sort_unstable();
    let sibs = count_octopus_sibs(&leaves);
    if sibs > UPORS_M_MAX {
        return None;
    }
    let leaf_addr = read_bits(d, UPORS_SELECT_MAX_DRAWS * UPORS_HEIGHT, HYPER_BITS);
    Some((leaf_addr, leaves, sibs))
}

#[inline]
fn parse_select_fast(d: &[u8; 32]) -> Option<(u64, [u16; UPORS_K], usize)> {
    let w0 = u64::from_le_bytes(d[0..8].try_into().unwrap());
    let w1 = u64::from_le_bytes(d[8..16].try_into().unwrap());
    let m5 = (1u64 << ((w0 >> 5) & 63))
        | (1u64 << ((w0 >> 16) & 63))
        | (1u64 << ((w0 >> 27) & 63))
        | (1u64 << ((w0 >> 38) & 63))
        | (1u64 << ((w0 >> 49) & 63))
        | (1u64 << (((w0 >> 60) | (w1 << 4)) & 63))
        | (1u64 << ((w1 >> 7) & 63))
        | (1u64 << ((w1 >> 18) & 63))
        | (1u64 << ((w1 >> 29) & 63));
    let n5 = m5.count_ones();
    if n5 == 9 {
        return None;
    }
    let m6 = m5 | (m5 >> 1);
    let m7 = m6 | (m6 >> 2);
    let m8 = m7 | (m7 >> 4);
    let m9 = m8 | (m8 >> 8);
    let m10 = m9 | (m9 >> 16);
    let lb = 5 * n5
        + (m6 & 0x5555_5555_5555_5555).count_ones()
        + (m7 & 0x1111_1111_1111_1111).count_ones()
        + (m8 & 0x0101_0101_0101_0101).count_ones()
        + (m9 & 0x0001_0001_0001_0001).count_ones()
        + (m10 & 0x0000_0001_0000_0001).count_ones();
    if lb > 52 {
        return None;
    }
    parse_select_digest(d)
}

fn grind_upors_selection(k_pub: &[u8; 32], d_seed: &[u8; 32]) -> UporsSel {
    let mut tmpl = [0u8; 52];
    tmpl[..16].copy_from_slice(&tweak(KIND_FEW_SELECT, UPORS_LAYER, 0, 0, 0, 0));
    tmpl[16..48].copy_from_slice(d_seed);
    let th = TreeHasher::new(Mode::Keyed(k_pub));
    let mut out = vec![[0u8; 32]; 1024];
    let mut start = 0u32;
    loop {
        th.hash_counter_range(&tmpl, 12, start, &mut out);
        for (i, d) in out.iter().enumerate() {
            if let Some((leaf_addr, leaves, sibs)) = parse_select_fast(d) {
                return UporsSel {
                    ctr: start + u32::try_from(i).unwrap(),
                    h_sel: *d,
                    leaf_addr,
                    leaves,
                    sibs,
                };
            }
        }
        start = start.checked_add(1024).expect("ctr_ft exhausted");
    }
}

fn verify_upors_selection(k_pub: &[u8; 32], d_seed: &[u8; 32], ctr: u32) -> Option<UporsSel> {
    let mut msg = [0u8; 52];
    msg[..16].copy_from_slice(&tweak(KIND_FEW_SELECT, UPORS_LAYER, 0, 0, 0, 0));
    msg[16..48].copy_from_slice(d_seed);
    msg[48..52].copy_from_slice(&ctr.to_le_bytes());
    let d = keyed(k_pub, &msg);
    let (leaf_addr, leaves, sibs) = parse_select_digest(&d)?;
    Some(UporsSel {
        ctr,
        h_sel: d,
        leaf_addr,
        leaves,
        sibs,
    })
}

fn extract_upors_codewords(
    k_pub: &[u8; 32],
    h_sel: &[u8; 32],
) -> Option<[[usize; UPORS_N]; UPORS_K]> {
    let mut out = [[0usize; UPORS_N]; UPORS_K];
    let mut got = 0usize;
    let mut msg = [0u8; 48];
    msg[16..48].copy_from_slice(h_sel);
    for block_idx in 0..=u16::MAX {
        msg[..16].copy_from_slice(&tweak(KIND_FEW_CODE, UPORS_LAYER, 0, 0, block_idx, 0));
        let b = keyed(k_pub, &msg);
        for j in 0..28usize {
            let v = usize::try_from(read_bits(&b, j * 9, 9)).unwrap();
            if v < UPORS_C {
                out[got] = hex_unrank(v);
                got += 1;
                if got == UPORS_K {
                    return Some(out);
                }
            }
        }
    }
    None
}

fn upors_build_leaves(
    k_sec: &[u8; 32],
    pub_h: &TreeHasher,
    sel: &UporsSel,
    codewords: &[[usize; UPORS_N]; UPORS_K],
    sig: &mut [u8; UPORS_LEN],
) -> Vec<[u8; N]> {
    let tree = sel.leaf_addr;
    let sec_h = TreeHasher::new(Mode::Keyed(k_sec));
    let total_chains = UPORS_LEAVES * UPORS_N;
    let mut out_h = vec![[0u8; 32]; total_chains];
    let start_tmpl = tweak(KIND_CHAIN_SECRET, UPORS_LAYER, tree, 0, 0, 0);
    sec_h.hash_counter_range(&start_tmpl, 3, 0, &mut out_h);

    let chains_off = UPORS_CTR_LEN;
    for (t, cw) in codewords.iter().enumerate() {
        let base = usize::from(sel.leaves[t]) * UPORS_N;
        for (c, &d) in cw.iter().enumerate() {
            if d == 0 {
                let off = chains_off + (t * UPORS_N + c) * N;
                sig[off..off + N].copy_from_slice(&out_h[base + c][..N]);
            }
        }
    }

    let mut b32 = Packed::<32>::new(total_chains);
    for l in 0..UPORS_LEAVES {
        let l_u16 = u16::try_from(l).unwrap();
        for c in 0..UPORS_N {
            let tw = tweak(
                KIND_CHAIN,
                UPORS_LAYER,
                tree,
                l_u16,
                u16::try_from(c).unwrap(),
                0,
            );
            b32[l * UPORS_N + c][..12].copy_from_slice(&tw[..12]);
        }
    }
    for step in 0..UPORS_STEPS {
        let sb = u32::try_from(step).unwrap().to_le_bytes();
        for (m, o) in b32.iter_mut().zip(out_h.iter()) {
            m[12..16].copy_from_slice(&sb);
            m[16..32].copy_from_slice(&o[..N]);
        }
        pub_h.hash_many(&b32, &mut out_h);
        let done = step + 1;
        for (t, cw) in codewords.iter().enumerate() {
            let base = usize::from(sel.leaves[t]) * UPORS_N;
            for (c, &d) in cw.iter().enumerate() {
                if d == done {
                    let off = chains_off + (t * UPORS_N + c) * N;
                    sig[off..off + N].copy_from_slice(&out_h[base + c][..N]);
                }
            }
        }
    }

    let mut b64 = vec![Block::ZERO; UPORS_LEAVES];
    for (l, blk) in b64.iter_mut().enumerate() {
        blk.0[..16].copy_from_slice(&tweak(
            KIND_ONE_TIME_KEY,
            UPORS_LAYER,
            tree,
            u16::try_from(l).unwrap(),
            0,
            0,
        ));
        for c in 0..UPORS_N {
            blk.0[16 + c * N..16 + (c + 1) * N].copy_from_slice(&out_h[l * UPORS_N + c][..N]);
        }
    }
    pub_h.hash_many(&Batch::from_blocks(&b64, 64), &mut out_h[..UPORS_LEAVES]);
    out_h[..UPORS_LEAVES].iter().map(first_n).collect()
}

fn upors_sign(
    k_sec: &[u8; 32],
    k_pub: &[u8; 32],
    sel: &UporsSel,
    codewords: &[[usize; UPORS_N]; UPORS_K],
) -> ([u8; N], [u8; UPORS_LEN]) {
    let tree = sel.leaf_addr;
    let pub_h = TreeHasher::new(Mode::Keyed(k_pub));
    let mut sig = [0u8; UPORS_LEN];
    sig[..UPORS_CTR_LEN].copy_from_slice(&sel.ctr.to_le_bytes());

    let mut nodes = upors_build_leaves(k_sec, &pub_h, sel, codewords, &mut sig);
    let octo_off = UPORS_CTR_LEN + UPORS_K * UPORS_N * N;
    let mut b48 = Packed::<48>::new(UPORS_LEAVES / 2);
    let mut out_h = vec![[0u8; 32]; UPORS_LEAVES / 2];
    let mut cur_idx = sel.leaves;
    let mut cur_len = UPORS_K;
    let mut sib_cursor = 0usize;
    let mut width = UPORS_LEAVES;

    for level in 1..=UPORS_HEIGHT {
        let level_u16 = u16::try_from(level).unwrap();
        let mut next_len = 0usize;
        let mut i = 0usize;
        while i < cur_len {
            let x = cur_idx[i];
            if i + 1 < cur_len && (x ^ 1) == cur_idx[i + 1] {
                cur_idx[next_len] = x >> 1;
                next_len += 1;
                i += 2;
            } else {
                let off = octo_off + sib_cursor * N;
                sig[off..off + N].copy_from_slice(&nodes[usize::from(x ^ 1)]);
                sib_cursor += 1;
                cur_idx[next_len] = x >> 1;
                next_len += 1;
                i += 1;
            }
        }
        cur_len = next_len;

        let parents = width / 2;
        for p in 0..parents {
            let dst = &mut b48[p];
            dst[..16].copy_from_slice(&tweak(
                KIND_NODE,
                UPORS_LAYER,
                tree,
                0,
                level_u16,
                u32::try_from(p).unwrap(),
            ));
            dst[16..32].copy_from_slice(&nodes[2 * p]);
            dst[32..48].copy_from_slice(&nodes[2 * p + 1]);
        }
        pub_h.hash_many(&b48.part(0..parents), &mut out_h[..parents]);
        for p in 0..parents {
            nodes[p] = first_n(&out_h[p]);
        }
        width = parents;
    }
    assert_eq!(sib_cursor, sel.sibs);
    sig[octo_off + sib_cursor * N..].fill(0);
    (nodes[0], sig)
}

fn upors_verify(
    k_pub: &[u8; 32],
    sel: &UporsSel,
    codewords: &[[usize; UPORS_N]; UPORS_K],
    sig: &[u8],
) -> Option<[u8; N]> {
    let tree = sel.leaf_addr;
    let chains_off = UPORS_CTR_LEN;
    let octo_off = UPORS_CTR_LEN + UPORS_K * UPORS_N * N;

    let mut cur_val = [[0u8; N]; UPORS_K];
    for (t, cw) in codewords.iter().enumerate() {
        let leaf = sel.leaves[t];
        let mut tops = [0u8; UPORS_N * N];
        for (c, &d) in cw.iter().enumerate() {
            let c_u16 = u16::try_from(c).unwrap();
            let off = chains_off + (t * UPORS_N + c) * N;
            let mut v: [u8; N] = sig[off..off + N].try_into().unwrap();
            for s in d..UPORS_STEPS {
                v = short_hash(
                    k_pub,
                    tweak(
                        KIND_CHAIN,
                        UPORS_LAYER,
                        tree,
                        leaf,
                        c_u16,
                        u32::try_from(s).unwrap(),
                    ),
                    &v,
                );
            }
            tops[c * N..(c + 1) * N].copy_from_slice(&v);
        }
        cur_val[t] = short_hash(
            k_pub,
            tweak(KIND_ONE_TIME_KEY, UPORS_LAYER, tree, leaf, 0, 0),
            &tops,
        );
    }

    let mut cur_idx = sel.leaves;
    let mut cur_len = UPORS_K;
    let mut sib_cursor = 0usize;
    for level in 1..=UPORS_HEIGHT {
        let level_u16 = u16::try_from(level).unwrap();
        let mut next_len = 0usize;
        let mut i = 0usize;
        while i < cur_len {
            let x = cur_idx[i];
            let p = x >> 1;
            let tw = tweak(KIND_NODE, UPORS_LAYER, tree, 0, level_u16, u32::from(p));
            let mut pair = [0u8; 2 * N];
            if i + 1 < cur_len && (x ^ 1) == cur_idx[i + 1] {
                pair[..N].copy_from_slice(&cur_val[i]);
                pair[N..].copy_from_slice(&cur_val[i + 1]);
                i += 2;
            } else {
                let off = octo_off + sib_cursor * N;
                let sib = &sig[off..off + N];
                sib_cursor += 1;
                if (x & 1) == 0 {
                    pair[..N].copy_from_slice(&cur_val[i]);
                    pair[N..].copy_from_slice(sib);
                } else {
                    pair[..N].copy_from_slice(sib);
                    pair[N..].copy_from_slice(&cur_val[i]);
                }
                i += 1;
            }
            cur_val[next_len] = short_hash(k_pub, tw, &pair);
            cur_idx[next_len] = p;
            next_len += 1;
        }
        cur_len = next_len;
    }
    assert_eq!(sib_cursor, sel.sibs);
    let pad = &sig[octo_off + sib_cursor * N..octo_off + UPORS_M_MAX * N];
    let zeros = [0u8; UPORS_M_MAX * N];
    if !ct_eq(pad, &zeros[..pad.len()]) {
        return None;
    }
    Some(cur_val[0])
}

// ---------------------------------------------------------------------------
// 7. Hypertree WOTS+C grinding, Merkle heaps & verification (SPEC.md §11)
// ---------------------------------------------------------------------------

fn chain_start(
    k_sec: &[u8; 32],
    layer: u8,
    tree: u64,
    leaf: u16,
    n_chains: usize,
    c: usize,
) -> [u8; N] {
    let slot = u32::try_from(usize::from(leaf) * n_chains + c).unwrap();
    short_hash(
        k_sec,
        tweak(KIND_CHAIN_SECRET, layer, tree, 0, 0, slot),
        &[],
    )
}

fn grind_wots_msg(
    k_pub: &[u8; 32],
    layer: u8,
    tree: u64,
    leaf: u16,
    child_root: &[u8; N],
) -> (u32, [usize; WOTS_N]) {
    let mut tmpl = [0u8; 36];
    tmpl[..16].copy_from_slice(&tweak(KIND_ONE_TIME_MSG, layer, tree, leaf, 0, 0));
    tmpl[16..32].copy_from_slice(child_root);
    let th = TreeHasher::new(Mode::Keyed(k_pub));
    let mut out = vec![[0u8; 32]; 1024];
    let mut start = 0u32;
    while start < (1u32 << 24) {
        let count = usize::try_from(((1u32 << 24) - start).min(1024)).unwrap();
        th.hash_counter_range(&tmpl, 8, start, &mut out[..count]);
        for (i, h) in out[..count].iter().enumerate() {
            if let Some(digits) = decode_wots_c(h) {
                return (start + u32::try_from(i).unwrap(), digits);
            }
        }
        start += u32::try_from(count).unwrap();
    }
    panic!("WOTS+C u24 counter exhausted");
}

fn verify_wots_msg(
    k_pub: &[u8; 32],
    layer: u8,
    tree: u64,
    leaf: u16,
    child_root: &[u8; N],
    ctr: u32,
) -> Option<[usize; WOTS_N]> {
    assert!(ctr < (1u32 << 24));
    let mut msg = [0u8; 36];
    msg[..16].copy_from_slice(&tweak(KIND_ONE_TIME_MSG, layer, tree, leaf, 0, 0));
    msg[16..32].copy_from_slice(child_root);
    msg[32..36].copy_from_slice(&ctr.to_le_bytes());
    let h = keyed(k_pub, &msg);
    decode_wots_c(&h)
}

fn build_wots_merkle_heap(
    k_sec: &[u8; 32],
    k_pub: &[u8; 32],
    layer: u8,
    tree: u64,
    height: usize,
) -> Vec<[u8; N]> {
    let leaves = 1usize << height;
    let tile = leaves.min(2048);
    let tile_chains = tile * WOTS_N;

    let sec_h = TreeHasher::new(Mode::Keyed(k_sec));
    let pub_h = TreeHasher::new(Mode::Keyed(k_pub));
    let mut b32 = Packed::<32>::new(tile_chains);
    let mut b_pk = Batch::new(16 + WOTS_N * N, tile);
    let mut out_h = vec![[0u8; 32]; tile_chains.max(leaves / 2)];
    let mut nodes = vec![[0u8; N]; 2 * leaves];

    let start_tmpl = tweak(KIND_CHAIN_SECRET, layer, tree, 0, 0, 0);
    let mut base = 0usize;
    while base < leaves {
        sec_h.hash_counter_range(
            &start_tmpl,
            3,
            u32::try_from(base * WOTS_N).unwrap(),
            &mut out_h[..tile_chains],
        );
        for rel in 0..tile {
            let leaf_u16 = u16::try_from(base + rel).unwrap();
            for c in 0..WOTS_N {
                let tw = tweak(
                    KIND_CHAIN,
                    layer,
                    tree,
                    leaf_u16,
                    u16::try_from(c).unwrap(),
                    0,
                );
                b32[rel * WOTS_N + c][..12].copy_from_slice(&tw[..12]);
            }
        }
        for step in 0..WOTS_STEPS {
            let sb = u32::try_from(step).unwrap().to_le_bytes();
            for (m, o) in b32.iter_mut().zip(out_h[..tile_chains].iter()) {
                m[12..16].copy_from_slice(&sb);
                m[16..32].copy_from_slice(&o[..N]);
            }
            pub_h.hash_many(&b32, &mut out_h[..tile_chains]);
        }
        for rel in 0..tile {
            let m = b_pk.message_mut(rel);
            m[..16].copy_from_slice(&tweak(
                KIND_ONE_TIME_KEY,
                layer,
                tree,
                u16::try_from(base + rel).unwrap(),
                0,
                0,
            ));
            for c in 0..WOTS_N {
                m[16 + c * N..16 + (c + 1) * N].copy_from_slice(&out_h[rel * WOTS_N + c][..N]);
            }
        }
        pub_h.hash_many(&b_pk, &mut out_h[..tile]);
        for rel in 0..tile {
            nodes[leaves + base + rel] = first_n(&out_h[rel]);
        }
        base += tile;
    }

    let mut b48 = Packed::<48>::new(leaves / 2);
    let mut level_start = leaves;
    let mut count = leaves;
    for level in 1..=height {
        let level_u16 = u16::try_from(level).unwrap();
        let parents = count / 2;
        let parent_start = level_start / 2;
        for j in 0..parents {
            let dst = &mut b48[j];
            dst[..16].copy_from_slice(&tweak(
                KIND_NODE,
                layer,
                tree,
                0,
                level_u16,
                u32::try_from(j).unwrap(),
            ));
            dst[16..32].copy_from_slice(&nodes[level_start + 2 * j]);
            dst[32..48].copy_from_slice(&nodes[level_start + 2 * j + 1]);
        }
        pub_h.hash_many(&b48.part(0..parents), &mut out_h[..parents]);
        for j in 0..parents {
            nodes[parent_start + j] = first_n(&out_h[j]);
        }
        level_start = parent_start;
        count = parents;
    }
    nodes
}

fn extract_auth(heap: &[[u8; N]], height: usize, leaf: usize) -> Vec<[u8; N]> {
    let mut out = Vec::with_capacity(height);
    let mut cursor = (1usize << height) + leaf;
    for _ in 0..height {
        out.push(heap[cursor ^ 1]);
        cursor >>= 1;
    }
    out
}

fn merkle_reconstruct(
    k_pub: &[u8; 32],
    layer: u8,
    tree: u64,
    mut idx: usize,
    mut cur: [u8; N],
    auth_bytes: &[u8],
) -> [u8; N] {
    for (level, sib) in (1u16..).zip(auth_bytes.chunks_exact(N)) {
        let mut buf = [0u8; 2 * N];
        if (idx & 1) == 0 {
            buf[..N].copy_from_slice(&cur);
            buf[N..].copy_from_slice(sib);
        } else {
            buf[..N].copy_from_slice(sib);
            buf[N..].copy_from_slice(&cur);
        }
        idx >>= 1;
        cur = short_hash(
            k_pub,
            tweak(
                KIND_NODE,
                layer,
                tree,
                0,
                level,
                u32::try_from(idx).unwrap(),
            ),
            &buf,
        );
    }
    cur
}

// ---------------------------------------------------------------------------
// 8. Quick startup self-test (SPEC.md §12)
// ---------------------------------------------------------------------------

const SELF_TEST_ID: [u8; 32] = [
    0x7e, 0xe7, 0xfe, 0x20, 0xda, 0xc8, 0x20, 0xb1, 0x76, 0x25, 0xca, 0xd3, 0xa3, 0x8a, 0x8a, 0xf6,
    0x96, 0xa6, 0x9a, 0x74, 0x99, 0x2f, 0x01, 0xa7, 0xc9, 0xed, 0x36, 0x80, 0x69, 0x9d, 0x2c, 0x5c,
];
const SELF_TEST_CTX: &[u8] = b"BLINCS-48-X reference vector v1";
const SELF_TEST_MSG: &[u8] = b"hello, BLINCS";
const SELF_TEST_IMPRINT: &[u8; IMPRINT_LEN] =
    include_bytes!("../../test_vectors/reference-imprint-1.bin");

/// Run the quick fail-closed startup self-test recommended by `SPEC.md §12`.
///
/// 1. Initializes `blake3-servil-core` (running its own CPU-kernel self-test).
/// 2. Verifies the canonical `BLINCS-48-X` reference imprint (`~63 us`).
/// 3. Confirms 1-bit tamper rejection and wrong-context rejection (`~126 us`).
///
/// Panics immediately on any mismatch.
pub fn self_test() {
    blake3_servil_core::initialize();
    let id = SignetId(SELF_TEST_ID);
    assert!(
        id.verify(SELF_TEST_CTX, SELF_TEST_MSG, SELF_TEST_IMPRINT),
        "BLINCS startup self-test failed: valid reference imprint rejected"
    );

    let mut tampered = *SELF_TEST_IMPRINT;
    tampered[0] ^= 0x01;
    assert!(
        !id.verify(SELF_TEST_CTX, SELF_TEST_MSG, &tampered),
        "BLINCS startup self-test failed: 1-bit tampered imprint accepted"
    );
    assert!(
        !id.verify(b"", SELF_TEST_MSG, SELF_TEST_IMPRINT),
        "BLINCS startup self-test failed: wrong-context imprint accepted"
    );
}
