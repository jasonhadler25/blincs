//! Teaching-clarity reference implementation of **`BLINCS-128-7x5`** (`U-FORS`).
//!
//! Optimized purely for legibility and 1-to-1 correspondence with [`SPEC.md`](../../SPEC.md),
//! not for signing speed or batching. For the production implementation with batched hashing
//! and lock-free local randomness management, see [`jasonhadler25/signet`](https://github.com/jasonhadler25/signet).
//!
//! Uses strictly single-threaded [`blake3_servil_core`] and forbids `unsafe` code.

#![forbid(unsafe_code)]

use blake3_servil_core::Mode;
use blake3_servil_core::convenience::{Hasher, hash_with};

// ---------------------------------------------------------------------------
// 1. Suite parameters (SPEC.md §3)
// ---------------------------------------------------------------------------

/// Byte length of truncated nodes, chain values, salt `e`, and randomizer `R`.
pub const N: usize = 16;
/// Number of uniform hypertree layers (`d`).
pub const LAYERS: usize = 7;
/// Uniform height of every Merkle tree in the scheme — all 7 hypertree layers
/// and all 15 `U-FORS` trees (`2^5 = 32` leaves per tree).
pub const TREE_HEIGHT: usize = 5;
/// Number of leaves in every Merkle tree (`32`).
pub const TREE_LEAVES: usize = 1 << TREE_HEIGHT;
/// Hypertree WOTS+ Winternitz parameter (`w = 16`, 4-bit nibbles in `0..=15`).
pub const W: usize = 16;
/// Maximum WOTS+ chain step count (`w - 1 = 15`).
pub const CHAIN_STEPS: usize = W - 1;
/// Number of WOTS+ message chains (`128 / 4 = 32` nibbles).
pub const MSG_CHAINS: usize = 32;
/// Number of WOTS+ checksum chains (`max checksum = 32 * 15 = 480 < 16^3`).
pub const CSUM_CHAINS: usize = 3;
/// Total WOTS+ chains per hypertree leaf (`32 + 3 = 35`).
pub const CHAINS: usize = MSG_CHAINS + CSUM_CHAINS;

/// Number of independent `U-FORS` height-5 trees (`k = 15`).
pub const UFORS_TREES: usize = 15;
/// Equal-length hash chains per `U-FORS` leaf (`n = 3`; `3 * 16 + 16 = 64` B = 1 BLAKE3 block).
pub const UFORS_CHAINS: usize = 3;
/// `U-FORS` chain cardinality (`w = 10`, digits in `0..=9`).
pub const UFORS_W: usize = 10;
/// Maximum `U-FORS` chain step count (`UFORS_W - 1 = 9`).
pub const UFORS_STEPS: usize = UFORS_W - 1;
/// Constant sum `c_0 + c_1 + c_2 = 16` across every `U-FORS` codeword (`11` verify steps/tree).
pub const UFORS_SUM: usize = 16;
/// Bit width of `U-FORS` codeword indices (`2^6 = 64` codewords).
pub const UFORS_CODE_BITS: usize = 6;
/// Tweak layer offset `0x80` separating `U-FORS` trees (`128..143`) from hypertree layers (`0..7`).
pub const UFORS_LAYER_BASE: u8 = 0x80;
/// Maximum length of the framed application context in bytes.
pub const MAX_CONTEXT_LEN: usize = 255;

/// Encoded byte length of one `U-FORS` tree opening (`(3 + 5) * 16 = 128`).
pub const UFORS_TREE_LEN: usize = (UFORS_CHAINS + TREE_HEIGHT) * N;
/// Encoded byte length of the `U-FORS` section (`15 * 128 = 1,920`).
pub const UFORS_LEN: usize = UFORS_TREES * UFORS_TREE_LEN;
/// Encoded byte length of one hypertree layer (`(35 + 5) * 16 = 640`).
pub const LAYER_LEN: usize = (CHAINS + TREE_HEIGHT) * N;
/// Encoded byte length of a complete `BLINCS-128-7x5` imprint (`6,432`).
pub const IMPRINT_LEN: usize = 2 * N + UFORS_LEN + LAYERS * LAYER_LEN;

/// Canonical 64-entry upper-layer constant-sum extreme-variance code in `{0..=9}^3`
/// with `a + b + c = 16` (`SPEC.md §10.1`).
///
/// Defined as all 69 triples in `{0..=9}^3` summing to `16`, minus the 5 triples with
/// smallest `(a^2 + b^2 + c^2, (a, b, c))` — `(5,5,6)`, `(5,6,5)`, `(6,5,5)`, `(4,6,6)`,
/// `(6,4,6)` — sorted lexicographically.
pub const UFORS_CODE: [[u8; UFORS_CHAINS]; 1 << UFORS_CODE_BITS] = [
    [0, 7, 9],
    [0, 8, 8],
    [0, 9, 7],
    [1, 6, 9],
    [1, 7, 8],
    [1, 8, 7],
    [1, 9, 6],
    [2, 5, 9],
    [2, 6, 8],
    [2, 7, 7],
    [2, 8, 6],
    [2, 9, 5],
    [3, 4, 9],
    [3, 5, 8],
    [3, 6, 7],
    [3, 7, 6],
    [3, 8, 5],
    [3, 9, 4],
    [4, 3, 9],
    [4, 4, 8],
    [4, 5, 7],
    [4, 7, 5],
    [4, 8, 4],
    [4, 9, 3],
    [5, 2, 9],
    [5, 3, 8],
    [5, 4, 7],
    [5, 7, 4],
    [5, 8, 3],
    [5, 9, 2],
    [6, 1, 9],
    [6, 2, 8],
    [6, 3, 7],
    [6, 6, 4],
    [6, 7, 3],
    [6, 8, 2],
    [6, 9, 1],
    [7, 0, 9],
    [7, 1, 8],
    [7, 2, 7],
    [7, 3, 6],
    [7, 4, 5],
    [7, 5, 4],
    [7, 6, 3],
    [7, 7, 2],
    [7, 8, 1],
    [7, 9, 0],
    [8, 0, 8],
    [8, 1, 7],
    [8, 2, 6],
    [8, 3, 5],
    [8, 4, 4],
    [8, 5, 3],
    [8, 6, 2],
    [8, 7, 1],
    [8, 8, 0],
    [9, 0, 7],
    [9, 1, 6],
    [9, 2, 5],
    [9, 3, 4],
    [9, 4, 3],
    [9, 5, 2],
    [9, 6, 1],
    [9, 7, 0],
];

// ---------------------------------------------------------------------------
// 2. Key-derivation contexts (SPEC.md §4)
// ---------------------------------------------------------------------------

const CTX_SECRET_VALUES: &str = "BLINCS-128-7x5 2026-11-26 secret values";
const CTX_CONTENT_SALT: &str = "BLINCS-128-7x5 2026-11-26 content salt";
const CTX_RANDOMIZER: &str = "BLINCS-128-7x5 2026-11-26 randomizer";
const CTX_PUBLIC_SEED: &str = "BLINCS-128-7x5 2026-11-26 public seed";
const CTX_PUBLIC_HASH: &str = "BLINCS-128-7x5 2026-11-26 public hash";
const CTX_CONTENT: &str = "BLINCS-128-7x5 2026-11-26 content";

// ---------------------------------------------------------------------------
// 3. Domain-separation tweaks (SPEC.md §5)
// ---------------------------------------------------------------------------

const KIND_CHAIN_SECRET: u8 = 1;
const KIND_CHAIN: u8 = 2;
const KIND_ONE_TIME_KEY: u8 = 3;
const KIND_NODE: u8 = 4;
const KIND_FEW_ROOT: u8 = 5;
const KIND_MESSAGE: u8 = 6;

/// Build the canonical 16-byte little-endian tweak (`SPEC.md §5`).
pub fn tweak(kind: u8, layer: u8, tree: u64, leaf: u16, a: u16, b: u32) -> [u8; 16] {
    assert!(
        tree < (1u64 << 48),
        "tree address exceeds 48-bit tweak field"
    );
    let mut out = [0u8; 16];
    out[0] = kind;
    out[1] = layer;
    out[2..8].copy_from_slice(&tree.to_le_bytes()[..6]);
    out[8..10].copy_from_slice(&leaf.to_le_bytes());
    out[10..12].copy_from_slice(&a.to_le_bytes());
    out[12..16].copy_from_slice(&b.to_le_bytes());
    out
}

/// `Derive(ctx, M)` — BLAKE3 key derivation mode (`SPEC.md §2`).
fn derive_key(ctx: &str, data: &[u8]) -> [u8; 32] {
    *hash_with(Mode::DeriveKey(ctx), data).as_bytes()
}

/// `Keyed(K, M)` — BLAKE3 keyed hash mode (`SPEC.md §2`).
fn keyed_hash(key: &[u8; 32], data: &[u8]) -> [u8; 32] {
    *hash_with(Mode::Keyed(key), data).as_bytes()
}

/// `ShortHash(K, T, data) = Keyed(K, T || data)[..16]` (`SPEC.md §5`).
fn short_hash(key: &[u8; 32], twk: [u8; 16], data: &[u8]) -> [u8; N] {
    let mut h = Hasher::new(Mode::Keyed(key), None);
    h.update(&twk);
    h.update(data);
    let full = *h.finalize().as_bytes();
    let mut out = [0u8; N];
    out.copy_from_slice(&full[..N]);
    out
}

/// Truncate a 32-byte digest to its first 16 bytes.
fn trunc16(bytes: &[u8; 32]) -> [u8; N] {
    let mut out = [0u8; N];
    out.copy_from_slice(&bytes[..N]);
    out
}

/// Constant-time 16-byte equality comparison.
fn eq16_ct(a: &[u8; N], b: &[u8; N]) -> bool {
    let mut diff = 0u8;
    for i in 0..N {
        diff |= a[i] ^ b[i];
    }
    diff == 0
}

// ---------------------------------------------------------------------------
// 4. Signet & SignetId (SPEC.md §6)
// ---------------------------------------------------------------------------

/// A derived `BLINCS-128-7x5` signing capability (`Signet`).
#[derive(Clone)]
pub struct Signet {
    k_sec: [u8; 32],
    k_salt: [u8; 32],
    k_r: [u8; 32],
    pk_seed: [u8; N],
    k_pub: [u8; 32],
    root: [u8; N],
    k_content: [u8; 32],
}

/// A 32-byte `BLINCS-128-7x5` verifying identifier (`SignetId = pk_seed || root`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignetId(pub [u8; 32]);

struct VerifierKeys {
    k_pub: [u8; 32],
    root: [u8; N],
    k_content: [u8; 32],
}

impl SignetId {
    fn derive_keys(&self) -> VerifierKeys {
        let mut pk_seed = [0u8; N];
        let mut root = [0u8; N];
        pk_seed.copy_from_slice(&self.0[..N]);
        root.copy_from_slice(&self.0[N..]);
        VerifierKeys {
            k_pub: derive_key(CTX_PUBLIC_HASH, &pk_seed),
            root,
            k_content: derive_key(CTX_CONTENT, &self.0),
        }
    }
}

impl Signet {
    /// Derive a [`Signet`] deterministically from a 32-byte seed (`SPEC.md §6`).
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        blake3_servil_core::initialize();
        let k_sec = derive_key(CTX_SECRET_VALUES, seed);
        let k_salt = derive_key(CTX_CONTENT_SALT, seed);
        let k_r = derive_key(CTX_RANDOMIZER, seed);
        let pk_seed = trunc16(&derive_key(CTX_PUBLIC_SEED, seed));
        let k_pub = derive_key(CTX_PUBLIC_HASH, &pk_seed);

        let top_layer = u8::try_from(LAYERS - 1).unwrap();
        let top_leaves = tree_leaves(&k_sec, &k_pub, top_layer, 0, CHAINS, CHAIN_STEPS);
        let root = merkle_root_and_auth(&k_pub, top_layer, 0, &top_leaves, 0).0;

        let mut id = [0u8; 32];
        id[..N].copy_from_slice(&pk_seed);
        id[N..].copy_from_slice(&root);
        let k_content = derive_key(CTX_CONTENT, &id);

        Self {
            k_sec,
            k_salt,
            k_r,
            pk_seed,
            k_pub,
            root,
            k_content,
        }
    }

    /// Return the 32-byte `SignetId = pk_seed || root`.
    pub fn id(&self) -> SignetId {
        let mut id = [0u8; 32];
        id[..N].copy_from_slice(&self.pk_seed);
        id[N..].copy_from_slice(&self.root);
        SignetId(id)
    }

    /// Produce a `6,432`-byte `BLINCS-128-7x5` imprint for `message` under `context`
    /// using per-imprint 32-byte randomness `draw` (`SPEC.md §§7–11`).
    pub fn imprint_deterministic(
        &self,
        draw: &[u8; 32],
        context: &[u8],
        message: &[u8],
    ) -> [u8; IMPRINT_LEN] {
        let framed_ctx = frame_context(context);

        // §7: single-pass salted content hashing
        let e = trunc16(&keyed_hash(&self.k_salt, draw));
        let short = content_short(&self.k_content, &e, &framed_ctx, message);

        // §8: deterministic randomizer R and digest D
        let mut r_in = Vec::with_capacity(short.len() + framed_ctx.len());
        r_in.extend_from_slice(&short);
        r_in.extend_from_slice(&framed_ctx);
        let r = trunc16(&keyed_hash(&self.k_r, &r_in));
        let digest = message_digest(&self.k_pub, &r, &self.root, &short, &framed_ctx);
        let (ufors_sel, leaf_addr) = extract_indices(&digest);

        let mut out = Vec::with_capacity(IMPRINT_LEN);
        out.extend_from_slice(&e);
        out.extend_from_slice(&r);

        // §10: U-FORS (15 height-5 trees of 3-chain upper-layer leaves)
        let (ufors_root, ufors_bytes) = ufors_sign(&self.k_sec, &self.k_pub, leaf_addr, &ufors_sel);
        out.extend_from_slice(&ufors_bytes);

        // §11: 7-layer uniform height-5 hypertree
        let mut node = ufors_root;
        let mut addr = leaf_addr;
        for layer in 0..LAYERS {
            let layer_u8 = u8::try_from(layer).unwrap();
            let leaf = usize::try_from(addr & ((1u64 << TREE_HEIGHT) - 1)).unwrap();
            let tree = addr >> TREE_HEIGHT;
            let digits = wots_digits(&node);
            let pos = LeafPos {
                layer: layer_u8,
                tree,
                leaf: u16::try_from(leaf).unwrap(),
            };
            for chunk in chain_sign(&self.k_sec, &self.k_pub, pos, &digits) {
                out.extend_from_slice(&chunk);
            }
            let leaves = tree_leaves(
                &self.k_sec,
                &self.k_pub,
                layer_u8,
                tree,
                CHAINS,
                CHAIN_STEPS,
            );
            let (tree_root, auth) =
                merkle_root_and_auth(&self.k_pub, layer_u8, tree, &leaves, leaf);
            for sibling in &auth {
                out.extend_from_slice(sibling);
            }
            node = tree_root;
            addr = tree;
        }
        assert_eq!(addr, 0);
        assert_eq!(node, self.root);
        out.try_into()
            .expect("encoded imprint must be exact IMPRINT_LEN bytes")
    }
}

impl SignetId {
    /// Verify a `6,432`-byte `BLINCS-128-7x5` imprint for `message` under `context`.
    pub fn verify(&self, context: &[u8], message: &[u8], imprint: &[u8; IMPRINT_LEN]) -> bool {
        blake3_servil_core::initialize();
        if context.len() > MAX_CONTEXT_LEN {
            return false;
        }
        let framed_ctx = frame_context(context);
        let keys = self.derive_keys();

        let e: [u8; N] = imprint[0..N].try_into().unwrap();
        let r: [u8; N] = imprint[N..2 * N].try_into().unwrap();
        let short = content_short(&keys.k_content, &e, &framed_ctx, message);
        let digest = message_digest(&keys.k_pub, &r, &keys.root, &short, &framed_ctx);
        let (ufors_sel, leaf_addr) = extract_indices(&digest);

        let ufors_slice = &imprint[2 * N..2 * N + UFORS_LEN];
        let mut node = ufors_verify(&keys.k_pub, leaf_addr, &ufors_sel, ufors_slice);

        let mut addr = leaf_addr;
        let mut cursor = 2 * N + UFORS_LEN;
        for layer in 0..LAYERS {
            let layer_u8 = u8::try_from(layer).unwrap();
            let leaf = usize::try_from(addr & ((1u64 << TREE_HEIGHT) - 1)).unwrap();
            let tree = addr >> TREE_HEIGHT;

            let wots_bytes = &imprint[cursor..cursor + CHAINS * N];
            cursor += CHAINS * N;
            let auth_bytes = &imprint[cursor..cursor + TREE_HEIGHT * N];
            cursor += TREE_HEIGHT * N;

            let digits = wots_digits(&node);
            let pos = LeafPos {
                layer: layer_u8,
                tree,
                leaf: u16::try_from(leaf).unwrap(),
            };
            let leaf_pk = chain_verify(&keys.k_pub, pos, &digits, CHAIN_STEPS, wots_bytes);
            node = merkle_reconstruct(&keys.k_pub, layer_u8, tree, leaf, leaf_pk, auth_bytes);
            addr = tree;
        }
        assert_eq!(cursor, IMPRINT_LEN);
        eq16_ct(&node, &keys.root)
    }
}

// ---------------------------------------------------------------------------
// 5. Context framing, salted content hash, and LSB-first bit extraction (§7–§8)
// ---------------------------------------------------------------------------

fn frame_context(context: &[u8]) -> Vec<u8> {
    assert!(
        context.len() <= MAX_CONTEXT_LEN,
        "context exceeds {MAX_CONTEXT_LEN} bytes"
    );
    let mut framed = Vec::with_capacity(1 + context.len());
    framed.push(u8::try_from(context.len()).unwrap());
    framed.extend_from_slice(context);
    framed
}

fn content_short(
    k_content: &[u8; 32],
    e: &[u8; N],
    framed_ctx: &[u8],
    message: &[u8],
) -> [u8; N + 32] {
    let mut k_in = Vec::with_capacity(N + framed_ctx.len());
    k_in.extend_from_slice(e);
    k_in.extend_from_slice(framed_ctx);
    let k_msg = keyed_hash(k_content, &k_in);
    let h_msg = keyed_hash(&k_msg, message);
    let mut short = [0u8; N + 32];
    short[..N].copy_from_slice(e);
    short[N..].copy_from_slice(&h_msg);
    short
}

fn message_digest(
    k_pub: &[u8; 32],
    r: &[u8; N],
    root: &[u8; N],
    short: &[u8; N + 32],
    framed_ctx: &[u8],
) -> [u8; 32] {
    let mut h = Hasher::new(Mode::Keyed(k_pub), None);
    h.update(&tweak(KIND_MESSAGE, 0, 0, 0, 0, 0));
    h.update(r);
    h.update(root);
    h.update(short);
    h.update(framed_ctx);
    *h.finalize().as_bytes()
}

/// Extract `width` bits (`1..=57`) starting at LSB-first bit offset `bit_off`
/// from the 256-bit little-endian digest `D` (`SPEC.md §8`).
pub fn read_bits(d: &[u8; 32], bit_off: usize, width: usize) -> u64 {
    assert!((1..=57).contains(&width) && bit_off + width <= 256);
    let byte_off = bit_off / 8;
    let shift = bit_off % 8;
    let mut raw = [0u8; 8];
    let avail = (32 - byte_off).min(8);
    raw[..avail].copy_from_slice(&d[byte_off..byte_off + avail]);
    (u64::from_le_bytes(raw) >> shift) & ((1u64 << width) - 1)
}

#[derive(Clone, Copy)]
struct UforsSel {
    leaf: usize,
    code: usize,
}

fn extract_indices(digest: &[u8; 32]) -> ([UforsSel; UFORS_TREES], u64) {
    let mut sel = [UforsSel { leaf: 0, code: 0 }; UFORS_TREES];
    for (t, slot) in sel.iter_mut().enumerate() {
        let base = (TREE_HEIGHT + UFORS_CODE_BITS) * t;
        slot.leaf = usize::try_from(read_bits(digest, base, TREE_HEIGHT)).unwrap();
        slot.code =
            usize::try_from(read_bits(digest, base + TREE_HEIGHT, UFORS_CODE_BITS)).unwrap();
    }
    let leaf_addr = read_bits(
        digest,
        UFORS_TREES * (TREE_HEIGHT + UFORS_CODE_BITS),
        LAYERS * TREE_HEIGHT,
    );
    (sel, leaf_addr)
}

// ---------------------------------------------------------------------------
// 6. Unified chain-and-Merkle primitive (SPEC.md §9)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct LeafPos {
    layer: u8,
    tree: u64,
    leaf: u16,
}

fn chain_step(
    k_pub: &[u8; 32],
    pos: LeafPos,
    chain_idx: usize,
    mut val: [u8; N],
    steps: core::ops::Range<usize>,
) -> [u8; N] {
    let c_u16 = u16::try_from(chain_idx).unwrap();
    for step in steps {
        val = short_hash(
            k_pub,
            tweak(
                KIND_CHAIN,
                pos.layer,
                pos.tree,
                pos.leaf,
                c_u16,
                u32::try_from(step).unwrap(),
            ),
            &val,
        );
    }
    val
}

fn chain_start(k_sec: &[u8; 32], pos: LeafPos, chain_idx: usize) -> [u8; N] {
    short_hash(
        k_sec,
        tweak(
            KIND_CHAIN_SECRET,
            pos.layer,
            pos.tree,
            pos.leaf,
            u16::try_from(chain_idx).unwrap(),
            0,
        ),
        &[],
    )
}

fn chain_pk(
    k_sec: &[u8; 32],
    k_pub: &[u8; 32],
    pos: LeafPos,
    n_chains: usize,
    steps: usize,
) -> [u8; N] {
    let mut ends = Vec::with_capacity(n_chains * N);
    for c in 0..n_chains {
        let x0 = chain_start(k_sec, pos, c);
        let x_end = chain_step(k_pub, pos, c, x0, 0..steps);
        ends.extend_from_slice(&x_end);
    }
    short_hash(
        k_pub,
        tweak(KIND_ONE_TIME_KEY, pos.layer, pos.tree, pos.leaf, 0, 0),
        &ends,
    )
}

fn chain_sign(k_sec: &[u8; 32], k_pub: &[u8; 32], pos: LeafPos, digits: &[usize]) -> Vec<[u8; N]> {
    digits
        .iter()
        .enumerate()
        .map(|(c, &d)| {
            let x0 = chain_start(k_sec, pos, c);
            chain_step(k_pub, pos, c, x0, 0..d)
        })
        .collect()
}

fn chain_verify(
    k_pub: &[u8; 32],
    pos: LeafPos,
    digits: &[usize],
    steps: usize,
    sig_bytes: &[u8],
) -> [u8; N] {
    let mut ends = Vec::with_capacity(digits.len() * N);
    for (c, &d) in digits.iter().enumerate() {
        let cur: [u8; N] = sig_bytes[c * N..(c + 1) * N].try_into().unwrap();
        let x_end = chain_step(k_pub, pos, c, cur, d..steps);
        ends.extend_from_slice(&x_end);
    }
    short_hash(
        k_pub,
        tweak(KIND_ONE_TIME_KEY, pos.layer, pos.tree, pos.leaf, 0, 0),
        &ends,
    )
}

fn tree_leaves(
    k_sec: &[u8; 32],
    k_pub: &[u8; 32],
    layer: u8,
    tree: u64,
    n_chains: usize,
    steps: usize,
) -> [[u8; N]; TREE_LEAVES] {
    core::array::from_fn(|leaf| {
        chain_pk(
            k_sec,
            k_pub,
            LeafPos {
                layer,
                tree,
                leaf: u16::try_from(leaf).unwrap(),
            },
            n_chains,
            steps,
        )
    })
}

fn merkle_root_and_auth(
    k_pub: &[u8; 32],
    layer: u8,
    tree: u64,
    leaves: &[[u8; N]; TREE_LEAVES],
    target: usize,
) -> ([u8; N], [[u8; N]; TREE_HEIGHT]) {
    assert!(target < TREE_LEAVES);
    let mut level_nodes = leaves.to_vec();
    let mut auth = [[0u8; N]; TREE_HEIGHT];
    let mut pos = target;
    for (h, auth_slot) in auth.iter_mut().enumerate() {
        *auth_slot = level_nodes[pos ^ 1];
        let level = u16::try_from(h + 1).unwrap();
        let mut next = Vec::with_capacity(level_nodes.len() / 2);
        for (p, pair) in level_nodes.chunks_exact(2).enumerate() {
            let mut buf = [0u8; 2 * N];
            buf[..N].copy_from_slice(&pair[0]);
            buf[N..].copy_from_slice(&pair[1]);
            next.push(short_hash(
                k_pub,
                tweak(KIND_NODE, layer, tree, 0, level, u32::try_from(p).unwrap()),
                &buf,
            ));
        }
        level_nodes = next;
        pos >>= 1;
    }
    (level_nodes[0], auth)
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
// 7. Few-time signatures: U-FORS (SPEC.md §10)
// ---------------------------------------------------------------------------

fn ufors_digits(code_idx: usize) -> [usize; UFORS_CHAINS] {
    let cw = UFORS_CODE[code_idx];
    [usize::from(cw[0]), usize::from(cw[1]), usize::from(cw[2])]
}

fn ufors_sign(
    k_sec: &[u8; 32],
    k_pub: &[u8; 32],
    leaf_addr: u64,
    sel: &[UforsSel; UFORS_TREES],
) -> ([u8; N], Vec<u8>) {
    let mut out = Vec::with_capacity(UFORS_LEN);
    let mut roots = Vec::with_capacity(UFORS_TREES * N);
    for (t, &s) in sel.iter().enumerate() {
        let layer = UFORS_LAYER_BASE + u8::try_from(t).unwrap();
        let digits = ufors_digits(s.code);
        let pos = LeafPos {
            layer,
            tree: leaf_addr,
            leaf: u16::try_from(s.leaf).unwrap(),
        };
        for chunk in chain_sign(k_sec, k_pub, pos, &digits) {
            out.extend_from_slice(&chunk);
        }
        let leaves = tree_leaves(k_sec, k_pub, layer, leaf_addr, UFORS_CHAINS, UFORS_STEPS);
        let (tree_root, auth) = merkle_root_and_auth(k_pub, layer, leaf_addr, &leaves, s.leaf);
        for sibling in &auth {
            out.extend_from_slice(sibling);
        }
        roots.extend_from_slice(&tree_root);
    }
    let ufors_root = short_hash(k_pub, tweak(KIND_FEW_ROOT, 0, leaf_addr, 0, 0, 0), &roots);
    (ufors_root, out)
}

fn ufors_verify(
    k_pub: &[u8; 32],
    leaf_addr: u64,
    sel: &[UforsSel; UFORS_TREES],
    ufors_bytes: &[u8],
) -> [u8; N] {
    let mut roots = Vec::with_capacity(UFORS_TREES * N);
    for (t, &s) in sel.iter().enumerate() {
        let layer = UFORS_LAYER_BASE + u8::try_from(t).unwrap();
        let entry = &ufors_bytes[t * UFORS_TREE_LEN..(t + 1) * UFORS_TREE_LEN];
        let chain_bytes = &entry[..UFORS_CHAINS * N];
        let auth_bytes = &entry[UFORS_CHAINS * N..];
        let digits = ufors_digits(s.code);
        let pos = LeafPos {
            layer,
            tree: leaf_addr,
            leaf: u16::try_from(s.leaf).unwrap(),
        };
        let leaf_pk = chain_verify(k_pub, pos, &digits, UFORS_STEPS, chain_bytes);
        let tree_root = merkle_reconstruct(k_pub, layer, leaf_addr, s.leaf, leaf_pk, auth_bytes);
        roots.extend_from_slice(&tree_root);
    }
    short_hash(k_pub, tweak(KIND_FEW_ROOT, 0, leaf_addr, 0, 0, 0), &roots)
}

// ---------------------------------------------------------------------------
// 8. WOTS+ digit encoding (SPEC.md §11)
// ---------------------------------------------------------------------------

/// Decompose a 16-byte message into 32 message nibbles + 3 checksum nibbles.
pub fn wots_digits(msg: &[u8; N]) -> [usize; CHAINS] {
    let mut d = [0usize; CHAINS];
    let mut csum = 0usize;
    for (i, &byte) in msg.iter().enumerate() {
        let lo = usize::from(byte & 0x0f);
        let hi = usize::from(byte >> 4);
        d[2 * i] = lo;
        d[2 * i + 1] = hi;
        csum += (CHAIN_STEPS - lo) + (CHAIN_STEPS - hi);
    }
    d[32] = csum & 0x0f;
    d[33] = (csum >> 4) & 0x0f;
    d[34] = (csum >> 8) & 0x0f;
    d
}

// ---------------------------------------------------------------------------
// 9. Quick startup self-test (SPEC.md §12)
// ---------------------------------------------------------------------------

const SELF_TEST_ID: [u8; 32] = [
    0x98, 0xa5, 0xb8, 0x31, 0x4b, 0x85, 0x4e, 0x78, 0xf7, 0x2c, 0xba, 0xdc, 0x9f, 0x5e, 0xd6, 0x7c,
    0x15, 0xbc, 0x2a, 0xd2, 0x53, 0xcd, 0x98, 0xbe, 0x1d, 0x59, 0x51, 0x59, 0x5f, 0x21, 0x75, 0x12,
];
const SELF_TEST_CTX: &[u8] = b"BLINCS-128-7x5 reference vector v1";
const SELF_TEST_MSG: &[u8] = b"hello, BLINCS";
const SELF_TEST_IMPRINT: &[u8; IMPRINT_LEN] =
    include_bytes!("../../test_vectors/reference-imprint-1.bin");

/// Run the quick fail-closed startup self-test recommended by `SPEC.md §12`.
///
/// 1. Initializes `blake3-servil-core` (running its own CPU-kernel self-test).
/// 2. Verifies the canonical `BLINCS-128-7x5` reference imprint (`~35 us`).
/// 3. Confirms 1-bit tamper rejection and wrong-context rejection (`~70 us`).
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
