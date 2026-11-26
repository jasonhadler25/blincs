/-
  BLINCS-128-7x5 Declarative Specification: Complete Scheme (`U-FORS`), Wire Format & Completeness.
  Matches SPEC.md §§4–11 verbatim over an abstract `HashOracle` (`keyed`, `derive`).
  Mechanically proves:
    1. Exact wire length (`(encodeImprint σ).length = 6432 = IMPRINT_LEN`).
    2. Exact wire injectivity (`encodeImprint σ₁ = encodeImprint σ₂ → σ₁ = σ₂`).
    3. **BLINCS Completeness Theorem**: every honestly generated imprint verifies to `true`.
-/
import Blincs.Params
import Blincs.Tweaks
import Blincs.Wots
import Blincs.Merkle

namespace Blincs

/-- Abstract BLAKE3 hash oracle (`SPEC.md §2`): `keyed` (KEYED_HASH) and `derive` (DERIVE_KEY). -/
structure HashOracle where
  keyed  : Bytes 32 → List UInt8 → Bytes 32
  derive : String → List UInt8 → Bytes 32

/-- Truncate a 32-byte digest to its first 16 bytes (`x[..16]`). -/
def trunc16 (b : Bytes 32) : Bytes 16 :=
  b.take 16 (by decide)

/-- `ShortHash(K, T, data) = Keyed(K, encodeTweak T || data)[..16]` (`SPEC.md §5`). -/
def shortHash (H : HashOracle) (K : Bytes 32) (T : Tweak) (data : List UInt8) : Bytes 16 :=
  trunc16 (H.keyed K (encodeTweak T ++ data))

/-- Flatten a fixed-length vector of 16-byte blocks into a byte list (`k * 16` bytes). -/
def flattenBytes16 {k : Nat} (xs : Fin k → Bytes 16) : List UInt8 :=
  (List.ofFn (fun i => (xs i).toList)).flatten

private theorem flatten_length_const {α : Type} {m : Nat} :
    ∀ (ls : List (List α)), (∀ l ∈ ls, l.length = m) → ls.flatten.length = ls.length * m
  | [], _ => by simp
  | l :: ls, h => by
    have hl : l.length = m := h l (by simp)
    have hls : ls.flatten.length = ls.length * m :=
      flatten_length_const ls (fun x hx => h x (by simp [hx]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hl, hls, Nat.succ_mul]
    omega

theorem flattenBytes16_length {k : Nat} (xs : Fin k → Bytes 16) :
    (flattenBytes16 xs).length = k * 16 := by
  unfold flattenBytes16
  rw [flatten_length_const (m := 16)]
  · simp
  · intro l hl
    rw [List.mem_ofFn] at hl
    rcases hl with ⟨i, rfl⟩
    exact Bytes.toList_length _

private theorem flatten_injective_const {α : Type} {m : Nat} :
    ∀ {l₁ l₂ : List (List α)},
      l₁.length = l₂.length →
      (∀ l ∈ l₁, l.length = m) →
      (∀ l ∈ l₂, l.length = m) →
      l₁.flatten = l₂.flatten →
      l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | _ :: _, [], hlen, _, _, _ => by simp at hlen
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | a :: as, b :: bs, hlen, h₁, h₂, hflat => by
    simp only [List.flatten_cons] at hflat
    have ha : a.length = m := h₁ a (by simp)
    have hb : b.length = m := h₂ b (by simp)
    have hab : a = b := by
      have := congrArg (List.take m) hflat
      simpa [ha, hb] using this
    have hrest : as.flatten = bs.flatten := by
      have := congrArg (List.drop m) hflat
      simpa [ha, hb] using this
    have htail := flatten_injective_const (Nat.succ.inj hlen)
      (fun x hx => h₁ x (by simp [hx]))
      (fun x hx => h₂ x (by simp [hx]))
      hrest
    rw [hab, htail]

theorem flattenBytes16_injective {k : Nat} {xs ys : Fin k → Bytes 16}
    (h : flattenBytes16 xs = flattenBytes16 ys) : xs = ys := by
  unfold flattenBytes16 at h
  have hlist : List.ofFn (fun i => (xs i).toList) = List.ofFn (fun i => (ys i).toList) := by
    apply flatten_injective_const (m := 16) (by simp)
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨i, rfl⟩; exact Bytes.toList_length _
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨i, rfl⟩; exact Bytes.toList_length _
    · exact h
  funext i
  have hi : (List.ofFn (fun j => (xs j).toList))[i.val]'(by simp) =
            (List.ofFn (fun j => (ys j).toList))[i.val]'(by simp) := by simp [hlist]
  simp only [List.getElem_ofFn] at hi
  exact Bytes.toList_injective hi

-- ---------------------------------------------------------------------------
-- Unified Chain-and-Merkle Primitive (`SPEC.md §9`, shared by U-FORS & Hypertree!)
-- ---------------------------------------------------------------------------

def chainStart (H : HashOracle) (K_sec : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16) (c : Nat) : Bytes 16 :=
  shortHash H K_sec ⟨.chainSecret, layer, tree, hTree, leaf, UInt16.ofNat c, 0⟩ []

def chainStepFn (H : HashOracle) (K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16) (c : Nat) :
    Nat → Bytes 16 → Bytes 16 :=
  fun s x => shortHash H K_pub ⟨.chain, layer, tree, hTree, leaf, UInt16.ofNat c, UInt32.ofNat s⟩ x.toList

def chainEndpoint (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    (maxSteps c : Nat) : Bytes 16 :=
  chainIter (chainStepFn H K_pub layer tree hTree leaf c) 0 maxSteps
    (chainStart H K_sec layer tree hTree leaf c)

def chainLeafPk (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    (nChains maxSteps : Nat) : Bytes 16 :=
  shortHash H K_pub ⟨.oneTimeKey, layer, tree, hTree, leaf, 0, 0⟩
    (flattenBytes16 (fun c : Fin nChains => chainEndpoint H K_sec K_pub layer tree hTree leaf maxSteps c.val))

def chainSignGeneric (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    {nChains : Nat} (digits : Fin nChains → Nat) : Fin nChains → Bytes 16 :=
  fun c =>
    chainIter (chainStepFn H K_pub layer tree hTree leaf c.val) 0 (digits c)
      (chainStart H K_sec layer tree hTree leaf c.val)

def chainVerifyGeneric (H : HashOracle) (K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    {nChains : Nat} (maxSteps : Nat) (digits : Fin nChains → Nat)
    (sig : Fin nChains → Bytes 16) : Bytes 16 :=
  let ends : Fin nChains → Bytes 16 := fun c =>
    let d := digits c
    chainIter (chainStepFn H K_pub layer tree hTree leaf c.val) d (maxSteps - d) (sig c)
  shortHash H K_pub ⟨.oneTimeKey, layer, tree, hTree, leaf, 0, 0⟩ (flattenBytes16 ends)

theorem chainVerifyGeneric_sign (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    {nChains : Nat} (maxSteps : Nat) (digits : Fin nChains → Nat)
    (hDigits : ∀ c, digits c ≤ maxSteps) :
    chainVerifyGeneric H K_pub layer tree hTree leaf maxSteps digits
      (chainSignGeneric H K_sec K_pub layer tree hTree leaf digits) =
    chainLeafPk H K_sec K_pub layer tree hTree leaf nChains maxSteps := by
  unfold chainVerifyGeneric chainSignGeneric chainLeafPk chainEndpoint
  apply congrArg (shortHash H K_pub _)
  apply congrArg flattenBytes16
  funext c
  exact chain_complete (chainStepFn H K_pub layer tree hTree leaf c.val)
    (chainStart H K_sec layer tree hTree leaf c.val) (hDigits c)

/-- Unified Merkle combine function for every height-5 tree (both hypertree and U-FORS). -/
def treeCombine (H : HashOracle) (K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) :
    Nat → Nat → Bytes 16 → Bytes 16 → Bytes 16 :=
  fun level p L R =>
    shortHash H K_pub ⟨.node, layer, tree, hTree, 0, UInt16.ofNat level, UInt32.ofNat p⟩ (L.toList ++ R.toList)

def treeLeaves (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (nChains maxSteps : Nat) :
    Fin (2 ^ TREE_HEIGHT) → Bytes 16 :=
  fun leaf => chainLeafPk H K_sec K_pub layer tree hTree (UInt16.ofNat leaf.val) nChains maxSteps

def treeRoot (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (nChains maxSteps : Nat) : Bytes 16 :=
  merkleNode (treeCombine H K_pub layer tree hTree) TREE_HEIGHT 0
    (treeLeaves H K_sec K_pub layer tree hTree nChains maxSteps)

-- ---------------------------------------------------------------------------
-- U-FORS Instantiated on Unified Chain-and-Merkle Primitive (`SPEC.md §10`)
-- ---------------------------------------------------------------------------

def uforsTreeRoot (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (t : Fin UFORS_TREES) : Bytes 16 :=
  treeRoot H K_sec K_pub (uforsLayerByte t) leafAddr hAddr UFORS_CHAINS UFORS_STEPS

def uforsRoot (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) : Bytes 16 :=
  shortHash H K_pub ⟨.fewRoot, 0, leafAddr, hAddr, 0, 0, 0⟩
    (flattenBytes16 (fun t : Fin UFORS_TREES => uforsTreeRoot H K_sec K_pub leafAddr hAddr t))

/-- One U-FORS tree opening: 3 chain values + 5-node authentication path (`128` bytes). -/
structure UforsTreeSig where
  chains : Fin UFORS_CHAINS → Bytes 16
  auth   : Fin TREE_HEIGHT → Bytes 16

/-- One hypertree layer signature: 35 WOTS+ values + 5-node authentication path (`640` bytes). -/
structure LayerSig where
  wots : Fin CHAINS → Bytes 16
  auth : Fin TREE_HEIGHT → Bytes 16

/-- Complete structured `BLINCS-128-7x5` imprint (`SPEC.md §11`: `6,432` bytes). -/
structure Imprint where
  e      : Bytes 16
  r      : Bytes 16
  ufors  : Fin UFORS_TREES → UforsTreeSig
  layers : Fin LAYERS → LayerSig

private def listToFinFn {α : Type} {h : Nat} (l : List α) (hl : l.length = h) : Fin h → α :=
  fun i => l[i.val]'(by omega)

private theorem ofFn_listToFinFn {α : Type} {h : Nat} (l : List α) (hl : l.length = h) :
    List.ofFn (listToFinFn l hl) = l := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp [listToFinFn]

def uforsSign (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48)
    (leafSel : Fin UFORS_TREES → Nat) (codeSel : Fin UFORS_TREES → Fin 64) :
    Fin UFORS_TREES → UforsTreeSig :=
  fun t =>
    let lByte := uforsLayerByte t
    let leaf := leafSel t
    let digits := fun c : Fin UFORS_CHAINS => uforsDigit (codeSel t) c
    let chains := chainSignGeneric H K_sec K_pub lByte leafAddr hAddr (UInt16.ofNat leaf) digits
    let leaves := treeLeaves H K_sec K_pub lByte leafAddr hAddr UFORS_CHAINS UFORS_STEPS
    let path := merklePath (treeCombine H K_pub lByte leafAddr hAddr) TREE_HEIGHT 0 leaves leaf
    { chains := chains
      auth   := listToFinFn path (merklePath_length _ _ _ _ _) }

def uforsVerify (H : HashOracle) (K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48)
    (leafSel : Fin UFORS_TREES → Nat) (codeSel : Fin UFORS_TREES → Fin 64)
    (sig : Fin UFORS_TREES → UforsTreeSig) : Bytes 16 :=
  let roots : Fin UFORS_TREES → Bytes 16 := fun t =>
    let lByte := uforsLayerByte t
    let leaf := leafSel t
    let digits := fun c : Fin UFORS_CHAINS => uforsDigit (codeSel t) c
    let leafPk := chainVerifyGeneric H K_pub lByte leafAddr hAddr (UInt16.ofNat leaf)
      UFORS_STEPS digits (sig t).chains
    merkleReconstruct (treeCombine H K_pub lByte leafAddr hAddr) leaf leafPk (List.ofFn (sig t).auth)
  shortHash H K_pub ⟨.fewRoot, 0, leafAddr, hAddr, 0, 0, 0⟩ (flattenBytes16 roots)

theorem uforsVerify_uforsSign (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48)
    (leafSel : Fin UFORS_TREES → Nat) (hLeaf : ∀ t, leafSel t < 2 ^ TREE_HEIGHT)
    (codeSel : Fin UFORS_TREES → Fin 64) :
    uforsVerify H K_pub leafAddr hAddr leafSel codeSel
      (uforsSign H K_sec K_pub leafAddr hAddr leafSel codeSel) =
    uforsRoot H K_sec K_pub leafAddr hAddr := by
  unfold uforsVerify uforsSign uforsRoot uforsTreeRoot treeRoot
  apply congrArg (shortHash H K_pub _)
  apply congrArg flattenBytes16
  funext t
  dsimp only
  have hchain : chainVerifyGeneric H K_pub (uforsLayerByte t) leafAddr hAddr (UInt16.ofNat (leafSel t))
      UFORS_STEPS (fun c : Fin UFORS_CHAINS => uforsDigit (codeSel t) c)
      (chainSignGeneric H K_sec K_pub (uforsLayerByte t) leafAddr hAddr (UInt16.ofNat (leafSel t))
        (fun c : Fin UFORS_CHAINS => uforsDigit (codeSel t) c)) =
      chainLeafPk H K_sec K_pub (uforsLayerByte t) leafAddr hAddr (UInt16.ofNat (leafSel t))
        UFORS_CHAINS UFORS_STEPS :=
    chainVerifyGeneric_sign H K_sec K_pub (uforsLayerByte t) leafAddr hAddr (UInt16.ofNat (leafSel t))
      UFORS_STEPS (fun c : Fin UFORS_CHAINS => uforsDigit (codeSel t) c)
      (fun c => uforsDigit_le_9 (codeSel t) c)
  rw [hchain, ofFn_listToFinFn]
  exact merkleReconstruct_correct (treeCombine H K_pub (uforsLayerByte t) leafAddr hAddr)
    TREE_HEIGHT (treeLeaves H K_sec K_pub (uforsLayerByte t) leafAddr hAddr UFORS_CHAINS UFORS_STEPS)
    (leafSel t) (hLeaf t)

-- ---------------------------------------------------------------------------
-- Key Schedule, Content Hashing, LSB-First Bit Extraction & Full Scheme (§§6–11)
-- ---------------------------------------------------------------------------

/-- Derived key bundle for a 32-byte `seed` (`SPEC.md §6`). -/
structure DerivedKeys where
  k_sec     : Bytes 32
  k_salt    : Bytes 32
  k_r       : Bytes 32
  pk_seed   : Bytes 16
  k_pub     : Bytes 32
  root      : Bytes 16
  id        : Bytes 32
  k_content : Bytes 32

def deriveKeys (H : HashOracle) (seed : Bytes 32) : DerivedKeys :=
  let k_sec   := H.derive CTX_SECRET_VALUES seed.toList
  let k_salt  := H.derive CTX_CONTENT_SALT  seed.toList
  let k_r     := H.derive CTX_RANDOMIZER    seed.toList
  let pk_seed := trunc16 (H.derive CTX_PUBLIC_SEED seed.toList)
  let k_pub   := H.derive CTX_PUBLIC_HASH   pk_seed.toList
  let root    := treeRoot H k_sec k_pub 6 0 (by decide) CHAINS CHAIN_STEPS
  let id      := pk_seed.append root
  let k_content := H.derive CTX_CONTENT id.toList
  { k_sec, k_salt, k_r, pk_seed, k_pub, root, id, k_content }

def signetId (H : HashOracle) (seed : Bytes 32) : Bytes 32 :=
  (deriveKeys H seed).id

def verifierKPub (H : HashOracle) (id : Bytes 32) : Bytes 32 :=
  H.derive CTX_PUBLIC_HASH (id.take 16 (by decide)).toList

def verifierRoot (id : Bytes 32) : Bytes 16 :=
  id.slice 16 16 (by decide)

def verifierKContent (H : HashOracle) (id : Bytes 32) : Bytes 32 :=
  H.derive CTX_CONTENT id.toList

theorem verifierKeys_match_deriveKeys (H : HashOracle) (seed : Bytes 32) :
    verifierKPub H (signetId H seed) = (deriveKeys H seed).k_pub ∧
    verifierRoot (signetId H seed) = (deriveKeys H seed).root ∧
    verifierKContent H (signetId H seed) = (deriveKeys H seed).k_content := by
  unfold signetId deriveKeys verifierKPub verifierRoot verifierKContent
  dsimp only
  have htake : (Bytes.append (trunc16 (H.derive CTX_PUBLIC_SEED seed.toList))
      (treeRoot H (H.derive CTX_SECRET_VALUES seed.toList)
        (H.derive CTX_PUBLIC_HASH (trunc16 (H.derive CTX_PUBLIC_SEED seed.toList)).toList) 6 0 (by decide) CHAINS CHAIN_STEPS)).take 16 (by decide) =
      trunc16 (H.derive CTX_PUBLIC_SEED seed.toList) := by
    funext i; simp [Bytes.take, Bytes.append, i.isLt]
  have hslice : (Bytes.append (trunc16 (H.derive CTX_PUBLIC_SEED seed.toList))
      (treeRoot H (H.derive CTX_SECRET_VALUES seed.toList)
        (H.derive CTX_PUBLIC_HASH (trunc16 (H.derive CTX_PUBLIC_SEED seed.toList)).toList) 6 0 (by decide) CHAINS CHAIN_STEPS)).slice 16 16 (by decide) =
      treeRoot H (H.derive CTX_SECRET_VALUES seed.toList)
        (H.derive CTX_PUBLIC_HASH (trunc16 (H.derive CTX_PUBLIC_SEED seed.toList)).toList) 6 0 (by decide) CHAINS CHAIN_STEPS := by
    funext i
    unfold Bytes.slice Bytes.append
    have hnot : ¬ (16 + i.val < 16) := by omega
    simp only [hnot, ↓reduceDIte]
    congr 1
    exact Fin.ext (by dsimp; omega)
  exact ⟨by rw [htake], hslice, rfl⟩

/-- Content message key `K_msg = Keyed(K_content, e || framed_ctx)` (`SPEC.md §7`). -/
def contentKey (H : HashOracle) (k_content : Bytes 32) (e : Bytes 16) (ctx : List UInt8) : Bytes 32 :=
  H.keyed k_content (e.toList ++ frameContext ctx)

/-- Single-pass salted message hash `h_msg = Keyed(K_msg, M)` (`SPEC.md §7`). -/
def contentHash (H : HashOracle) (k_content : Bytes 32) (e : Bytes 16) (ctx M : List UInt8) : Bytes 32 :=
  H.keyed (contentKey H k_content e ctx) M

/-- `short = e || h_msg` (`48` bytes, `SPEC.md §7`). -/
def contentShort (H : HashOracle) (k_content : Bytes 32) (e : Bytes 16) (ctx M : List UInt8) : List UInt8 :=
  e.toList ++ (contentHash H k_content e ctx M).toList

/-- Message digest `D = Keyed(K_pub, tweak(MESSAGE) || R || root || short || framed_ctx)` (`SPEC.md §8`). -/
def messageDigest (H : HashOracle) (k_pub : Bytes 32) (r root : Bytes 16)
    (short : List UInt8) (ctx : List UInt8) : Bytes 32 :=
  let twk : Tweak := ⟨.message, 0, 0, by decide, 0, 0, 0⟩
  H.keyed k_pub (encodeTweak twk ++ r.toList ++ root.toList ++ short ++ frameContext ctx)

/-- Extract `width` bits from LSB-first little-endian 256-bit digest `D` at bit offset `off` (`SPEC.md §8`). -/
def readBits (D : Bytes 32) (off width : Nat) : Nat :=
  (decodeLE D.toList / 2 ^ off) % 2 ^ width

/-- Extract U-FORS leaf index (`0..31`) for tree `t : Fin 15` (`SPEC.md §8`). -/
def extractUforsLeaf (D : Bytes 32) (t : Fin UFORS_TREES) : Nat :=
  readBits D (11 * t.val) TREE_HEIGHT

theorem extractUforsLeaf_lt (D : Bytes 32) (t : Fin UFORS_TREES) :
    extractUforsLeaf D t < 2 ^ TREE_HEIGHT :=
  Nat.mod_lt _ (by decide)

/-- Extract U-FORS codeword index (`Fin 64`) for tree `t : Fin 15` (`SPEC.md §8`). -/
def extractUforsCode (D : Bytes 32) (t : Fin UFORS_TREES) : Fin 64 :=
  ⟨readBits D (11 * t.val + TREE_HEIGHT) UFORS_CODE_BITS, Nat.mod_lt _ (by decide)⟩

/-- Extract 35-bit hypertree leaf address (`bits 165..200`, `SPEC.md §8`). -/
def extractLeafAddr (D : Bytes 32) : Nat :=
  readBits D 165 HYPER_BITS

theorem extractLeafAddr_lt (D : Bytes 32) : extractLeafAddr D < 2 ^ HYPER_BITS :=
  Nat.mod_lt _ (by decide)

theorem extractLeafAddr_lt_48 (D : Bytes 32) : extractLeafAddr D < 2 ^ 48 := by
  have h1 := extractLeafAddr_lt D
  have h2 := params_tree_fits_tweak
  omega

/-- Address at layer `ℓ` of the hypertree: `leafAddr / 2^(5 * ℓ)`. -/
def layerAddr (leafAddr : Nat) (ℓ : Nat) : Nat :=
  leafAddr / 2 ^ (TREE_HEIGHT * ℓ)

/-- Tree index at layer `ℓ`: `layerAddr leafAddr ℓ / 32 = layerAddr leafAddr (ℓ + 1)`. -/
def layerTree (leafAddr : Nat) (ℓ : Nat) : Nat :=
  layerAddr leafAddr ℓ / 2 ^ TREE_HEIGHT

/-- Leaf index within its tree at layer `ℓ`: `layerAddr leafAddr ℓ % 32`. -/
def layerLeaf (leafAddr : Nat) (ℓ : Nat) : Nat :=
  layerAddr leafAddr ℓ % 2 ^ TREE_HEIGHT

theorem layerTree_eq_next_addr (leafAddr ℓ : Nat) :
    layerTree leafAddr ℓ = layerAddr leafAddr (ℓ + 1) := by
  unfold layerTree layerAddr
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]

theorem layerTree_lt_48 (leafAddr ℓ : Nat) (h : leafAddr < 2 ^ HYPER_BITS) :
    layerTree leafAddr ℓ < 2 ^ 48 := by
  unfold layerTree layerAddr
  have h1 : leafAddr / 2 ^ (TREE_HEIGHT * ℓ) ≤ leafAddr := Nat.div_le_self _ _
  have h2 : (leafAddr / 2 ^ (TREE_HEIGHT * ℓ)) / 2 ^ TREE_HEIGHT ≤ leafAddr / 2 ^ (TREE_HEIGHT * ℓ) :=
    Nat.div_le_self _ _
  have h3 := params_tree_fits_tweak
  omega

theorem layerLeaf_lt (leafAddr ℓ : Nat) : layerLeaf leafAddr ℓ < 2 ^ TREE_HEIGHT :=
  Nat.mod_lt _ (by decide)

theorem top_layerTree_zero {leafAddr : Nat} (h : leafAddr < 2 ^ HYPER_BITS) :
    layerTree leafAddr 6 = 0 := by
  rw [layerTree_eq_next_addr]
  unfold layerAddr
  have hpow : 2 ^ (TREE_HEIGHT * 7) = 2 ^ HYPER_BITS := rfl
  rw [hpow]
  exact Nat.div_eq_of_lt h

/-- Honest message signed at hypertree layer `ℓ` (`uforsRoot` at layer 0, child `treeRoot` at `ℓ > 0`). -/
def honestLayerInput (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS) : Nat → Bytes 16
  | 0 => uforsRoot H K_sec K_pub leafAddr (by have := params_tree_fits_tweak; omega)
  | ℓ + 1 => treeRoot H K_sec K_pub (UInt8.ofNat ℓ) (layerTree leafAddr ℓ) (layerTree_lt_48 leafAddr ℓ hAddr) CHAINS CHAIN_STEPS

/-- Declarative hypertree signing for all 7 layers (`SPEC.md §11`). -/
def hypertreeSign (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS) : Fin LAYERS → LayerSig :=
  fun ℓ =>
    let tree := layerTree leafAddr ℓ.val
    let hTree := layerTree_lt_48 leafAddr ℓ.val hAddr
    let leaf := layerLeaf leafAddr ℓ.val
    let lByte := UInt8.ofNat ℓ.val
    let msg := honestLayerInput H K_sec K_pub leafAddr hAddr ℓ.val
    let wots := chainSignGeneric H K_sec K_pub lByte tree hTree (UInt16.ofNat leaf) (wotsDigit msg)
    let leaves := treeLeaves H K_sec K_pub lByte tree hTree CHAINS CHAIN_STEPS
    let path := merklePath (treeCombine H K_pub lByte tree hTree) TREE_HEIGHT 0 leaves leaf
    { wots := wots
      auth := listToFinFn path (merklePath_length _ _ _ _ _) }

/-- Reconstruct layer `ℓ`'s tree root from `node` and `sig`. -/
def verifyLayerStep (H : HashOracle) (K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (ℓ : Fin LAYERS) (node : Bytes 16) (sig : LayerSig) : Bytes 16 :=
  let tree := layerTree leafAddr ℓ.val
  let hTree := layerTree_lt_48 leafAddr ℓ.val hAddr
  let leaf := layerLeaf leafAddr ℓ.val
  let lByte := UInt8.ofNat ℓ.val
  let leafPk := chainVerifyGeneric H K_pub lByte tree hTree (UInt16.ofNat leaf)
    CHAIN_STEPS (wotsDigit node) sig.wots
  merkleReconstruct (treeCombine H K_pub lByte tree hTree) leaf leafPk (List.ofFn sig.auth)

/-- Declarative hypertree verification fold over layers `0 .. k-1` (`k ≤ 7`). -/
def hypertreeVerifyUpTo (H : HashOracle) (K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (initNode : Bytes 16) (sigs : Fin LAYERS → LayerSig) : (k : Nat) → k ≤ LAYERS → Bytes 16
  | 0, _     => initNode
  | k + 1, hk =>
    let prev := hypertreeVerifyUpTo H K_pub leafAddr hAddr initNode sigs k (by omega)
    verifyLayerStep H K_pub leafAddr hAddr ⟨k, hk⟩ prev (sigs ⟨k, hk⟩)

/-- Full hypertree verification producing the reconstructed layer-6 root. -/
def hypertreeVerify (H : HashOracle) (K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (uforsNode : Bytes 16) (sigs : Fin LAYERS → LayerSig) : Bytes 16 :=
  hypertreeVerifyUpTo H K_pub leafAddr hAddr uforsNode sigs LAYERS (Nat.le_refl _)

/-- Declarative `BLINCS-128-7x5` imprinting (`SPEC.md §§6–11`). -/
def imprint (H : HashOracle) (seed draw : Bytes 32) (ctx M : List UInt8) : Imprint :=
  let k := deriveKeys H seed
  let e := trunc16 (H.keyed k.k_salt draw.toList)
  let short := contentShort H k.k_content e ctx M
  let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
  let D := messageDigest H k.k_pub r k.root short ctx
  let leafSel := extractUforsLeaf D
  let codeSel := extractUforsCode D
  let leafAddr := extractLeafAddr D
  let hAddr := extractLeafAddr_lt D
  let hAddr48 := extractLeafAddr_lt_48 D
  { e      := e
    r      := r
    ufors  := uforsSign H k.k_sec k.k_pub leafAddr hAddr48 leafSel codeSel
    layers := hypertreeSign H k.k_sec k.k_pub leafAddr hAddr }

/-- Declarative `BLINCS-128-7x5` verification (`SPEC.md §§6–11`). -/
def verify (H : HashOracle) (id : Bytes 32) (ctx M : List UInt8) (σ : Imprint) : Prop :=
  ctx.length ≤ MAX_CONTEXT_LEN ∧
  let k_pub := verifierKPub H id
  let root  := verifierRoot id
  let k_content := verifierKContent H id
  let short := contentShort H k_content σ.e ctx M
  let D := messageDigest H k_pub σ.r root short ctx
  let leafSel := extractUforsLeaf D
  let codeSel := extractUforsCode D
  let leafAddr := extractLeafAddr D
  let hAddr := extractLeafAddr_lt D
  let hAddr48 := extractLeafAddr_lt_48 D
  let uforsNode := uforsVerify H k_pub leafAddr hAddr48 leafSel codeSel σ.ufors
  hypertreeVerify H k_pub leafAddr hAddr uforsNode σ.layers = root

/-- Induction invariant for honest hypertree verification. -/
theorem hypertreeVerifyUpTo_honest (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS) :
    ∀ (k : Nat) (hk : k ≤ LAYERS),
      hypertreeVerifyUpTo H K_pub leafAddr hAddr
        (uforsRoot H K_sec K_pub leafAddr (by have := params_tree_fits_tweak; omega))
        (hypertreeSign H K_sec K_pub leafAddr hAddr) k hk =
      honestLayerInput H K_sec K_pub leafAddr hAddr k
  | 0, _ => rfl
  | k + 1, hk => by
    unfold hypertreeVerifyUpTo
    rw [hypertreeVerifyUpTo_honest H K_sec K_pub leafAddr hAddr k (by omega)]
    unfold verifyLayerStep hypertreeSign
    dsimp only
    let m := honestLayerInput H K_sec K_pub leafAddr hAddr k
    have hchain : chainVerifyGeneric H K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
        (UInt16.ofNat (layerLeaf leafAddr k)) CHAIN_STEPS (wotsDigit m)
        (chainSignGeneric H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
          (UInt16.ofNat (layerLeaf leafAddr k)) (wotsDigit m)) =
        chainLeafPk H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
          (UInt16.ofNat (layerLeaf leafAddr k)) CHAINS CHAIN_STEPS :=
      chainVerifyGeneric_sign H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
        (UInt16.ofNat (layerLeaf leafAddr k)) CHAIN_STEPS (wotsDigit m)
        (fun c => Nat.le_of_lt_succ (wotsDigit_lt_16 m c))
    rw [hchain, ofFn_listToFinFn]
    unfold honestLayerInput treeRoot
    exact merkleReconstruct_correct
      (treeCombine H K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr))
      TREE_HEIGHT
      (treeLeaves H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr) CHAINS CHAIN_STEPS)
      (layerLeaf leafAddr k) (layerLeaf_lt leafAddr k)

private theorem top_root_eq (H : HashOracle) (K_sec K_pub : Bytes 32)
    (t : Nat) (ht : t < 2 ^ 48) (h0 : t = 0) :
    treeRoot H K_sec K_pub 6 t ht CHAINS CHAIN_STEPS =
    treeRoot H K_sec K_pub 6 0 (by decide) CHAINS CHAIN_STEPS := by
  subst h0
  rfl

/--
  **BLINCS-128-7x5 Completeness Theorem:**
  For ANY hash oracle `H`, ANY 32-byte `seed`, ANY 32-byte `draw`, ANY valid context `ctx`
  (`ctx.length ≤ 255`), and ANY message `M`, the imprint produced by `imprint H seed draw ctx M`
  ALWAYS verifies against `signetId H seed`.
-/
theorem blincs_completeness (H : HashOracle) (seed draw : Bytes 32) (ctx M : List UInt8)
    (hCtx : ctx.length ≤ MAX_CONTEXT_LEN) :
    verify H (signetId H seed) ctx M (imprint H seed draw ctx M) := by
  refine ⟨hCtx, ?_⟩
  rcases verifierKeys_match_deriveKeys H seed with ⟨hkpub, hroot, hkcontent⟩
  dsimp only
  rw [hkpub, hroot, hkcontent]
  unfold imprint
  dsimp only
  rw [uforsVerify_uforsSign H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub _ _ _ (extractUforsLeaf_lt _) _]
  unfold hypertreeVerify
  rw [hypertreeVerifyUpTo_honest H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub _ _ LAYERS (Nat.le_refl _)]
  unfold honestLayerInput LAYERS
  exact top_root_eq H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub _ _ (top_layerTree_zero (extractLeafAddr_lt _))

-- ---------------------------------------------------------------------------
-- Wire Serialization (`SPEC.md §11`: Exact 6,432 Bytes & Bijection)
-- ---------------------------------------------------------------------------

def encodeUforsTreeSig (s : UforsTreeSig) : List UInt8 :=
  flattenBytes16 s.chains ++ flattenBytes16 s.auth

theorem encodeUforsTreeSig_length (s : UforsTreeSig) : (encodeUforsTreeSig s).length = 128 := by
  unfold encodeUforsTreeSig
  rw [List.length_append, flattenBytes16_length, flattenBytes16_length]
  rfl

def encodeLayerSig (s : LayerSig) : List UInt8 :=
  flattenBytes16 s.wots ++ flattenBytes16 s.auth

theorem encodeLayerSig_length (s : LayerSig) : (encodeLayerSig s).length = 640 := by
  unfold encodeLayerSig
  rw [List.length_append, flattenBytes16_length, flattenBytes16_length]
  rfl

/-- Canonical wire serialization of a `BLINCS-128-7x5` imprint (`SPEC.md §11`). -/
def encodeImprint (σ : Imprint) : List UInt8 :=
  σ.e.toList
    ++ σ.r.toList
    ++ (List.ofFn (fun t => encodeUforsTreeSig (σ.ufors t))).flatten
    ++ (List.ofFn (fun ℓ => encodeLayerSig (σ.layers ℓ))).flatten

/-- **Wire Length Theorem:** every encoded `BLINCS-128-7x5` imprint is EXACTLY `6,432` bytes. -/
theorem encodeImprint_length (σ : Imprint) : (encodeImprint σ).length = IMPRINT_LEN := by
  unfold encodeImprint
  have h1 : (List.ofFn (fun t => encodeUforsTreeSig (σ.ufors t))).flatten.length = 1920 := by
    rw [flatten_length_const (m := 128)]
    · simp [UFORS_TREES]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨t, rfl⟩; exact encodeUforsTreeSig_length _
  have h2 : (List.ofFn (fun ℓ => encodeLayerSig (σ.layers ℓ))).flatten.length = 4480 := by
    rw [flatten_length_const (m := 640)]
    · simp [LAYERS]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨ℓ, rfl⟩; exact encodeLayerSig_length _
  simp only [List.length_append, Bytes.toList_length, h1, h2]
  rfl

private theorem ofFn_eq_at {n : Nat} {α : Type} {f g : Fin n → α}
    (h : List.ofFn f = List.ofFn g) (i : Fin n) : f i = g i := by
  have h1 := congrArg (fun l => l[i.val]?) h
  simp only [List.getElem?_eq_getElem (show i.val < (List.ofFn f).length by simp),
             List.getElem?_eq_getElem (show i.val < (List.ofFn g).length by simp),
             List.getElem_ofFn] at h1
  exact Option.some.inj h1

/-- **Wire Injectivity Theorem:** distinct structured imprints always encode to distinct 6,432-byte strings. -/
theorem encodeImprint_injective {σ₁ σ₂ : Imprint} (h : encodeImprint σ₁ = encodeImprint σ₂) : σ₁ = σ₂ := by
  have splitEq : ∀ {a b c d : List UInt8}, a.length = c.length → a ++ b = c ++ d → a = c ∧ b = d := by
    intro a b c d hlen heq
    exact ⟨by simpa [hlen] using congrArg (List.take a.length) heq,
           by simpa [hlen] using congrArg (List.drop a.length) heq⟩
  unfold encodeImprint at h
  simp only [List.append_assoc] at h
  have ⟨heL, hrest1⟩ := splitEq (by simp) h
  have ⟨hrL, hrest2⟩ := splitEq (by simp) hrest1
  have hf1Len : (List.ofFn (fun t => encodeUforsTreeSig (σ₁.ufors t))).flatten.length = 1920 := by
    rw [flatten_length_const (m := 128)]
    · simp [UFORS_TREES]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨t, rfl⟩; exact encodeUforsTreeSig_length _
  have hf2Len : (List.ofFn (fun t => encodeUforsTreeSig (σ₂.ufors t))).flatten.length = 1920 := by
    rw [flatten_length_const (m := 128)]
    · simp [UFORS_TREES]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨t, rfl⟩; exact encodeUforsTreeSig_length _
  have ⟨hfFlat, hlFlat⟩ := splitEq (by omega) hrest2
  have he : σ₁.e = σ₂.e := Bytes.toList_injective heL
  have hr : σ₁.r = σ₂.r := Bytes.toList_injective hrL
  have hufors : σ₁.ufors = σ₂.ufors := by
    have hfl : List.ofFn (fun t => encodeUforsTreeSig (σ₁.ufors t)) =
               List.ofFn (fun t => encodeUforsTreeSig (σ₂.ufors t)) := by
      apply flatten_injective_const (m := 128) (by simp)
      · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨t, rfl⟩; exact encodeUforsTreeSig_length _
      · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨t, rfl⟩; exact encodeUforsTreeSig_length _
      · exact hfFlat
    funext t
    have ht : encodeUforsTreeSig (σ₁.ufors t) = encodeUforsTreeSig (σ₂.ufors t) := ofFn_eq_at hfl t
    unfold encodeUforsTreeSig at ht
    have ⟨hc, ha⟩ := splitEq (by simp [flattenBytes16_length]) ht
    cases h1 : σ₁.ufors t; cases h2 : σ₂.ufors t
    rw [h1, h2] at hc ha
    dsimp only at hc ha
    rw [flattenBytes16_injective hc, flattenBytes16_injective ha]
  have hlayers : σ₁.layers = σ₂.layers := by
    have hll : List.ofFn (fun ℓ => encodeLayerSig (σ₁.layers ℓ)) =
               List.ofFn (fun ℓ => encodeLayerSig (σ₂.layers ℓ)) := by
      apply flatten_injective_const (m := 640) (by simp)
      · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨ℓ, rfl⟩; exact encodeLayerSig_length _
      · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨ℓ, rfl⟩; exact encodeLayerSig_length _
      · exact hlFlat
    funext ℓ
    have hl : encodeLayerSig (σ₁.layers ℓ) = encodeLayerSig (σ₂.layers ℓ) := ofFn_eq_at hll ℓ
    unfold encodeLayerSig at hl
    have ⟨hw, ha⟩ := splitEq (by simp [flattenBytes16_length]) hl
    cases h1 : σ₁.layers ℓ; cases h2 : σ₂.layers ℓ
    rw [h1, h2] at hw ha
    dsimp only at hw ha
    rw [flattenBytes16_injective hw, flattenBytes16_injective ha]
  cases σ₁; cases σ₂
  simp only at he hr hufors hlayers
  subst he; subst hr; subst hufors; subst hlayers
  rfl

end Blincs
