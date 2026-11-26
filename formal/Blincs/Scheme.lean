/-
  BLINCS-128-A2 Declarative Specification: Complete Scheme (`S-WOTS+Z` + `U-PORS`), Wire Format & Completeness.
  Matches SPEC.md §§4–12 verbatim over an abstract `HashOracle` (`keyed`, `derive`).
  Mechanically proves (ZERO `sorry`, ZERO custom axioms):
    1. Exact wire length (`(encodeImprint σ).length = 3292 = IMPRINT_LEN`).
    2. Exact wire injectivity (`encodeImprint σ₁ = encodeImprint σ₂ → σ₁ = σ₂`).
    3. **BLINCS-128-A2 Completeness Theorem**: every honestly generated imprint (with valid
       grinding counters `ctrFt` and `layerCtrs`) ALWAYS verifies to `True` — including exact
       Octopus root recovery and canonical trailing zero-padding!
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

/-- The all-zero 16-byte block (used for canonical trailing zero-padding of Octopus slots). -/
def zero16 : Bytes 16 :=
  fun _ => 0

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
-- Unified Chain-and-Merkle Primitive (`SPEC.md §9`, shared by U-PORS & Hypertree!)
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

/-- Unified Merkle combine function (`SPEC.md §9`, used by BOTH hypertree and U-PORS). -/
def treeCombine (H : HashOracle) (K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) :
    Nat → Nat → Bytes 16 → Bytes 16 → Bytes 16 :=
  fun level p L R =>
    shortHash H K_pub ⟨.node, layer, tree, hTree, 0, UInt16.ofNat level, UInt32.ofNat p⟩ (L.toList ++ R.toList)

def treeLeaves (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (h nChains maxSteps : Nat) :
    Fin (2 ^ h) → Bytes 16 :=
  fun leaf => chainLeafPk H K_sec K_pub layer tree hTree (UInt16.ofNat leaf.val) nChains maxSteps

def treeRoot (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (h nChains maxSteps : Nat) : Bytes 16 :=
  merkleNode (treeCombine H K_pub layer tree hTree) h 0
    (treeLeaves H K_sec K_pub layer tree hTree h nChains maxSteps)

-- ---------------------------------------------------------------------------
-- U-PORS Single Height-10 Tree & Octopus Multi-Proof (`SPEC.md §10`)
-- ---------------------------------------------------------------------------

/-- Leaf oracle `Nat → Bytes 16` for the single height-10 U-PORS tree at `leafAddr`. -/
def uporsLeafFn (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) : Nat → Bytes 16 :=
  fun leaf => chainLeafPk H K_sec K_pub uporsLayerByte leafAddr hAddr (UInt16.ofNat leaf) UPORS_N UPORS_STEPS

/-- Honest root of the single height-10 U-PORS tree at `leafAddr` (`SPEC.md §10.2`). -/
def uporsRoot (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) : Bytes 16 :=
  treeNodeAt (treeCombine H K_pub uporsLayerByte leafAddr hAddr)
    (uporsLeafFn H K_sec K_pub leafAddr hAddr) UPORS_HEIGHT 0

/-- Extract `width` bits from LSB-first little-endian 256-bit digest `D` at bit offset `off`. -/
def readBits (D : Bytes 32) (off width : Nat) : Nat :=
  (decodeLE D.toList / 2 ^ off) % 2 ^ width

/-- `D_sel = Keyed(K_pub, tweak(FEW_SELECT, ctr_ft) || D_seed)` (`SPEC.md §10.3`). -/
def fewSelectDigest (H : HashOracle) (K_pub : Bytes 32) (D_seed : Bytes 32) (ctrFt : UInt32) : Bytes 32 :=
  let twk : Tweak := ⟨.fewSelect, 0, 0, by decide, 0, 0, ctrFt⟩
  H.keyed K_pub (encodeTweak twk ++ D_seed.toList)

/-- 33-bit hypertree leaf address `bits 0..33` of `D_sel` (`SPEC.md §10.3`). -/
def extractLeafAddr (D_sel : Bytes 32) : Nat :=
  readBits D_sel 0 HYPER_BITS

theorem extractLeafAddr_lt (D_sel : Bytes 32) : extractLeafAddr D_sel < 2 ^ HYPER_BITS :=
  Nat.mod_lt _ (by decide)

theorem extractLeafAddr_lt_48 (D_sel : Bytes 32) : extractLeafAddr D_sel < 2 ^ 48 := by
  have h1 := extractLeafAddr_lt D_sel
  have h2 := params_tree_fits_tweak
  omega

/-- Insert `x` into a strictly ascending list, returning `none` if `x` is a duplicate. -/
def insertUniqueSorted (x : Nat) : List Nat → Option (List Nat)
  | [] => some [x]
  | y :: ys =>
    if x < y then some (x :: y :: ys)
    else if x = y then none
    else
      match insertUniqueSorted x ys with
      | none => none
      | some zs => some (y :: zs)

/-- Extract the sorted list of 10 strictly distinct 10-bit U-PORS leaves from `D_sel` (`SPEC.md §10.3`). -/
def extractUporsLeaves (D_sel : Bytes 32) : Option (List Nat) :=
  let rec go : (i : Nat) → List Nat → Option (List Nat)
    | 0, acc => some acc
    | i + 1, acc =>
      let idx := readBits D_sel (HYPER_BITS + i * UPORS_HEIGHT) UPORS_HEIGHT
      match insertUniqueSorted idx acc with
      | none => none
      | some acc' => go i acc'
  go UPORS_K []

/-- Declarative indexed-block rejection sampler for U-PORS codeword indices (`SPEC.md §10.3`, ZERO XOF!). -/
def extractUporsCodesFromBlock (blk : Bytes 32) : (j : Nat) → List (Fin UPORS_C)
  | 0 => []
  | j + 1 =>
    let rest := extractUporsCodesFromBlock blk j
    let draw := readBits blk (j * 9) 9
    if h : draw < UPORS_C then rest ++ [⟨draw, h⟩] else rest

def extractUporsCodesAux (H : HashOracle) (K_pub : Bytes 32) (D_sel : Bytes 32) :
    (fuel blockIdx : Nat) → List (Fin UPORS_C) → List (Fin UPORS_C)
  | 0, _, acc => acc
  | fuel + 1, blkIdx, acc =>
    if acc.length ≥ UPORS_K then acc.take UPORS_K
    else
      let twk : Tweak := ⟨.fewCode, 0, 0, by decide, 0, 0, UInt32.ofNat blkIdx⟩
      let blk := H.keyed K_pub (encodeTweak twk ++ D_sel.toList)
      let acc' := acc ++ extractUporsCodesFromBlock blk 28
      extractUporsCodesAux H K_pub D_sel fuel (blkIdx + 1) acc'

/-- Extract the `10` U-PORS codeword indices (`Fin 376`). -/
@[irreducible]
def extractUporsCodes (H : HashOracle) (K_pub : Bytes 32) (D_sel : Bytes 32) : Fin UPORS_K → Fin UPORS_C :=
  let lst := extractUporsCodesAux H K_pub D_sel 64 0 []
  fun j => lst.getD j.val ⟨0, by decide⟩

/-- Extracted Octopus sibling list for `leaves` in the height-10 U-PORS tree. -/
def uporsExtract (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (leaves : List Nat) : List Nat × List (Bytes 16) :=
  octopusExtractAux (treeCombine H K_pub uporsLayerByte leafAddr hAddr)
    (uporsLeafFn H K_sec K_pub leafAddr hAddr) 0 UPORS_HEIGHT leaves

/-- Validity predicate for a U-PORS grinding counter `ctrFt` (`SPEC.md §10.2–10.3`). -/
def ValidUporsSelection (H : HashOracle) (K_sec K_pub : Bytes 32) (D_seed : Bytes 32) (ctrFt : UInt32) : Prop :=
  let D_sel := fewSelectDigest H K_pub D_seed ctrFt
  let leafAddr := extractLeafAddr D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  ∃ leaves : List Nat,
    extractUporsLeaves D_sel = some leaves ∧
    leaves.length = UPORS_K ∧
    (uporsExtract H K_sec K_pub leafAddr hAddr48 leaves).1 = [0] ∧
    (uporsExtract H K_sec K_pub leafAddr hAddr48 leaves).2.length ≤ UPORS_M_MAX

-- ---------------------------------------------------------------------------
-- S-WOTS+Z Message Grinding & Hypertree Addressing (`SPEC.md §11`)
-- ---------------------------------------------------------------------------

/-- `h = ShortHash(K_pub, tweak(ONE_TIME_MSG, layer, tree, leaf, ctr), msg)` (`SPEC.md §11.1`). -/
def wotsMsgHash (H : HashOracle) (K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    (msg : Bytes 16) (ctr : UInt16) : Bytes 16 :=
  shortHash H K_pub ⟨.oneTimeMsg, layer, tree, hTree, leaf, 0, UInt32.ofNat ctr.toNat⟩ msg.toList

/-- 120-bit little-endian Sperner rank extracted from `h[1..16]` (`SPEC.md §11.1`). -/
def wotsRank (h : Bytes 16) : Nat :=
  decodeLE (h.toList.drop 1)

/-- Validity predicate on an `S-WOTS+Z` message hash: `h[0] = 0` (`z = 8`) and `rank < sliceCount 40 24 468`. -/
def ValidWotsHash (h : Bytes 16) : Prop :=
  h ⟨0, by decide⟩ = 0 ∧ wotsRank h < sliceCount WOTS_W WOTS_N WOTS_SUM

/-- If two valid `S-WOTS+Z` hashes have equal 120-bit rank, they are byte-for-byte EQUAL (`16 B` collision!). -/
theorem validWotsHash_eq_of_rank_eq {h₁ h₂ : Bytes 16}
    (hv₁ : ValidWotsHash h₁) (hv₂ : ValidWotsHash h₂)
    (hr : wotsRank h₁ = wotsRank h₂) : h₁ = h₂ := by
  have hlen1 : (h₁.toList.drop 1).length = 15 := by simp
  have hlen2 : (h₂.toList.drop 1).length = 15 := by simp
  have hdrop : h₁.toList.drop 1 = h₂.toList.drop 1 := by
    have hdec : ∀ (l₁ l₂ : List UInt8), l₁.length = l₂.length → decodeLE l₁ = decodeLE l₂ → l₁ = l₂ := by
      intro l₁
      induction l₁ with
      | nil => intro l₂ hl _; cases l₂ with | nil => rfl | cons _ _ => simp at hl
      | cons a as ih =>
        intro l₂ hl hdeq
        cases l₂ with
        | nil => simp at hl
        | cons b bs =>
          simp only [decodeLE] at hdeq
          have ha : a.toNat < 256 := a.toBitVec.isLt
          have hb : b.toNat < 256 := b.toBitVec.isLt
          have habNat : a.toNat = b.toNat := by omega
          have hab : a = b := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq habNat)
          have htail : decodeLE as = decodeLE bs := by omega
          rw [hab, ih bs (Nat.succ.inj hl) htail]
    exact hdec _ _ (by omega) hr
  apply Bytes.toList_injective
  cases hl1 : h₁.toList with
  | nil => have := Bytes.toList_length h₁; rw [hl1] at this; simp at this
  | cons a as =>
    cases hl2 : h₂.toList with
    | nil => have := Bytes.toList_length h₂; rw [hl2] at this; simp at this
    | cons b bs =>
      rw [hl1, hl2] at hdrop
      simp only [List.drop_succ_cons, List.drop_zero] at hdrop
      have ha0 : a = h₁ ⟨0, by decide⟩ := by
        have h0 : h₁.toList[0]'(by simp) = h₁ ⟨0, by decide⟩ := by simp [Bytes.toList]
        simpa [hl1] using h0
      have hb0 : b = h₂ ⟨0, by decide⟩ := by
        have h0 : h₂.toList[0]'(by simp) = h₂ ⟨0, by decide⟩ := by simp [Bytes.toList]
        simpa [hl2] using h0
      rw [ha0, hb0, hv₁.1, hv₂.1, hdrop]

/-- Height of hypertree layer `ℓ` indexed by `Nat` (`7` for `ℓ ≠ 3`, `12` for `ℓ = 3`). -/
def layerHeightNat (ℓ : Nat) : Nat :=
  if ℓ = 3 then TOP_HEIGHT else LOW_HEIGHT

theorem layerHeight_eq_nat (ℓ : Fin LAYERS) : layerHeight ℓ = layerHeightNat ℓ.val := rfl

/-- Hypertree addressing for heterogeneous heights `7 + 7 + 7 + 12 = 33` (`SPEC.md §11.2`). -/
def layerShift : Nat → Nat
  | 0 => 0
  | 1 => 7
  | 2 => 14
  | 3 => 21
  | _ => 33

def layerAddr (leafAddr : Nat) (ℓ : Nat) : Nat :=
  leafAddr / 2 ^ (layerShift ℓ)

def layerTree (leafAddr : Nat) (ℓ : Nat) : Nat :=
  layerAddr leafAddr ℓ / 2 ^ (layerHeightNat ℓ)

def layerLeaf (leafAddr : Nat) (ℓ : Nat) : Nat :=
  layerAddr leafAddr ℓ % 2 ^ (layerHeightNat ℓ)

theorem layerTree_lt_48 (leafAddr ℓ : Nat) (h : leafAddr < 2 ^ HYPER_BITS) :
    layerTree leafAddr ℓ < 2 ^ 48 := by
  unfold layerTree layerAddr
  have h1 : leafAddr / 2 ^ (layerShift ℓ) ≤ leafAddr := Nat.div_le_self _ _
  have h2 : (leafAddr / 2 ^ (layerShift ℓ)) / 2 ^ (layerHeightNat ℓ) ≤ leafAddr / 2 ^ (layerShift ℓ) :=
    Nat.div_le_self _ _
  have h3 := params_tree_fits_tweak
  omega

theorem layerLeaf_lt (leafAddr ℓ : Nat) : layerLeaf leafAddr ℓ < 2 ^ (layerHeightNat ℓ) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem top_layerTree_zero {leafAddr : Nat} (h : leafAddr < 2 ^ HYPER_BITS) :
    layerTree leafAddr 3 = 0 := by
  unfold layerTree layerAddr layerShift layerHeightNat
  simp only [↓reduceIte]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hpow : 2 ^ (21 + TOP_HEIGHT) = 2 ^ HYPER_BITS := rfl
  rw [hpow]
  exact Nat.div_eq_of_lt h

-- ---------------------------------------------------------------------------
-- Imprint Wire Structures (`SPEC.md §12`: Exact 3,292 Bytes)
-- ---------------------------------------------------------------------------

/-- One hypertree layer signature (`ℓ < 4`): 2-byte `S-WOTS+Z` counter + 24 chain values + `layerHeight ℓ` auth nodes. -/
structure LayerSig (ℓ : Fin LAYERS) where
  ctr  : UInt16
  wots : Fin WOTS_N → Bytes 16
  auth : Fin (layerHeightNat ℓ.val) → Bytes 16

/-- Complete structured `BLINCS-128-A2` imprint (`SPEC.md §12`: `3,292` bytes). -/
structure Imprint where
  e           : Bytes 16
  r           : Bytes 16
  ctrFt       : UInt32
  uporsChains : Fin UPORS_K → Fin UPORS_N → Bytes 16
  uporsSibs   : Fin UPORS_M_MAX → Bytes 16
  layers      : (ℓ : Fin LAYERS) → LayerSig ℓ

private def listToFinFn {α : Type} {h : Nat} (l : List α) (hl : l.length = h) : Fin h → α :=
  fun i => l[i.val]'(by omega)

private theorem ofFn_listToFinFn {α : Type} {h : Nat} (l : List α) (hl : l.length = h) :
    List.ofFn (listToFinFn l hl) = l := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp [listToFinFn]

/-- Pad a list `sibs` (of length `≤ UPORS_M_MAX`) with trailing `zero16` blocks to exact length `44`. -/
def padSibs (sibs : List (Bytes 16)) : Fin UPORS_M_MAX → Bytes 16 :=
  fun i => sibs.getD i.val zero16

theorem ofFn_padSibs {sibs : List (Bytes 16)} (hlen : sibs.length ≤ UPORS_M_MAX) :
    List.ofFn (padSibs sibs) = sibs ++ List.replicate (UPORS_M_MAX - sibs.length) zero16 := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_ofFn, padSibs, List.getD_eq_getElem?_getD]
    by_cases hi : i < sibs.length
    · rw [List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_append_left hi]
    · rw [List.getElem?_eq_none (by omega), Option.getD_none, List.getElem_append_right (by omega)]
      simp

-- ---------------------------------------------------------------------------
-- Key Schedule, Content Hashing & Complete Scheme (`SPEC.md §§6–11`)
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
  let k_sec     := H.derive CTX_SECRET_VALUES seed.toList
  let k_salt    := H.derive CTX_CONTENT_SALT  seed.toList
  let k_r       := H.derive CTX_RANDOMIZER    seed.toList
  let pk_seed   := trunc16 (H.derive CTX_PUBLIC_SEED seed.toList)
  let k_pub     := H.derive CTX_PUBLIC_HASH   pk_seed.toList
  let root      := treeRoot H k_sec k_pub 3 0 (by decide) TOP_HEIGHT WOTS_N WOTS_STEPS
  let id        := pk_seed.append root
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

private theorem append_take_left (a b : Bytes 16) :
    (a.append b).take 16 (by decide) = a := by
  funext i; simp [Bytes.take, Bytes.append, i.isLt]

private theorem append_slice_right (a b : Bytes 16) :
    (a.append b).slice 16 16 (by decide) = b := by
  funext i
  unfold Bytes.slice Bytes.append
  have hnot : ¬ (16 + i.val < 16) := by omega
  simp only [hnot, ↓reduceDIte]
  congr 1
  exact Fin.ext (by dsimp; omega)

theorem verifierKeys_match_deriveKeys (H : HashOracle) (seed : Bytes 32) :
    verifierKPub H (signetId H seed) = (deriveKeys H seed).k_pub ∧
    verifierRoot (signetId H seed) = (deriveKeys H seed).root ∧
    verifierKContent H (signetId H seed) = (deriveKeys H seed).k_content := by
  unfold signetId verifierKPub verifierRoot verifierKContent
  have htake := append_take_left (deriveKeys H seed).pk_seed (deriveKeys H seed).root
  have hslice := append_slice_right (deriveKeys H seed).pk_seed (deriveKeys H seed).root
  have hid : (deriveKeys H seed).id = (deriveKeys H seed).pk_seed.append (deriveKeys H seed).root := rfl
  have hkpub : (deriveKeys H seed).k_pub = H.derive CTX_PUBLIC_HASH (deriveKeys H seed).pk_seed.toList := rfl
  have hkcon : (deriveKeys H seed).k_content = H.derive CTX_CONTENT (deriveKeys H seed).id.toList := rfl
  rw [hid, htake, hslice]
  exact ⟨hkpub.symm, rfl, by rw [hkcon, hid]⟩

/-- Content message key `K_msg = Keyed(K_content, e || framed_ctx)` (`SPEC.md §7`). -/
def contentKey (H : HashOracle) (k_content : Bytes 32) (e : Bytes 16) (ctx : List UInt8) : Bytes 32 :=
  H.keyed k_content (e.toList ++ frameContext ctx)

/-- Single-pass salted message hash `h_msg = Keyed(K_msg, M)` (`SPEC.md §7`). -/
def contentHash (H : HashOracle) (k_content : Bytes 32) (e : Bytes 16) (ctx M : List UInt8) : Bytes 32 :=
  H.keyed (contentKey H k_content e ctx) M

/-- `short = e || h_msg` (`48` bytes, `SPEC.md §7`). -/
def contentShort (H : HashOracle) (k_content : Bytes 32) (e : Bytes 16) (ctx M : List UInt8) : List UInt8 :=
  e.toList ++ (contentHash H k_content e ctx M).toList

/-- Message seed digest `D_seed = Keyed(K_pub, tweak(MESSAGE) || R || root || short || framed_ctx)` (`SPEC.md §8`). -/
def messageDigest (H : HashOracle) (k_pub : Bytes 32) (r root : Bytes 16)
    (short : List UInt8) (ctx : List UInt8) : Bytes 32 :=
  let twk : Tweak := ⟨.message, 0, 0, by decide, 0, 0, 0⟩
  H.keyed k_pub (encodeTweak twk ++ r.toList ++ root.toList ++ short ++ frameContext ctx)

/-- Honest message signed at hypertree layer `ℓ` (`uporsRoot` at layer 0, child `treeRoot` at `ℓ > 0`). -/
def honestLayerInput (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS) : Nat → Bytes 16
  | 0 => uporsRoot H K_sec K_pub leafAddr (by have := params_tree_fits_tweak; omega)
  | ℓ + 1 => treeRoot H K_sec K_pub (UInt8.ofNat ℓ) (layerTree leafAddr ℓ)
      (layerTree_lt_48 leafAddr ℓ hAddr) (layerHeightNat ℓ) WOTS_N WOTS_STEPS

/-- Declarative U-PORS signing for a validated counter `ctrFt` (`SPEC.md §10`). -/
def uporsSignChains (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48)
    (leaves : List Nat) (codes : Fin UPORS_K → Fin UPORS_C) :
    Fin UPORS_K → Fin UPORS_N → Bytes 16 :=
  fun j =>
    let leaf := leaves.getD j.val 0
    chainSignGeneric H K_sec K_pub uporsLayerByte leafAddr hAddr (UInt16.ofNat leaf)
      (fun c => uporsDigit (codes j) c)

/-- Declarative U-PORS Octopus verification (returns `some root` iff sorted distinct 10 leaves climb cleanly
    to root `[0]` AND every trailing unused sibling slot equals `zero16`, `SPEC.md §10.2–10.3`). -/
def uporsVerify (H : HashOracle) (K_pub : Bytes 32)
    (D_sel : Bytes 32)
    (chains : Fin UPORS_K → Fin UPORS_N → Bytes 16)
    (sibs : Fin UPORS_M_MAX → Bytes 16) : Option (Bytes 16) :=
  let leafAddr := extractLeafAddr D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  let codes := extractUporsCodes H K_pub D_sel
  match extractUporsLeaves D_sel with
  | none => none
  | some leaves =>
    if hlen : leaves.length = UPORS_K then
      let leafPairs : List (Nat × Bytes 16) :=
        List.ofFn (fun j : Fin UPORS_K =>
          let leaf := leaves[j.val]'(by omega)
          let pk := chainVerifyGeneric H K_pub uporsLayerByte leafAddr hAddr48
            (UInt16.ofNat leaf) UPORS_STEPS (fun c => uporsDigit (codes j) c) (chains j)
          (leaf, pk))
      match octopusClimbAux (treeCombine H K_pub uporsLayerByte leafAddr hAddr48)
          0 UPORS_HEIGHT leafPairs (List.ofFn sibs) with
      | some ([(0, root)], remSibs) =>
        if remSibs.all (fun z => z.toList == zero16.toList) then some root else none
      | _ => none
    else none

/-- Declarative `S-WOTS+Z` hypertree signing for all 4 layers given valid counters `layerCtrs` (`SPEC.md §11`). -/
def hypertreeSign (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (layerCtrs : Fin LAYERS → UInt16) : (ℓ : Fin LAYERS) → LayerSig ℓ :=
  fun ℓ =>
    let tree := layerTree leafAddr ℓ.val
    let hTree := layerTree_lt_48 leafAddr ℓ.val hAddr
    let leaf := layerLeaf leafAddr ℓ.val
    let lByte := UInt8.ofNat ℓ.val
    let msg := honestLayerInput H K_sec K_pub leafAddr hAddr ℓ.val
    let ctr := layerCtrs ℓ
    let h := wotsMsgHash H K_pub lByte tree hTree (UInt16.ofNat leaf) msg ctr
    let rank := wotsRank h
    let wots := chainSignGeneric H K_sec K_pub lByte tree hTree (UInt16.ofNat leaf) (wotsDigit rank)
    let leaves := treeLeaves H K_sec K_pub lByte tree hTree (layerHeightNat ℓ.val) WOTS_N WOTS_STEPS
    let path := merklePath (treeCombine H K_pub lByte tree hTree) (layerHeightNat ℓ.val) 0 leaves leaf
    { ctr  := ctr
      wots := wots
      auth := listToFinFn path (merklePath_length _ _ _ _ _) }

/-- Single hypertree layer verification (`SPEC.md §11.1–11.2`): rejects unless `ValidWotsHash h`. -/
def verifyLayerStep (H : HashOracle) (K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (ℓ : Fin LAYERS) (node : Bytes 16) (sig : LayerSig ℓ) : Prop × Bytes 16 :=
  let tree := layerTree leafAddr ℓ.val
  let hTree := layerTree_lt_48 leafAddr ℓ.val hAddr
  let leaf := layerLeaf leafAddr ℓ.val
  let lByte := UInt8.ofNat ℓ.val
  let h := wotsMsgHash H K_pub lByte tree hTree (UInt16.ofNat leaf) node sig.ctr
  let rank := wotsRank h
  let leafPk := chainVerifyGeneric H K_pub lByte tree hTree (UInt16.ofNat leaf)
    WOTS_STEPS (wotsDigit rank) sig.wots
  (ValidWotsHash h, merkleReconstruct (treeCombine H K_pub lByte tree hTree) leaf leafPk (List.ofFn sig.auth))

/-- Declarative hypertree verification fold over layers `0 .. k-1` (`k ≤ 4`). -/
def hypertreeVerifyUpTo (H : HashOracle) (K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (initNode : Bytes 16) (sigs : (ℓ : Fin LAYERS) → LayerSig ℓ) : (k : Nat) → k ≤ LAYERS → Prop × Bytes 16
  | 0, _     => (True, initNode)
  | k + 1, hk =>
    let (prevOk, prevNode) := hypertreeVerifyUpTo H K_pub leafAddr hAddr initNode sigs k (by omega)
    let (stepOk, nextNode) := verifyLayerStep H K_pub leafAddr hAddr ⟨k, hk⟩ prevNode (sigs ⟨k, hk⟩)
    (prevOk ∧ stepOk, nextNode)

/-- Declarative `BLINCS-128-A2` imprinting given the ground counters `(ctrFt, layerCtrs)` (`SPEC.md §§6–12`). -/
def imprintWithCounters (H : HashOracle) (seed draw : Bytes 32) (ctx M : List UInt8)
    (ctrFt : UInt32) (layerCtrs : Fin LAYERS → UInt16) : Imprint :=
  let k := deriveKeys H seed
  let e := trunc16 (H.keyed k.k_salt draw.toList)
  let short := contentShort H k.k_content e ctx M
  let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
  let D_seed := messageDigest H k.k_pub r k.root short ctx
  let D_sel := fewSelectDigest H k.k_pub D_seed ctrFt
  let leafAddr := extractLeafAddr D_sel
  let hAddr := extractLeafAddr_lt D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  let leaves := (extractUporsLeaves D_sel).getD []
  let codes := extractUporsCodes H k.k_pub D_sel
  let sibs := (uporsExtract H k.k_sec k.k_pub leafAddr hAddr48 leaves).2
  { e           := e
    r           := r
    ctrFt       := ctrFt
    uporsChains := uporsSignChains H k.k_sec k.k_pub leafAddr hAddr48 leaves codes
    uporsSibs   := padSibs sibs
    layers      := hypertreeSign H k.k_sec k.k_pub leafAddr hAddr layerCtrs }

/-- Declarative `BLINCS-128-A2` verification (`SPEC.md §§6–12`). -/
def verify (H : HashOracle) (id : Bytes 32) (ctx M : List UInt8) (σ : Imprint) : Prop :=
  ctx.length ≤ MAX_CONTEXT_LEN ∧
  let k_pub := verifierKPub H id
  let root  := verifierRoot id
  let k_content := verifierKContent H id
  let short := contentShort H k_content σ.e ctx M
  let D_seed := messageDigest H k_pub σ.r root short ctx
  let D_sel := fewSelectDigest H k_pub D_seed σ.ctrFt
  let leafAddr := extractLeafAddr D_sel
  let hAddr := extractLeafAddr_lt D_sel
  ∃ uporsNode : Bytes 16,
    uporsVerify H k_pub D_sel σ.uporsChains σ.uporsSibs = some uporsNode ∧
    let (htOk, htRoot) := hypertreeVerifyUpTo H k_pub leafAddr hAddr uporsNode σ.layers LAYERS (Nat.le_refl _)
    htOk ∧ htRoot = root

-- ---------------------------------------------------------------------------
-- Completeness Proofs (`SPEC.md §§9–12`)
-- ---------------------------------------------------------------------------

theorem uporsVerify_honest (H : HashOracle) (K_sec K_pub : Bytes 32) (D_seed : Bytes 32) (ctrFt : UInt32)
    (hSel : ValidUporsSelection H K_sec K_pub D_seed ctrFt) :
    let D_sel := fewSelectDigest H K_pub D_seed ctrFt
    let leafAddr := extractLeafAddr D_sel
    let hAddr48 := extractLeafAddr_lt_48 D_sel
    let leaves := (extractUporsLeaves D_sel).getD []
    let codes := extractUporsCodes H K_pub D_sel
    let sibs := (uporsExtract H K_sec K_pub leafAddr hAddr48 leaves).2
    uporsVerify H K_pub D_sel
      (uporsSignChains H K_sec K_pub leafAddr hAddr48 leaves codes)
      (padSibs sibs) =
    some (uporsRoot H K_sec K_pub leafAddr hAddr48) := by
  rcases hSel with ⟨leaves, hLeaves, hLen, hTop, hSibs⟩
  dsimp only
  let D_sel := fewSelectDigest H K_pub D_seed ctrFt
  let leafAddr := extractLeafAddr D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  let codes := extractUporsCodes H K_pub D_sel
  unfold uporsVerify
  dsimp only
  rw [hLeaves]
  simp only [Option.getD_some, hLen, ↓reduceDIte]
  have hMapEq : List.ofFn (fun j : Fin UPORS_K =>
      let leaf := leaves[j.val]'(by omega)
      let pk := chainVerifyGeneric H K_pub uporsLayerByte leafAddr hAddr48
        (UInt16.ofNat leaf) UPORS_STEPS (fun c => uporsDigit (codes j) c)
        (uporsSignChains H K_sec K_pub leafAddr hAddr48 leaves codes j)
      (leaf, pk)) =
      leaves.map (fun x => (x, treeNodeAt (treeCombine H K_pub uporsLayerByte leafAddr hAddr48)
        (uporsLeafFn H K_sec K_pub leafAddr hAddr48) 0 x)) := by
    apply List.ext_getElem
    · simp [hLen]
    · intro i h1 h2
      simp only [List.length_ofFn, List.length_map] at h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, treeNodeAt, uporsSignChains, uporsLeafFn]
      have hget : leaves.getD i 0 = leaves[i]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < leaves.length)]
      rw [hget]
      congr 1
      exact chainVerifyGeneric_sign H K_sec K_pub uporsLayerByte leafAddr hAddr48
        (UInt16.ofNat (leaves[i]'(by omega))) UPORS_STEPS
        (fun c => uporsDigit (codes ⟨i, h1⟩) c)
        (fun c => uporsDigit_le_23 (codes ⟨i, h1⟩) c)
  rw [hMapEq]
  generalize hext : uporsExtract H K_sec K_pub leafAddr hAddr48 leaves = extPair at hTop hSibs ⊢
  have hext' : octopusExtractAux (treeCombine H K_pub uporsLayerByte leafAddr hAddr48)
      (uporsLeafFn H K_sec K_pub leafAddr hAddr48) 0 UPORS_HEIGHT leaves = extPair := hext
  rcases extPair with ⟨top, sibs⟩
  dsimp only at hTop hSibs ⊢
  have hclimb := octopusClimbAux_extract (treeCombine H K_pub uporsLayerByte leafAddr hAddr48)
    (uporsLeafFn H K_sec K_pub leafAddr hAddr48) 0 UPORS_HEIGHT leaves
    (List.replicate (UPORS_M_MAX - sibs.length) zero16)
  rw [hext'] at hclimb
  dsimp only at hclimb
  rw [hTop, Nat.zero_add] at hclimb
  simp only [List.map_cons, List.map_nil] at hclimb
  rw [ofFn_padSibs hSibs, hclimb]
  have hall : (List.replicate (UPORS_M_MAX - sibs.length) zero16).all (fun z => z.toList == zero16.toList) = true := by
    rw [List.all_eq_true]
    intro z hz
    rw [List.mem_replicate] at hz
    rw [hz.2]
    exact beq_self_eq_true zero16.toList
  simp only [hall, ↓reduceIte]
  rfl

theorem hypertreeVerifyUpTo_honest (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (layerCtrs : Fin LAYERS → UInt16)
    (hCtrs : ∀ ℓ : Fin LAYERS, ValidWotsHash
      (wotsMsgHash H K_pub (UInt8.ofNat ℓ.val) (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
        (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
        (honestLayerInput H K_sec K_pub leafAddr hAddr ℓ.val) (layerCtrs ℓ))) :
    ∀ (k : Nat) (hk : k ≤ LAYERS),
      let res := hypertreeVerifyUpTo H K_pub leafAddr hAddr
        (uporsRoot H K_sec K_pub leafAddr (by have := params_tree_fits_tweak; omega))
        (hypertreeSign H K_sec K_pub leafAddr hAddr layerCtrs) k hk
      res.1 ∧ res.2 = honestLayerInput H K_sec K_pub leafAddr hAddr k
  | 0, _ => ⟨trivial, rfl⟩
  | k + 1, hk => by
    have ⟨hprevOk, hprevNode⟩ := hypertreeVerifyUpTo_honest H K_sec K_pub leafAddr hAddr layerCtrs hCtrs k (by omega)
    dsimp only at hprevOk hprevNode ⊢
    unfold hypertreeVerifyUpTo
    dsimp only
    rw [hprevNode]
    unfold verifyLayerStep hypertreeSign
    dsimp only
    let ℓ : Fin LAYERS := ⟨k, hk⟩
    have hv : ValidWotsHash (wotsMsgHash H K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
        (UInt16.ofNat (layerLeaf leafAddr k))
        (honestLayerInput H K_sec K_pub leafAddr hAddr k) (layerCtrs ℓ)) := hCtrs ℓ
    refine ⟨⟨hprevOk, hv⟩, ?_⟩
    have hchain : chainVerifyGeneric H K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
        (UInt16.ofNat (layerLeaf leafAddr k)) WOTS_STEPS
        (wotsDigit (wotsRank (wotsMsgHash H K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
          (UInt16.ofNat (layerLeaf leafAddr k))
          (honestLayerInput H K_sec K_pub leafAddr hAddr k) (layerCtrs ℓ))))
        (chainSignGeneric H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
          (UInt16.ofNat (layerLeaf leafAddr k))
          (wotsDigit (wotsRank (wotsMsgHash H K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
            (UInt16.ofNat (layerLeaf leafAddr k))
            (honestLayerInput H K_sec K_pub leafAddr hAddr k) (layerCtrs ℓ))))) =
        chainLeafPk H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
          (UInt16.ofNat (layerLeaf leafAddr k)) WOTS_N WOTS_STEPS :=
      chainVerifyGeneric_sign H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
        (UInt16.ofNat (layerLeaf leafAddr k)) WOTS_STEPS _ (fun c => wotsDigit_le_39 hv.2 c)
    rw [hchain, ofFn_listToFinFn]
    unfold honestLayerInput treeRoot
    exact merkleReconstruct_correct
      (treeCombine H K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr))
      (layerHeightNat k)
      (treeLeaves H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
        (layerHeightNat k) WOTS_N WOTS_STEPS)
      (layerLeaf leafAddr k) (layerLeaf_lt leafAddr k)

private theorem top_root_eq (H : HashOracle) (K_sec K_pub : Bytes 32)
    (t : Nat) (ht : t < 2 ^ 48) (h0 : t = 0) :
    treeRoot H K_sec K_pub 3 t ht (layerHeightNat 3) WOTS_N WOTS_STEPS =
    treeRoot H K_sec K_pub 3 0 (by decide) TOP_HEIGHT WOTS_N WOTS_STEPS := by
  subst h0
  have hh : layerHeightNat 3 = TOP_HEIGHT := rfl
  simp only [hh]

/--
  **BLINCS-128-A2 Completeness Theorem:**
  For ANY hash oracle `H`, ANY 32-byte `seed`, ANY 32-byte `draw`, ANY valid context `ctx`
  (`ctx.length ≤ 255`), ANY message `M`, and ANY valid grinding counters `(ctrFt, layerCtrs)`,
  the imprint produced by `imprintWithCounters H seed draw ctx M ctrFt layerCtrs`
  ALWAYS verifies against `signetId H seed`!
-/
theorem blincs_completeness (H : HashOracle) (seed draw : Bytes 32) (ctx M : List UInt8)
    (hCtx : ctx.length ≤ MAX_CONTEXT_LEN)
    (ctrFt : UInt32) (layerCtrs : Fin LAYERS → UInt16)
    (hSel : let k := deriveKeys H seed
            let e := trunc16 (H.keyed k.k_salt draw.toList)
            let short := contentShort H k.k_content e ctx M
            let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
            let D_seed := messageDigest H k.k_pub r k.root short ctx
            ValidUporsSelection H k.k_sec k.k_pub D_seed ctrFt)
    (hCtrs : let k := deriveKeys H seed
             let e := trunc16 (H.keyed k.k_salt draw.toList)
             let short := contentShort H k.k_content e ctx M
             let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
             let D_seed := messageDigest H k.k_pub r k.root short ctx
             let D_sel := fewSelectDigest H k.k_pub D_seed ctrFt
             let leafAddr := extractLeafAddr D_sel
             let hAddr := extractLeafAddr_lt D_sel
             ∀ ℓ : Fin LAYERS, ValidWotsHash
               (wotsMsgHash H k.k_pub (UInt8.ofNat ℓ.val) (layerTree leafAddr ℓ.val)
                 (layerTree_lt_48 leafAddr ℓ.val hAddr)
                 (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
                 (honestLayerInput H k.k_sec k.k_pub leafAddr hAddr ℓ.val) (layerCtrs ℓ))) :
    verify H (signetId H seed) ctx M (imprintWithCounters H seed draw ctx M ctrFt layerCtrs) := by
  refine ⟨hCtx, ?_⟩
  rcases verifierKeys_match_deriveKeys H seed with ⟨hkpub, hroot, hkcontent⟩
  dsimp only
  rw [hkpub, hroot, hkcontent]
  unfold imprintWithCounters
  dsimp only
  let k := deriveKeys H seed
  let e := trunc16 (H.keyed k.k_salt draw.toList)
  let short := contentShort H k.k_content e ctx M
  let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
  let D_seed := messageDigest H k.k_pub r k.root short ctx
  let D_sel := fewSelectDigest H k.k_pub D_seed ctrFt
  let leafAddr := extractLeafAddr D_sel
  let hAddr := extractLeafAddr_lt D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  refine ⟨uporsRoot H k.k_sec k.k_pub leafAddr hAddr48, ?_, ?_⟩
  · exact uporsVerify_honest H k.k_sec k.k_pub D_seed ctrFt hSel
  · have ⟨htOk, htRoot⟩ := hypertreeVerifyUpTo_honest H k.k_sec k.k_pub leafAddr hAddr layerCtrs hCtrs LAYERS (Nat.le_refl _)
    refine ⟨htOk, ?_⟩
    rw [htRoot]
    have h4 : honestLayerInput H k.k_sec k.k_pub leafAddr hAddr LAYERS =
        treeRoot H k.k_sec k.k_pub 3 (layerTree leafAddr 3) (layerTree_lt_48 leafAddr 3 hAddr)
          (layerHeightNat 3) WOTS_N WOTS_STEPS := rfl
    have hkroot : k.root = treeRoot H k.k_sec k.k_pub 3 0 (by decide) TOP_HEIGHT WOTS_N WOTS_STEPS := rfl
    rw [h4, hkroot]
    exact top_root_eq H k.k_sec k.k_pub (layerTree leafAddr 3) (layerTree_lt_48 leafAddr 3 hAddr) (top_layerTree_zero hAddr)

-- ---------------------------------------------------------------------------
-- Wire Serialization (`SPEC.md §12`: Exact 3,292 Bytes & Bijection)
-- ---------------------------------------------------------------------------

def encodeLayerSig {ℓ : Fin LAYERS} (s : LayerSig ℓ) : List UInt8 :=
  encodeLE s.ctr.toNat 2 ++ flattenBytes16 s.wots ++ flattenBytes16 s.auth

theorem encodeLayerSig_length {ℓ : Fin LAYERS} (s : LayerSig ℓ) :
    (encodeLayerSig s).length = 2 + WOTS_N * 16 + layerHeightNat ℓ.val * 16 := by
  unfold encodeLayerSig
  rw [List.length_append, List.length_append, encodeLE_length, flattenBytes16_length, flattenBytes16_length]

/-- Canonical wire serialization of a `BLINCS-128-A2` imprint (`SPEC.md §12`). -/
def encodeImprint (σ : Imprint) : List UInt8 :=
  σ.e.toList
    ++ σ.r.toList
    ++ encodeLE σ.ctrFt.toNat 4
    ++ (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten
    ++ flattenBytes16 σ.uporsSibs
    ++ encodeLayerSig (σ.layers ⟨0, by decide⟩)
    ++ encodeLayerSig (σ.layers ⟨1, by decide⟩)
    ++ encodeLayerSig (σ.layers ⟨2, by decide⟩)
    ++ encodeLayerSig (σ.layers ⟨3, by decide⟩)

/-- **Wire Length Theorem:** every encoded `BLINCS-128-A2` imprint is EXACTLY `3,292` bytes. -/
theorem encodeImprint_length (σ : Imprint) : (encodeImprint σ).length = IMPRINT_LEN := by
  unfold encodeImprint
  have hchains : (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length = 480 := by
    rw [flatten_length_const (m := 48)]
    · simp [UPORS_K]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨j, rfl⟩
      rw [flattenBytes16_length]; rfl
  simp only [List.length_append, Bytes.toList_length, encodeLE_length, hchains,
    flattenBytes16_length, encodeLayerSig_length]
  rfl

private theorem ofFn_eq_at {n : Nat} {α : Type} {f g : Fin n → α}
    (h : List.ofFn f = List.ofFn g) (i : Fin n) : f i = g i := by
  have h1 := congrArg (fun l => l[i.val]?) h
  simp only [List.getElem?_eq_getElem (show i.val < (List.ofFn f).length by simp),
             List.getElem?_eq_getElem (show i.val < (List.ofFn g).length by simp),
             List.getElem_ofFn] at h1
  exact Option.some.inj h1

private theorem encodeLayerSig_injective {ℓ : Fin LAYERS} {s₁ s₂ : LayerSig ℓ}
    (h : encodeLayerSig s₁ = encodeLayerSig s₂) : s₁ = s₂ := by
  unfold encodeLayerSig at h
  simp only [List.append_assoc] at h
  have ⟨hctrL, hrest⟩ := append_eq_of_length_eq (by simp [encodeLE_length]) h
  have ⟨hwotsL, hauthL⟩ := append_eq_of_length_eq (by simp [flattenBytes16_length]) hrest
  have hctrNat : s₁.ctr.toNat = s₂.ctr.toNat :=
    encodeLE_injective (m := 2) (by have := s₁.ctr.toNat_lt; omega) (by have := s₂.ctr.toNat_lt; omega) hctrL
  have hctr : s₁.ctr = s₂.ctr := UInt16.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hctrNat)
  have hwots : s₁.wots = s₂.wots := flattenBytes16_injective hwotsL
  have hauth : s₁.auth = s₂.auth := flattenBytes16_injective hauthL
  cases s₁; cases s₂
  simp only at hctr hwots hauth
  subst hctr; subst hwots; subst hauth
  rfl

/-- **Wire Injectivity Theorem:** distinct structured `BLINCS-128-A2` imprints ALWAYS encode to distinct `3,292`-byte strings. -/
theorem encodeImprint_injective {σ₁ σ₂ : Imprint} (h : encodeImprint σ₁ = encodeImprint σ₂) : σ₁ = σ₂ := by
  unfold encodeImprint at h
  simp only [List.append_assoc] at h
  have ⟨heL, h1⟩ := append_eq_of_length_eq (by simp) h
  have ⟨hrL, h2⟩ := append_eq_of_length_eq (by simp) h1
  have ⟨hctrL, h3⟩ := append_eq_of_length_eq (by simp [encodeLE_length]) h2
  have hcLen1 : (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ₁.uporsChains j))).flatten.length = 480 := by
    rw [flatten_length_const (m := 48)]; · simp [UPORS_K]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨j, rfl⟩; rw [flattenBytes16_length]; rfl
  have hcLen2 : (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ₂.uporsChains j))).flatten.length = 480 := by
    rw [flatten_length_const (m := 48)]; · simp [UPORS_K]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨j, rfl⟩; rw [flattenBytes16_length]; rfl
  have ⟨hchFlat, h4⟩ := append_eq_of_length_eq (by omega) h3
  have ⟨hsibsL, h5⟩ := append_eq_of_length_eq (by simp [flattenBytes16_length]) h4
  have ⟨hl0, h6⟩ := append_eq_of_length_eq (by simp [encodeLayerSig_length]) h5
  have ⟨hl1, h7⟩ := append_eq_of_length_eq (by simp [encodeLayerSig_length]) h6
  have ⟨hl2, hl3⟩ := append_eq_of_length_eq (by simp [encodeLayerSig_length]) h7
  have he : σ₁.e = σ₂.e := Bytes.toList_injective heL
  have hr : σ₁.r = σ₂.r := Bytes.toList_injective hrL
  have hctrNat : σ₁.ctrFt.toNat = σ₂.ctrFt.toNat :=
    encodeLE_injective (m := 4) (by have := σ₁.ctrFt.toNat_lt; omega) (by have := σ₂.ctrFt.toNat_lt; omega) hctrL
  have hctrFt : σ₁.ctrFt = σ₂.ctrFt := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hctrNat)
  have hchains : σ₁.uporsChains = σ₂.uporsChains := by
    have hfl : List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ₁.uporsChains j)) =
               List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ₂.uporsChains j)) := by
      apply flatten_injective_const (m := 48) (by simp)
      · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨j, rfl⟩; rw [flattenBytes16_length]; rfl
      · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨j, rfl⟩; rw [flattenBytes16_length]; rfl
      · exact hchFlat
    funext j
    exact flattenBytes16_injective (ofFn_eq_at hfl j)
  have hsibs : σ₁.uporsSibs = σ₂.uporsSibs := flattenBytes16_injective hsibsL
  have hlayers : σ₁.layers = σ₂.layers := by
    funext ℓ
    rcases ℓ with ⟨v, hv⟩
    match v with
    | 0 => exact encodeLayerSig_injective hl0
    | 1 => exact encodeLayerSig_injective hl1
    | 2 => exact encodeLayerSig_injective hl2
    | 3 => exact encodeLayerSig_injective hl3
    | n + 4 => unfold LAYERS at hv; omega
  cases σ₁; cases σ₂
  simp only at he hr hctrFt hchains hsibs hlayers
  subst he; subst hr; subst hctrFt; subst hchains; subst hsibs; subst hlayers
  rfl

end Blincs
