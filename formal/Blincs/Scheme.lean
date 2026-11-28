/-
  BLINCS-48-X Declarative Specification: Complete Scheme (`WOTS+C` + `U-PORS`), Wire Format & Completeness.
  Matches SPEC.md §§4–11 byte-for-byte over an abstract `HashOracle` (`keyed`, `derive`):
    - `CHAIN_SECRET`: `tweak(1, layer, tree, 0, 0, leaf * n_chains + c)`, empty data (`SPEC.md §§5, 9`)
    - `ONE_TIME_MSG`: `tweak(5, layer, tree, leaf, 0, 0)`, data `child_root || u32_le(ctr_l)` (`SPEC.md §§5, 11.1`)
    - `FEW_SELECT`:   `tweak(7, 0x80, 0, 0, 0, 0)`, data `D_seed || u32_le(ctr_ft)` (`SPEC.md §§5, 8.1`)
    - `FEW_CODE`:     `tweak(8, 0x80, 0, 0, block_idx, 0)`, data `H_sel` (`48 B`, chained from `FEW_SELECT`, `SPEC.md §§5, 8.2`),
                      returning `Option` (fails closed as `none` on block-index exhaustion, never defaulting to `0`)
    - `U-PORS` selection: up to 18 consecutive 11-bit draws from bits `0..198` collecting first 9 distinct leaves
      sorted ascending, plus 48-bit `leaf_addr` from bits `198..246` (`SPEC.md §8.1`).
  Mechanically proves (ZERO `sorry`, ZERO custom axioms):
    1. Exact wire length (`encodeImprint_length`: `3,990` bytes), injectivity (`encodeImprint_injective`),
       and parser round-trip (`decodeImprint_encodeImprint`) + wrong-length rejection (`decodeImprint_bad_len`).
    2. Exact 128-bit `WOTS+C` bijection (`validWotsHash_eq_of_digits_eq`, `encodeWotsCDigits_valid`,
       `wotsCDigit_encodeWotsCDigits`, `encodeWotsCDigits_wotsCDigit`) and strict antichain dominance
       (`wotsC_dominance`: any two distinct valid `WOTS+C` hashes have `∃ c, wotsCDigit h₁ c < wotsCDigit h₂ c`).
    3. Conditional completeness (`blincs_completeness`) and normative bounded minimum-counter signer
       soundness (`signNormative_sound`: fails closed on exhaustion, verifies cleanly, minimal counters).
-/
import Blincs.Params
import Blincs.Tweaks
import Blincs.Wots
import Blincs.Merkle

namespace Blincs

/-- Abstract BLAKE3 hash oracle (`SPEC.md §2`): `keyed` (`KEYED_HASH`) and `derive` (`DERIVE_KEY`). -/
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
-- Unified Chain-and-Merkle Primitive (`SPEC.md §§5, 9`)
-- ---------------------------------------------------------------------------

/-- `CHAIN_SECRET` (`SPEC.md §5`): `leaf = 0`, `a = 0`, `b = leaf * nChains + c`, empty data. -/
def chainStart (H : HashOracle) (K_sec : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    (nChains c : Nat) : Bytes 16 :=
  shortHash H K_sec ⟨.chainSecret, layer, tree, hTree, 0, 0, UInt32.ofNat (leaf.toNat * nChains + c)⟩ []

def chainStepFn (H : HashOracle) (K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16) (c : Nat) :
    Nat → Bytes 16 → Bytes 16 :=
  fun s x => shortHash H K_pub ⟨.chain, layer, tree, hTree, leaf, UInt16.ofNat c, UInt32.ofNat s⟩ x.toList

def chainEndpoint (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    (nChains maxSteps c : Nat) : Bytes 16 :=
  chainIter (chainStepFn H K_pub layer tree hTree leaf c) 0 maxSteps
    (chainStart H K_sec layer tree hTree leaf nChains c)

def chainLeafPk (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    (nChains maxSteps : Nat) : Bytes 16 :=
  shortHash H K_pub ⟨.oneTimeKey, layer, tree, hTree, leaf, 0, 0⟩
    (flattenBytes16 (fun c : Fin nChains => chainEndpoint H K_sec K_pub layer tree hTree leaf nChains maxSteps c.val))

def chainSignGeneric (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    {nChains : Nat} (digits : Fin nChains → Nat) : Fin nChains → Bytes 16 :=
  fun c =>
    chainIter (chainStepFn H K_pub layer tree hTree leaf c.val) 0 (digits c)
      (chainStart H K_sec layer tree hTree leaf nChains c.val)

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
    (chainStart H K_sec layer tree hTree leaf nChains c.val) (hDigits c)

/-- Unified Merkle combine function (`SPEC.md §§5, 9`, used by BOTH hypertree and U-PORS). -/
def treeCombine (H : HashOracle) (K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) :
    Nat → Nat → Bytes 16 → Bytes 16 → Bytes 16 :=
  fun level p L R =>
    shortHash H K_pub ⟨.node, layer, tree, hTree, 0, UInt16.ofNat level, UInt32.ofNat p⟩ (L.toList ++ R.toList)

def treeLeafFn (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (nChains maxSteps : Nat) :
    Nat → Bytes 16 :=
  fun leaf => chainLeafPk H K_sec K_pub layer tree hTree (UInt16.ofNat leaf) nChains maxSteps

def treeLeaves (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (h nChains maxSteps : Nat) :
    Fin (2 ^ h) → Bytes 16 :=
  fun leaf => treeLeafFn H K_sec K_pub layer tree hTree nChains maxSteps leaf.val

def treeRoot (H : HashOracle) (K_sec K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (h nChains maxSteps : Nat) : Bytes 16 :=
  merkleNode (treeCombine H K_pub layer tree hTree) h 0
    (treeLeaves H K_sec K_pub layer tree hTree h nChains maxSteps)

-- ---------------------------------------------------------------------------
-- U-PORS Selection, Codeword Extraction & Octopus Multi-Proof (`SPEC.md §§8, 10`)
-- ---------------------------------------------------------------------------

/-- Leaf oracle `Nat → Bytes 16` for the single height-11 U-PORS tree at `leafAddr`. -/
def uporsLeafFn (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) : Nat → Bytes 16 :=
  treeLeafFn H K_sec K_pub uporsLayerByte leafAddr hAddr UPORS_N UPORS_STEPS

/-- Honest root of the single height-11 U-PORS tree at `leafAddr` (`SPEC.md §10.2`). -/
def uporsRoot (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) : Bytes 16 :=
  treeNodeAt (treeCombine H K_pub uporsLayerByte leafAddr hAddr)
    (uporsLeafFn H K_sec K_pub leafAddr hAddr) UPORS_HEIGHT 0

/-- Extract `width` bits from LSB-first little-endian 256-bit digest `D` at bit offset `off`. -/
def readBits (D : Bytes 32) (off width : Nat) : Nat :=
  (decodeLE D.toList / 2 ^ off) % 2 ^ width

/-- `FEW_SELECT` (`SPEC.md §§5, 8.1`): `layer = 0x80`, data = `D_seed || u32_le(ctr_ft)`. -/
def fewSelectDigest (H : HashOracle) (K_pub : Bytes 32) (D_seed : Bytes 32) (ctrFt : UInt32) : Bytes 32 :=
  let twk : Tweak := ⟨.fewSelect, uporsLayerByte, 0, by decide, 0, 0, 0⟩
  H.keyed K_pub (encodeTweak twk ++ D_seed.toList ++ encodeLE ctrFt.toNat 4)

/-- 48-bit hypertree leaf address `bits 198..246` of `D_sel` (`SPEC.md §8.1`). -/
def extractLeafAddr (D_sel : Bytes 32) : Nat :=
  readBits D_sel (UPORS_SELECT_MAX_DRAWS * UPORS_HEIGHT) HYPER_BITS

theorem extractLeafAddr_lt (D_sel : Bytes 32) : extractLeafAddr D_sel < 2 ^ HYPER_BITS :=
  Nat.mod_lt _ (by decide)

theorem extractLeafAddr_lt_48 (D_sel : Bytes 32) : extractLeafAddr D_sel < 2 ^ 48 := by
  have h1 := extractLeafAddr_lt D_sel
  have h2 := params_tree_fits_tweak
  omega

/-- Insert `x` into a strictly ascending list if not already present (idempotent on duplicates). -/
def insertSortedDedup (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys
    else y :: insertSortedDedup x ys

/-- Strictly ascending predicate (`∀` adjacent elements strictly increase, implying `Nodup`). -/
def StrictlySorted : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x < y ∧ StrictlySorted (y :: rest)

private theorem strictlySorted_head_lt_all {x : Nat} {ys : List Nat}
    (hs : StrictlySorted (x :: ys)) : ∀ z ∈ ys, x < z := by
  induction ys generalizing x with
  | nil => intro _ hz; cases hz
  | cons y rest ih =>
    intro z hz
    simp only [StrictlySorted] at hs
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hmem
    · exact hs.1
    · have h2 := ih hs.2 z hmem
      omega

theorem strictlySorted_nodup : ∀ {l : List Nat}, StrictlySorted l → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => by simp
  | x :: y :: rest, hs => by
    rw [List.nodup_cons]
    refine ⟨?_, strictlySorted_nodup hs.2⟩
    intro hmem
    have hlt := strictlySorted_head_lt_all hs x hmem
    omega

private theorem insertSortedDedup_strictlySorted (x : Nat) :
    ∀ {l : List Nat}, StrictlySorted l → StrictlySorted (insertSortedDedup x l)
  | [], _ => trivial
  | [y], _ => by
    unfold insertSortedDedup
    by_cases h1 : x < y
    · rw [ite_eq_left h1]; exact ⟨h1, trivial⟩
    · rw [ite_eq_right h1]
      by_cases h2 : x = y
      · rw [ite_eq_left h2]; trivial
      · rw [ite_eq_right h2]; exact ⟨by omega, trivial⟩
  | y :: z :: rest, hs => by
    unfold insertSortedDedup
    by_cases h1 : x < y
    · rw [ite_eq_left h1]; exact ⟨h1, hs⟩
    · rw [ite_eq_right h1]
      by_cases h2 : x = y
      · rw [ite_eq_left h2]; exact hs
      · rw [ite_eq_right h2]
        have hrec := insertSortedDedup_strictlySorted x hs.2
        have hlt_y : y < x := by omega
        -- Check head of `insertSortedDedup x (z :: rest)` is `min x z > y`
        unfold insertSortedDedup at hrec ⊢
        by_cases h3 : x < z
        · rw [ite_eq_left h3] at hrec ⊢; exact ⟨hlt_y, hrec⟩
        · rw [ite_eq_right h3] at hrec ⊢
          by_cases h4 : x = z
          · rw [ite_eq_left h4] at hrec ⊢; exact ⟨hs.1, hrec⟩
          · rw [ite_eq_right h4] at hrec ⊢; exact ⟨hs.1, hrec⟩

/-- Scan up to `UPORS_SELECT_MAX_DRAWS` (18) consecutive 11-bit draws from bits `0..198` of `D_sel`,
    collecting the first `UPORS_K` (9) distinct leaves sorted strictly ascending (`SPEC.md §8.1`). -/
def extractUporsLeavesAux (D_sel : Bytes 32) : (i rem : Nat) → List Nat → Option (List Nat)
  | _, 0, acc => if acc.length = UPORS_K then some acc else none
  | i, rem + 1, acc =>
    if acc.length = UPORS_K then some acc
    else
      let idx := readBits D_sel (i * UPORS_HEIGHT) UPORS_HEIGHT
      extractUporsLeavesAux D_sel (i + 1) rem (insertSortedDedup idx acc)

def extractUporsLeaves (D_sel : Bytes 32) : Option (List Nat) :=
  extractUporsLeavesAux D_sel 0 UPORS_SELECT_MAX_DRAWS []

private theorem extractUporsLeavesAux_spec (D_sel : Bytes 32) :
    ∀ (i rem : Nat) (acc leaves : List Nat),
      StrictlySorted acc →
      extractUporsLeavesAux D_sel i rem acc = some leaves →
      leaves.length = UPORS_K ∧ StrictlySorted leaves
  | _, 0, acc, leaves, hs, heq => by
    unfold extractUporsLeavesAux at heq
    by_cases h : acc.length = UPORS_K
    · rw [ite_eq_left h] at heq; cases heq; exact ⟨h, hs⟩
    · rw [ite_eq_right h] at heq; cases heq
  | i, rem + 1, acc, leaves, hs, heq => by
    unfold extractUporsLeavesAux at heq
    by_cases h : acc.length = UPORS_K
    · rw [ite_eq_left h] at heq; cases heq; exact ⟨h, hs⟩
    · rw [ite_eq_right h] at heq
      exact extractUporsLeavesAux_spec D_sel (i + 1) rem _ leaves (insertSortedDedup_strictlySorted _ hs) heq

theorem extractUporsLeaves_spec {D_sel : Bytes 32} {leaves : List Nat}
    (h : extractUporsLeaves D_sel = some leaves) :
    leaves.length = UPORS_K ∧ leaves.Nodup := by
  have ⟨hlen, hsort⟩ := extractUporsLeavesAux_spec D_sel 0 UPORS_SELECT_MAX_DRAWS [] leaves trivial h
  exact ⟨hlen, strictlySorted_nodup hsort⟩

/-- Declarative indexed-block rejection sampler for U-PORS codeword indices (`SPEC.md §8.2`, ZERO XOF):
    extracts `28` consecutive 9-bit draws from one 32-byte `FEW_CODE` block, accepting `< 376`. -/
def extractUporsCodesFromBlock (blk : Bytes 32) : (j : Nat) → List (Fin UPORS_C)
  | 0 => []
  | j + 1 =>
    let rest := extractUporsCodesFromBlock blk j
    let draw := readBits blk (j * 9) 9
    if h : draw < UPORS_C then rest ++ [⟨draw, h⟩] else rest

/-- `FEW_CODE` block hash (`SPEC.md §§5, 8.2`):
    `layer = 0x80`, `a = block_idx`, `b = 0`, data = `H_sel` (`48 B` total, chained from `FEW_SELECT`). -/
def fewCodeBlock (H : HashOracle) (K_pub : Bytes 32) (D_sel : Bytes 32) (blkIdx : Nat) : Bytes 32 :=
  let twk : Tweak := ⟨.fewCode, uporsLayerByte, 0, by decide, 0, UInt16.ofNat blkIdx, 0⟩
  H.keyed K_pub (encodeTweak twk ++ D_sel.toList)

/-- Bounded-block `FEW_CODE` extraction returning `Option (List (Fin UPORS_C))`:
    scans up to `fuel` indexed blocks (`block_idx = 0, 1, ...`) chained from `D_sel` and returns `none`
    (fail-closed) if fewer than `UPORS_K` (9) draws `< 376` are produced — NEVER defaulting to `0`! -/
def extractUporsCodesAux (H : HashOracle) (K_pub : Bytes 32) (D_sel : Bytes 32) :
    (fuel blockIdx : Nat) → List (Fin UPORS_C) → Option (List (Fin UPORS_C))
  | 0, _, acc =>
    if acc.length ≥ UPORS_K then some (acc.take UPORS_K) else none
  | fuel + 1, blkIdx, acc =>
    if acc.length ≥ UPORS_K then some (acc.take UPORS_K)
    else
      let blk := fewCodeBlock H K_pub D_sel blkIdx
      let acc' := acc ++ extractUporsCodesFromBlock blk 28
      extractUporsCodesAux H K_pub D_sel fuel (blkIdx + 1) acc'

private theorem extractUporsCodesAux_length (H : HashOracle) (K_pub : Bytes 32) (D_sel : Bytes 32) :
    ∀ (fuel blkIdx : Nat) (acc res : List (Fin UPORS_C)),
      extractUporsCodesAux H K_pub D_sel fuel blkIdx acc = some res →
      res.length = UPORS_K
  | 0, _, acc, res, heq => by
    unfold extractUporsCodesAux at heq
    by_cases h : acc.length ≥ UPORS_K
    · rw [ite_eq_left h] at heq; cases heq; simp; omega
    · rw [ite_eq_right h] at heq; cases heq
  | fuel + 1, blkIdx, acc, res, heq => by
    unfold extractUporsCodesAux at heq
    by_cases h : acc.length ≥ UPORS_K
    · rw [ite_eq_left h] at heq; cases heq; simp; omega
    · rw [ite_eq_right h] at heq
      exact extractUporsCodesAux_length H K_pub D_sel fuel (blkIdx + 1) _ res heq

/-- Extract the `9` U-PORS codeword indices (`Fin 376`) chained from `D_sel` over `u16` block index
    space (`fuel = 65536`), failing closed (`none`) if `u16` block indices exhaust (`SPEC.md §8.2`). -/
@[irreducible]
def extractUporsCodes (H : HashOracle) (K_pub : Bytes 32) (D_sel : Bytes 32) :
    Option (Fin UPORS_K → Fin UPORS_C) :=
  match h : extractUporsCodesAux H K_pub D_sel 65536 0 [] with
  | none => none
  | some lst =>
    have hlen : lst.length = UPORS_K :=
      extractUporsCodesAux_length H K_pub D_sel 65536 0 [] lst h
    some (fun j => lst[j.val]'(by omega))

/-- Extracted Octopus sibling list for `leaves` in the height-11 U-PORS tree (`SPEC.md §10.2`). -/
def uporsExtract (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (leaves : List Nat) : List Nat × List (Bytes 16) :=
  octopusExtractAux (treeCombine H K_pub uporsLayerByte leafAddr hAddr)
    (uporsLeafFn H K_sec K_pub leafAddr hAddr) 0 UPORS_HEIGHT leaves

/-- Pure selection validity predicate on `D_sel` (`SPEC.md §8.1`, independent of `FEW_CODE`):
    extracts `9` distinct leaves whose Octopus proof climbs to `[0]` with `exactOctopusSibs ≤ 45`. -/
def ValidUporsSelection (H : HashOracle) (K_sec K_pub : Bytes 32) (D_seed : Bytes 32) (ctrFt : UInt32) : Prop :=
  let D_sel := fewSelectDigest H K_pub D_seed ctrFt
  let leafAddr := extractLeafAddr D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  ∃ leaves : List Nat,
    extractUporsLeaves D_sel = some leaves ∧
    leaves.length = UPORS_K ∧
    (uporsExtract H K_sec K_pub leafAddr hAddr48 leaves).1 = [0] ∧
    exactOctopusSibs UPORS_HEIGHT leaves ≤ UPORS_M_MAX

-- ---------------------------------------------------------------------------
-- WOTS+C Message Grinding, Bijection & Hypertree Addressing (`SPEC.md §§5, 11`)
-- ---------------------------------------------------------------------------

/-- `ONE_TIME_MSG` (`SPEC.md §§5, 11.1`): fixed address tweak `(layer, tree, leaf, 0, 0)`,
    appended data = `msg || u32_le(ctr.val)` (`ctr : U24` zero-extended to 4-byte LE). -/
def wotsMsgHash (H : HashOracle) (K_pub : Bytes 32)
    (layer : UInt8) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
    (msg : Bytes 16) (ctr : U24) : Bytes 16 :=
  shortHash H K_pub ⟨.oneTimeMsg, layer, tree, hTree, leaf, 0, 0⟩
    (msg.toList ++ encodeLE ctr.val 4)

/-- Direct 6-bit `WOTS+C` digit `c ∈ Fin 21` extracted from `H_l[0..16]` (`SPEC.md §11.1`). -/
def wotsCDigit (h : Bytes 16) (c : Fin WOTS_N) : Nat :=
  (decodeLE h.toList / 2 ^ (WOTS_Z + 6 * c.val)) % 64

private theorem decodeLE_lt_pow : ∀ (bs : List UInt8), decodeLE bs < 256 ^ bs.length
  | [] => by simp [decodeLE]
  | b :: bs => by
    simp only [decodeLE, List.length_cons, Nat.pow_succ]
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have ih := decodeLE_lt_pow bs
    have hmul : 256 * decodeLE bs + b.toNat < 256 * (decodeLE bs + 1) := by omega
    have hpow : 256 * (decodeLE bs + 1) ≤ 256 * 256 ^ bs.length := Nat.mul_le_mul_left 256 ih
    rw [Nat.mul_comm (256 ^ bs.length) 256]
    omega

private theorem eq_of_base64_digits :
    ∀ (k a b : Nat), a < 64 ^ k → b < 64 ^ k →
      (∀ i : Fin k, (a / 64 ^ i.val) % 64 = (b / 64 ^ i.val) % 64) → a = b
  | 0, a, b, ha, hb, _ => by simp at ha hb; omega
  | k + 1, a, b, ha, hb, hdig => by
    have hmod : a % 64 = b % 64 := by
      have h0 := hdig ⟨0, by omega⟩
      simpa using h0
    have ha' : a / 64 < 64 ^ k := by
      have hpow : 64 ^ (k + 1) = 64 * 64 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow] at ha
      exact Nat.div_lt_of_lt_mul ha
    have hb' : b / 64 < 64 ^ k := by
      have hpow : 64 ^ (k + 1) = 64 * 64 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow] at hb
      exact Nat.div_lt_of_lt_mul hb
    have hdiv : a / 64 = b / 64 := by
      apply eq_of_base64_digits k (a / 64) (b / 64) ha' hb'
      intro i
      have hi := hdig ⟨i.val + 1, by omega⟩
      have hpow : 64 ^ (i.val + 1) = 64 * 64 ^ i.val := by rw [Nat.pow_succ, Nat.mul_comm]
      simpa [hpow, Nat.div_div_eq_div_mul] using hi
    have hda := Nat.div_add_mod a 64
    have hdb := Nat.div_add_mod b 64
    omega

/-- Validity predicate on a `WOTS+C` message hash (`SPEC.md §11.1`):
    2 LSB-first zero bits, all 21 packed 6-bit digits `< 60`, and constant sum `679`. -/
def ValidWotsHash (h : Bytes 16) : Prop :=
  decodeLE h.toList % 2 ^ WOTS_Z = 0 ∧
  (∀ c : Fin WOTS_N, wotsCDigit h c < WOTS_W) ∧
  finSum WOTS_N (wotsCDigit h) = WOTS_SUM

theorem wotsCDigit_le_steps {h : Bytes 16} (hv : ValidWotsHash h) (c : Fin WOTS_N) :
    wotsCDigit h c ≤ WOTS_STEPS := by
  have hlt := hv.2.1 c
  unfold WOTS_STEPS WOTS_W at *
  omega

/-- If two valid `WOTS+C` hashes produce identical 21-digit vectors, they are byte-for-byte EQUAL (`16 B` collision!). -/
theorem validWotsHash_eq_of_digits_eq {h₁ h₂ : Bytes 16}
    (hv₁ : ValidWotsHash h₁) (hv₂ : ValidWotsHash h₂)
    (hd : wotsCDigit h₁ = wotsCDigit h₂) : h₁ = h₂ := by
  have hqEq : decodeLE h₁.toList / 2 ^ WOTS_Z = decodeLE h₂.toList / 2 ^ WOTS_Z := by
    have hlt1 : decodeLE h₁.toList / 2 ^ WOTS_Z < 64 ^ WOTS_N := by
      have hlt := decodeLE_lt_pow h₁.toList
      rw [Bytes.toList_length] at hlt
      have hpow : 256 ^ 16 = 2 ^ WOTS_Z * 64 ^ WOTS_N := by decide
      rw [hpow] at hlt
      exact Nat.div_lt_of_lt_mul hlt
    have hlt2 : decodeLE h₂.toList / 2 ^ WOTS_Z < 64 ^ WOTS_N := by
      have hlt := decodeLE_lt_pow h₂.toList
      rw [Bytes.toList_length] at hlt
      have hpow : 256 ^ 16 = 2 ^ WOTS_Z * 64 ^ WOTS_N := by decide
      rw [hpow] at hlt
      exact Nat.div_lt_of_lt_mul hlt
    apply eq_of_base64_digits WOTS_N _ _ hlt1 hlt2
    intro c
    have hc : wotsCDigit h₁ c = wotsCDigit h₂ c := congrFun hd c
    unfold wotsCDigit at hc
    have hpow : 2 ^ (WOTS_Z + 6 * c.val) = 2 ^ WOTS_Z * 64 ^ c.val := by
      rw [Nat.pow_add, Nat.pow_mul]
    simpa [hpow, Nat.div_div_eq_div_mul] using hc
  have hdecEq : decodeLE h₁.toList = decodeLE h₂.toList := by
    have hd1 := Nat.div_add_mod (decodeLE h₁.toList) (2 ^ WOTS_Z)
    have hd2 := Nat.div_add_mod (decodeLE h₂.toList) (2 ^ WOTS_Z)
    rw [← hd1, ← hd2, hv₁.1, hv₂.1, hqEq]
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
  exact Bytes.toList_injective (hdec _ _ (by simp) hdecEq)

/-- **`WOTS+C` Dominance Theorem:** any two distinct valid 16-byte `WOTS+C` hashes `h₁ ≠ h₂`
    have an explicit chain `c : Fin 21` with `wotsCDigit h₁ c < wotsCDigit h₂ c`. -/
theorem wotsC_dominance {h₁ h₂ : Bytes 16}
    (hv₁ : ValidWotsHash h₁) (hv₂ : ValidWotsHash h₂) (hne : h₁ ≠ h₂) :
    ∃ c : Fin WOTS_N, wotsCDigit h₁ c < wotsCDigit h₂ c := by
  have hdigNe : wotsCDigit h₁ ≠ wotsCDigit h₂ :=
    fun heq => hne (validWotsHash_eq_of_digits_eq hv₁ hv₂ heq)
  exact constantSum_antichain (hv₁.2.2.trans hv₂.2.2.symm) hdigNe

/-- Pack `k` base-64 digits into a natural number `∑_{i=0}^{k-1} ds(i) · 64^i`. -/
def packBase64 : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _     => 0
  | k + 1, f => f ⟨0, by omega⟩ + 64 * packBase64 k (fun i => f ⟨i.val + 1, by omega⟩)

private theorem packBase64_lt : ∀ (k : Nat) (f : Fin k → Nat), (∀ i, f i < 64) → packBase64 k f < 64 ^ k
  | 0, _, _ => by simp [packBase64]
  | k + 1, f, hlt => by
    simp only [packBase64]
    have h0 : f ⟨0, by omega⟩ < 64 := hlt ⟨0, by omega⟩
    have ih := packBase64_lt k (fun i => f ⟨i.val + 1, by omega⟩) (fun i => hlt ⟨i.val + 1, by omega⟩)
    have hpow : 64 ^ (k + 1) = 64 * 64 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    omega

private theorem packBase64_digit : ∀ (k : Nat) (f : Fin k → Nat), (∀ i, f i < 64) →
    ∀ (c : Fin k), (packBase64 k f / 64 ^ c.val) % 64 = f c
  | 0, _, _, c => Fin.elim0 c
  | k + 1, f, hlt, ⟨0, _⟩ => by
    simp only [packBase64, Nat.pow_zero, Nat.div_one]
    have h0 : f ⟨0, by omega⟩ < 64 := hlt ⟨0, by omega⟩
    have : (f ⟨0, by omega⟩ + 64 * packBase64 k (fun i => f ⟨i.val + 1, by omega⟩)) % 64 = f ⟨0, by omega⟩ := by omega
    exact this
  | k + 1, f, hlt, ⟨j + 1, hj⟩ => by
    simp only [packBase64]
    have h0 : f ⟨0, by omega⟩ < 64 := hlt ⟨0, by omega⟩
    have hpow : 64 ^ (j + 1) = 64 * 64 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, ← Nat.div_div_eq_div_mul]
    have hdiv : (f ⟨0, by omega⟩ + 64 * packBase64 k (fun i => f ⟨i.val + 1, by omega⟩)) / 64 =
        packBase64 k (fun i => f ⟨i.val + 1, by omega⟩) := by omega
    rw [hdiv]
    exact packBase64_digit k (fun i => f ⟨i.val + 1, by omega⟩) (fun i => hlt ⟨i.val + 1, by omega⟩) ⟨j, by omega⟩

/-- Surjective inverse encoding any 21-digit vector `ds` into its exact 16-byte `WOTS+C` digest `4 · ∑ d_i 64^i`. -/
def encodeWotsCDigits (ds : Fin WOTS_N → Nat) : Bytes 16 :=
  let bytes := encodeLE (2 ^ WOTS_Z * packBase64 WOTS_N ds) 16
  fun i => bytes.getD i.val 0

private theorem encodeWotsCDigits_toList (ds : Fin WOTS_N → Nat) :
    (encodeWotsCDigits ds).toList = encodeLE (2 ^ WOTS_Z * packBase64 WOTS_N ds) 16 := by
  apply List.ext_getElem
  · simp [encodeLE_length]
  · intro i h1 h2
    simp only [Bytes.toList, List.getElem_ofFn, encodeWotsCDigits]
    have hlen : (encodeLE (2 ^ WOTS_Z * packBase64 WOTS_N ds) 16).length = 16 := encodeLE_length _ 16
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < (encodeLE _ 16).length)]

private theorem decodeLE_encodeWotsCDigits (ds : Fin WOTS_N → Nat) (hlt : ∀ c, ds c < 64) :
    decodeLE (encodeWotsCDigits ds).toList = 2 ^ WOTS_Z * packBase64 WOTS_N ds := by
  rw [encodeWotsCDigits_toList]
  apply decodeLE_encodeLE 16
  have hp := packBase64_lt WOTS_N ds hlt
  have hpow : 256 ^ 16 = 2 ^ WOTS_Z * 64 ^ WOTS_N := by decide
  rw [hpow]
  exact Nat.mul_lt_mul_of_pos_left hp (by decide)

/-- **`WOTS+C` Left-Inverse (Surjectivity):** decoding `encodeWotsCDigits ds` recovers every digit `ds c`. -/
theorem wotsCDigit_encodeWotsCDigits (ds : Fin WOTS_N → Nat) (hlt : ∀ c, ds c < 64) (c : Fin WOTS_N) :
    wotsCDigit (encodeWotsCDigits ds) c = ds c := by
  unfold wotsCDigit
  rw [decodeLE_encodeWotsCDigits ds hlt]
  have hpow : 2 ^ (WOTS_Z + 6 * c.val) = 2 ^ WOTS_Z * 64 ^ c.val := by rw [Nat.pow_add, Nat.pow_mul]
  rw [hpow, ← Nat.div_div_eq_div_mul]
  have hdiv : 2 ^ WOTS_Z * packBase64 WOTS_N ds / 2 ^ WOTS_Z = packBase64 WOTS_N ds :=
    Nat.mul_div_right _ (by decide)
  rw [hdiv]
  exact packBase64_digit WOTS_N ds hlt c

/-- **`WOTS+C` Surjectivity onto `ValidWotsHash`:** every codeword `ds ∈ L_679(21, 60)` encodes to a valid 16-byte digest. -/
theorem encodeWotsCDigits_valid (ds : Fin WOTS_N → Nat)
    (hlt : ∀ c, ds c < WOTS_W) (hsum : finSum WOTS_N ds = WOTS_SUM) :
    ValidWotsHash (encodeWotsCDigits ds) := by
  have h64 : ∀ c, ds c < 64 := fun c => by have := hlt c; unfold WOTS_W at this; omega
  have hdig : wotsCDigit (encodeWotsCDigits ds) = ds := funext (wotsCDigit_encodeWotsCDigits ds h64)
  refine ⟨?_, ?_, ?_⟩
  · rw [decodeLE_encodeWotsCDigits ds h64]; exact Nat.mul_mod_right _ _
  · intro c; rw [hdig]; exact hlt c
  · rw [hdig]; exact hsum

/-- **`WOTS+C` Right-Inverse (Bijection):** re-encoding the digits of any valid 16-byte digest recovers it identically. -/
theorem encodeWotsCDigits_wotsCDigit {h : Bytes 16} (hv : ValidWotsHash h) :
    encodeWotsCDigits (wotsCDigit h) = h := by
  have hvEnc := encodeWotsCDigits_valid (wotsCDigit h) hv.2.1 hv.2.2
  have h64 : ∀ c, wotsCDigit h c < 64 := fun c => by have := hv.2.1 c; unfold WOTS_W at this; omega
  exact validWotsHash_eq_of_digits_eq hvEnc hv (funext (wotsCDigit_encodeWotsCDigits (wotsCDigit h) h64))

/-- Height of hypertree layer `ℓ` indexed by `Nat` (`7` for `ℓ ≠ 5`, `13` for `ℓ = 5`). -/
def layerHeightNat (ℓ : Nat) : Nat :=
  if ℓ = 5 then TOP_HEIGHT else LOW_HEIGHT

theorem layerHeight_eq_nat (ℓ : Fin LAYERS) : layerHeight ℓ = layerHeightNat ℓ.val := rfl

/-- Hypertree addressing for `7 + 7 + 7 + 7 + 7 + 13 = 48` (`SPEC.md §11.2`). -/
def layerShift : Nat → Nat
  | 0 => 0
  | 1 => 7
  | 2 => 14
  | 3 => 21
  | 4 => 28
  | 5 => 35
  | _ => 48

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
    layerTree leafAddr 5 = 0 := by
  unfold layerTree layerAddr layerShift layerHeightNat
  simp only [↓reduceIte]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hpow : 2 ^ (35 + TOP_HEIGHT) = 2 ^ HYPER_BITS := rfl
  rw [hpow]
  exact Nat.div_eq_of_lt h

-- ---------------------------------------------------------------------------
-- Imprint Wire Structures (`SPEC.md §11.2`: Exact 3,990 Bytes)
-- ---------------------------------------------------------------------------

/-- One hypertree layer signature (`ℓ < 6`): 3-byte `u24` `WOTS+C` counter + 21 chain values + `layerHeight ℓ` auth nodes. -/
structure LayerSig (ℓ : Fin LAYERS) where
  ctr  : U24
  wots : Fin WOTS_N → Bytes 16
  auth : Fin (layerHeightNat ℓ.val) → Bytes 16

/-- Complete structured `BLINCS-48-X` imprint (`SPEC.md §11.2`: `3,990` bytes). -/
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

/-- Pad a list `sibs` (of length `≤ UPORS_M_MAX`) with trailing `zero16` blocks to exact length `45`. -/
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
  let root      := treeRoot H k_sec k_pub 5 0 (by decide) TOP_HEIGHT WOTS_N WOTS_STEPS
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

/-- Declarative U-PORS Octopus verification (`SPEC.md §§8.1–8.2, 10.2`):
    returns `some root` iff 9 distinct leaves extract cleanly from `D_sel`, 9 codewords extract cleanly
    from `FEW_CODE(D_sel)`, Octopus climbs to `[0]` (`exactOctopusSibs ≤ 45`), AND all unused trailing
    sibling slots equal `zero16`. -/
def uporsVerify (H : HashOracle) (K_pub : Bytes 32)
    (D_seed : Bytes 32) (ctrFt : UInt32)
    (chains : Fin UPORS_K → Fin UPORS_N → Bytes 16)
    (sibs : Fin UPORS_M_MAX → Bytes 16) : Option (Bytes 16) :=
  let D_sel := fewSelectDigest H K_pub D_seed ctrFt
  let leafAddr := extractLeafAddr D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  match extractUporsLeaves D_sel, extractUporsCodes H K_pub D_sel with
  | some leaves, some codes =>
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
  | _, _ => none

/-- Declarative `WOTS+C` hypertree signing for all 6 layers given valid counters `layerCtrs` (`SPEC.md §11`). -/
def hypertreeSign (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (layerCtrs : Fin LAYERS → U24) : (ℓ : Fin LAYERS) → LayerSig ℓ :=
  fun ℓ =>
    let tree := layerTree leafAddr ℓ.val
    let hTree := layerTree_lt_48 leafAddr ℓ.val hAddr
    let leaf := layerLeaf leafAddr ℓ.val
    let lByte := UInt8.ofNat ℓ.val
    let msg := honestLayerInput H K_sec K_pub leafAddr hAddr ℓ.val
    let ctr := layerCtrs ℓ
    let h := wotsMsgHash H K_pub lByte tree hTree (UInt16.ofNat leaf) msg ctr
    let wots := chainSignGeneric H K_sec K_pub lByte tree hTree (UInt16.ofNat leaf) (wotsCDigit h)
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
  let leafPk := chainVerifyGeneric H K_pub lByte tree hTree (UInt16.ofNat leaf)
    WOTS_STEPS (wotsCDigit h) sig.wots
  (ValidWotsHash h, merkleReconstruct (treeCombine H K_pub lByte tree hTree) leaf leafPk (List.ofFn sig.auth))

/-- Declarative hypertree verification fold over layers `0 .. k-1` (`k ≤ 6`). -/
def hypertreeVerifyUpTo (H : HashOracle) (K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (initNode : Bytes 16) (sigs : (ℓ : Fin LAYERS) → LayerSig ℓ) : (k : Nat) → k ≤ LAYERS → Prop × Bytes 16
  | 0, _     => (True, initNode)
  | k + 1, hk =>
    let (prevOk, prevNode) := hypertreeVerifyUpTo H K_pub leafAddr hAddr initNode sigs k (by omega)
    let (stepOk, nextNode) := verifyLayerStep H K_pub leafAddr hAddr ⟨k, hk⟩ prevNode (sigs ⟨k, hk⟩)
    (prevOk ∧ stepOk, nextNode)

/-- Declarative `BLINCS-48-X` imprinting given the ground counters `(ctrFt, layerCtrs)` (`SPEC.md §§6–11`). -/
def imprintWithCounters (H : HashOracle) (seed draw : Bytes 32) (ctx M : List UInt8)
    (ctrFt : UInt32) (layerCtrs : Fin LAYERS → U24) : Imprint :=
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
  let codes := (extractUporsCodes H k.k_pub D_sel).getD (fun _ => ⟨0, by decide⟩)
  let sibs := (uporsExtract H k.k_sec k.k_pub leafAddr hAddr48 leaves).2
  { e           := e
    r           := r
    ctrFt       := ctrFt
    uporsChains := uporsSignChains H k.k_sec k.k_pub leafAddr hAddr48 leaves codes
    uporsSibs   := padSibs sibs
    layers      := hypertreeSign H k.k_sec k.k_pub leafAddr hAddr layerCtrs }

/-- Declarative `BLINCS-48-X` verification (`SPEC.md §§6–11`). -/
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
    uporsVerify H k_pub D_seed σ.ctrFt σ.uporsChains σ.uporsSibs = some uporsNode ∧
    let (htOk, htRoot) := hypertreeVerifyUpTo H k_pub leafAddr hAddr uporsNode σ.layers LAYERS (Nat.le_refl _)
    htOk ∧ htRoot = root

-- ---------------------------------------------------------------------------
-- Completeness Proofs (`SPEC.md §§8–11`)
-- ---------------------------------------------------------------------------

theorem uporsVerify_honest (H : HashOracle) (K_sec K_pub : Bytes 32) (D_seed : Bytes 32) (ctrFt : UInt32)
    (hSel : ValidUporsSelection H K_sec K_pub D_seed ctrFt)
    (hCodesEx : ∃ codes : Fin UPORS_K → Fin UPORS_C,
      extractUporsCodes H K_pub (fewSelectDigest H K_pub D_seed ctrFt) = some codes) :
    let D_sel := fewSelectDigest H K_pub D_seed ctrFt
    let leafAddr := extractLeafAddr D_sel
    let hAddr48 := extractLeafAddr_lt_48 D_sel
    let leaves := (extractUporsLeaves D_sel).getD []
    let codes := (extractUporsCodes H K_pub D_sel).getD (fun _ => ⟨0, by decide⟩)
    let sibs := (uporsExtract H K_sec K_pub leafAddr hAddr48 leaves).2
    uporsVerify H K_pub D_seed ctrFt
      (uporsSignChains H K_sec K_pub leafAddr hAddr48 leaves codes)
      (padSibs sibs) =
    some (uporsRoot H K_sec K_pub leafAddr hAddr48) := by
  rcases hSel with ⟨leaves, hLeaves, hLen, hTop, hExactSibs⟩
  rcases hCodesEx with ⟨codes, hCodes⟩
  dsimp only
  let D_sel := fewSelectDigest H K_pub D_seed ctrFt
  let leafAddr := extractLeafAddr D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  have hSibs : (uporsExtract H K_sec K_pub leafAddr hAddr48 leaves).2.length ≤ UPORS_M_MAX := by
    unfold uporsExtract
    rw [octopusExtractAux_len_eq_exactSibs]
    exact hExactSibs
  unfold uporsVerify
  dsimp only
  rw [hLeaves, hCodes]
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
      simp only [List.getElem_ofFn, List.getElem_map, treeNodeAt, uporsSignChains, uporsLeafFn, treeLeafFn]
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
    (layerCtrs : Fin LAYERS → U24)
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
        (wotsCDigit (wotsMsgHash H K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
          (UInt16.ofNat (layerLeaf leafAddr k))
          (honestLayerInput H K_sec K_pub leafAddr hAddr k) (layerCtrs ℓ)))
        (chainSignGeneric H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
          (UInt16.ofNat (layerLeaf leafAddr k))
          (wotsCDigit (wotsMsgHash H K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
            (UInt16.ofNat (layerLeaf leafAddr k))
            (honestLayerInput H K_sec K_pub leafAddr hAddr k) (layerCtrs ℓ)))) =
        chainLeafPk H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
          (UInt16.ofNat (layerLeaf leafAddr k)) WOTS_N WOTS_STEPS :=
      chainVerifyGeneric_sign H K_sec K_pub (UInt8.ofNat k) (layerTree leafAddr k) (layerTree_lt_48 leafAddr k hAddr)
        (UInt16.ofNat (layerLeaf leafAddr k)) WOTS_STEPS _ (fun c => wotsCDigit_le_steps hv c)
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
    treeRoot H K_sec K_pub 5 t ht (layerHeightNat 5) WOTS_N WOTS_STEPS =
    treeRoot H K_sec K_pub 5 0 (by decide) TOP_HEIGHT WOTS_N WOTS_STEPS := by
  subst h0
  have hh : layerHeightNat 5 = TOP_HEIGHT := rfl
  simp only [hh]

/--
  **BLINCS-48-X Conditional Completeness Theorem:**
  Given any hash oracle `H`, 32-byte `seed`, 32-byte `draw`, valid `ctx` (`≤ 255` bytes), `M`,
  and valid grinding counters `(ctrFt, layerCtrs)` (including non-exhausted `FEW_CODE`),
  `imprintWithCounters H seed draw ctx M ctrFt layerCtrs` always verifies against `signetId H seed`.
-/
theorem blincs_completeness (H : HashOracle) (seed draw : Bytes 32) (ctx M : List UInt8)
    (hCtx : ctx.length ≤ MAX_CONTEXT_LEN)
    (ctrFt : UInt32) (layerCtrs : Fin LAYERS → U24)
    (hSel : let k := deriveKeys H seed
            let e := trunc16 (H.keyed k.k_salt draw.toList)
            let short := contentShort H k.k_content e ctx M
            let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
            let D_seed := messageDigest H k.k_pub r k.root short ctx
            ValidUporsSelection H k.k_sec k.k_pub D_seed ctrFt)
    (hCodesEx : let k := deriveKeys H seed
                let e := trunc16 (H.keyed k.k_salt draw.toList)
                let short := contentShort H k.k_content e ctx M
                let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
                let D_seed := messageDigest H k.k_pub r k.root short ctx
                ∃ codes : Fin UPORS_K → Fin UPORS_C,
                  extractUporsCodes H k.k_pub (fewSelectDigest H k.k_pub D_seed ctrFt) = some codes)
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
  · exact uporsVerify_honest H k.k_sec k.k_pub D_seed ctrFt hSel hCodesEx
  · have ⟨htOk, htRoot⟩ := hypertreeVerifyUpTo_honest H k.k_sec k.k_pub leafAddr hAddr layerCtrs hCtrs LAYERS (Nat.le_refl _)
    refine ⟨htOk, ?_⟩
    rw [htRoot]
    have h6 : honestLayerInput H k.k_sec k.k_pub leafAddr hAddr LAYERS =
        treeRoot H k.k_sec k.k_pub 5 (layerTree leafAddr 5) (layerTree_lt_48 leafAddr 5 hAddr)
          (layerHeightNat 5) WOTS_N WOTS_STEPS := rfl
    have hkroot : k.root = treeRoot H k.k_sec k.k_pub 5 0 (by decide) TOP_HEIGHT WOTS_N WOTS_STEPS := rfl
    rw [h6, hkroot]
    exact top_root_eq H k.k_sec k.k_pub (layerTree leafAddr 5) (layerTree_lt_48 leafAddr 5 hAddr) (top_layerTree_zero hAddr)

-- ---------------------------------------------------------------------------
-- Wire Serialization & Parser Round-Trip (`SPEC.md §11.2`: Exact 3,990 Bytes)
-- ---------------------------------------------------------------------------

def encodeLayerSig {ℓ : Fin LAYERS} (s : LayerSig ℓ) : List UInt8 :=
  encodeLE s.ctr.val 3 ++ flattenBytes16 s.wots ++ flattenBytes16 s.auth

theorem encodeLayerSig_length {ℓ : Fin LAYERS} (s : LayerSig ℓ) :
    (encodeLayerSig s).length = 3 + WOTS_N * 16 + layerHeightNat ℓ.val * 16 := by
  unfold encodeLayerSig
  rw [List.length_append, List.length_append, encodeLE_length, flattenBytes16_length, flattenBytes16_length]

/-- Canonical wire serialization of a `BLINCS-48-X` imprint (`SPEC.md §11.2`). -/
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
    ++ encodeLayerSig (σ.layers ⟨4, by decide⟩)
    ++ encodeLayerSig (σ.layers ⟨5, by decide⟩)

/-- **Wire Length Theorem:** every encoded `BLINCS-48-X` imprint is EXACTLY `3,990` bytes. -/
theorem encodeImprint_length (σ : Imprint) : (encodeImprint σ).length = IMPRINT_LEN := by
  unfold encodeImprint
  have hchains : (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length = 432 := by
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
  have hctrNat : s₁.ctr.val = s₂.ctr.val :=
    encodeLE_injective (m := 3) (by have := s₁.ctr.isLt; omega) (by have := s₂.ctr.isLt; omega) hctrL
  have hctr : s₁.ctr = s₂.ctr := U24.ext hctrNat
  have hwots : s₁.wots = s₂.wots := flattenBytes16_injective hwotsL
  have hauth : s₁.auth = s₂.auth := flattenBytes16_injective hauthL
  cases s₁; cases s₂
  simp only at hctr hwots hauth
  subst hctr; subst hwots; subst hauth
  rfl

/-- **Wire Injectivity Theorem:** distinct structured `BLINCS-48-X` imprints encode to distinct `3,990`-byte strings. -/
theorem encodeImprint_injective {σ₁ σ₂ : Imprint} (h : encodeImprint σ₁ = encodeImprint σ₂) : σ₁ = σ₂ := by
  unfold encodeImprint at h
  simp only [List.append_assoc] at h
  have ⟨heL, h1⟩ := append_eq_of_length_eq (by simp) h
  have ⟨hrL, h2⟩ := append_eq_of_length_eq (by simp) h1
  have ⟨hctrL, h3⟩ := append_eq_of_length_eq (by simp [encodeLE_length]) h2
  have hcLen1 : (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ₁.uporsChains j))).flatten.length = 432 := by
    rw [flatten_length_const (m := 48)]; · simp [UPORS_K]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨j, rfl⟩; rw [flattenBytes16_length]; rfl
  have hcLen2 : (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ₂.uporsChains j))).flatten.length = 432 := by
    rw [flatten_length_const (m := 48)]; · simp [UPORS_K]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨j, rfl⟩; rw [flattenBytes16_length]; rfl
  have ⟨hchFlat, h4⟩ := append_eq_of_length_eq (by omega) h3
  have ⟨hsibsL, h5⟩ := append_eq_of_length_eq (by simp [flattenBytes16_length]) h4
  have ⟨hl0, h6⟩ := append_eq_of_length_eq (by simp [encodeLayerSig_length]) h5
  have ⟨hl1, h7⟩ := append_eq_of_length_eq (by simp [encodeLayerSig_length]) h6
  have ⟨hl2, h8⟩ := append_eq_of_length_eq (by simp [encodeLayerSig_length]) h7
  have ⟨hl3, h9⟩ := append_eq_of_length_eq (by simp [encodeLayerSig_length]) h8
  have ⟨hl4, hl5⟩ := append_eq_of_length_eq (by simp [encodeLayerSig_length]) h9
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
    | 4 => exact encodeLayerSig_injective hl4
    | 5 => exact encodeLayerSig_injective hl5
    | n + 6 => unfold LAYERS at hv; omega
  cases σ₁; cases σ₂
  simp only at he hr hctrFt hchains hsibs hlayers
  subst he; subst hr; subst hctrFt; subst hchains; subst hsibs; subst hlayers
  rfl

-- Total wire decoder returning `none` on any length `≠ 3,990` and inverting `encodeImprint`!
private def readBytes16At (raw : List UInt8) (off : Nat) : Bytes 16 :=
  fun i => raw.getD (off + i.val) 0

private def readVec16At (raw : List UInt8) (off k : Nat) : Fin k → Bytes 16 :=
  fun j => readBytes16At raw (off + j.val * 16)

private def decodeLayerSigAt (raw : List UInt8) (off : Nat) (ℓ : Fin LAYERS) : LayerSig ℓ :=
  { ctr  := U24.ofNat (decodeLE ((raw.drop off).take 3))
    wots := readVec16At raw (off + 3) WOTS_N
    auth := readVec16At raw (off + 3 + WOTS_N * 16) (layerHeightNat ℓ.val) }

/-- Strict wire parser for `BLINCS-48-X` (`SPEC.md §11.2`): rejects any length `≠ 3,990`. -/
def decodeImprint (raw : List UInt8) : Option Imprint :=
  if raw.length = IMPRINT_LEN then
    some {
      e           := readBytes16At raw 0
      r           := readBytes16At raw 16
      ctrFt       := UInt32.ofNat (decodeLE ((raw.drop 32).take 4))
      uporsChains := fun j => readVec16At raw (36 + j.val * 48) UPORS_N
      uporsSibs   := readVec16At raw 468 UPORS_M_MAX
      layers      := fun ℓ =>
        match ℓ with
        | ⟨0, _⟩ => decodeLayerSigAt raw 1188 ⟨0, by decide⟩
        | ⟨1, _⟩ => decodeLayerSigAt raw 1639 ⟨1, by decide⟩
        | ⟨2, _⟩ => decodeLayerSigAt raw 2090 ⟨2, by decide⟩
        | ⟨3, _⟩ => decodeLayerSigAt raw 2541 ⟨3, by decide⟩
        | ⟨4, _⟩ => decodeLayerSigAt raw 2992 ⟨4, by decide⟩
        | ⟨5, _⟩ => decodeLayerSigAt raw 3443 ⟨5, by decide⟩
    }
  else none

/-- Wrong-length wire rejection theorem: any byte list of length `≠ 3,990` is rejected (`none`). -/
theorem decodeImprint_bad_len {raw : List UInt8} (h : raw.length ≠ IMPRINT_LEN) :
    decodeImprint raw = none := by
  unfold decodeImprint
  rw [ite_eq_right h]

private theorem getD_append_left {α : Type} (xs ys : List α) (i : Nat) (d : α) (hi : i < xs.length) :
    (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_right {α : Type} (xs ys : List α) (i : Nat) (d : α) (hi : xs.length ≤ i) :
    (xs ++ ys).getD i d = ys.getD (i - xs.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private theorem bytes16_toList_getD (b : Bytes 16) (i : Fin 16) :
    b.toList.getD i.val 0 = b i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i.val < b.toList.length by simp), Option.getD_some]
  simp only [Bytes.toList, List.getElem_ofFn]

private theorem drop_append_ge {α : Type} (xs ys : List α) (n : Nat) (h : xs.length ≤ n) :
    (xs ++ ys).drop n = ys.drop (n - xs.length) := by
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

private theorem readBytes16At_prefix (b : Bytes 16) (rest : List UInt8) :
    readBytes16At (b.toList ++ rest) 0 = b := by
  funext i
  unfold readBytes16At
  simp only [Nat.zero_add]
  rw [getD_append_left _ _ _ _ (by simp)]
  exact bytes16_toList_getD b i

private theorem readBytes16At_shift (pre rest : List UInt8) (off : Nat) (h : pre.length ≤ off) :
    readBytes16At (pre ++ rest) off = readBytes16At rest (off - pre.length) := by
  funext i
  unfold readBytes16At
  rw [getD_append_right _ _ _ _ (by omega)]
  have hsub : off + i.val - pre.length = off - pre.length + i.val := by omega
  rw [hsub]

private theorem readVec16At_shift (pre rest : List UInt8) (off k : Nat) (h : pre.length ≤ off) :
    readVec16At (pre ++ rest) off k = readVec16At rest (off - pre.length) k := by
  funext j
  unfold readVec16At
  rw [readBytes16At_shift pre rest (off + j.val * 16) (by omega)]
  have hsub : off + j.val * 16 - pre.length = off - pre.length + j.val * 16 := by omega
  rw [hsub]

private theorem flatten_getD_const {m : Nat} :
    ∀ (ls : List (List UInt8)), (∀ l ∈ ls, l.length = m) →
      ∀ (j i : Nat) (hj : j < ls.length) (_hi : i < m),
        ls.flatten.getD (j * m + i) 0 = (ls[j]'hj).getD i 0
  | [], _, _, _, hj, _ => by simp at hj
  | l :: ls, hlen, 0, i, _, hi => by
    simp only [Nat.zero_mul, Nat.zero_add, List.flatten_cons, List.getElem_cons_zero]
    exact getD_append_left l ls.flatten i 0 (by rw [hlen l (by simp)]; exact hi)
  | l :: ls, hlen, j + 1, i, hj, hi => by
    simp only [List.flatten_cons, List.getElem_cons_succ]
    have hl : l.length = m := hlen l (by simp)
    rw [getD_append_right l ls.flatten ((j + 1) * m + i) 0 (by rw [hl, Nat.succ_mul]; omega)]
    have hsub : (j + 1) * m + i - l.length = j * m + i := by rw [hl, Nat.succ_mul]; omega
    rw [hsub]
    exact flatten_getD_const ls (fun x hx => hlen x (by simp [hx])) j i (by simp at hj; omega) hi

private theorem readVec16At_prefix {k : Nat} (xs : Fin k → Bytes 16) (rest : List UInt8) :
    readVec16At (flattenBytes16 xs ++ rest) 0 k = xs := by
  funext j i
  unfold readVec16At readBytes16At
  simp only [Nat.zero_add]
  have hlt : j.val * 16 + i.val < (flattenBytes16 xs).length := by
    rw [flattenBytes16_length]
    have hj := j.isLt; have hi := i.isLt; omega
  rw [getD_append_left _ _ _ _ hlt]
  unfold flattenBytes16
  rw [flatten_getD_const (m := 16) _ (by intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨t, rfl⟩; simp)
      j.val i.val (by simp) i.isLt]
  simp only [List.getElem_ofFn]
  exact bytes16_toList_getD (xs j) i

private theorem decodeLayerSigAt_prefix {ℓ : Fin LAYERS} (s : LayerSig ℓ) (rest : List UInt8) :
    decodeLayerSigAt (encodeLayerSig s ++ rest) 0 ℓ = s := by
  unfold decodeLayerSigAt encodeLayerSig
  simp only [List.append_assoc, List.drop_zero]
  have htake : (encodeLE s.ctr.val 3 ++ (flattenBytes16 s.wots ++ (flattenBytes16 s.auth ++ rest))).take 3 =
      encodeLE s.ctr.val 3 := by
    rw [List.take_append_of_le_length (by simp [encodeLE_length]), List.take_of_length_le (by simp [encodeLE_length])]
  have hctrNat : decodeLE (encodeLE s.ctr.val 3) = s.ctr.val :=
    decodeLE_encodeLE 3 s.ctr.val (by have := s.ctr.isLt; omega)
  have hctr : U24.ofNat (decodeLE (encodeLE s.ctr.val 3)) = s.ctr := by
    rw [hctrNat]
    apply U24.ext
    exact Nat.mod_eq_of_lt s.ctr.isLt
  have hwots : readVec16At (encodeLE s.ctr.val 3 ++ (flattenBytes16 s.wots ++ (flattenBytes16 s.auth ++ rest))) 3 WOTS_N = s.wots := by
    rw [readVec16At_shift _ _ 3 WOTS_N (by simp [encodeLE_length])]
    simpa [encodeLE_length] using readVec16At_prefix s.wots (flattenBytes16 s.auth ++ rest)
  have hauth : readVec16At (encodeLE s.ctr.val 3 ++ (flattenBytes16 s.wots ++ (flattenBytes16 s.auth ++ rest))) (3 + WOTS_N * 16) (layerHeightNat ℓ.val) = s.auth := by
    rw [readVec16At_shift _ _ (3 + WOTS_N * 16) _ (by simp [encodeLE_length])]
    have hsub : 3 + WOTS_N * 16 - (encodeLE s.ctr.val 3).length = WOTS_N * 16 := by simp [encodeLE_length]
    rw [hsub, readVec16At_shift _ _ (WOTS_N * 16) _ (by simp [flattenBytes16_length])]
    simpa [flattenBytes16_length] using readVec16At_prefix s.auth rest
  cases s
  simp only [htake] at hctr ⊢
  simp only [hctr, hwots, hauth]

/-- **Wire Parser Round-Trip Theorem:** `decodeImprint (encodeImprint σ) = some σ` for EVERY imprint `σ`! -/
theorem decodeImprint_encodeImprint (σ : Imprint) :
    decodeImprint (encodeImprint σ) = some σ := by
  unfold decodeImprint
  rw [ite_eq_left (encodeImprint_length σ)]
  congr 1
  let raw :=
    σ.e.toList ++ (σ.r.toList ++ (encodeLE σ.ctrFt.toNat 4 ++
      ((List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten ++
       (flattenBytes16 σ.uporsSibs ++
        (encodeLayerSig (σ.layers ⟨0, by decide⟩) ++
         (encodeLayerSig (σ.layers ⟨1, by decide⟩) ++
          (encodeLayerSig (σ.layers ⟨2, by decide⟩) ++
           (encodeLayerSig (σ.layers ⟨3, by decide⟩) ++
            (encodeLayerSig (σ.layers ⟨4, by decide⟩) ++
             encodeLayerSig (σ.layers ⟨5, by decide⟩))))))))))
  have hraw : encodeImprint σ = raw := by
    unfold encodeImprint raw; simp only [List.append_assoc]
  rw [hraw]
  have hcLen : (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length = 432 := by
    rw [flatten_length_const (m := 48)]; · simp [UPORS_K]
    · intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨j, rfl⟩; rw [flattenBytes16_length]; rfl
  have hl0Len : (encodeLayerSig (σ.layers ⟨0, by decide⟩)).length = 451 := by simp [encodeLayerSig_length, layerHeightNat, LOW_HEIGHT, WOTS_N]
  have hl1Len : (encodeLayerSig (σ.layers ⟨1, by decide⟩)).length = 451 := by simp [encodeLayerSig_length, layerHeightNat, LOW_HEIGHT, WOTS_N]
  have hl2Len : (encodeLayerSig (σ.layers ⟨2, by decide⟩)).length = 451 := by simp [encodeLayerSig_length, layerHeightNat, LOW_HEIGHT, WOTS_N]
  have hl3Len : (encodeLayerSig (σ.layers ⟨3, by decide⟩)).length = 451 := by simp [encodeLayerSig_length, layerHeightNat, LOW_HEIGHT, WOTS_N]
  have hl4Len : (encodeLayerSig (σ.layers ⟨4, by decide⟩)).length = 451 := by simp [encodeLayerSig_length, layerHeightNat, LOW_HEIGHT, WOTS_N]
  have hsibsLen : (flattenBytes16 σ.uporsSibs).length = 720 := by rw [flattenBytes16_length]; rfl
  have he : readBytes16At raw 0 = σ.e := readBytes16At_prefix σ.e _
  have hr : readBytes16At raw 16 = σ.r := by
    dsimp only [raw]
    rw [readBytes16At_shift _ _ 16 (by simp)]
    simpa using readBytes16At_prefix σ.r _
  have hctrFt : UInt32.ofNat (decodeLE ((raw.drop 32).take 4)) = σ.ctrFt := by
    dsimp only [raw]
    have hdrop : (σ.e.toList ++ (σ.r.toList ++ (encodeLE σ.ctrFt.toNat 4 ++
        ((List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten ++
         (flattenBytes16 σ.uporsSibs ++
          (encodeLayerSig (σ.layers ⟨0, by decide⟩) ++
           (encodeLayerSig (σ.layers ⟨1, by decide⟩) ++
            (encodeLayerSig (σ.layers ⟨2, by decide⟩) ++
             (encodeLayerSig (σ.layers ⟨3, by decide⟩) ++
              (encodeLayerSig (σ.layers ⟨4, by decide⟩) ++
               encodeLayerSig (σ.layers ⟨5, by decide⟩))))))))))).drop 32 =
        encodeLE σ.ctrFt.toNat 4 ++
        ((List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten ++
         (flattenBytes16 σ.uporsSibs ++
          (encodeLayerSig (σ.layers ⟨0, by decide⟩) ++
           (encodeLayerSig (σ.layers ⟨1, by decide⟩) ++
            (encodeLayerSig (σ.layers ⟨2, by decide⟩) ++
             (encodeLayerSig (σ.layers ⟨3, by decide⟩) ++
              (encodeLayerSig (σ.layers ⟨4, by decide⟩) ++
               encodeLayerSig (σ.layers ⟨5, by decide⟩)))))))) := by
      rw [drop_append_ge _ _ 32 (by simp)]
      have h16 : 32 - σ.e.toList.length = 16 := by simp
      rw [h16, drop_append_ge _ _ 16 (by simp)]
      simp
    rw [hdrop, List.take_append_of_le_length (by simp [encodeLE_length]), List.take_of_length_le (by simp [encodeLE_length])]
    rw [decodeLE_encodeLE 4 σ.ctrFt.toNat (by have := σ.ctrFt.toNat_lt; omega)]
    exact UInt32.ofNat_toNat
  have hchains : (fun j : Fin UPORS_K => readVec16At raw (36 + j.val * 48) UPORS_N) = σ.uporsChains := by
    funext j c i
    dsimp only [raw]
    unfold readVec16At readBytes16At
    rw [getD_append_right _ _ _ _ (by simp; omega)]
    rw [getD_append_right _ _ _ _ (by simp; omega)]
    rw [getD_append_right _ _ _ _ (by simp [encodeLE_length]; omega)]
    have hidx : 36 + j.val * 48 + c.val * 16 + i.val - σ.e.toList.length - σ.r.toList.length - (encodeLE σ.ctrFt.toNat 4).length =
        j.val * 48 + (c.val * 16 + i.val) := by
      simp [encodeLE_length]; omega
    rw [hidx, getD_append_left _ _ _ _ (by rw [hcLen]; have hj := j.isLt; have hc := c.isLt; have hi := i.isLt; unfold UPORS_K UPORS_N at *; omega)]
    rw [flatten_getD_const (m := 48) _ (by intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨t, rfl⟩; rw [flattenBytes16_length]; rfl)
        j.val (c.val * 16 + i.val) (by simp) (by have hc := c.isLt; have hi := i.isLt; unfold UPORS_N at *; omega)]
    simp only [List.getElem_ofFn]
    unfold flattenBytes16
    rw [flatten_getD_const (m := 16) _ (by intro l hl; rw [List.mem_ofFn] at hl; rcases hl with ⟨t, rfl⟩; simp)
        c.val i.val (by simp) i.isLt]
    simp only [List.getElem_ofFn]
    exact bytes16_toList_getD (σ.uporsChains j c) i
  have hsibs : readVec16At raw 468 UPORS_M_MAX = σ.uporsSibs := by
    dsimp only [raw]
    rw [readVec16At_shift _ _ 468 _ (by simp)]
    rw [readVec16At_shift _ _ _ _ (by simp)]
    rw [readVec16At_shift _ _ _ _ (by simp [encodeLE_length])]
    rw [readVec16At_shift _ _ _ _ (by rw [hcLen]; simp [encodeLE_length])]
    have h0 : 468 - σ.e.toList.length - σ.r.toList.length - (encodeLE σ.ctrFt.toNat 4).length -
        (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length = 0 := by
      rw [hcLen]; simp [encodeLE_length]
    rw [h0]
    exact readVec16At_prefix σ.uporsSibs _
  have hdecShift : ∀ (pre rest : List UInt8) (off : Nat) (ℓ : Fin LAYERS),
      pre.length ≤ off → decodeLayerSigAt (pre ++ rest) off ℓ = decodeLayerSigAt rest (off - pre.length) ℓ := by
    intro pre rest off ℓ hle
    unfold decodeLayerSigAt
    have hd : (pre ++ rest).drop off = rest.drop (off - pre.length) := drop_append_ge pre rest off hle
    have hw : readVec16At (pre ++ rest) (off + 3) WOTS_N = readVec16At rest (off - pre.length + 3) WOTS_N := by
      rw [readVec16At_shift pre rest (off + 3) WOTS_N (by omega)]
      have : off + 3 - pre.length = off - pre.length + 3 := by omega
      rw [this]
    have ha : readVec16At (pre ++ rest) (off + 3 + WOTS_N * 16) (layerHeightNat ℓ.val) =
              readVec16At rest (off - pre.length + 3 + WOTS_N * 16) (layerHeightNat ℓ.val) := by
      rw [readVec16At_shift pre rest (off + 3 + WOTS_N * 16) _ (by omega)]
      have : off + 3 + WOTS_N * 16 - pre.length = off - pre.length + 3 + WOTS_N * 16 := by omega
      rw [this]
    rw [hd, hw, ha]
  have hlayers : (fun ℓ : Fin LAYERS =>
      match ℓ with
      | ⟨0, _⟩ => decodeLayerSigAt raw 1188 ⟨0, by decide⟩
      | ⟨1, _⟩ => decodeLayerSigAt raw 1639 ⟨1, by decide⟩
      | ⟨2, _⟩ => decodeLayerSigAt raw 2090 ⟨2, by decide⟩
      | ⟨3, _⟩ => decodeLayerSigAt raw 2541 ⟨3, by decide⟩
      | ⟨4, _⟩ => decodeLayerSigAt raw 2992 ⟨4, by decide⟩
      | ⟨5, _⟩ => decodeLayerSigAt raw 3443 ⟨5, by decide⟩) = σ.layers := by
    funext ℓ
    rcases ℓ with ⟨v, hv⟩
    match v with
    | 0 =>
      dsimp only [raw]
      rw [hdecShift _ _ 1188 _ (by simp), hdecShift _ _ _ _ (by simp),
          hdecShift _ _ _ _ (by simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen]; simp [encodeLE_length])]
      have h0 : 1188 - σ.e.toList.length - σ.r.toList.length - (encodeLE σ.ctrFt.toNat 4).length -
          (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length -
          (flattenBytes16 σ.uporsSibs).length = 0 := by rw [hcLen, hsibsLen]; simp [encodeLE_length]
      rw [h0]; exact decodeLayerSigAt_prefix (σ.layers ⟨0, by decide⟩) _
    | 1 =>
      dsimp only [raw]
      rw [hdecShift _ _ 1639 _ (by simp), hdecShift _ _ _ _ (by simp),
          hdecShift _ _ _ _ (by simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len]; simp [encodeLE_length])]
      have h0 : 1639 - σ.e.toList.length - σ.r.toList.length - (encodeLE σ.ctrFt.toNat 4).length -
          (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length -
          (flattenBytes16 σ.uporsSibs).length - (encodeLayerSig (σ.layers ⟨0, by decide⟩)).length = 0 := by
        rw [hcLen, hsibsLen, hl0Len]; simp [encodeLE_length]
      rw [h0]; exact decodeLayerSigAt_prefix (σ.layers ⟨1, by decide⟩) _
    | 2 =>
      dsimp only [raw]
      rw [hdecShift _ _ 2090 _ (by simp), hdecShift _ _ _ _ (by simp),
          hdecShift _ _ _ _ (by simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len]; simp [encodeLE_length])]
      have h0 : 2090 - σ.e.toList.length - σ.r.toList.length - (encodeLE σ.ctrFt.toNat 4).length -
          (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length -
          (flattenBytes16 σ.uporsSibs).length - (encodeLayerSig (σ.layers ⟨0, by decide⟩)).length -
          (encodeLayerSig (σ.layers ⟨1, by decide⟩)).length = 0 := by
        rw [hcLen, hsibsLen, hl0Len, hl1Len]; simp [encodeLE_length]
      rw [h0]; exact decodeLayerSigAt_prefix (σ.layers ⟨2, by decide⟩) _
    | 3 =>
      dsimp only [raw]
      rw [hdecShift _ _ 2541 _ (by simp), hdecShift _ _ _ _ (by simp),
          hdecShift _ _ _ _ (by simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len, hl2Len]; simp [encodeLE_length])]
      have h0 : 2541 - σ.e.toList.length - σ.r.toList.length - (encodeLE σ.ctrFt.toNat 4).length -
          (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length -
          (flattenBytes16 σ.uporsSibs).length - (encodeLayerSig (σ.layers ⟨0, by decide⟩)).length -
          (encodeLayerSig (σ.layers ⟨1, by decide⟩)).length - (encodeLayerSig (σ.layers ⟨2, by decide⟩)).length = 0 := by
        rw [hcLen, hsibsLen, hl0Len, hl1Len, hl2Len]; simp [encodeLE_length]
      rw [h0]; exact decodeLayerSigAt_prefix (σ.layers ⟨3, by decide⟩) _
    | 4 =>
      dsimp only [raw]
      rw [hdecShift _ _ 2992 _ (by simp), hdecShift _ _ _ _ (by simp),
          hdecShift _ _ _ _ (by simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len, hl2Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len, hl2Len, hl3Len]; simp [encodeLE_length])]
      have h0 : 2992 - σ.e.toList.length - σ.r.toList.length - (encodeLE σ.ctrFt.toNat 4).length -
          (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length -
          (flattenBytes16 σ.uporsSibs).length - (encodeLayerSig (σ.layers ⟨0, by decide⟩)).length -
          (encodeLayerSig (σ.layers ⟨1, by decide⟩)).length - (encodeLayerSig (σ.layers ⟨2, by decide⟩)).length -
          (encodeLayerSig (σ.layers ⟨3, by decide⟩)).length = 0 := by
        rw [hcLen, hsibsLen, hl0Len, hl1Len, hl2Len, hl3Len]; simp [encodeLE_length]
      rw [h0]; exact decodeLayerSigAt_prefix (σ.layers ⟨4, by decide⟩) _
    | 5 =>
      dsimp only [raw]
      rw [hdecShift _ _ 3443 _ (by simp), hdecShift _ _ _ _ (by simp),
          hdecShift _ _ _ _ (by simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len, hl2Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len, hl2Len, hl3Len]; simp [encodeLE_length]),
          hdecShift _ _ _ _ (by rw [hcLen, hsibsLen, hl0Len, hl1Len, hl2Len, hl3Len, hl4Len]; simp [encodeLE_length])]
      have h0 : 3443 - σ.e.toList.length - σ.r.toList.length - (encodeLE σ.ctrFt.toNat 4).length -
          (List.ofFn (fun j : Fin UPORS_K => flattenBytes16 (σ.uporsChains j))).flatten.length -
          (flattenBytes16 σ.uporsSibs).length - (encodeLayerSig (σ.layers ⟨0, by decide⟩)).length -
          (encodeLayerSig (σ.layers ⟨1, by decide⟩)).length - (encodeLayerSig (σ.layers ⟨2, by decide⟩)).length -
          (encodeLayerSig (σ.layers ⟨3, by decide⟩)).length - (encodeLayerSig (σ.layers ⟨4, by decide⟩)).length = 0 := by
        rw [hcLen, hsibsLen, hl0Len, hl1Len, hl2Len, hl3Len, hl4Len]; simp [encodeLE_length]
      rw [h0]
      have h5 := decodeLayerSigAt_prefix (σ.layers ⟨5, by decide⟩) []
      simpa using h5
    | n + 6 => unfold LAYERS at hv; omega
  rw [he, hr, hctrFt, hchains, hsibs, hlayers]

-- ---------------------------------------------------------------------------
-- Normative Bounded Minimum-Counter Signer (`SPEC.md §§8, 10, 11`, Fail-Closed)
-- ---------------------------------------------------------------------------

/-- Bounded search returning the smallest `cur ≤ cur + rem - 1` satisfying `p`, or `none` on exhaustion. -/
def findMinAux (p : Nat → Bool) : (cur rem : Nat) → Option Nat
  | _, 0 => none
  | cur, rem + 1 => if p cur then some cur else findMinAux p (cur + 1) rem

private theorem findMinAux_spec (p : Nat → Bool) :
    ∀ (cur rem x : Nat), findMinAux p cur rem = some x →
      cur ≤ x ∧ x < cur + rem ∧ p x = true ∧ ∀ y, cur ≤ y → y < x → p y = false
  | _, 0, _, h => by cases h
  | cur, rem + 1, x, h => by
    unfold findMinAux at h
    by_cases hp : p cur = true
    · rw [ite_eq_left hp] at h; cases h
      refine ⟨Nat.le_refl _, by omega, hp, fun y h1 h2 => by omega⟩
    · rw [ite_eq_right hp] at h
      have hfalse : p cur = false := Bool.eq_false_iff.mpr hp
      have ⟨h1, h2, h3, h4⟩ := findMinAux_spec p (cur + 1) rem x h
      refine ⟨by omega, by omega, h3, fun y hy1 hy2 => ?_⟩
      by_cases hy : y = cur
      · subst hy; exact hfalse
      · exact h4 y (by omega) hy2

/-- Decidable check of `ValidWotsHash h`. -/
def checkValidWotsHash (h : Bytes 16) : Bool :=
  (decodeLE h.toList % 2 ^ WOTS_Z == 0) &&
  (List.finRange WOTS_N).all (fun c => decide (wotsCDigit h c < WOTS_W)) &&
  (finSum WOTS_N (wotsCDigit h) == WOTS_SUM)

theorem checkValidWotsHash_iff (h : Bytes 16) :
    checkValidWotsHash h = true ↔ ValidWotsHash h := by
  unfold checkValidWotsHash ValidWotsHash
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro hc; exact ⟨hc.1.1, fun c => hc.1.2 c (List.mem_finRange c), hc.2⟩
  · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, fun c _ => h2 c⟩, h3⟩

theorem checkValidWotsHash_eq_true {h : Bytes 16} (hc : checkValidWotsHash h = true) :
    ValidWotsHash h := (checkValidWotsHash_iff h).mp hc

/-- Decidable check of `ValidUporsSelection` (`SPEC.md §8.1`, independent of `FEW_CODE`). -/
def checkValidUporsSel (H : HashOracle) (K_sec K_pub : Bytes 32) (D_seed : Bytes 32) (ctr : Nat) : Bool :=
  if ctr < 2 ^ 32 then
    let D_sel := fewSelectDigest H K_pub D_seed (UInt32.ofNat ctr)
    let leafAddr := extractLeafAddr D_sel
    let hAddr48 := extractLeafAddr_lt_48 D_sel
    match extractUporsLeaves D_sel with
    | none => false
    | some leaves =>
      (leaves.length == UPORS_K) &&
      ((uporsExtract H K_sec K_pub leafAddr hAddr48 leaves).1 == [0]) &&
      decide (exactOctopusSibs UPORS_HEIGHT leaves ≤ UPORS_M_MAX)
  else false

theorem checkValidUporsSel_iff (H : HashOracle) (K_sec K_pub D_seed : Bytes 32) (ctr : Nat) :
    checkValidUporsSel H K_sec K_pub D_seed ctr = true ↔
      ctr < 2 ^ 32 ∧ ValidUporsSelection H K_sec K_pub D_seed (UInt32.ofNat ctr) := by
  unfold checkValidUporsSel ValidUporsSelection
  constructor
  · intro hc
    by_cases hlt : ctr < 2 ^ 32
    · rw [ite_eq_left hlt] at hc
      dsimp only at hc
      cases hl : extractUporsLeaves (fewSelectDigest H K_pub D_seed (UInt32.ofNat ctr)) with
      | none => rw [hl] at hc; cases hc
      | some leaves =>
        rw [hl] at hc
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        exact ⟨hlt, leaves, hl, hc.1.1, hc.1.2, hc.2⟩
    · rw [ite_eq_right hlt] at hc; cases hc
  · intro ⟨hlt, leaves, hl, hlen, htop, hcap⟩
    rw [ite_eq_left hlt]
    dsimp only
    rw [hl]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨hlen, htop⟩, hcap⟩

theorem checkValidUporsSel_eq_true {H : HashOracle} {K_sec K_pub D_seed : Bytes 32} {ctr : Nat}
    (hc : checkValidUporsSel H K_sec K_pub D_seed ctr = true) :
    ctr < 2 ^ 32 ∧ ValidUporsSelection H K_sec K_pub D_seed (UInt32.ofNat ctr) :=
  (checkValidUporsSel_iff H K_sec K_pub D_seed ctr).mp hc

/-- Normative bounded minimum-counter `WOTS+C` search over `[0, 2^24)`, failing closed on exhaustion. -/
def findMinWotsCtr (H : HashOracle) (K_pub : Bytes 32) (layer : UInt8)
    (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16) (msg : Bytes 16) : Option U24 :=
  match h : findMinAux (fun c =>
    if hc : c < 2 ^ 24 then
      checkValidWotsHash (wotsMsgHash H K_pub layer tree hTree leaf msg ⟨c, hc⟩)
    else false) 0 (2 ^ 24) with
  | none => none
  | some c =>
    have hlt : c < 2 ^ 24 := by
      have ⟨_, h2, _, _⟩ := findMinAux_spec _ 0 (2 ^ 24) c h; omega
    some ⟨c, hlt⟩

/-- Per-layer helper for normative minimum-counter `WOTS+C` search. -/
def findMinLayerCtr (H : HashOracle) (K_sec K_pub : Bytes 32)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS) (ℓ : Fin LAYERS) : Option U24 :=
  findMinWotsCtr H K_pub (UInt8.ofNat ℓ.val)
    (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
    (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
    (honestLayerInput H K_sec K_pub leafAddr hAddr ℓ.val)

/-- Normative bounded minimum-counter `BLINCS-48-X` signer (`SPEC.md §§6–11`):
    searches `[0, 2^32)` for minimal `ctr_ft`, extracts `FEW_CODE` (failing closed on `u16` exhaustion),
    and searches `[0, 2^24)` for minimal `ctr_ℓ` at all 6 layers (failing closed on `u24` exhaustion). -/
def signNormative (H : HashOracle) (seed draw : Bytes 32) (ctx M : List UInt8) : Option Imprint :=
  if ctx.length ≤ MAX_CONTEXT_LEN then
    let k := deriveKeys H seed
    let e := trunc16 (H.keyed k.k_salt draw.toList)
    let short := contentShort H k.k_content e ctx M
    let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
    let D_seed := messageDigest H k.k_pub r k.root short ctx
    match findMinAux (checkValidUporsSel H k.k_sec k.k_pub D_seed) 0 (2 ^ 32) with
    | none => none
    | some ctrFtNat =>
      let ctrFt := UInt32.ofNat ctrFtNat
      let D_sel := fewSelectDigest H k.k_pub D_seed ctrFt
      match extractUporsCodes H k.k_pub D_sel with
      | none => none
      | some _ =>
        let leafAddr := extractLeafAddr D_sel
        let hAddr := extractLeafAddr_lt D_sel
        match findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨0, by decide⟩,
              findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨1, by decide⟩,
              findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨2, by decide⟩,
              findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨3, by decide⟩,
              findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨4, by decide⟩,
              findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨5, by decide⟩ with
        | some c0, some c1, some c2, some c3, some c4, some c5 =>
          let layerCtrs : Fin LAYERS → U24 := fun ℓ =>
            match ℓ.val with
            | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | _ => c5
          some (imprintWithCounters H seed draw ctx M ctrFt layerCtrs)
        | _, _, _, _, _, _ => none
  else none

private theorem findMinWotsCtr_spec {H : HashOracle} {K_pub : Bytes 32} {layer : UInt8}
    {tree : Nat} {hTree : tree < 2 ^ 48} {leaf : UInt16} {msg : Bytes 16} {ctr : U24}
    (hf : findMinWotsCtr H K_pub layer tree hTree leaf msg = some ctr) :
    ValidWotsHash (wotsMsgHash H K_pub layer tree hTree leaf msg ctr) ∧
    ∀ (y : U24), y.val < ctr.val →
      checkValidWotsHash (wotsMsgHash H K_pub layer tree hTree leaf msg y) = false := by
  unfold findMinWotsCtr at hf
  split at hf
  · cases hf
  · rename_i c hcEq
    simp only [Option.some.injEq] at hf
    have ⟨_, _, htrue, hmin⟩ := findMinAux_spec _ 0 (2 ^ 24) c hcEq
    have hlt : c < 2 ^ 24 := by
      have ⟨_, h2, _, _⟩ := findMinAux_spec _ 0 (2 ^ 24) c hcEq; omega
    rw [dite_eq_left hlt] at htrue
    subst hf
    refine ⟨checkValidWotsHash_eq_true htrue, fun y hy => ?_⟩
    have hm := hmin y.val (Nat.zero_le _) hy
    rw [dite_eq_left y.isLt] at hm
    exact hm

/-- **Normative Signer Soundness & Counter Minimality Theorem:**
    whenever the bounded fail-closed normative signer `signNormative` returns `some σ`,
    (1) `σ` passes `verify`,
    (2) `σ.ctrFt` is the strictly smallest valid `U-PORS` selection counter (`¬ ValidUporsSelection` for all `y < σ.ctrFt`), and
    (3) for EVERY hypertree layer `ℓ ∈ 0..5`, `(σ.layers ℓ).ctr` is the strictly smallest valid `WOTS+C`
        counter (`¬ ValidWotsHash` for all `y < (σ.layers ℓ).ctr`) at that physical hypertree address. -/
theorem signNormative_sound (H : HashOracle) (seed draw : Bytes 32) (ctx M : List UInt8) (σ : Imprint)
    (hsig : signNormative H seed draw ctx M = some σ) :
    verify H (signetId H seed) ctx M σ ∧
    (let k := deriveKeys H seed
     let e := trunc16 (H.keyed k.k_salt draw.toList)
     let short := contentShort H k.k_content e ctx M
     let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
     let D_seed := messageDigest H k.k_pub r k.root short ctx
     let D_sel := fewSelectDigest H k.k_pub D_seed σ.ctrFt
     let leafAddr := extractLeafAddr D_sel
     let hAddr := extractLeafAddr_lt_48 D_sel
     (∀ y < σ.ctrFt.toNat, ¬ ValidUporsSelection H k.k_sec k.k_pub D_seed (UInt32.ofNat y)) ∧
     (∀ (ℓ : Fin LAYERS) (y : U24), y.val < (σ.layers ℓ).ctr.val →
       ¬ ValidWotsHash (wotsMsgHash H k.k_pub (UInt8.ofNat ℓ.val) (layerTree leafAddr ℓ.val)
         (layerTree_lt_48 leafAddr ℓ.val hAddr)
         (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
         (honestLayerInput H k.k_sec k.k_pub leafAddr hAddr ℓ.val) y))) := by
  unfold signNormative at hsig
  by_cases hCtx : ctx.length ≤ MAX_CONTEXT_LEN
  · rw [ite_eq_left hCtx] at hsig
    dsimp only at hsig
    let k := deriveKeys H seed
    let e := trunc16 (H.keyed k.k_salt draw.toList)
    let short := contentShort H k.k_content e ctx M
    let r := trunc16 (H.keyed k.k_r (short ++ frameContext ctx))
    let D_seed := messageDigest H k.k_pub r k.root short ctx
    cases hFt : findMinAux (checkValidUporsSel H k.k_sec k.k_pub D_seed) 0 (2 ^ 32) with
    | none => rw [hFt] at hsig; cases hsig
    | some ctrFtNat =>
      rw [hFt] at hsig
      dsimp only at hsig
      have ⟨_, hFtLt, hFtTrue, hFtMin⟩ := findMinAux_spec _ 0 (2 ^ 32) ctrFtNat hFt
      have ⟨_, hSel⟩ := checkValidUporsSel_eq_true hFtTrue
      let ctrFt := UInt32.ofNat ctrFtNat
      let D_sel := fewSelectDigest H k.k_pub D_seed ctrFt
      cases hCodes : extractUporsCodes H k.k_pub D_sel with
      | none => rw [hCodes] at hsig; cases hsig
      | some codes =>
        rw [hCodes] at hsig
        dsimp only at hsig
        let leafAddr := extractLeafAddr D_sel
        let hAddr := extractLeafAddr_lt D_sel
        cases hc0 : findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨0, by decide⟩ with | none => rw [hc0] at hsig; cases hsig | some c0 =>
        cases hc1 : findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨1, by decide⟩ with | none => rw [hc0, hc1] at hsig; cases hsig | some c1 =>
        cases hc2 : findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨2, by decide⟩ with | none => rw [hc0, hc1, hc2] at hsig; cases hsig | some c2 =>
        cases hc3 : findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨3, by decide⟩ with | none => rw [hc0, hc1, hc2, hc3] at hsig; cases hsig | some c3 =>
        cases hc4 : findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨4, by decide⟩ with | none => rw [hc0, hc1, hc2, hc3, hc4] at hsig; cases hsig | some c4 =>
        cases hc5 : findMinLayerCtr H k.k_sec k.k_pub leafAddr hAddr ⟨5, by decide⟩ with | none => rw [hc0, hc1, hc2, hc3, hc4, hc5] at hsig; cases hsig | some c5 =>
        rw [hc0, hc1, hc2, hc3, hc4, hc5] at hsig
        simp only [Option.some.injEq] at hsig
        let layerCtrs : Fin LAYERS → U24 := fun ℓ =>
          match ℓ.val with | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | _ => c5
        have hCtrs : ∀ ℓ : Fin LAYERS, ValidWotsHash
            (wotsMsgHash H k.k_pub (UInt8.ofNat ℓ.val) (layerTree leafAddr ℓ.val)
              (layerTree_lt_48 leafAddr ℓ.val hAddr)
              (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
              (honestLayerInput H k.k_sec k.k_pub leafAddr hAddr ℓ.val) (layerCtrs ℓ)) := by
          intro ⟨lv, hlv⟩
          match lv with
          | 0 => exact (findMinWotsCtr_spec hc0).1
          | 1 => exact (findMinWotsCtr_spec hc1).1
          | 2 => exact (findMinWotsCtr_spec hc2).1
          | 3 => exact (findMinWotsCtr_spec hc3).1
          | 4 => exact (findMinWotsCtr_spec hc4).1
          | 5 => exact (findMinWotsCtr_spec hc5).1
          | n + 6 => unfold LAYERS at hlv; omega
        subst hsig
        refine ⟨blincs_completeness H seed draw ctx M hCtx ctrFt layerCtrs hSel ⟨codes, hCodes⟩ hCtrs, ?_, ?_⟩
        · intro y hy hVal
          have hnat : (imprintWithCounters H seed draw ctx M ctrFt layerCtrs).ctrFt.toNat = ctrFtNat := by
            simp [imprintWithCounters, ctrFt, UInt32.toNat_ofNat']; omega
          rw [hnat] at hy
          have hfalse := hFtMin y (Nat.zero_le _) hy
          have htrue := (checkValidUporsSel_iff H k.k_sec k.k_pub D_seed y).mpr ⟨by omega, hVal⟩
          rw [hfalse] at htrue; cases htrue
        · intro ⟨lv, hlv⟩ y hy hVal
          have hfalse : checkValidWotsHash (wotsMsgHash H k.k_pub (UInt8.ofNat lv)
              (layerTree leafAddr lv) (layerTree_lt_48 leafAddr lv hAddr)
              (UInt16.ofNat (layerLeaf leafAddr lv))
              (honestLayerInput H k.k_sec k.k_pub leafAddr hAddr lv) y) = false := by
            simp only [imprintWithCounters] at hy
            match lv with
            | 0 => exact (findMinWotsCtr_spec hc0).2 y hy
            | 1 => exact (findMinWotsCtr_spec hc1).2 y hy
            | 2 => exact (findMinWotsCtr_spec hc2).2 y hy
            | 3 => exact (findMinWotsCtr_spec hc3).2 y hy
            | 4 => exact (findMinWotsCtr_spec hc4).2 y hy
            | 5 => exact (findMinWotsCtr_spec hc5).2 y hy
            | n + 6 => unfold LAYERS at hlv; omega
          have htrue := (checkValidWotsHash_iff _).mpr hVal
          simp only [imprintWithCounters] at htrue
          change checkValidWotsHash (wotsMsgHash H k.k_pub (UInt8.ofNat lv)
              (layerTree leafAddr lv) (layerTree_lt_48 leafAddr lv hAddr)
              (UInt16.ofNat (layerLeaf leafAddr lv))
              (honestLayerInput H k.k_sec k.k_pub leafAddr hAddr lv) y) = true at htrue
          rw [hfalse] at htrue; cases htrue
  · rw [ite_eq_right hCtx] at hsig; cases hsig

end Blincs
