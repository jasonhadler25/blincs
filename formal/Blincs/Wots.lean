/-
  BLINCS-128-7x5 Declarative Specification: WOTS+ (w = 16, 32 + 3 chains).
  Mechanically proves:
    1. All 35 digits lie in 0..15 and the checksum fits in 3 nibbles (≤ 480 < 4096).
    2. Message nibble extraction is injective (`m₁ = m₂`).
    3. Chain composition / WOTS+ completeness (`chain d (15 - d) (chain 0 d x₀) = chain 0 15 x₀`).
    4. **WOTS+ Dominance Lemma**: for ANY two distinct 16-byte messages `m₁ ≠ m₂`,
       there exists a chain `c : Fin 35` with `wotsDigit m₁ c < wotsDigit m₂ c`.
    5. **WOTS+ Chain Forgery Extraction**: forging a chain endpoint from a strictly
       smaller digit `d₁ < d₂` either recovers the honest earlier node `chain 0 d₁ x₀`
       (inverting the hash chain backwards!) OR yields an explicit `CHAIN` 2nd-preimage.
-/
import Blincs.Params

namespace Blincs

/-- Extract the `j`-th message nibble (`j ∈ 0..31`) in little-endian nibble order (`SPEC.md §10`). -/
def msgDigit (m : Bytes 16) (j : Fin 32) : Nat :=
  let byte := (m ⟨j.val / 2, by omega⟩).toNat
  if j.val % 2 == 0 then byte % 16 else byte / 16

theorem msgDigit_lt_16 (m : Bytes 16) (j : Fin 32) : msgDigit m j < 16 := by
  unfold msgDigit
  dsimp only
  have hb : (m ⟨j.val / 2, by omega⟩).toNat < 256 := (m ⟨j.val / 2, by omega⟩).toNat_lt
  split <;> omega

/-- Declarative sum over `0 .. n-1`. -/
def finSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _     => 0
  | n + 1, f => finSum n (fun i => f ⟨i.val, by omega⟩) + f ⟨n, by omega⟩

theorem finSum_le_bound {n B : Nat} {f : Fin n → Nat} (h : ∀ i, f i ≤ B) :
    finSum n f ≤ n * B := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    have h1 := ih (f := fun i => f ⟨i.val, by omega⟩) (fun i => h ⟨i.val, by omega⟩)
    have h2 := h ⟨n, by omega⟩
    have : (n + 1) * B = n * B + B := by rw [Nat.succ_mul]
    omega

private theorem finSum_le_finSum {n : Nat} {f g : Fin n → Nat} (hle : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => simp [finSum]
  | succ m ih =>
    simp only [finSum]
    have a := ih (fun j => hle ⟨j.val, by omega⟩)
    have b := hle ⟨m, by omega⟩
    omega

theorem finSum_lt_of_le_and_lt {n : Nat} {f g : Fin n → Nat}
    (hle : ∀ i, f i ≤ g i) (hlt : ∃ i, f i < g i) :
    finSum n f < finSum n g := by
  induction n with
  | zero =>
    rcases hlt with ⟨i, _⟩
    exact Fin.elim0 i
  | succ n ih =>
    simp only [finSum]
    rcases hlt with ⟨i, hi⟩
    by_cases hlast : i.val = n
    · have htail : finSum n (fun j => f ⟨j.val, by omega⟩) ≤ finSum n (fun j => g ⟨j.val, by omega⟩) :=
        finSum_le_finSum (fun j => hle ⟨j.val, by omega⟩)
      have hflast : f ⟨n, by omega⟩ < g ⟨n, by omega⟩ := by
        have heq : i = ⟨n, by omega⟩ := Fin.ext hlast
        rwa [← heq]
      omega
    · have hi' : i.val < n := by omega
      have h1 := ih (fun j => hle ⟨j.val, by omega⟩) ⟨⟨i.val, hi'⟩, hi⟩
      have h2 := hle ⟨n, by omega⟩
      omega

/-- WOTS+ checksum `∑_{j=0..31} (15 - msgDigit m j)` (`SPEC.md §10`). -/
def checksum (m : Bytes 16) : Nat :=
  finSum 32 (fun j => 15 - msgDigit m j)

theorem checksum_le_480 (m : Bytes 16) : checksum m ≤ 480 := by
  unfold checksum
  have h := finSum_le_bound (n := 32) (B := 15) (f := fun j => 15 - msgDigit m j) (fun _ => by omega)
  omega

/-- All 35 WOTS+ digits: 32 message nibbles followed by 3 little-endian checksum nibbles (`SPEC.md §10`). -/
def wotsDigit (m : Bytes 16) (c : Fin 35) : Nat :=
  if h : c.val < 32 then
    msgDigit m ⟨c.val, h⟩
  else
    let cs := checksum m
    if c.val = 32 then cs % 16
    else if c.val = 33 then (cs / 16) % 16
    else (cs / 256) % 16

theorem wotsDigit_lt_16 (m : Bytes 16) (c : Fin 35) : wotsDigit m c < 16 := by
  unfold wotsDigit
  split
  · exact msgDigit_lt_16 m _
  · dsimp only
    split
    · omega
    · split <;> omega

/-- Message nibble extraction is injective: equal nibbles imply equal 16-byte messages. -/
theorem msgDigits_injective {m₁ m₂ : Bytes 16}
    (h : ∀ j : Fin 32, msgDigit m₁ j = msgDigit m₂ j) : m₁ = m₂ := by
  funext i
  have hlo := h ⟨2 * i.val, by omega⟩
  have hhi := h ⟨2 * i.val + 1, by omega⟩
  unfold msgDigit at hlo hhi
  dsimp only at hlo hhi
  have heven : ((2 * i.val) % 2 == 0) = true := by simp
  have hodd  : ((2 * i.val + 1) % 2 == 0) = false := by
    have : (2 * i.val + 1) % 2 = 1 := by omega
    simp [this]
  have hdiv1 : (2 * i.val) / 2 = i.val := by omega
  have hdiv2 : (2 * i.val + 1) / 2 = i.val := by omega
  simp only [heven, hodd, ↓reduceIte, Bool.false_eq_true] at hlo hhi
  have h1 : (m₁ i).toNat % 16 = (m₂ i).toNat % 16 := by
    have eq1 : (⟨(2 * i.val) / 2, by omega⟩ : Fin 16) = i := Fin.ext hdiv1
    simpa [eq1] using hlo
  have h2 : (m₁ i).toNat / 16 = (m₂ i).toNat / 16 := by
    have eq2 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin 16) = i := Fin.ext hdiv2
    simpa [eq2] using hhi
  have hnat : (m₁ i).toNat = (m₂ i).toNat := by omega
  exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hnat)

private theorem base16_lt_three_digits {a b : Nat} (ha : a < 4096) (hb : b < 4096) (hlt : a < b) :
    (a / 256) % 16 < (b / 256) % 16 ∨
    (a / 16) % 16 < (b / 16) % 16 ∨
    a % 16 < b % 16 := by
  omega

/--
  **WOTS+ Dominance Theorem (`BLINCS-128-7x5`):**
  For any two distinct 16-byte messages `m₁ ≠ m₂`, there exists a chain index `c : Fin 35`
  such that `wotsDigit m₁ c < wotsDigit m₂ c`.
  (Equivalently, knowing an honest WOTS+ signature on `m₂` does NOT allow advancing forward
  in every chain to produce a signature on `m₁`.)
-/
theorem wots_dominance {m₁ m₂ : Bytes 16} (hne : m₁ ≠ m₂) :
    ∃ c : Fin 35, wotsDigit m₁ c < wotsDigit m₂ c := by
  by_cases hmsg : ∃ j : Fin 32, msgDigit m₁ j < msgDigit m₂ j
  · rcases hmsg with ⟨j, hj⟩
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    simp [wotsDigit, j.isLt, hj]
  · -- Every message nibble satisfies `msgDigit m₁ j ≥ msgDigit m₂ j`.
    have hge : ∀ j : Fin 32, msgDigit m₂ j ≤ msgDigit m₁ j := by
      intro j
      have : ¬ msgDigit m₁ j < msgDigit m₂ j := fun h => hmsg ⟨j, h⟩
      omega
    -- Since `m₁ ≠ m₂`, at least one message nibble must be strictly greater.
    have hgt : ∃ j : Fin 32, msgDigit m₂ j < msgDigit m₁ j := by
      apply Classical.byContradiction
      intro hno
      apply hne
      apply msgDigits_injective
      intro j
      have h1 := hge j
      have h2 : ¬ msgDigit m₂ j < msgDigit m₁ j := fun h => hno ⟨j, h⟩
      omega
    -- Therefore `checksum m₁ < checksum m₂`.
    have hcs_lt : checksum m₁ < checksum m₂ := by
      unfold checksum
      apply finSum_lt_of_le_and_lt
      · intro j
        have := hge j
        have := msgDigit_lt_16 m₁ j
        have := msgDigit_lt_16 m₂ j
        omega
      · rcases hgt with ⟨j, hj⟩
        refine ⟨j, ?_⟩
        have := msgDigit_lt_16 m₁ j
        have := msgDigit_lt_16 m₂ j
        omega
    have hcs1 : checksum m₁ < 4096 := by have := checksum_le_480 m₁; omega
    have hcs2 : checksum m₂ < 4096 := by have := checksum_le_480 m₂; omega
    rcases base16_lt_three_digits hcs1 hcs2 hcs_lt with h34 | h33 | h32
    · exact ⟨⟨34, by omega⟩, by simp [wotsDigit, h34]⟩
    · exact ⟨⟨33, by omega⟩, by simp [wotsDigit, h33]⟩
    · exact ⟨⟨32, by omega⟩, by simp [wotsDigit, h32]⟩

-- ---------------------------------------------------------------------------
-- WOTS+ Hash Chains: Completeness & Constructive Forgery Extraction
-- ---------------------------------------------------------------------------

/-- Declarative WOTS+ chain iteration: apply `step` `steps` times starting at step index `start`. -/
def chainIter {H : Type} (step : Nat → H → H) (start : Nat) : Nat → H → H
  | 0, x     => x
  | k + 1, x => chainIter step (start + 1) k (step start x)

/-- Chain composition: advancing `k₁` steps then `k₂` steps equals advancing `k₁ + k₂` steps. -/
theorem chainIter_add {H : Type} (step : Nat → H → H) (start k₁ k₂ : Nat) (x : H) :
    chainIter step (start + k₁) k₂ (chainIter step start k₁ x) =
    chainIter step start (k₁ + k₂) x := by
  induction k₁ generalizing start x with
  | zero =>
    simp [chainIter]
  | succ k₁ ih =>
    have h1 : start + (k₁ + 1) = (start + 1) + k₁ := by omega
    have h2 : k₁ + 1 + k₂ = (k₁ + k₂) + 1 := by omega
    rw [h1, h2]
    simp only [chainIter]
    exact ih (start + 1) (step start x)

/-- Generic hash-chain completeness for any chain length `maxSteps`. -/
theorem chain_complete {H : Type} (step : Nat → H → H) (x₀ : H) {d maxSteps : Nat} (hd : d ≤ maxSteps) :
    chainIter step d (maxSteps - d) (chainIter step 0 d x₀) = chainIter step 0 maxSteps x₀ := by
  have h := chainIter_add step 0 d (maxSteps - d) x₀
  simp only [Nat.zero_add] at h
  rw [h]
  congr 1
  omega

/-- WOTS+ chain verification completeness: signing `d` steps and verifying `15 - d` steps yields the endpoint `x₁₅`. -/
theorem wots_chain_complete {H : Type} (step : Nat → H → H) (x₀ : H) {d : Nat} (hd : d ≤ 15) :
    chainIter step d (15 - d) (chainIter step 0 d x₀) = chainIter step 0 15 x₀ :=
  chain_complete step x₀ hd

/--
  **Chain Collision-or-Preimage Extractor:**
  If `u ≠ v` produce the exact same value after `k` chain steps from `start`, then there exists
  an explicit step index `s ∈ [start, start + k)` and two distinct inputs `a ≠ b` with `step s a = step s b`.
-/
theorem chainIter_collision {H : Type} (step : Nat → H → H) (start k : Nat) (u v : H)
    (hne : u ≠ v) (heq : chainIter step start k u = chainIter step start k v) :
    ∃ s a b, start ≤ s ∧ s < start + k ∧ a ≠ b ∧ step s a = step s b := by
  induction k generalizing start u v with
  | zero =>
    simp [chainIter] at heq
    exact absurd heq hne
  | succ k ih =>
    simp only [chainIter] at heq
    by_cases hstep : step start u = step start v
    · exact ⟨start, u, v, Nat.le_refl _, by omega, hne, hstep⟩
    · rcases ih (start + 1) (step start u) (step start v) hstep heq with ⟨s, a, b, hs1, hs2, hab, hcol⟩
      exact ⟨s, a, b, by omega, by omega, hab, hcol⟩

/--
  **Unified Chain Forgery Extraction Lemma (used by BOTH WOTS+ and U-FORS):**
  Suppose an adversary supplies a forged value `y` at step `d₁ ≤ maxSteps` that verifies to the honest
  endpoint `chainIter step 0 maxSteps x₀`. Then EITHER:
    (a) `y = chainIter step 0 d₁ x₀` (an explicit chain preimage!), OR
    (b) there exists an explicit step `s ∈ [d₁, maxSteps)` and distinct `a ≠ b` with `step s a = step s b`
        (an explicit `CHAIN` 2nd-preimage witness!).
-/
theorem chain_forgery_extract {H : Type} (step : Nat → H → H) (x₀ y : H) {d₁ maxSteps : Nat} (hd₁ : d₁ ≤ maxSteps)
    (hver : chainIter step d₁ (maxSteps - d₁) y = chainIter step 0 maxSteps x₀) :
    y = chainIter step 0 d₁ x₀ ∨
    ∃ s a b, d₁ ≤ s ∧ s < maxSteps ∧ a ≠ b ∧ step s a = step s b := by
  by_cases hy : y = chainIter step 0 d₁ x₀
  · exact Or.inl hy
  · right
    have hcomp := chain_complete step x₀ hd₁
    rw [← hcomp] at hver
    rcases chainIter_collision step d₁ (maxSteps - d₁) y (chainIter step 0 d₁ x₀) hy hver with ⟨s, a, b, h1, h2, hne, hcol⟩
    exact ⟨s, a, b, h1, by omega, hne, hcol⟩

/-- WOTS+ specialization (`maxSteps = 15`). -/
theorem wots_chain_forgery_extract {H : Type} (step : Nat → H → H) (x₀ y : H) {d₁ : Nat} (hd₁ : d₁ ≤ 15)
    (hver : chainIter step d₁ (15 - d₁) y = chainIter step 0 15 x₀) :
    y = chainIter step 0 d₁ x₀ ∨
    ∃ s a b, d₁ ≤ s ∧ s < 15 ∧ a ≠ b ∧ step s a = step s b :=
  chain_forgery_extract step x₀ y hd₁ hver

-- ---------------------------------------------------------------------------
-- U-FORS Upper-Layer Constant-Sum Code (SPEC.md §10.1)
-- ---------------------------------------------------------------------------

/-- Canonical 64-entry upper-layer constant-sum code in `{0..9}^3` with sum `16`. -/
def uforsCodeTable : Array (Nat × Nat × Nat) :=
  #[ (0,7,9), (0,8,8), (0,9,7), (1,6,9), (1,7,8), (1,8,7), (1,9,6), (2,5,9),
     (2,6,8), (2,7,7), (2,8,6), (2,9,5), (3,4,9), (3,5,8), (3,6,7), (3,7,6),
     (3,8,5), (3,9,4), (4,3,9), (4,4,8), (4,5,7), (4,7,5), (4,8,4), (4,9,3),
     (5,2,9), (5,3,8), (5,4,7), (5,7,4), (5,8,3), (5,9,2), (6,1,9), (6,2,8),
     (6,3,7), (6,6,4), (6,7,3), (6,8,2), (6,9,1), (7,0,9), (7,1,8), (7,2,7),
     (7,3,6), (7,4,5), (7,5,4), (7,6,3), (7,7,2), (7,8,1), (7,9,0), (8,0,8),
     (8,1,7), (8,2,6), (8,3,5), (8,4,4), (8,5,3), (8,6,2), (8,7,1), (8,8,0),
     (9,0,7), (9,1,6), (9,2,5), (9,3,4), (9,4,3), (9,5,2), (9,6,1), (9,7,0) ]

theorem uforsCodeTable_size : uforsCodeTable.size = 64 := rfl

/-- Extract chain digit `c : Fin 3` for U-FORS codeword index `idx : Fin 64`. -/
def uforsDigit (idx : Fin 64) (c : Fin 3) : Nat :=
  let t := uforsCodeTable[idx.val]'(by simp [uforsCodeTable_size, idx.isLt])
  match c.val with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

/-- Every U-FORS digit lies in `0..9` (`≤ UFORS_STEPS = 9`). -/
theorem uforsDigit_le_9 (idx : Fin 64) (c : Fin 3) : uforsDigit idx c ≤ 9 := by
  revert idx c; decide

/-- Every U-FORS codeword has exact constant sum `16` (constant `27 - 16 = 11` verify steps/tree). -/
theorem uforsCode_sum (idx : Fin 64) :
    uforsDigit idx ⟨0, by decide⟩ + uforsDigit idx ⟨1, by decide⟩ + uforsDigit idx ⟨2, by decide⟩ = 16 := by
  revert idx; decide

/--
  **U-FORS Strict Antichain Theorem:**
  For any two distinct codewords `i ≠ j` in `UFORS_CODE`, there exists a chain `c : Fin 3`
  with `uforsDigit i c < uforsDigit j c`. (Hence a single honest reveal on a U-FORS leaf
  covers ONLY that 1 exact codeword out of 64!)
-/
theorem uforsCode_antichain :
    ∀ (i j : Fin 64), i ≠ j → ∃ c : Fin 3, uforsDigit i c < uforsDigit j c := by
  decide

end Blincs
