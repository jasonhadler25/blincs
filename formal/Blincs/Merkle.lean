/-
  BLINCS-128-7x5 Declarative Specification: Binary Merkle Trees.
  Pure structural recursion on tree height `h` (used identically for height-5
  hypertree layers and height-8 FORS trees).
  Mechanically proves:
    1. Exact authentication path length (`(merklePath ...).length = h`).
    2. Exact Merkle reconstruction completeness (`merkleReconstruct ... (merklePath ...) = merkleNode ...`).
    3. **Constructive Merkle Forgery Collision Extractor**: if a forged leaf `leaf' ≠ leaves idx`
       reconstructs to the true root under ANY authentication path of length `h`, then there exists
       an explicit `(level, pos)` and two distinct child pairs `(L₁, R₁) ≠ (L₂, R₂)` hashing to the
       same node value (`combine level pos L₁ R₁ = combine level pos L₂ R₂`).
-/

namespace Blincs

/-- Split a `2^(h+1)`-leaf array into its left half (`0 .. 2^h - 1`). -/
def leftHalf {H : Type} {h : Nat} (leaves : Fin (2 ^ (h + 1)) → H) : Fin (2 ^ h) → H :=
  fun i => leaves ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩

/-- Split a `2^(h+1)`-leaf array into its right half (`2^h .. 2^(h+1) - 1`). -/
def rightHalf {H : Type} {h : Nat} (leaves : Fin (2 ^ (h + 1)) → H) : Fin (2 ^ h) → H :=
  fun i => leaves ⟨2 ^ h + i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩

/--
  Declarative binary Merkle root at height `h` and node index `pos`.
  `combine level p L R` computes the internal node at `(level, p)` from children `(L, R)`.
  At `h = 0`, returns the single leaf; at `h + 1`, combines left child `(h, 2*pos)` and right child `(h, 2*pos + 1)`
  with level `h + 1` and index `pos` — matching `SPEC.md §§9, 11` bottom-up indexing identically!
-/
def merkleNode {H : Type} (combine : Nat → Nat → H → H → H) :
    (h : Nat) → (pos : Nat) → (Fin (2 ^ h) → H) → H
  | 0, _, leaves => leaves ⟨0, by decide⟩
  | h + 1, pos, leaves =>
    let L := merkleNode combine h (2 * pos) (leftHalf leaves)
    let R := merkleNode combine h (2 * pos + 1) (rightHalf leaves)
    combine (h + 1) pos L R

/--
  Declarative authentication path for leaf `idx < 2^h` (ordered bottom-up from level `0` sibling
  up to level `h - 1` sibling, matching `SPEC.md §§9, 11` wire order!).
-/
def merklePath {H : Type} (combine : Nat → Nat → H → H → H) :
    (h : Nat) → (pos : Nat) → (Fin (2 ^ h) → H) → (idx : Nat) → List H
  | 0, _, _, _ => []
  | h + 1, pos, leaves, idx =>
    if idx < 2 ^ h then
      merklePath combine h (2 * pos) (leftHalf leaves) idx
        ++ [merkleNode combine h (2 * pos + 1) (rightHalf leaves)]
    else
      merklePath combine h (2 * pos + 1) (rightHalf leaves) (idx - 2 ^ h)
        ++ [merkleNode combine h (2 * pos) (leftHalf leaves)]

theorem merklePath_length {H : Type} (combine : Nat → Nat → H → H → H)
    (h pos : Nat) (leaves : Fin (2 ^ h) → H) (idx : Nat) :
    (merklePath combine h pos leaves idx).length = h := by
  induction h generalizing pos idx with
  | zero => rfl
  | succ h ih =>
    unfold merklePath
    split <;> simp [ih]

/--
  Declarative Merkle root reconstruction from a leaf value `cur` at index `idx` and a bottom-up
  authentication path `path` (`SPEC.md §§9, 11`).
  At step `level` (starting at `curLevel`), bit 0 of `idx` chooses left vs right child and `idx / 2`
  gives the parent node position at `level`!
-/
def merkleReconstructAux {H : Type} (combine : Nat → Nat → H → H → H)
    (curLevel : Nat) (idx : Nat) (cur : H) : List H → H
  | [] => cur
  | sib :: rest =>
    let parentIdx := idx / 2
    let next :=
      if idx % 2 = 0 then
        combine curLevel parentIdx cur sib
      else
        combine curLevel parentIdx sib cur
    merkleReconstructAux combine (curLevel + 1) parentIdx next rest

/-- Top-level Merkle reconstruction starting from leaf level (`curLevel = 1`). -/
def merkleReconstruct {H : Type} (combine : Nat → Nat → H → H → H)
    (idx : Nat) (leaf : H) (path : List H) : H :=
  merkleReconstructAux combine 1 idx leaf path

theorem merkleReconstructAux_append {H : Type} (combine : Nat → Nat → H → H → H)
    (curLevel idx : Nat) (cur : H) (p₁ p₂ : List H) :
    merkleReconstructAux combine curLevel idx cur (p₁ ++ p₂) =
    merkleReconstructAux combine (curLevel + p₁.length) (idx / 2 ^ p₁.length)
      (merkleReconstructAux combine curLevel idx cur p₁) p₂ := by
  induction p₁ generalizing curLevel idx cur with
  | nil => simp [merkleReconstructAux]
  | cons sib rest ih =>
    simp only [List.cons_append, List.length_cons, merkleReconstructAux]
    rw [ih]
    have h1 : curLevel + 1 + rest.length = curLevel + (rest.length + 1) := by omega
    have h2 : (idx / 2) / 2 ^ rest.length = idx / 2 ^ (rest.length + 1) := by
      rw [Nat.pow_succ', Nat.div_div_eq_div_mul]
    rw [h1, h2]

private theorem pos_mul_pow_succ (h pos : Nat) :
    pos * 2 ^ (h + 1) = (2 * pos) * 2 ^ h := by
  rw [Nat.pow_succ', ← Nat.mul_assoc, Nat.mul_comm pos 2]

private theorem shift_right_left {h pos idx : Nat} (hi : idx < 2 ^ h) :
    (pos * 2 ^ (h + 1) + idx) / 2 ^ h = 2 * pos := by
  have hpos : 0 < 2 ^ h := Nat.two_pow_pos h
  rw [pos_mul_pow_succ, Nat.mul_comm (2 * pos) (2 ^ h), Nat.mul_add_div hpos,
      Nat.div_eq_of_lt hi, Nat.add_zero]

private theorem shift_right_right {h pos idx : Nat} (hi1 : ¬ idx < 2 ^ h) (hi2 : idx < 2 ^ (h + 1)) :
    (pos * 2 ^ (h + 1) + idx) / 2 ^ h = 2 * pos + 1 := by
  have hpos : 0 < 2 ^ h := Nat.two_pow_pos h
  have hrem : idx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hi2; omega
  have heq : pos * 2 ^ (h + 1) + idx = 2 ^ h * (2 * pos + 1) + (idx - 2 ^ h) := by
    rw [pos_mul_pow_succ, Nat.mul_comm (2 ^ h), Nat.add_mul, Nat.one_mul]
    omega
  rw [heq, Nat.mul_add_div hpos, Nat.div_eq_of_lt hrem, Nat.add_zero]

/-- Strengthened reconstruction correctness for any subtree at `(h, pos)`. -/
theorem merkleReconstructAux_correct {H : Type} (combine : Nat → Nat → H → H → H)
    (h pos : Nat) (leaves : Fin (2 ^ h) → H) (idx : Nat) (hi : idx < 2 ^ h) :
    merkleReconstructAux combine 1 (pos * 2 ^ h + idx) (leaves ⟨idx, hi⟩)
      (merklePath combine h pos leaves idx) =
    merkleNode combine h pos leaves := by
  induction h generalizing pos idx with
  | zero =>
    have hidx : idx = 0 := by omega
    subst hidx
    rfl
  | succ h ih =>
    unfold merklePath
    by_cases hleft : idx < 2 ^ h
    · simp only [hleft, ↓reduceIte]
      rw [merkleReconstructAux_append, merklePath_length]
      have hidx_eq : pos * 2 ^ (h + 1) + idx = (2 * pos) * 2 ^ h + idx := by
        rw [pos_mul_pow_succ]
      have hleaf_eq : leaves ⟨idx, hi⟩ = leftHalf leaves ⟨idx, hleft⟩ := rfl
      rw [hleaf_eq, hidx_eq]
      rw [ih (2 * pos) (leftHalf leaves) idx hleft]
      rw [← hidx_eq, shift_right_left hleft]
      have h1 : 1 + h = h + 1 := by omega
      simp only [merkleReconstructAux, Nat.mul_mod_right, ↓reduceIte,
        Nat.mul_div_cancel_left _ (by decide : 0 < 2), h1]
      rfl
    · simp only [hleft, ↓reduceIte]
      rw [merkleReconstructAux_append, merklePath_length]
      have hrem : idx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hi; omega
      have hidx_eq : pos * 2 ^ (h + 1) + idx = (2 * pos + 1) * 2 ^ h + (idx - 2 ^ h) := by
        rw [pos_mul_pow_succ, Nat.add_mul, Nat.one_mul]; omega
      have hleaf_eq : leaves ⟨idx, hi⟩ = rightHalf leaves ⟨idx - 2 ^ h, hrem⟩ := by
        unfold rightHalf
        have hfin : (⟨idx, hi⟩ : Fin (2 ^ (h + 1))) = ⟨2 ^ h + (idx - 2 ^ h), by rw [Nat.pow_succ]; omega⟩ :=
          Fin.ext (by dsimp; omega)
        exact congrArg leaves hfin
      rw [hleaf_eq, hidx_eq]
      rw [ih (2 * pos + 1) (rightHalf leaves) (idx - 2 ^ h) hrem]
      rw [← hidx_eq, shift_right_right hleft hi]
      have hodd : ¬ (2 * pos + 1) % 2 = 0 := by omega
      have hdiv : (2 * pos + 1) / 2 = pos := by omega
      have h1 : 1 + h = h + 1 := by omega
      simp only [merkleReconstructAux, hodd, ↓reduceIte, hdiv, h1]
      rfl

/-- **Merkle Completeness Theorem:** reconstructing from any honest leaf and its authentication path recovers the exact Merkle root. -/
theorem merkleReconstruct_correct {H : Type} (combine : Nat → Nat → H → H → H)
    (h : Nat) (leaves : Fin (2 ^ h) → H) (idx : Nat) (hi : idx < 2 ^ h) :
    merkleReconstruct combine idx (leaves ⟨idx, hi⟩) (merklePath combine h 0 leaves idx) =
    merkleNode combine h 0 leaves := by
  have := merkleReconstructAux_correct combine h 0 leaves idx hi
  simpa [merkleReconstruct] using this

private theorem list_split_last {α : Type} :
    ∀ (l : List α) {n : Nat}, l.length = n + 1 → ∃ init x, l = init ++ [x] ∧ init.length = n
  | [], _, h => by simp at h
  | [x], n, h => ⟨[], x, rfl, by simp only [List.length_cons, List.length_nil] at h ⊢; omega⟩
  | a :: b :: rest, n, h => by
    cases n with
    | zero => simp at h
    | succ m =>
      have hlen : (b :: rest).length = m + 1 := Nat.succ.inj h
      rcases list_split_last (b :: rest) hlen with ⟨init, x, heq, hilen⟩
      exact ⟨a :: init, x, by simp [heq], by simp [hilen]⟩

/--
  **Constructive Merkle Forgery Collision Extractor (general subtree version):**
  If a forged leaf `leaf' ≠ leaves ⟨idx, hi⟩` reconstructs to the honest root `merkleNode combine h pos leaves`
  using ANY path of length `h`, then there exists an explicit internal node `(level, p)` with `1 ≤ level ≤ h`
  and two DISTINCT child pairs `(L₁, R₁) ≠ (L₂, R₂)` hashing to the exact same value `combine level p L₁ R₁ = combine level p L₂ R₂`.
-/
theorem merkle_forgery_collision_aux {H : Type} (combine : Nat → Nat → H → H → H)
    (h pos : Nat) (leaves : Fin (2 ^ h) → H) (idx : Nat) (hi : idx < 2 ^ h)
    (leaf' : H) (path : List H) (hlen : path.length = h)
    (hne : leaf' ≠ leaves ⟨idx, hi⟩)
    (hroot : merkleReconstructAux combine 1 (pos * 2 ^ h + idx) leaf' path = merkleNode combine h pos leaves) :
    ∃ level p L₁ R₁ L₂ R₂,
      1 ≤ level ∧ level ≤ h ∧
      (L₁ ≠ L₂ ∨ R₁ ≠ R₂) ∧
      combine level p L₁ R₁ = combine level p L₂ R₂ := by
  induction h generalizing pos idx leaf' path with
  | zero =>
    have hp : path = [] := List.eq_nil_of_length_eq_zero hlen
    subst hp
    have hidx : idx = 0 := by omega
    subst hidx
    simp [merkleReconstructAux, merkleNode] at hroot
    exact absurd hroot hne
  | succ h ih =>
    rcases list_split_last path hlen with ⟨pInit, topSib, hsplit, hpInit_len⟩
    rw [hsplit, merkleReconstructAux_append, hpInit_len] at hroot
    unfold merkleNode at hroot
    dsimp only at hroot
    by_cases hleft : idx < 2 ^ h
    · have hidx_eq : pos * 2 ^ (h + 1) + idx = (2 * pos) * 2 ^ h + idx := by
        rw [pos_mul_pow_succ]
      rw [shift_right_left hleft] at hroot
      have hlvl : 1 + h = h + 1 := by omega
      simp only [merkleReconstructAux, Nat.mul_mod_right, ↓reduceIte,
        Nat.mul_div_cancel_left _ (by decide : 0 < 2), hlvl] at hroot
      let subForged := merkleReconstructAux combine 1 (pos * 2 ^ (h + 1) + idx) leaf' pInit
      let subHonest := merkleNode combine h (2 * pos) (leftHalf leaves)
      let sibHonest := merkleNode combine h (2 * pos + 1) (rightHalf leaves)
      by_cases hsub : subForged = subHonest
      · have hleaf_ne : leaf' ≠ leftHalf leaves ⟨idx, hleft⟩ := hne
        have hsub' : merkleReconstructAux combine 1 ((2 * pos) * 2 ^ h + idx) leaf' pInit = subHonest := by
          simpa [subForged, hidx_eq] using hsub
        rcases ih (2 * pos) (leftHalf leaves) idx hleft leaf' pInit hpInit_len hleaf_ne hsub' with
          ⟨lvl, p, L₁, R₁, L₂, R₂, h1, h2, hdiff, hcol⟩
        exact ⟨lvl, p, L₁, R₁, L₂, R₂, h1, by omega, hdiff, hcol⟩
      · exact ⟨h + 1, pos, subForged, topSib, subHonest, sibHonest, by omega, Nat.le_refl _, Or.inl hsub, hroot⟩
    · have hrem : idx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hi; omega
      have hidx_eq : pos * 2 ^ (h + 1) + idx = (2 * pos + 1) * 2 ^ h + (idx - 2 ^ h) := by
        rw [pos_mul_pow_succ, Nat.add_mul, Nat.one_mul]; omega
      rw [shift_right_right hleft hi] at hroot
      have hodd : ¬ (2 * pos + 1) % 2 = 0 := by omega
      have hdiv : (2 * pos + 1) / 2 = pos := by omega
      have hlvl : 1 + h = h + 1 := by omega
      simp only [merkleReconstructAux, hodd, ↓reduceIte, hdiv, hlvl] at hroot
      let subForged := merkleReconstructAux combine 1 (pos * 2 ^ (h + 1) + idx) leaf' pInit
      let sibHonest := merkleNode combine h (2 * pos) (leftHalf leaves)
      let subHonest := merkleNode combine h (2 * pos + 1) (rightHalf leaves)
      by_cases hsub : subForged = subHonest
      · have hleaf_ne : leaf' ≠ rightHalf leaves ⟨idx - 2 ^ h, hrem⟩ := by
          intro heq
          apply hne
          have hfin : (⟨idx, hi⟩ : Fin (2 ^ (h + 1))) = ⟨2 ^ h + (idx - 2 ^ h), by rw [Nat.pow_succ]; omega⟩ :=
            Fin.ext (by dsimp; omega)
          simpa [rightHalf, hfin] using heq
        have hsub' : merkleReconstructAux combine 1 ((2 * pos + 1) * 2 ^ h + (idx - 2 ^ h)) leaf' pInit = subHonest := by
          simpa [subForged, hidx_eq] using hsub
        rcases ih (2 * pos + 1) (rightHalf leaves) (idx - 2 ^ h) hrem leaf' pInit hpInit_len hleaf_ne hsub' with
          ⟨lvl, p, L₁, R₁, L₂, R₂, h1, h2, hdiff, hcol⟩
        exact ⟨lvl, p, L₁, R₁, L₂, R₂, h1, by omega, hdiff, hcol⟩
      · exact ⟨h + 1, pos, topSib, subForged, sibHonest, subHonest, by omega, Nat.le_refl _, Or.inr hsub, hroot⟩

/-- **Top-level Merkle Forgery Collision Theorem.** -/
theorem merkle_forgery_collision {H : Type} (combine : Nat → Nat → H → H → H)
    (h : Nat) (leaves : Fin (2 ^ h) → H) (idx : Nat) (hi : idx < 2 ^ h)
    (leaf' : H) (path : List H) (hlen : path.length = h)
    (hne : leaf' ≠ leaves ⟨idx, hi⟩)
    (hroot : merkleReconstruct combine idx leaf' path = merkleNode combine h 0 leaves) :
    ∃ level p L₁ R₁ L₂ R₂,
      1 ≤ level ∧ level ≤ h ∧
      (L₁ ≠ L₂ ∨ R₁ ≠ R₂) ∧
      combine level p L₁ R₁ = combine level p L₂ R₂ := by
  apply merkle_forgery_collision_aux combine h 0 leaves idx hi leaf' path hlen hne
  simpa [merkleReconstruct] using hroot

end Blincs
