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

-- ---------------------------------------------------------------------------
-- Single-Tree Bottom-Up Octopus Multi-Proofs (`SPEC.md §10.2`, U-PORS)
-- ---------------------------------------------------------------------------

/-- Honest bottom-up binary Merkle node at `(level, p)` over a leaf oracle `leafFn : Nat → H`. -/
def treeNodeAt {H : Type} (combine : Nat → Nat → H → H → H) (leafFn : Nat → H) :
    (level : Nat) → (p : Nat) → H
  | 0, p => leafFn p
  | level + 1, p =>
    combine (level + 1) p
      (treeNodeAt combine leafFn level (2 * p))
      (treeNodeAt combine leafFn level (2 * p + 1))

/-- Sibling index `x ^^^ 1` in `Nat` arithmetic. -/
def sibIdx (x : Nat) : Nat :=
  if x % 2 = 0 then x + 1 else x - 1

/-- Extract one level of Octopus parent indices and authentication siblings from a sorted list of active indices (`SPEC.md §10.2`). -/
def octopusExtractLevel {H : Type} (nodeAt : Nat → H) : List Nat → List Nat × List H
  | [] => ([], [])
  | [x] => ([x / 2], [nodeAt (sibIdx x)])
  | x :: y :: rest =>
    if x % 2 = 0 ∧ y = x + 1 then
      let (ps, ss) := octopusExtractLevel nodeAt rest
      (x / 2 :: ps, ss)
    else
      let (ps, ss) := octopusExtractLevel nodeAt (y :: rest)
      (x / 2 :: ps, nodeAt (sibIdx x) :: ss)

/-- Extract all `h` levels of Octopus siblings bottom-up (`SPEC.md §10.2`). -/
def octopusExtractAux {H : Type} (combine : Nat → Nat → H → H → H) (leafFn : Nat → H) :
    (startLevel rem : Nat) → List Nat → List Nat × List H
  | _, 0, cur => (cur, [])
  | lvl, rem + 1, cur =>
    let (ps, ss) := octopusExtractLevel (treeNodeAt combine leafFn lvl) cur
    let (top, rest) := octopusExtractAux combine leafFn (lvl + 1) rem ps
    (top, ss ++ rest)

/-- Climb one level of an Octopus multi-proof, consuming siblings from `sibs` (`SPEC.md §10.2`). -/
def octopusClimbLevel {H : Type} (combineLvl : Nat → H → H → H) :
    List (Nat × H) → List H → Option (List (Nat × H) × List H)
  | [], sibs => some ([], sibs)
  | [(x, vx)], sib :: restSibs =>
    let p := x / 2
    let pv := if x % 2 = 0 then combineLvl p vx sib else combineLvl p sib vx
    some ([(p, pv)], restSibs)
  | [(_, _)], [] => none
  | (x, vx) :: (y, vy) :: rest, sibs =>
    if x % 2 = 0 ∧ y = x + 1 then
      match octopusClimbLevel combineLvl rest sibs with
      | none => none
      | some (ps, remSibs) => some (((x / 2, combineLvl (x / 2) vx vy) :: ps), remSibs)
    else
      match sibs with
      | [] => none
      | sib :: restSibs =>
        match octopusClimbLevel combineLvl ((y, vy) :: rest) restSibs with
        | none => none
        | some (ps, remSibs) =>
          let p := x / 2
          let pv := if x % 2 = 0 then combineLvl p vx sib else combineLvl p sib vx
          some (((p, pv) :: ps), remSibs)

/-- Climb `rem` levels of an Octopus multi-proof starting from `startLevel` (`SPEC.md §10.2`). -/
def octopusClimbAux {H : Type} (combine : Nat → Nat → H → H → H) :
    (startLevel rem : Nat) → List (Nat × H) → List H → Option (List (Nat × H) × List H)
  | _, 0, cur, sibs => some (cur, sibs)
  | lvl, rem + 1, cur, sibs =>
    match octopusClimbLevel (combine (lvl + 1)) cur sibs with
    | none => none
    | some (ps, remSibs) => octopusClimbAux combine (lvl + 1) rem ps remSibs

private theorem pair_combine_even {H : Type} (combine : Nat → Nat → H → H → H) (leafFn : Nat → H)
    (lvl x : Nat) (heven : x % 2 = 0) :
    combine (lvl + 1) (x / 2) (treeNodeAt combine leafFn lvl x) (treeNodeAt combine leafFn lvl (x + 1)) =
    treeNodeAt combine leafFn (lvl + 1) (x / 2) := by
  have h2x : 2 * (x / 2) = x := by omega
  simp only [treeNodeAt, h2x]

private theorem pair_combine_odd {H : Type} (combine : Nat → Nat → H → H → H) (leafFn : Nat → H)
    (lvl x : Nat) (hodd : ¬ x % 2 = 0) :
    combine (lvl + 1) (x / 2) (treeNodeAt combine leafFn lvl (x - 1)) (treeNodeAt combine leafFn lvl x) =
    treeNodeAt combine leafFn (lvl + 1) (x / 2) := by
  have h2x : 2 * (x / 2) = x - 1 := by omega
  have hxm : x - 1 + 1 = x := by omega
  simp only [treeNodeAt, h2x, hxm]

private theorem octopusClimbLevel_extract_len {H : Type} (combine : Nat → Nat → H → H → H) (leafFn : Nat → H)
    (lvl : Nat) :
    ∀ (n : Nat) (cur : List Nat), cur.length ≤ n → ∀ (extra : List H),
      let (ps, ss) := octopusExtractLevel (treeNodeAt combine leafFn lvl) cur
      octopusClimbLevel (combine (lvl + 1))
        (cur.map (fun x => (x, treeNodeAt combine leafFn lvl x))) (ss ++ extra) =
      some (ps.map (fun p => (p, treeNodeAt combine leafFn (lvl + 1) p)), extra) := by
  intro n
  induction n with
  | zero =>
    intro cur hlen extra
    cases cur with
    | nil => rfl
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro cur hlen extra
    cases cur with
    | nil => rfl
    | cons x rest =>
      cases rest with
      | nil =>
        simp only [octopusExtractLevel, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          octopusClimbLevel, sibIdx]
        by_cases heven : x % 2 = 0
        · simp only [heven, ↓reduceIte, pair_combine_even combine leafFn lvl x heven]
        · simp only [heven, ↓reduceIte, pair_combine_odd combine leafFn lvl x heven]
      | cons y ys =>
        dsimp only
        simp only [octopusExtractLevel, List.map_cons, octopusClimbLevel]
        by_cases hpair : x % 2 = 0 ∧ y = x + 1
        · rw [ite_eq_left hpair, ite_eq_left hpair]
          have hih := ih ys (by simp at hlen; omega) extra
          cases hext : octopusExtractLevel (treeNodeAt combine leafFn lvl) ys with
          | mk ps ss =>
            simp only [hext] at hih
            dsimp only
            rw [hih, hpair.2, pair_combine_even combine leafFn lvl x hpair.1]
            rfl
        · rw [ite_eq_right hpair, ite_eq_right hpair]
          have hih := ih (y :: ys) (by simp at hlen; omega) extra
          cases hext : octopusExtractLevel (treeNodeAt combine leafFn lvl) (y :: ys) with
          | mk ps ss =>
            simp only [hext, List.map_cons] at hih
            dsimp only
            simp only [List.cons_append, sibIdx]
            rw [hih]
            by_cases heven : x % 2 = 0
            · simp only [heven, ↓reduceIte, pair_combine_even combine leafFn lvl x heven]; rfl
            · simp only [heven, ↓reduceIte, pair_combine_odd combine leafFn lvl x heven]; rfl

/-- **Octopus Multi-Proof Completeness Theorem (`SPEC.md §10.2`):**
    Climbing honest active leaves with the extracted Octopus siblings recovers the exact honest
    level-`rem` nodes and consumes every sibling cleanly! -/
theorem octopusClimbAux_extract {H : Type} (combine : Nat → Nat → H → H → H) (leafFn : Nat → H)
    (lvl rem : Nat) :
    ∀ (cur : List Nat) (extra : List H),
      let (top, ss) := octopusExtractAux combine leafFn lvl rem cur
      octopusClimbAux combine lvl rem
        (cur.map (fun x => (x, treeNodeAt combine leafFn lvl x))) (ss ++ extra) =
      some (top.map (fun p => (p, treeNodeAt combine leafFn (lvl + rem) p)), extra) := by
  induction rem generalizing lvl with
  | zero =>
    intro cur extra
    simp [octopusExtractAux, octopusClimbAux]
  | succ rem ih =>
    intro cur extra
    simp only [octopusExtractAux, octopusClimbAux]
    have hstep := octopusClimbLevel_extract_len combine leafFn lvl cur.length cur (Nat.le_refl _)
    cases hext1 : octopusExtractLevel (treeNodeAt combine leafFn lvl) cur with
    | mk ps ss =>
      cases hext2 : octopusExtractAux combine leafFn (lvl + 1) rem ps with
      | mk top rest =>
        simp only [List.append_assoc]
        have hs := hstep (rest ++ extra)
        simp only [hext1] at hs
        rw [hs]
        have hih := ih (lvl + 1) ps extra
        simp only [hext2] at hih
        have hadd : lvl + 1 + rem = lvl + (rem + 1) := by omega
        rw [hadd] at hih
        exact hih

/-- One-level constructive Octopus forgery collision extractor. -/
private theorem octopusClimbLevel_collision_len {H : Type} (combine : Nat → Nat → H → H → H) (leafFn : Nat → H)
    (lvl : Nat) :
    ∀ (n : Nat) (cur : List (Nat × H)), cur.length ≤ n →
      ∀ (sibs : List H) (ps : List (Nat × H)) (remSibs : List H),
        octopusClimbLevel (combine (lvl + 1)) cur sibs = some (ps, remSibs) →
        (∀ pv ∈ ps, pv.2 = treeNodeAt combine leafFn (lvl + 1) pv.1) →
        (∀ xv ∈ cur, xv.2 = treeNodeAt combine leafFn lvl xv.1) ∨
        ∃ p L₁ R₁ L₂ R₂,
          (L₁ ≠ L₂ ∨ R₁ ≠ R₂) ∧
          combine (lvl + 1) p L₁ R₁ = combine (lvl + 1) p L₂ R₂ := by
  intro n
  induction n with
  | zero =>
    intro cur hlen _ _ _ _ _
    cases cur with
    | nil => left; intro _ h; cases h
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro cur hlen sibs ps remSibs hclimb hall
    cases cur with
    | nil => left; intro _ h; cases h
    | cons head rest =>
      rcases head with ⟨x, vx⟩
      cases rest with
      | nil =>
        cases sibs with
        | nil => simp [octopusClimbLevel] at hclimb
        | cons sib restSibs =>
          simp only [octopusClimbLevel, Option.some.injEq, Prod.mk.injEq] at hclimb
          rcases hclimb with ⟨rfl, _⟩
          have hp := hall (x / 2, if x % 2 = 0 then combine (lvl + 1) (x / 2) vx sib else combine (lvl + 1) (x / 2) sib vx) (by simp)
          dsimp only at hp
          by_cases hx : vx = treeNodeAt combine leafFn lvl x
          · left
            intro xv hmem
            simp only [List.mem_singleton] at hmem
            subst hmem; exact hx
          · right
            by_cases heven : x % 2 = 0
            · rw [ite_eq_left heven] at hp
              rw [← pair_combine_even combine leafFn lvl x heven] at hp
              exact ⟨x / 2, vx, sib, treeNodeAt combine leafFn lvl x, treeNodeAt combine leafFn lvl (x + 1), Or.inl hx, hp⟩
            · rw [ite_eq_right heven] at hp
              rw [← pair_combine_odd combine leafFn lvl x heven] at hp
              exact ⟨x / 2, sib, vx, treeNodeAt combine leafFn lvl (x - 1), treeNodeAt combine leafFn lvl x, Or.inr hx, hp⟩
      | cons head2 ys =>
        rcases head2 with ⟨y, vy⟩
        simp only [octopusClimbLevel] at hclimb
        by_cases hpair : x % 2 = 0 ∧ y = x + 1
        · rw [ite_eq_left hpair] at hclimb
          cases hrec : octopusClimbLevel (combine (lvl + 1)) ys sibs with
          | none => rw [hrec] at hclimb; cases hclimb
          | some res =>
            rcases res with ⟨ps', rSibs⟩
            rw [hrec] at hclimb
            simp only [Option.some.injEq, Prod.mk.injEq] at hclimb
            rcases hclimb with ⟨rfl, _⟩
            have hp0 := hall (x / 2, combine (lvl + 1) (x / 2) vx vy) (by simp)
            dsimp only at hp0
            have htail := ih ys (by simp at hlen; omega) sibs ps' rSibs hrec (fun pv hpv => hall pv (by simp [hpv]))
            by_cases hxy : vx = treeNodeAt combine leafFn lvl x ∧ vy = treeNodeAt combine leafFn lvl y
            · rcases htail with hok | hcol
              · left
                intro xv hmem
                simp only [List.mem_cons] at hmem
                rcases hmem with rfl | rfl | hm
                · exact hxy.1
                · exact hxy.2
                · exact hok xv hm
              · exact Or.inr hcol
            · right
              rw [← pair_combine_even combine leafFn lvl x hpair.1] at hp0
              have hdiff : vx ≠ treeNodeAt combine leafFn lvl x ∨ vy ≠ treeNodeAt combine leafFn lvl (x + 1) := by
                by_cases hx : vx = treeNodeAt combine leafFn lvl x
                · right; intro hy; apply hxy; exact ⟨hx, by rw [hpair.2]; exact hy⟩
                · exact Or.inl hx
              exact ⟨x / 2, vx, vy, treeNodeAt combine leafFn lvl x, treeNodeAt combine leafFn lvl (x + 1), hdiff, hp0⟩
        · rw [ite_eq_right hpair] at hclimb
          cases sibs with
          | nil => cases hclimb
          | cons sib restSibs =>
            dsimp only at hclimb
            cases hrec : octopusClimbLevel (combine (lvl + 1)) ((y, vy) :: ys) restSibs with
            | none => rw [hrec] at hclimb; cases hclimb
            | some res =>
              rcases res with ⟨ps', rSibs⟩
              rw [hrec] at hclimb
              simp only [Option.some.injEq, Prod.mk.injEq] at hclimb
              rcases hclimb with ⟨rfl, _⟩
              have hp0 := hall (x / 2, if x % 2 = 0 then combine (lvl + 1) (x / 2) vx sib else combine (lvl + 1) (x / 2) sib vx) (by simp)
              dsimp only at hp0
              have htail := ih ((y, vy) :: ys) (by simp at hlen; omega) restSibs ps' rSibs hrec (fun pv hpv => hall pv (by simp [hpv]))
              by_cases hx : vx = treeNodeAt combine leafFn lvl x
              · rcases htail with hok | hcol
                · left
                  intro xv hmem
                  simp only [List.mem_cons] at hmem
                  rcases hmem with rfl | hm
                  · exact hx
                  · exact hok xv (by simp [hm])
                · exact Or.inr hcol
              · right
                by_cases heven : x % 2 = 0
                · rw [ite_eq_left heven] at hp0
                  rw [← pair_combine_even combine leafFn lvl x heven] at hp0
                  exact ⟨x / 2, vx, sib, treeNodeAt combine leafFn lvl x, treeNodeAt combine leafFn lvl (x + 1), Or.inl hx, hp0⟩
                · rw [ite_eq_right heven] at hp0
                  rw [← pair_combine_odd combine leafFn lvl x heven] at hp0
                  exact ⟨x / 2, sib, vx, treeNodeAt combine leafFn lvl (x - 1), treeNodeAt combine leafFn lvl x, Or.inr hx, hp0⟩

/-- **Constructive Multi-Level Octopus Forgery Collision Extractor (`SPEC.md §10.2`):**
    If climbing `rem` levels from `cur` yields honest nodes at level `lvl + rem`, then EITHER
    every input `(x, vx) ∈ cur` matches the honest level-`lvl` node `treeNodeAt combine leafFn lvl x`,
    OR there is an explicit internal `NODE` 2nd-preimage collision at some `level ∈ [lvl + 1, lvl + rem]`! -/
theorem octopus_forgery_collision_aux {H : Type} (combine : Nat → Nat → H → H → H) (leafFn : Nat → H)
    (lvl rem : Nat) :
    ∀ (cur : List (Nat × H)) (sibs : List H) (top : List (Nat × H)) (remSibs : List H),
      octopusClimbAux combine lvl rem cur sibs = some (top, remSibs) →
      (∀ pv ∈ top, pv.2 = treeNodeAt combine leafFn (lvl + rem) pv.1) →
      (∀ xv ∈ cur, xv.2 = treeNodeAt combine leafFn lvl xv.1) ∨
      ∃ level p L₁ R₁ L₂ R₂,
        lvl + 1 ≤ level ∧ level ≤ lvl + rem ∧
        (L₁ ≠ L₂ ∨ R₁ ≠ R₂) ∧
        combine level p L₁ R₁ = combine level p L₂ R₂ := by
  induction rem generalizing lvl with
  | zero =>
    intro cur sibs top remSibs hclimb hall
    simp only [octopusClimbAux, Option.some.injEq, Prod.mk.injEq] at hclimb
    rcases hclimb with ⟨rfl, _⟩
    left; simpa using hall
  | succ rem ih =>
    intro cur sibs top remSibs hclimb hall
    simp only [octopusClimbAux] at hclimb
    cases h1 : octopusClimbLevel (combine (lvl + 1)) cur sibs with
    | none => rw [h1] at hclimb; cases hclimb
    | some mid =>
      rcases mid with ⟨ps, rSibs⟩
      rw [h1] at hclimb
      have hadd : lvl + 1 + rem = lvl + (rem + 1) := by omega
      have hmid := ih (lvl + 1) ps rSibs top remSibs hclimb (by rw [hadd]; exact hall)
      rcases hmid with hps_ok | ⟨level, p, L₁, R₁, L₂, R₂, h1l, h2l, hdiff, hcol⟩
      · have hcur := octopusClimbLevel_collision_len combine leafFn lvl cur.length cur (Nat.le_refl _) sibs ps rSibs h1 hps_ok
        rcases hcur with hok | ⟨p, L₁, R₁, L₂, R₂, hdiff, hcol⟩
        · exact Or.inl hok
        · exact Or.inr ⟨lvl + 1, p, L₁, R₁, L₂, R₂, Nat.le_refl _, by omega, hdiff, hcol⟩
      · exact Or.inr ⟨level, p, L₁, R₁, L₂, R₂, by omega, by omega, hdiff, hcol⟩

/-- **Top-Level Octopus Forgery Collision Theorem (`SPEC.md §10.2`):**
    If an Octopus multi-proof reconstructs to the honest root `treeNodeAt combine leafFn h 0`,
    then EITHER every opened leaf `(idx, v)` matches `leafFn idx`, OR an explicit `NODE` collision exists! -/
theorem octopus_forgery_collision {H : Type} (combine : Nat → Nat → H → H → H) (leafFn : Nat → H)
    (h : Nat) (cur : List (Nat × H)) (sibs : List H) (remSibs : List H)
    (hclimb : octopusClimbAux combine 0 h cur sibs = some ([(0, treeNodeAt combine leafFn h 0)], remSibs)) :
    (∀ xv ∈ cur, xv.2 = leafFn xv.1) ∨
    ∃ level p L₁ R₁ L₂ R₂,
      1 ≤ level ∧ level ≤ h ∧
      (L₁ ≠ L₂ ∨ R₁ ≠ R₂) ∧
      combine level p L₁ R₁ = combine level p L₂ R₂ := by
  have hres := octopus_forgery_collision_aux combine leafFn 0 h cur sibs
    [(0, treeNodeAt combine leafFn h 0)] remSibs hclimb
    (by intro pv hpv; simp only [List.mem_singleton] at hpv; subst hpv; simp)
  simpa [treeNodeAt] using hres

end Blincs
