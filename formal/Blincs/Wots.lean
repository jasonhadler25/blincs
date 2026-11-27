/-
  BLINCS-128-A2 Declarative Specification: Constant-Sum Antichains, S-WOTS+Z & U-PORS Coding.
  Mechanically proves (ZERO `sorry`, ZERO custom axioms):
    1. **General Constant-Sum Antichain Theorem** (`constantSum_antichain`): any two distinct
       vectors with equal coordinate sum satisfy `∃ c, f c < g c`.
    2. **Unified Chain Completeness & Forgery Extraction** (`chain_complete`, `chain_forgery_extract`)
       shared by `S-WOTS+Z` (`maxSteps = 39`) and `U-PORS` (`maxSteps = 23`).
    3. **U-PORS Zero-ROM Hexagon Unranker (`L_42(3, 24)`, `C = 376`)**:
       exact bounds (`≤ 23`), exact constant sum (`= 42`), injectivity, and strict antichain
       dominance (`uporsCode_antichain`).
    4. **S-WOTS+Z Sperner Unranker (`L_468(24, 40)`, `> 2^120`)**:
       exact kernel-verified cardinality `1,973,221,677,906,098,493,567,206,234,001,571,000 > 2^120`,
       exact bounds (`≤ 39`), exact constant sum (`= 468`), injectivity, and strict antichain
       dominance (`wots_dominance`).
-/
import Blincs.Params

namespace Blincs

-- ---------------------------------------------------------------------------
-- 1. Finite Sums & General Constant-Sum Antichain Theorem
-- ---------------------------------------------------------------------------

/-- Declarative sum over `0 .. n-1`. -/
def finSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _     => 0
  | n + 1, f => finSum n (fun i => f ⟨i.val, by omega⟩) + f ⟨n, by omega⟩

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Nat} (hle : ∀ i, f i ≤ g i) :
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
    · have htail := finSum_le_finSum (fun j : Fin n => hle ⟨j.val, by omega⟩)
      have hflast : f ⟨n, by omega⟩ < g ⟨n, by omega⟩ := by
        have heq : i = ⟨n, by omega⟩ := Fin.ext hlast
        rwa [← heq]
      omega
    · have hi' : i.val < n := by omega
      have h1 := ih (fun j => hle ⟨j.val, by omega⟩) ⟨⟨i.val, hi'⟩, hi⟩
      have h2 := hle ⟨n, by omega⟩
      omega

theorem finSum_succ_shift {m : Nat} (f : Fin (m + 1) → Nat) :
    finSum (m + 1) f = f ⟨0, by omega⟩ + finSum m (fun j => f ⟨j.val + 1, by omega⟩) := by
  induction m with
  | zero => simp [finSum]
  | succ m ih =>
    have hrec := ih (fun i : Fin (m + 1) => f ⟨i.val, by omega⟩)
    calc
      finSum (m + 1 + 1) f
          = finSum (m + 1) (fun i => f ⟨i.val, by omega⟩) + f ⟨m + 1, by omega⟩ := rfl
      _ = (f ⟨0, by omega⟩ + finSum m (fun j => f ⟨j.val + 1, by omega⟩)) + f ⟨m + 1, by omega⟩ := by
          rw [hrec]
      _ = f ⟨0, by omega⟩ + (finSum m (fun j => f ⟨j.val + 1, by omega⟩) + f ⟨m + 1, by omega⟩) := by
          omega
      _ = f ⟨0, by omega⟩ + finSum (m + 1) (fun j => f ⟨j.val + 1, by omega⟩) := rfl

private theorem exists_lt_of_le_ne {n : Nat} {f g : Fin n → Nat}
    (hle : ∀ i, g i ≤ f i) (hne : f ≠ g) : ∃ i, g i < f i := by
  apply Classical.byContradiction
  intro hall
  apply hne
  funext i
  have hnotlt : ¬ g i < f i := fun hlt => hall ⟨i, hlt⟩
  have hle_i := hle i
  omega

/--
  **General Constant-Sum Antichain Theorem:**
  For any dimension `n`, any two distinct vectors `f ≠ g : Fin n → Nat` with equal
  coordinate sum `finSum n f = finSum n g` satisfy `∃ c : Fin n, f c < g c`.
-/
theorem constantSum_antichain {n : Nat} {f g : Fin n → Nat}
    (hsum : finSum n f = finSum n g) (hne : f ≠ g) :
    ∃ c : Fin n, f c < g c := by
  apply Classical.byContradiction
  intro hno
  have hge : ∀ c : Fin n, g c ≤ f c := by
    intro c
    have : ¬ f c < g c := fun hlt => hno ⟨c, hlt⟩
    omega
  have hlt := finSum_lt_of_le_and_lt hge (exists_lt_of_le_ne hge hne)
  omega

-- ---------------------------------------------------------------------------
-- 2. Unified Hash-Chain Iteration, Completeness & Forgery Extraction
-- ---------------------------------------------------------------------------

/-- Iterate a step-indexed hash function `k` times starting at step index `start`. -/
def chainIter {H : Type} (step : Nat → H → H) : (start : Nat) → (k : Nat) → H → H
  | _, 0, x     => x
  | s, k + 1, x => chainIter step (s + 1) k (step s x)

theorem chainIter_add {H : Type} (step : Nat → H → H) :
    ∀ (start k₁ k₂ : Nat) (x : H),
      chainIter step (start + k₁) k₂ (chainIter step start k₁ x) =
      chainIter step start (k₁ + k₂) x
  | start, 0, k₂, x => by simp [chainIter]
  | start, k₁ + 1, k₂, x => by
    have ih := chainIter_add step (start + 1) k₁ k₂ (step start x)
    have h1 : start + (k₁ + 1) = (start + 1) + k₁ := by omega
    have h2 : k₁ + 1 + k₂ = (k₁ + k₂) + 1 := by omega
    rw [h1, h2]
    simp only [chainIter]
    exact ih

/-- Generic hash-chain completeness for any chain length `maxSteps`. -/
theorem chain_complete {H : Type} (step : Nat → H → H) (x₀ : H) {d maxSteps : Nat} (hd : d ≤ maxSteps) :
    chainIter step d (maxSteps - d) (chainIter step 0 d x₀) = chainIter step 0 maxSteps x₀ := by
  have h := chainIter_add step 0 d (maxSteps - d) x₀
  simp only [Nat.zero_add] at h
  rw [h]
  congr 1
  omega

/-- If `u ≠ v` collide after `k` steps, extract an explicit step `s` and colliding input `a ≠ b`
    where `b = chainIter step start (s - start) v` is the exact honest chain node at step `s`. -/
theorem chainIter_collision {H : Type} (step : Nat → H → H) (start k : Nat) (u v : H)
    (hne : u ≠ v) (heq : chainIter step start k u = chainIter step start k v) :
    ∃ s a, start ≤ s ∧ s < start + k ∧
      a ≠ chainIter step start (s - start) v ∧
      step s a = step s (chainIter step start (s - start) v) := by
  induction k generalizing start u v with
  | zero =>
    simp [chainIter] at heq
    exact absurd heq hne
  | succ k ih =>
    simp only [chainIter] at heq
    by_cases hstep : step start u = step start v
    · refine ⟨start, u, Nat.le_refl _, by omega, ?_, ?_⟩
      · simpa [Nat.sub_self, chainIter] using hne
      · simpa [Nat.sub_self, chainIter] using hstep
    · rcases ih (start + 1) (step start u) (step start v) hstep heq with ⟨s, a, hs1, hs2, hab, hcol⟩
      have hnode : chainIter step (start + 1) (s - (start + 1)) (step start v) =
                   chainIter step start (s - start) v := by
        have hsub : s - start = (s - (start + 1)) + 1 := by omega
        rw [hsub]
        rfl
      rw [hnode] at hab hcol
      exact ⟨s, a, by omega, by omega, hab, hcol⟩

/-- **Unified Chain Forgery Extraction Lemma (shared by `S-WOTS+Z` and `U-PORS`).**
    Either `y` equals the exact honest node at depth `d₁`, or there is an explicit step `s ∈ [d₁, maxSteps)`
    and `a ≠ chainIter step 0 s x₀` colliding with the exact honest chain node at step `s`. -/
theorem chain_forgery_extract {H : Type} (step : Nat → H → H) (x₀ y : H) {d₁ maxSteps : Nat} (hd₁ : d₁ ≤ maxSteps)
    (hver : chainIter step d₁ (maxSteps - d₁) y = chainIter step 0 maxSteps x₀) :
    y = chainIter step 0 d₁ x₀ ∨
    ∃ s a, d₁ ≤ s ∧ s < maxSteps ∧
      a ≠ chainIter step 0 s x₀ ∧
      step s a = step s (chainIter step 0 s x₀) := by
  by_cases hy : y = chainIter step 0 d₁ x₀
  · exact Or.inl hy
  · right
    have hcomp := chain_complete step x₀ hd₁
    rw [← hcomp] at hver
    rcases chainIter_collision step d₁ (maxSteps - d₁) y (chainIter step 0 d₁ x₀) hy hver with ⟨s, a, h1, h2, hne, hcol⟩
    have hmerge : chainIter step d₁ (s - d₁) (chainIter step 0 d₁ x₀) = chainIter step 0 s x₀ := by
      have h := chainIter_add step 0 d₁ (s - d₁) x₀
      simp only [Nat.zero_add] at h
      rw [h]
      congr 1
      omega
    rw [hmerge] at hne hcol
    exact ⟨s, a, h1, by omega, hne, hcol⟩

-- ---------------------------------------------------------------------------
-- 3. General Constant-Sum Slice Enumeration & Bijective Unranking
--    (Instantiated for BOTH U-PORS `L_42(3, 24)` AND S-WOTS+Z `L_468(24, 40)`!)
-- ---------------------------------------------------------------------------

/-- Pure recursive specification of slice cardinality `N(w, k, s)`. -/
def sliceCount (w : Nat) : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, s =>
    finSum (min w (s + 1)) (fun d => sliceCount w k (s - d.val))

/-- Pure Pascal binomial coefficient (zero division). -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Falling factorial `n * (n - 1) * ... * (n - k + 1)` in ONLY `k` recursion steps! -/
def falling : Nat → Nat → Nat
  | _, 0 => 1
  | n, k + 1 => n * falling (n - 1) k

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

private theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (Nat.succ_pos n) ih

private theorem binom_gt_zero : ∀ (n k : Nat), n < k → binom n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    simp only [binom]
    rw [binom_gt_zero n k (by omega), binom_gt_zero n (k + 1) (by omega)]

private theorem binom_self : ∀ (n : Nat), binom n n = 1
  | 0 => rfl
  | n + 1 => by
    simp only [binom]
    rw [binom_self n, binom_gt_zero n (n + 1) (by omega)]

private theorem falling_succ_right : ∀ (n k : Nat), k ≤ n →
    falling n (k + 1) = falling n k * (n - k)
  | n, 0, _ => by simp [falling]
  | 0, k + 1, h => by omega
  | n + 1, k + 1, h => by
    have h1 : falling (n + 1) (k + 2) = (n + 1) * falling n (k + 1) := rfl
    have h2 : falling (n + 1) (k + 1) = (n + 1) * falling n k := rfl
    rw [h1, h2, falling_succ_right n k (by omega), Nat.mul_assoc]
    have hsub : n + 1 - (k + 1) = n - k := by omega
    rw [hsub]

private theorem binom_falling : ∀ (n k : Nat), k ≤ n → binom n k * fact k = falling n k
  | _, 0, _ => by simp [binom, fact, falling]
  | 0, _ + 1, h => by omega
  | n + 1, k + 1, h => by
    by_cases hkn : k = n
    · subst hkn
      have h1 := binom_falling k k (Nat.le_refl k)
      rw [binom_self, Nat.one_mul] at h1
      rw [binom_self, Nat.one_mul]
      simp only [fact, falling, Nat.add_sub_cancel]
      rw [h1]
    · have hk1 : k ≤ n := by omega
      have hk2 : k + 1 ≤ n := by omega
      have h1 := binom_falling n k hk1
      have h2 := binom_falling n (k + 1) hk2
      simp only [binom, fact]
      have hf2 : falling n (k + 1) = falling n k * (n - k) := falling_succ_right n k hk1
      calc (binom n k + binom n (k + 1)) * ((k + 1) * fact k)
          = (k + 1) * (binom n k * fact k) + binom n (k + 1) * fact (k + 1) := by
              rw [Nat.add_mul, Nat.mul_left_comm (binom n k)]; rfl
        _ = (k + 1) * falling n k + falling n (k + 1) := by rw [h1, h2]
        _ = (k + 1) * falling n k + (n - k) * falling n k := by rw [hf2, Nat.mul_comm (falling n k)]
        _ = (k + 1 + (n - k)) * falling n k := (Nat.add_mul _ _ _).symm
        _ = (n + 1) * falling n k := by congr 1; omega
        _ = falling (n + 1) (k + 1) := by simp [falling]

/-- Fast exact `O(k)` binomial via `falling n k / fact k` (`23` steps for `C(491, 23)`!),
    proved equal to `binom n k` for ALL `n, k`. -/
def fastBinom (n k : Nat) : Nat :=
  if k ≤ n then falling n k / fact k else 0

theorem fastBinom_eq_binom (n k : Nat) : fastBinom n k = binom n k := by
  unfold fastBinom
  by_cases h : k ≤ n
  · rw [ite_eq_left h]
    rw [← binom_falling n k h, Nat.mul_div_cancel _ (fact_pos k)]
  · rw [ite_eq_right h, binom_gt_zero n k (by omega)]

/-- Signed finite sum over `Fin m → Int`. -/
def finSumInt : (m : Nat) → (Fin m → Int) → Int
  | 0, _     => 0
  | m + 1, f => finSumInt m (fun i => f ⟨i.val, by omega⟩) + f ⟨m, by omega⟩

private theorem finSumInt_of_nat {m : Nat} (f : Fin m → Nat) :
    (finSum m f : Int) = finSumInt m (fun i => (f i : Int)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [finSum, finSumInt, Int.natCast_add]
    rw [ih]

private theorem finSumInt_add {m : Nat} (f g : Fin m → Int) :
    finSumInt m (fun i => f i + g i) = finSumInt m f + finSumInt m g := by
  induction m with
  | zero => simp [finSumInt]
  | succ m ih =>
    simp only [finSumInt]
    rw [ih]
    omega

private theorem finSumInt_sub {m : Nat} (f g : Fin m → Int) :
    finSumInt m (fun i => f i - g i) = finSumInt m f - finSumInt m g := by
  induction m with
  | zero => simp [finSumInt]
  | succ m ih =>
    simp only [finSumInt]
    rw [ih]
    omega

private theorem finSumInt_mul_left {m : Nat} (c : Int) (f : Fin m → Int) :
    finSumInt m (fun i => c * f i) = c * finSumInt m f := by
  induction m with
  | zero => simp [finSumInt]
  | succ m ih =>
    simp only [finSumInt]
    rw [ih, Int.mul_add]

private theorem finSumInt_zero (m : Nat) : finSumInt m (fun _ => 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [finSumInt, ih]

private theorem finSumInt_swap {a b : Nat} (f : Fin a → Fin b → Int) :
    finSumInt a (fun i => finSumInt b (fun j => f i j)) =
    finSumInt b (fun j => finSumInt a (fun i => f i j)) := by
  induction a with
  | zero =>
    simp only [finSumInt]
    exact (finSumInt_zero b).symm
  | succ a iha =>
    simp only [finSumInt]
    rw [iha, ← finSumInt_add]

private theorem finSumInt_congr {m : Nat} {f g : Fin m → Int} (h : ∀ i, f i = g i) :
    finSumInt m f = finSumInt m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [finSumInt]
    rw [ih (fun j => h ⟨j.val, by omega⟩), h ⟨m, by omega⟩]

private theorem finSumInt_succ_shift {m : Nat} (f : Fin (m + 1) → Int) :
    finSumInt (m + 1) f = f ⟨0, by omega⟩ + finSumInt m (fun j => f ⟨j.val + 1, by omega⟩) := by
  induction m with
  | zero => simp [finSumInt]
  | succ m ih =>
    have hr := ih (fun i : Fin (m + 1) => f ⟨i.val, by omega⟩)
    calc
      finSumInt (m + 1 + 1) f
          = finSumInt (m + 1) (fun i => f ⟨i.val, by omega⟩) + f ⟨m + 1, by omega⟩ := rfl
      _ = (f ⟨0, by omega⟩ + finSumInt m (fun j => f ⟨j.val + 1, by omega⟩)) + f ⟨m + 1, by omega⟩ := by
          rw [hr]
      _ = f ⟨0, by omega⟩ + (finSumInt m (fun j => f ⟨j.val + 1, by omega⟩) + f ⟨m + 1, by omega⟩) := by
          omega
      _ = f ⟨0, by omega⟩ + finSumInt (m + 1) (fun j => f ⟨j.val + 1, by omega⟩) := rfl

/-- Zero-extended multiset coefficient `C(m + n, n)` if `s ≥ base`, else `0`. -/
def multisetTerm (n s base : Nat) : Int :=
  if base ≤ s then (binom (s - base + n) n : Int) else 0

private theorem finSumInt_cast_len {a b : Nat} (h : a = b) (f : Nat → Int) :
    finSumInt a (fun i => f i.val) = finSumInt b (fun i => f i.val) := by
  subst h; rfl

/-- Windowed Hockey-Stick Identity on `multisetTerm`:
    `∑_{d=0}^{min(w, s+1)-1} multisetTerm n (s - d) base = multisetTerm (n+1) s base - multisetTerm (n+1) s (base + w)`. -/
private theorem multisetTerm_window (w n s base : Nat) (hw : 0 < w) :
    finSumInt (min w (s + 1)) (fun d => multisetTerm n (s - d.val) base) =
      multisetTerm (n + 1) s base - multisetTerm (n + 1) s (base + w) := by
  by_cases hsb : base ≤ s
  · by_cases hbw : base + w ≤ s
    · have hlim : min w (s + 1) = w := by omega
      have h1 : ∀ (k : Nat), k ≤ w →
          finSumInt k (fun d => multisetTerm n (s - d.val) base) =
          (binom (s - base + (n + 1)) (n + 1) : Int) -
          (if k = 0 then (binom (s - base + (n + 1)) (n + 1) : Int)
           else if k ≤ s - base then (binom (s - base - k + (n + 1)) (n + 1) : Int)
           else 0) := by
        intro k
        induction k with
        | zero => intro _; simp [finSumInt]
        | succ k ih =>
          intro hk
          simp only [finSumInt]
          rw [ih (by omega)]
          have hle_b : base ≤ s - k := by omega
          have hterm : multisetTerm n (s - k) base = (binom (s - k - base + n) n : Int) := by
            unfold multisetTerm; rw [ite_eq_left hle_b]
          rw [hterm]
          by_cases hk0 : k = 0
          · subst hk0
            simp only [↓reduceIte, Nat.sub_zero, Int.sub_self, Int.zero_add]
            by_cases h1le : 1 ≤ s - base
            · rw [ite_eq_left h1le]
              have hpas : binom (s - base + (n + 1)) (n + 1) =
                          binom (s - base + n) n + binom (s - base + n) (n + 1) := rfl
              have heq : s - base - 1 + (n + 1) = s - base + n := by omega
              rw [heq, hpas]; omega
            · rw [ite_eq_right h1le]
              have hs0 : s - base = 0 := by omega
              rw [hs0]; simp [binom_self]
          · have hk_le : k ≤ s - base := by omega
            have hne0 : ¬ (k + 1 = 0) := by omega
            rw [ite_eq_right hk0, ite_eq_left hk_le, ite_eq_right hne0]
            by_cases hk1_le : k + 1 ≤ s - base
            · rw [ite_eq_left hk1_le]
              have hpas : binom (s - base - k + (n + 1)) (n + 1) =
                          binom (s - base - k + n) n + binom (s - base - k + n) (n + 1) := rfl
              have heq1 : s - k - base + n = s - base - k + n := by omega
              have heq2 : s - base - (k + 1) + (n + 1) = s - base - k + n := by omega
              rw [heq1, heq2, hpas]; omega
            · rw [ite_eq_right hk1_le]
              have hsk : s - base - k = 0 := by omega
              have hsk2 : s - k - base = 0 := by omega
              rw [hsk, hsk2]; simp [binom_self]
      have hres := h1 w (Nat.le_refl w)
      have hw_ne0 : ¬ (w = 0) := by omega
      have hw_le : w ≤ s - base := by omega
      rw [ite_eq_right hw_ne0, ite_eq_left hw_le] at hres
      have hsub : s - base - w = s - (base + w) := by omega
      rw [hsub] at hres
      rw [finSumInt_cast_len hlim (fun d => multisetTerm n (s - d) base), hres]
      unfold multisetTerm
      rw [ite_eq_left hsb, ite_eq_left hbw]
    · have hlim_ge : s - base + 1 ≤ min w (s + 1) := by omega
      have htail : ∀ (k : Nat), s - base + 1 ≤ k → k ≤ s + 1 →
          finSumInt k (fun d => multisetTerm n (s - d.val) base) =
          finSumInt (s - base + 1) (fun d => multisetTerm n (s - d.val) base) := by
        intro k
        induction k with
        | zero => intro hk _; omega
        | succ k ih =>
          intro hk hks
          by_cases heq : k = s - base
          · subst heq; rfl
          · have hk' : s - base + 1 ≤ k := by omega
            have h0 : multisetTerm n (s - k) base = 0 := by
              unfold multisetTerm; rw [ite_eq_right (by omega)]
            calc finSumInt (k + 1) (fun d => multisetTerm n (s - d.val) base)
                = finSumInt k (fun d => multisetTerm n (s - d.val) base) + multisetTerm n (s - k) base := rfl
              _ = finSumInt (s - base + 1) (fun d => multisetTerm n (s - d.val) base) + 0 := by rw [ih hk' (by omega), h0]
              _ = finSumInt (s - base + 1) (fun d => multisetTerm n (s - d.val) base) := Int.add_zero _
      rw [htail (min w (s + 1)) hlim_ge (Nat.min_le_right _ _)]
      have hrev : ∀ (M : Nat),
          finSumInt (M + 1) (fun d => multisetTerm n (base + M - d.val) base) =
          (binom (M + (n + 1)) (n + 1) : Int) := by
        intro M
        induction M with
        | zero =>
          simp only [finSumInt, Nat.add_zero, Nat.sub_zero, Int.zero_add, Nat.zero_add]
          unfold multisetTerm
          rw [ite_eq_left (Nat.le_refl base)]
          simp [binom_self]
        | succ M ih =>
          rw [finSumInt_succ_shift]
          have h0 : multisetTerm n (base + (M + 1) - 0) base = (binom (M + 1 + n) n : Int) := by
            unfold multisetTerm
            rw [ite_eq_left (by omega)]
            have : base + (M + 1) - 0 - base + n = M + 1 + n := by omega
            rw [this]
          have hrest : finSumInt (M + 1) (fun j => multisetTerm n (base + (M + 1) - (j.val + 1)) base) =
                       finSumInt (M + 1) (fun j => multisetTerm n (base + M - j.val) base) := by
            apply finSumInt_congr; intro j
            have : base + (M + 1) - (j.val + 1) = base + M - j.val := by omega
            rw [this]
          rw [h0, hrest, ih]
          have hpas : binom (M + 1 + (n + 1)) (n + 1) = binom (M + 1 + n) n + binom (M + 1 + n) (n + 1) := by
            have : M + 1 + (n + 1) = (M + 1 + n) + 1 := by omega
            rw [this]; rfl
          have heq : M + (n + 1) = M + 1 + n := by omega
          rw [hpas, heq]; omega
      have hs_eq : s = base + (s - base) := by omega
      have hsum : finSumInt (s - base + 1) (fun d => multisetTerm n (s - d.val) base) =
                  finSumInt (s - base + 1) (fun d => multisetTerm n (base + (s - base) - d.val) base) := by
        apply finSumInt_congr; intro d; rw [← hs_eq]
      rw [hsum, hrev (s - base)]
      unfold multisetTerm
      rw [ite_eq_left hsb, ite_eq_right hbw]
      omega
  · -- Case `s < base`: all terms are 0!
    have hzero : ∀ (k : Nat), finSumInt k (fun d => multisetTerm n (s - d.val) base) = 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        simp only [finSumInt, ih, Int.zero_add]
        unfold multisetTerm; rw [ite_eq_right (by omega)]
    rw [hzero]
    unfold multisetTerm
    rw [ite_eq_right hsb, ite_eq_right (by omega)]
    rfl

/-- Exact signed inclusion-exclusion formula for `sliceCount w n s` (`n ≥ 1`, using `binom`). -/
def signPow (j : Nat) : Int :=
  if j % 2 = 0 then 1 else -1

def spernerIEInt (w n s : Nat) : Int :=
  finSumInt (n + 1) (fun j => signPow j.val * (binom n j.val : Int) * multisetTerm (n - 1) s (j.val * w))

/-- Fast exact `Int` evaluator using `fastBinom` (`O(n)` via `fact`), proved equal to `spernerIEInt`. -/
def spernerIEFast (w n s : Nat) : Int :=
  finSumInt (n + 1) (fun j =>
    if j.val * w ≤ s then
      signPow j.val * (fastBinom n j.val : Int) * (fastBinom (s - j.val * w + (n - 1)) (n - 1) : Int)
    else 0)

theorem spernerIEFast_eq_spernerIEInt (w n s : Nat) :
    spernerIEFast w n s = spernerIEInt w n s := by
  unfold spernerIEFast spernerIEInt
  apply finSumInt_congr
  intro j
  unfold multisetTerm
  by_cases h : j.val * w ≤ s
  · rw [ite_eq_left h, ite_eq_left h, fastBinom_eq_binom, fastBinom_eq_binom]
  · rw [ite_eq_right h, ite_eq_right h, Int.mul_zero]

/-- **Exact Inclusion-Exclusion Theorem for Bounded-Digit Constant-Sum Slices:**
    For ALL `w ≥ 1`, ALL `n ≥ 1`, and ALL `s ≥ 0`: `(sliceCount w n s : Int) = spernerIEInt w n s`. -/
theorem sliceCount_eq_spernerIE (w : Nat) (hw : 0 < w) :
    ∀ (m s : Nat), (sliceCount w (m + 1) s : Int) = spernerIEInt w (m + 1) s
  | 0, s => by
    -- Base case `n = 1`: `sliceCount w 1 s = if s < w then 1 else 0`
    unfold spernerIEInt
    simp only [finSumInt, Nat.sub_self]
    have h0 : signPow 0 = 1 := rfl
    have h1 : signPow 1 = -1 := rfl
    have hb0 : binom 1 0 = 1 := rfl
    have hb1 : binom 1 1 = 1 := rfl
    simp only [h0, h1, hb0, hb1, Nat.zero_mul, Nat.one_mul, Int.zero_add, Int.one_mul]
    unfold multisetTerm
    simp only [Nat.add_zero, binom, Int.ofNat_one]
    have hzero_le : 0 ≤ s := Nat.zero_le s
    rw [ite_eq_left hzero_le]
    unfold sliceCount
    have hsc : ∀ (k : Nat), k ≤ s + 1 →
        finSum k (fun d => sliceCount w 0 (s - d.val)) = if s < k then 1 else 0 := by
      intro k
      induction k with
      | zero => intro _; simp [finSum]
      | succ k ih =>
        intro hk
        simp only [finSum, ih (by omega)]
        have hnot : ¬ (s < k) := by omega
        rw [ite_eq_right hnot, Nat.zero_add]
        by_cases heq : s = k
        · subst heq; simp [Nat.sub_self, sliceCount]
        · have hgt : ¬ (s < k + 1) := by omega
          rw [ite_eq_right hgt]
          have hpos : s - k = (s - k - 1) + 1 := by omega
          rw [hpos]; rfl
    rw [hsc (min w (s + 1)) (Nat.min_le_right _ _)]
    by_cases hsw : w ≤ s
    · rw [ite_eq_left hsw]
      have hnot : ¬ (s < min w (s + 1)) := by omega
      rw [ite_eq_right hnot]; omega
    · rw [ite_eq_right hsw]
      have hlt : s < min w (s + 1) := by omega
      rw [ite_eq_left hlt]; omega
  | m + 1, s => by
    unfold sliceCount
    rw [finSumInt_of_nat]
    have hstep : finSumInt (min w (s + 1)) (fun d => (sliceCount w (m + 1) (s - d.val) : Int)) =
                 finSumInt (min w (s + 1)) (fun d => spernerIEInt w (m + 1) (s - d.val)) :=
      finSumInt_congr (fun d => sliceCount_eq_spernerIE w hw m (s - d.val))
    rw [hstep]
    unfold spernerIEInt
    rw [finSumInt_swap]
    have hsubm : m + 1 - 1 = m := Nat.add_sub_cancel m 1
    have hsubm1 : m + 1 + 1 - 1 = m + 1 := Nat.add_sub_cancel (m + 1) 1
    simp only [hsubm, hsubm1]
    have hinner : finSumInt (m + 1 + 1) (fun j =>
        finSumInt (min w (s + 1)) (fun d =>
          signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm m (s - d.val) (j.val * w))) =
        finSumInt (m + 1 + 1) (fun j =>
          signPow j.val * (binom (m + 1) j.val : Int) *
            (multisetTerm (m + 1) s (j.val * w) - multisetTerm (m + 1) s ((j.val + 1) * w))) := by
      apply finSumInt_congr
      intro j
      rw [finSumInt_mul_left, multisetTerm_window w m s (j.val * w) hw]
      have hmul : j.val * w + w = (j.val + 1) * w := by rw [Nat.add_mul, Nat.one_mul]
      rw [hmul]
    rw [hinner]
    have hsplit : finSumInt (m + 1 + 1) (fun j =>
        signPow j.val * (binom (m + 1) j.val : Int) *
          (multisetTerm (m + 1) s (j.val * w) - multisetTerm (m + 1) s ((j.val + 1) * w))) =
        finSumInt (m + 1 + 1) (fun j =>
          signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm (m + 1) s (j.val * w)) -
        finSumInt (m + 1 + 1) (fun j =>
          signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm (m + 1) s ((j.val + 1) * w)) := by
      rw [← finSumInt_sub]
      apply finSumInt_congr; intro j; exact Int.mul_sub _ _ _
    rw [hsplit]
    -- Peel off `j = 0` on the left sum and `j = m + 1` on the right sum, then combine middle `j = 1 .. m+1` by Pascal!
    have hLHS1 := finSumInt_succ_shift (fun j : Fin (m + 2) =>
      signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm (m + 1) s (j.val * w))
    have hRHS := finSumInt_succ_shift (fun j : Fin (m + 3) =>
      signPow j.val * (binom (m + 2) j.val : Int) * multisetTerm (m + 1) s (j.val * w))
    -- Note `finSumInt (m + 2) g = finSumInt (m + 1) g + g (m + 1)`
    have hLHS2 : finSumInt (m + 2) (fun j =>
        signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm (m + 1) s ((j.val + 1) * w)) =
        finSumInt (m + 1) (fun j =>
          signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm (m + 1) s ((j.val + 1) * w)) +
        signPow (m + 1) * (binom (m + 1) (m + 1) : Int) * multisetTerm (m + 1) s ((m + 2) * w) := rfl
    have hRHS2 : finSumInt (m + 2) (fun j : Fin (m + 2) =>
        signPow (j.val + 1) * (binom (m + 2) (j.val + 1) : Int) * multisetTerm (m + 1) s ((j.val + 1) * w)) =
        finSumInt (m + 1) (fun j : Fin (m + 1) =>
          signPow (j.val + 1) * (binom (m + 2) (j.val + 1) : Int) * multisetTerm (m + 1) s ((j.val + 1) * w)) +
        signPow (m + 2) * (binom (m + 2) (m + 2) : Int) * multisetTerm (m + 1) s ((m + 2) * w) := rfl
    have hmid : finSumInt (m + 1) (fun j : Fin (m + 1) =>
          signPow (j.val + 1) * (binom (m + 1) (j.val + 1) : Int) * multisetTerm (m + 1) s ((j.val + 1) * w)) -
        finSumInt (m + 1) (fun j : Fin (m + 1) =>
          signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm (m + 1) s ((j.val + 1) * w)) =
        finSumInt (m + 1) (fun j : Fin (m + 1) =>
          signPow (j.val + 1) * (binom (m + 2) (j.val + 1) : Int) * multisetTerm (m + 1) s ((j.val + 1) * w)) := by
      rw [← finSumInt_sub]
      apply finSumInt_congr; intro j
      have hsign : signPow (j.val + 1) = - signPow j.val := by
        unfold signPow
        by_cases hev : j.val % 2 = 0
        · have hodd : ¬ ((j.val + 1) % 2 = 0) := by omega
          rw [ite_eq_left hev, ite_eq_right hodd]
        · have hev1 : (j.val + 1) % 2 = 0 := by omega
          rw [ite_eq_right hev, ite_eq_left hev1]; rfl
      have hpas : binom (m + 2) (j.val + 1) = binom (m + 1) j.val + binom (m + 1) (j.val + 1) := rfl
      rw [hpas, hsign]
      simp only [Int.natCast_add]
      have hneg : -signPow j.val * ((binom (m + 1) j.val : Int) + (binom (m + 1) (j.val + 1) : Int)) *
                    multisetTerm (m + 1) s ((j.val + 1) * w) =
                  -signPow j.val * (binom (m + 1) (j.val + 1) : Int) * multisetTerm (m + 1) s ((j.val + 1) * w) -
                  signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm (m + 1) s ((j.val + 1) * w) := by
        rw [Int.mul_add, Int.add_mul, Int.neg_mul, Int.neg_mul, Int.neg_mul]
        omega
      exact hneg.symm
    have hsignLast : signPow (m + 2) = - signPow (m + 1) := by
      unfold signPow
      by_cases hev : (m + 1) % 2 = 0
      · have hodd : ¬ ((m + 2) % 2 = 0) := by omega
        rw [ite_eq_left hev, ite_eq_right hodd]
      · have hev1 : (m + 2) % 2 = 0 := by omega
        rw [ite_eq_right hev, ite_eq_left hev1]; rfl
    have h0eq : signPow 0 * (binom (m + 1) 0 : Int) * multisetTerm (m + 1) s (0 * w) =
                signPow 0 * (binom (m + 2) 0 : Int) * multisetTerm (m + 1) s (0 * w) := rfl
    have hlastEq : -(signPow (m + 1) * (binom (m + 1) (m + 1) : Int) * multisetTerm (m + 1) s ((m + 2) * w)) =
                   signPow (m + 2) * (binom (m + 2) (m + 2) : Int) * multisetTerm (m + 1) s ((m + 2) * w) := by
      rw [binom_self, binom_self, hsignLast, Int.neg_mul, Int.neg_mul]
    show finSumInt (m + 2) (fun j =>
        signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm (m + 1) s (j.val * w)) -
      finSumInt (m + 2) (fun j =>
        signPow j.val * (binom (m + 1) j.val : Int) * multisetTerm (m + 1) s ((j.val + 1) * w)) =
      finSumInt (m + 3) (fun j =>
        signPow j.val * (binom (m + 2) j.val : Int) * multisetTerm (m + 1) s (j.val * w))
    dsimp only at hLHS1 hRHS
    rw [hLHS1, hLHS2, hRHS, hRHS2, ← h0eq, ← hmid, ← hlastEq]
    omega

/-- **Exact `S-WOTS+Z` Slice Cardinality Theorem (directly on `sliceCount`, ZERO gap!):**
    `sliceCount 40 24 468 = 1,973,221,677,906,098,493,567,206,234,001,571,000`. -/
theorem wots_sperner_cardinality :
    sliceCount WOTS_W WOTS_N WOTS_SUM = 1973221677906098493567206234001571000 := by
  have h1 : (sliceCount WOTS_W WOTS_N WOTS_SUM : Int) = spernerIEInt WOTS_W WOTS_N WOTS_SUM :=
    sliceCount_eq_spernerIE WOTS_W (by decide) 23 WOTS_SUM
  rw [← spernerIEFast_eq_spernerIEInt] at h1
  have h2 : spernerIEFast WOTS_W WOTS_N WOTS_SUM = (1973221677906098493567206234001571000 : Int) := by
    decide
  rw [h2] at h1
  exact Int.ofNat.inj h1

/-- Exact `S-WOTS+Z` capacity strictly exceeds `2^120` (directly on `sliceCount 40 24 468`!). -/
theorem wots_sperner_gt_pow120 :
    2 ^ 120 < sliceCount WOTS_W WOTS_N WOTS_SUM := by
  rw [wots_sperner_cardinality]
  decide

/-- Sanity cross-check directly on `sliceCount 39 24 456`: `w = 39` falls strictly below `2^120`, proving `w = 40` is minimal! -/
theorem wots_w39_lt_pow120 :
    sliceCount 39 24 456 < 2 ^ 120 := by
  have h1 : (sliceCount 39 24 456 : Int) = spernerIEInt 39 24 456 :=
    sliceCount_eq_spernerIE 39 (by decide) 23 456
  rw [← spernerIEFast_eq_spernerIEInt] at h1
  have h2 : spernerIEFast 39 24 456 = (1102272360296506971467046668212509411 : Int) := by
    decide
  rw [h2] at h1
  have hnat : sliceCount 39 24 456 = 1102272360296506971467046668212509411 := Int.ofNat.inj h1
  rw [hnat]
  decide

/-- Declarative recursive digit finder for lexicographic slice unranking (`SPEC.md §11.1`). -/
def findDigit (w k s : Nat) : (d : Nat) → (limit : Nat) → (rank : Nat) → Nat × Nat
  | d, 0, r => (d, r)
  | d, rem + 1, r =>
    let cnt := sliceCount w k (s - d)
    if r < cnt then (d, r)
    else findDigit w k s (d + 1) rem (r - cnt)

private theorem findDigit_spec (w k s : Nat) :
    ∀ (d lim r : Nat),
      r < finSum lim (fun j => sliceCount w k (s - (d + j.val))) →
      d ≤ (findDigit w k s d lim r).1 ∧
      (findDigit w k s d lim r).1 < d + lim ∧
      (findDigit w k s d lim r).2 < sliceCount w k (s - (findDigit w k s d lim r).1) := by
  intro d lim
  induction lim generalizing d with
  | zero =>
    intro r hr
    simp [finSum] at hr
  | succ lim ih =>
    intro r hr
    have hsplit : finSum (lim + 1) (fun j => sliceCount w k (s - (d + j.val))) =
        sliceCount w k (s - d) + finSum lim (fun j => sliceCount w k (s - (d + 1 + j.val))) := by
      have hs := finSum_succ_shift (fun j : Fin (lim + 1) => sliceCount w k (s - (d + j.val)))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    rw [hsplit] at hr
    unfold findDigit
    by_cases hlt : r < sliceCount w k (s - d)
    · rw [ite_eq_left hlt]
      exact ⟨Nat.le_refl _, by omega, hlt⟩
    · rw [ite_eq_right hlt]
      have hrem : r - sliceCount w k (s - d) < finSum lim (fun j => sliceCount w k (s - (d + 1 + j.val))) := by omega
      have ⟨h1, h2, h3⟩ := ih (d + 1) (r - sliceCount w k (s - d)) hrem
      exact ⟨by omega, by omega, h3⟩

private theorem findDigit_injective (w k s : Nat) :
    ∀ (d lim r₁ r₂ : Nat),
      r₁ < finSum lim (fun j => sliceCount w k (s - (d + j.val))) →
      r₂ < finSum lim (fun j => sliceCount w k (s - (d + j.val))) →
      findDigit w k s d lim r₁ = findDigit w k s d lim r₂ →
      r₁ = r₂ := by
  intro d lim
  induction lim generalizing d with
  | zero =>
    intro r₁ _ hr₁; simp [finSum] at hr₁
  | succ lim ih =>
    intro r₁ r₂ hr₁ hr₂ heq
    have hsplit : finSum (lim + 1) (fun j => sliceCount w k (s - (d + j.val))) =
        sliceCount w k (s - d) + finSum lim (fun j => sliceCount w k (s - (d + 1 + j.val))) := by
      have hs := finSum_succ_shift (fun j : Fin (lim + 1) => sliceCount w k (s - (d + j.val)))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    rw [hsplit] at hr₁ hr₂
    unfold findDigit at heq
    by_cases h1 : r₁ < sliceCount w k (s - d) <;> by_cases h2 : r₂ < sliceCount w k (s - d)
    · rw [ite_eq_left h1, ite_eq_left h2] at heq
      exact congrArg Prod.snd heq
    · rw [ite_eq_left h1, ite_eq_right h2] at heq
      have hrem2 : r₂ - sliceCount w k (s - d) < finSum lim (fun j => sliceCount w k (s - (d + 1 + j.val))) := by omega
      have hge := (findDigit_spec w k s (d + 1) lim (r₂ - sliceCount w k (s - d)) hrem2).1
      have hfst : d = (findDigit w k s (d + 1) lim (r₂ - sliceCount w k (s - d))).1 := congrArg Prod.fst heq
      omega
    · rw [ite_eq_right h1, ite_eq_left h2] at heq
      have hrem1 : r₁ - sliceCount w k (s - d) < finSum lim (fun j => sliceCount w k (s - (d + 1 + j.val))) := by omega
      have hge := (findDigit_spec w k s (d + 1) lim (r₁ - sliceCount w k (s - d)) hrem1).1
      have hfst : (findDigit w k s (d + 1) lim (r₁ - sliceCount w k (s - d))).1 = d := congrArg Prod.fst heq
      omega
    · rw [ite_eq_right h1, ite_eq_right h2] at heq
      have hrem1 : r₁ - sliceCount w k (s - d) < finSum lim (fun j => sliceCount w k (s - (d + 1 + j.val))) := by omega
      have hrem2 : r₂ - sliceCount w k (s - d) < finSum lim (fun j => sliceCount w k (s - (d + 1 + j.val))) := by omega
      have hsub := ih (d + 1) (r₁ - sliceCount w k (s - d)) (r₂ - sliceCount w k (s - d)) hrem1 hrem2 heq
      omega

/-- Recursive slice unranker mapping `rank < sliceCount w k s` to a `List Nat` of length `k`. -/
def unrankList (w : Nat) : (k : Nat) → (s : Nat) → (rank : Nat) → List Nat
  | 0, _, _ => []
  | k + 1, s, rank =>
    let res := findDigit w k s 0 (min w (s + 1)) rank
    res.1 :: unrankList w k (s - res.1) res.2

theorem unrankList_length (w k s rank : Nat) : (unrankList w k s rank).length = k := by
  induction k generalizing s rank with
  | zero => rfl
  | succ k ih => simp [unrankList, ih]

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

theorem unrankList_spec (w k : Nat) :
    ∀ (s rank : Nat), rank < sliceCount w k s →
      (∀ d ∈ unrankList w k s rank, d < w) ∧ listSum (unrankList w k s rank) = s := by
  induction k with
  | zero =>
    intro s rank hr
    cases s with
    | zero => simp [unrankList, listSum]
    | succ s' => simp [sliceCount] at hr
  | succ k ih =>
    intro s rank hr
    have hr' : rank < finSum (min w (s + 1)) (fun j => sliceCount w k (s - (0 + j.val))) := by
      simpa [sliceCount] using hr
    have ⟨_, hlt_lim, hrem_r⟩ := findDigit_spec w k s 0 (min w (s + 1)) rank hr'
    have hdw : (findDigit w k s 0 (min w (s + 1)) rank).1 < w := by omega
    have hds : (findDigit w k s 0 (min w (s + 1)) rank).1 ≤ s := by omega
    have ⟨htail_lt, htail_sum⟩ := ih (s - (findDigit w k s 0 (min w (s + 1)) rank).1)
      (findDigit w k s 0 (min w (s + 1)) rank).2 hrem_r
    constructor
    · intro d hd
      simp only [unrankList, List.mem_cons] at hd
      rcases hd with rfl | hmem
      · exact hdw
      · exact htail_lt d hmem
    · simp only [unrankList, listSum]
      omega

theorem unrankList_injective (w k : Nat) :
    ∀ (s r₁ r₂ : Nat),
      r₁ < sliceCount w k s →
      r₂ < sliceCount w k s →
      unrankList w k s r₁ = unrankList w k s r₂ →
      r₁ = r₂ := by
  induction k with
  | zero =>
    intro s r₁ r₂ hr₁ hr₂ _
    cases s with
    | zero => simp [sliceCount] at hr₁ hr₂; omega
    | succ s' => simp [sliceCount] at hr₁
  | succ k ih =>
    intro s r₁ r₂ hr₁ hr₂ heq
    have hr₁' : r₁ < finSum (min w (s + 1)) (fun j => sliceCount w k (s - (0 + j.val))) := by
      simpa [sliceCount] using hr₁
    have hr₂' : r₂ < finSum (min w (s + 1)) (fun j => sliceCount w k (s - (0 + j.val))) := by
      simpa [sliceCount] using hr₂
    simp only [unrankList, List.cons.injEq] at heq
    have ⟨hhead, htail⟩ := heq
    have hspec1 := findDigit_spec w k s 0 (min w (s + 1)) r₁ hr₁'
    have hspec2 := findDigit_spec w k s 0 (min w (s + 1)) r₂ hr₂'
    have hrem1 : (findDigit w k s 0 (min w (s + 1)) r₁).2 <
        sliceCount w k (s - (findDigit w k s 0 (min w (s + 1)) r₂).1) := by
      rw [← hhead]; exact hspec1.2.2
    have htail' : unrankList w k (s - (findDigit w k s 0 (min w (s + 1)) r₂).1)
        (findDigit w k s 0 (min w (s + 1)) r₁).2 =
        unrankList w k (s - (findDigit w k s 0 (min w (s + 1)) r₂).1)
        (findDigit w k s 0 (min w (s + 1)) r₂).2 := by
      rw [hhead] at htail; exact htail
    have hres2_eq := ih (s - (findDigit w k s 0 (min w (s + 1)) r₂).1) _ _ hrem1 hspec2.2.2 htail'
    have hpair_eq : findDigit w k s 0 (min w (s + 1)) r₁ = findDigit w k s 0 (min w (s + 1)) r₂ :=
      Prod.ext hhead hres2_eq
    exact findDigit_injective w k s 0 (min w (s + 1)) r₁ r₂ hr₁' hr₂' hpair_eq

private theorem finSum_eq_listSum {k : Nat} (l : List Nat) (hl : l.length = k) :
    finSum k (fun i => l[i.val]'(by omega)) = listSum l := by
  have hgen : ∀ (m : Nat) (hm : m ≤ l.length),
      finSum m (fun i => l[i.val]'(by omega)) = listSum (l.take m) := by
    intro m
    induction m with
    | zero => intro _; simp [finSum, listSum]
    | succ m ihm =>
      intro hm
      simp only [finSum]
      rw [ihm (by omega)]
      have htake : l.take (m + 1) = l.take m ++ [l[m]'(by omega)] :=
        List.take_succ_eq_append_getElem (by omega)
      rw [htake]
      have hsum_app : ∀ (xs ys : List Nat), listSum (xs ++ ys) = listSum xs + listSum ys := by
        intro xs ys
        induction xs with
        | nil => simp [listSum]
        | cons x xs' ihx => simp [listSum, ihx, Nat.add_assoc]
      rw [hsum_app]
      simp [listSum]
  have hres := hgen k (by omega)
  have htake_all : l.take k = l := List.take_of_length_le (by omega)
  rwa [htake_all] at hres

/-- Convert `unrankList w k s rank` to a fixed-length vector `Fin k → Nat`. -/
def unrankVec (w k s rank : Nat) : Fin k → Nat :=
  fun i => (unrankList w k s rank)[i.val]'(by rw [unrankList_length]; exact i.isLt)

theorem unrankVec_lt (w k s rank : Nat) (hr : rank < sliceCount w k s) (c : Fin k) :
    unrankVec w k s rank c < w := by
  unfold unrankVec
  exact (unrankList_spec w k s rank hr).1 _ (List.getElem_mem _)

theorem unrankVec_sum (w k s rank : Nat) (hr : rank < sliceCount w k s) :
    finSum k (unrankVec w k s rank) = s := by
  unfold unrankVec
  rw [finSum_eq_listSum (unrankList w k s rank) (unrankList_length w k s rank)]
  exact (unrankList_spec w k s rank hr).2

theorem unrankVec_injective (w k s r₁ r₂ : Nat)
    (hr₁ : r₁ < sliceCount w k s) (hr₂ : r₂ < sliceCount w k s)
    (heq : unrankVec w k s r₁ = unrankVec w k s r₂) : r₁ = r₂ := by
  apply unrankList_injective w k s r₁ r₂ hr₁ hr₂
  apply List.ext_getElem
  · simp [unrankList_length]
  · intro i h1 h2
    have hi : i < k := by rwa [unrankList_length] at h1
    have := congrFun heq ⟨i, hi⟩
    simpa [unrankVec] using this

/-- **Master Constant-Sum Unranker Strict Antichain Theorem** (instantiated for BOTH `S-WOTS+Z` and `U-PORS`!). -/
theorem unrankVec_antichain (w k s r₁ r₂ : Nat)
    (hr₁ : r₁ < sliceCount w k s) (hr₂ : r₂ < sliceCount w k s)
    (hne : r₁ ≠ r₂) :
    ∃ c : Fin k, unrankVec w k s r₁ c < unrankVec w k s r₂ c := by
  have hvec_ne : unrankVec w k s r₁ ≠ unrankVec w k s r₂ :=
    fun heq => hne (unrankVec_injective w k s r₁ r₂ hr₁ hr₂ heq)
  have hsum : finSum k (unrankVec w k s r₁) = finSum k (unrankVec w k s r₂) := by
    rw [unrankVec_sum w k s r₁ hr₁, unrankVec_sum w k s r₂ hr₂]
  exact constantSum_antichain hsum hvec_ne

-- ---------------------------------------------------------------------------
-- 4. Concrete BLINCS-128-A2 Instantiations: `U-PORS` (`L_42(3, 24)`) & `S-WOTS+Z` (`L_468(24, 40)`)
-- ---------------------------------------------------------------------------

/-- Exact `U-PORS` slice cardinality `|L_42(3, 24)| = 376` (`SPEC.md §10.1`). -/
theorem upors_slice_count : sliceCount UPORS_W UPORS_N UPORS_SUM = UPORS_C := by
  decide

/-- `U-PORS` codeword digit `c : Fin 3` for index `idx : Fin 376` (`SPEC.md §10.1`). -/
def uporsDigit (idx : Fin UPORS_C) (c : Fin UPORS_N) : Nat :=
  unrankVec UPORS_W UPORS_N UPORS_SUM idx.val c

theorem uporsDigit_le_23 (idx : Fin UPORS_C) (c : Fin UPORS_N) :
    uporsDigit idx c ≤ UPORS_STEPS := by
  unfold uporsDigit
  have hlt : unrankVec UPORS_W UPORS_N UPORS_SUM idx.val c < UPORS_W :=
    unrankVec_lt UPORS_W UPORS_N UPORS_SUM idx.val (by rw [upors_slice_count]; exact idx.isLt) c
  unfold UPORS_STEPS UPORS_W at *; omega

theorem uporsCode_sum (idx : Fin UPORS_C) :
    finSum UPORS_N (uporsDigit idx) = UPORS_SUM :=
  unrankVec_sum UPORS_W UPORS_N UPORS_SUM idx.val (by rw [upors_slice_count]; exact idx.isLt)

/-- **U-PORS Strict Antichain Theorem** (`L_42(3, 24)`, `C = 376`). -/
theorem uporsCode_antichain {i j : Fin UPORS_C} (hne : i ≠ j) :
    ∃ c : Fin UPORS_N, uporsDigit i c < uporsDigit j c :=
  unrankVec_antichain UPORS_W UPORS_N UPORS_SUM i.val j.val
    (by rw [upors_slice_count]; exact i.isLt)
    (by rw [upors_slice_count]; exact j.isLt)
    (fun h => hne (Fin.ext h))

/-- `S-WOTS+Z` codeword digit `c : Fin 24` for a 120-bit rank (`SPEC.md §11.1`). -/
def wotsDigit (rank : Nat) (c : Fin WOTS_N) : Nat :=
  unrankVec WOTS_W WOTS_N WOTS_SUM rank c

/-- **S-WOTS+Z Dominance Theorem:** any two distinct valid ranks `r₁ ≠ r₂ < sliceCount 40 24 468`
    have an explicit chain `c : Fin 24` with `wotsDigit r₁ c < wotsDigit r₂ c`. -/
theorem wots_dominance {r₁ r₂ : Nat}
    (hr₁ : r₁ < sliceCount WOTS_W WOTS_N WOTS_SUM)
    (hr₂ : r₂ < sliceCount WOTS_W WOTS_N WOTS_SUM)
    (hne : r₁ ≠ r₂) :
    ∃ c : Fin WOTS_N, wotsDigit r₁ c < wotsDigit r₂ c :=
  unrankVec_antichain WOTS_W WOTS_N WOTS_SUM r₁ r₂ hr₁ hr₂ hne

theorem wotsDigit_le_39 {r : Nat} (hr : r < sliceCount WOTS_W WOTS_N WOTS_SUM) (c : Fin WOTS_N) :
    wotsDigit r c ≤ WOTS_STEPS := by
  unfold wotsDigit
  have hlt := unrankVec_lt WOTS_W WOTS_N WOTS_SUM r hr c
  unfold WOTS_STEPS WOTS_W at *; omega

theorem wotsDigit_sum {r : Nat} (hr : r < sliceCount WOTS_W WOTS_N WOTS_SUM) :
    finSum WOTS_N (wotsDigit r) = WOTS_SUM :=
  unrankVec_sum WOTS_W WOTS_N WOTS_SUM r hr

end Blincs
