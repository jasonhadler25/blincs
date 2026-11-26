/-
  BLINCS-128-A2 Declarative Specification: Suite Parameters & Fixed-Width Bytes.
  Matches SPEC.md §3 verbatim (`12+7+7+7` `S-WOTS+Z` + `U-PORS`, `3,292` bytes).
-/

namespace Blincs

/-- Fixed-length byte vector represented declaratively as a total function `Fin n → UInt8`. -/
abbrev Bytes (n : Nat) := Fin n → UInt8

/-- Convert a fixed-length byte vector to a `List UInt8` of exact length `n`. -/
def Bytes.toList {n : Nat} (b : Bytes n) : List UInt8 :=
  List.ofFn b

@[simp]
theorem Bytes.toList_length {n : Nat} (b : Bytes n) : b.toList.length = n := by
  simp [Bytes.toList]

theorem Bytes.toList_injective {n : Nat} {a b : Bytes n} (h : a.toList = b.toList) : a = b := by
  funext i
  have hi : a.toList[i.val]'(by simp) = b.toList[i.val]'(by simp) := by simp [h]
  simpa [Bytes.toList] using hi

/-- Take the first `m` bytes of an `n`-byte vector (`m ≤ n`). -/
def Bytes.take {n : Nat} (m : Nat) (h : m ≤ n) (b : Bytes n) : Bytes m :=
  fun i => b ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/-- Take bytes `offset .. offset + m` of an `n`-byte vector. -/
def Bytes.slice {n : Nat} (offset m : Nat) (h : offset + m ≤ n) (b : Bytes n) : Bytes m :=
  fun i => b ⟨offset + i.val, by omega⟩

/-- Concatenate two fixed-length byte vectors. -/
def Bytes.append {n m : Nat} (a : Bytes n) (b : Bytes m) : Bytes (n + m) :=
  fun i =>
    if hi : i.val < n then
      a ⟨i.val, hi⟩
    else
      b ⟨i.val - n, by omega⟩

-- ---------------------------------------------------------------------------
-- BLINCS-128-A2 Suite Parameters (SPEC.md §3)
-- ---------------------------------------------------------------------------

def N : Nat := 16
def LAYERS : Nat := 4
def LOW_HEIGHT : Nat := 7
def LOW_LEAVES : Nat := 2 ^ LOW_HEIGHT
def TOP_HEIGHT : Nat := 12
def TOP_LEAVES : Nat := 2 ^ TOP_HEIGHT
def HYPER_BITS : Nat := 3 * LOW_HEIGHT + TOP_HEIGHT

def layerHeight (ℓ : Fin LAYERS) : Nat :=
  if ℓ.val = 3 then TOP_HEIGHT else LOW_HEIGHT

def WOTS_N : Nat := 24
def WOTS_W : Nat := 40
def WOTS_STEPS : Nat := WOTS_W - 1
def WOTS_SUM : Nat := 468
def WOTS_Z : Nat := 8
def WOTS_CTR_LEN : Nat := 2

def UPORS_HEIGHT : Nat := 10
def UPORS_LEAVES : Nat := 2 ^ UPORS_HEIGHT
def UPORS_N : Nat := 3
def UPORS_W : Nat := 24
def UPORS_STEPS : Nat := UPORS_W - 1
def UPORS_SUM : Nat := 42
def UPORS_C : Nat := 376
def UPORS_K : Nat := 10
def UPORS_M_MAX : Nat := 44
def UPORS_CTR_LEN : Nat := 4
def UPORS_SELECT_MAX_DRAWS : Nat := 22
def UPORS_LAYER : Nat := 128
def MAX_CONTEXT_LEN : Nat := 255

def UPORS_LEN : Nat := UPORS_CTR_LEN + (UPORS_K * UPORS_N + UPORS_M_MAX) * N
def LOW_LAYER_LEN : Nat := WOTS_CTR_LEN + (WOTS_N + LOW_HEIGHT) * N
def TOP_LAYER_LEN : Nat := WOTS_CTR_LEN + (WOTS_N + TOP_HEIGHT) * N
def IMPRINT_LEN : Nat := 2 * N + UPORS_LEN + 3 * LOW_LAYER_LEN + TOP_LAYER_LEN

-- Exact arithmetic identities verified by the Lean kernel.
theorem params_hyper_bits : HYPER_BITS = 33 := rfl
theorem params_low_leaves : LOW_LEAVES = 128 := rfl
theorem params_top_leaves : TOP_LEAVES = 4096 := rfl
theorem params_upors_leaves : UPORS_LEAVES = 1024 := rfl
theorem params_wots_verify_steps : WOTS_N * WOTS_STEPS - WOTS_SUM = 468 := rfl
theorem params_upors_leaf_fits_blake3_block : 16 + UPORS_N * N = 64 := rfl
theorem params_upors_verify_steps : UPORS_N * UPORS_STEPS - UPORS_SUM = 27 := rfl
theorem params_upors_len : UPORS_LEN = 1188 := rfl
theorem params_low_layer_len : LOW_LAYER_LEN = 498 := rfl
theorem params_top_layer_len : TOP_LAYER_LEN = 578 := rfl
theorem params_imprint_len : IMPRINT_LEN = 3292 := rfl
theorem params_select_bits_fit : UPORS_SELECT_MAX_DRAWS * UPORS_HEIGHT + HYPER_BITS = 253 := rfl
theorem params_tree_fits_tweak : 2 ^ HYPER_BITS < 2 ^ 48 := by decide
theorem params_layers_disjoint : LAYERS ≤ UPORS_LAYER ∧ UPORS_LAYER < 256 := by decide

-- Suite-separated key-derivation context strings (SPEC.md §4).
def CTX_SECRET_VALUES : String := "BLINCS-128-A2 2026-11-26 secret values"
def CTX_CONTENT_SALT  : String := "BLINCS-128-A2 2026-11-26 content salt"
def CTX_RANDOMIZER    : String := "BLINCS-128-A2 2026-11-26 randomizer"
def CTX_PUBLIC_SEED   : String := "BLINCS-128-A2 2026-11-26 public seed"
def CTX_PUBLIC_HASH   : String := "BLINCS-128-A2 2026-11-26 public hash"
def CTX_CONTENT       : String := "BLINCS-128-A2 2026-11-26 content"

/-- All 6 algorithm key-derivation context strings are pairwise distinct. -/
theorem key_contexts_distinct :
    [CTX_SECRET_VALUES, CTX_CONTENT_SALT, CTX_RANDOMIZER,
     CTX_PUBLIC_SEED, CTX_PUBLIC_HASH, CTX_CONTENT].Nodup := by
  decide

end Blincs
