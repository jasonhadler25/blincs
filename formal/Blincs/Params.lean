/-
  BLINCS-128-7x5 Declarative Specification: Suite Parameters & Fixed-Width Bytes.
  Matches SPEC.md §3 verbatim (U-FORS unified height-5 architecture).
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
-- BLINCS-128-7x5 Suite Parameters (SPEC.md §3)
-- ---------------------------------------------------------------------------

def N : Nat := 16
def LAYERS : Nat := 7
def TREE_HEIGHT : Nat := 5
def TREE_LEAVES : Nat := 2 ^ TREE_HEIGHT
def HYPER_BITS : Nat := LAYERS * TREE_HEIGHT
def W : Nat := 16
def CHAIN_STEPS : Nat := W - 1
def MSG_CHAINS : Nat := 32
def CSUM_CHAINS : Nat := 3
def CHAINS : Nat := MSG_CHAINS + CSUM_CHAINS

def UFORS_TREES : Nat := 15
def UFORS_CHAINS : Nat := 3
def UFORS_W : Nat := 10
def UFORS_STEPS : Nat := UFORS_W - 1
def UFORS_SUM : Nat := 16
def UFORS_CODE_BITS : Nat := 6
def UFORS_CODE_LEN : Nat := 2 ^ UFORS_CODE_BITS
def UFORS_LAYER_BASE : Nat := 128
def MAX_CONTEXT_LEN : Nat := 255

def UFORS_TREE_LEN : Nat := (UFORS_CHAINS + TREE_HEIGHT) * N
def UFORS_LEN : Nat := UFORS_TREES * UFORS_TREE_LEN
def LAYER_LEN : Nat := (CHAINS + TREE_HEIGHT) * N
def IMPRINT_LEN : Nat := 2 * N + UFORS_LEN + LAYERS * LAYER_LEN

-- Exact arithmetic identities verified by the Lean kernel.
theorem params_hyper_bits : HYPER_BITS = 35 := rfl
theorem params_tree_leaves : TREE_LEAVES = 32 := rfl
theorem params_chains : CHAINS = 35 := rfl
theorem params_max_checksum_fits : MSG_CHAINS * CHAIN_STEPS < W ^ CSUM_CHAINS := by decide
theorem params_ufors_leaf_fits_blake3_block : 16 + UFORS_CHAINS * N = 64 := rfl
theorem params_ufors_verify_steps : UFORS_CHAINS * UFORS_STEPS - UFORS_SUM = 11 := rfl
theorem params_ufors_len : UFORS_LEN = 1920 := rfl
theorem params_layer_len : LAYER_LEN = 640 := rfl
theorem params_imprint_len : IMPRINT_LEN = 6432 := rfl
theorem params_digest_bits_fit : UFORS_TREES * (TREE_HEIGHT + UFORS_CODE_BITS) + HYPER_BITS = 200 := rfl
theorem params_tree_fits_tweak : 2 ^ HYPER_BITS < 2 ^ 48 := by decide
theorem params_layers_disjoint : LAYERS ≤ UFORS_LAYER_BASE ∧ UFORS_LAYER_BASE + UFORS_TREES < 256 := by decide

-- Suite-separated key-derivation context strings (SPEC.md §4).
def CTX_SECRET_VALUES : String := "BLINCS-128-7x5 2026-11-26 secret values"
def CTX_CONTENT_SALT  : String := "BLINCS-128-7x5 2026-11-26 content salt"
def CTX_RANDOMIZER    : String := "BLINCS-128-7x5 2026-11-26 randomizer"
def CTX_PUBLIC_SEED   : String := "BLINCS-128-7x5 2026-11-26 public seed"
def CTX_PUBLIC_HASH   : String := "BLINCS-128-7x5 2026-11-26 public hash"
def CTX_CONTENT       : String := "BLINCS-128-7x5 2026-11-26 content"

/-- All 6 algorithm key-derivation context strings are pairwise distinct. -/
theorem key_contexts_distinct :
    [CTX_SECRET_VALUES, CTX_CONTENT_SALT, CTX_RANDOMIZER,
     CTX_PUBLIC_SEED, CTX_PUBLIC_HASH, CTX_CONTENT].Nodup := by
  decide

end Blincs
