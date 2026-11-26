/-
  BLINCS-128-A2 Declarative Specification: Tweaks & Context Framing.
  Proves exact 16-byte serialization, global tweak injectivity across all 8 kinds,
  disjointness of hypertree vs U-PORS layer namespaces, and prefix-free context framing.
-/
import Blincs.Params

namespace Blincs

/-- The eight domain-separated tweak kinds (`SPEC.md §5`). -/
inductive TweakKind where
  | chainSecret   -- 1
  | chain         -- 2
  | oneTimeKey    -- 3
  | node          -- 4
  | oneTimeMsg    -- 5
  | message       -- 6
  | fewSelect     -- 7
  | fewCode       -- 8
  deriving DecidableEq, Repr

def TweakKind.toUInt8 : TweakKind → UInt8
  | .chainSecret => 1
  | .chain       => 2
  | .oneTimeKey  => 3
  | .node        => 4
  | .oneTimeMsg  => 5
  | .message     => 6
  | .fewSelect   => 7
  | .fewCode     => 8

theorem TweakKind.toUInt8_injective {a b : TweakKind} (h : a.toUInt8 = b.toUInt8) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

/-- Tweak layer byte for the single U-PORS tree (`0x80 = 128`). -/
def uporsLayerByte : UInt8 :=
  UInt8.ofNat UPORS_LAYER

/-- The U-PORS layer byte (`128`) is strictly disjoint from all hypertree layer bytes (`0..3`). -/
theorem uporsLayerByte_ne_htLayer (ℓ : Fin LAYERS) :
    uporsLayerByte ≠ UInt8.ofNat ℓ.val := by
  intro h
  have hnat := congrArg UInt8.toNat h
  unfold uporsLayerByte UPORS_LAYER at hnat
  have hl := ℓ.isLt
  unfold LAYERS at hl
  simp only [UInt8.toNat_ofNat'] at hnat
  omega

/-- Structured 16-byte BLINCS tweak with statically bounded 48-bit `tree` field. -/
structure Tweak where
  kind  : TweakKind
  layer : UInt8
  tree  : Nat
  hTree : tree < 2 ^ 48
  leaf  : UInt16
  a     : UInt16
  b     : UInt32
  deriving DecidableEq

/-- Extract the `k`-th little-endian byte of a natural number. -/
def leByte (x : Nat) (k : Nat) : UInt8 :=
  UInt8.ofNat ((x / 256 ^ k) % 256)

/-- Encode `x` into `m` little-endian bytes. -/
def encodeLE (x : Nat) (m : Nat) : List UInt8 :=
  List.ofFn (fun i : Fin m => leByte x i.val)

theorem encodeLE_length (x m : Nat) : (encodeLE x m).length = m := by
  simp [encodeLE]

/-- Reconstruct a natural number from little-endian bytes. -/
def decodeLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLE bs

private theorem encodeLE_succ (x m : Nat) :
    encodeLE x (m + 1) = UInt8.ofNat (x % 256) :: encodeLE (x / 256) m := by
  apply List.ext_getElem
  · simp [encodeLE]
  · intro i h1 h2
    cases i with
    | zero => simp [encodeLE, leByte]
    | succ j => simp [encodeLE, leByte, Nat.pow_succ', Nat.div_div_eq_div_mul]

private theorem decodeLE_encodeLE (m : Nat) : ∀ x < 256 ^ m, decodeLE (encodeLE x m) = x := by
  induction m with
  | zero =>
    intro x hx
    simp [encodeLE, decodeLE]
    omega
  | succ m ih =>
    intro x hx
    rw [encodeLE_succ, decodeLE]
    have hmod : (UInt8.ofNat (x % 256)).toNat = x % 256 := by simp
    have hdiv : x / 256 < 256 ^ m := by
      rw [Nat.pow_succ'] at hx
      exact Nat.div_lt_of_lt_mul hx
    rw [hmod, ih (x / 256) hdiv]
    omega

theorem encodeLE_injective {m x y : Nat} (hx : x < 256 ^ m) (hy : y < 256 ^ m)
    (h : encodeLE x m = encodeLE y m) : x = y := by
  have := congrArg decodeLE h
  rwa [decodeLE_encodeLE m x hx, decodeLE_encodeLE m y hy] at this

/-- Canonical 16-byte serialization of a BLINCS tweak (`SPEC.md §5`). -/
def encodeTweak (t : Tweak) : List UInt8 :=
  [t.kind.toUInt8, t.layer]
    ++ encodeLE t.tree 6
    ++ encodeLE t.leaf.toNat 2
    ++ encodeLE t.a.toNat 2
    ++ encodeLE t.b.toNat 4

theorem encodeTweak_length (t : Tweak) : (encodeTweak t).length = 16 := by
  simp [encodeTweak, encodeLE_length]

theorem append_eq_of_length_eq {α : Type} {a b c d : List α}
    (hlen : a.length = c.length) (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  constructor
  · have := congrArg (List.take a.length) h
    simpa [hlen] using this
  · have := congrArg (List.drop a.length) h
    simpa [hlen] using this

/-- **Global Tweak Injectivity Theorem:** distinct tweaks always serialize to distinct 16-byte headers. -/
theorem encodeTweak_injective {t₁ t₂ : Tweak} (h : encodeTweak t₁ = encodeTweak t₂) : t₁ = t₂ := by
  unfold encodeTweak at h
  simp only [List.append_assoc] at h
  have ⟨h1, hrest⟩ := append_eq_of_length_eq (a := [t₁.kind.toUInt8, t₁.layer]) (c := [t₂.kind.toUInt8, t₂.layer]) rfl h
  have hkind : t₁.kind = t₂.kind := TweakKind.toUInt8_injective (by injection h1)
  have hlayer : t₁.layer = t₂.layer := by injection h1 with _ h1'; injection h1'
  have ⟨htreeE, hrest2⟩ := append_eq_of_length_eq (by simp [encodeLE_length]) hrest
  have ⟨hleafE, hrest3⟩ := append_eq_of_length_eq (by simp [encodeLE_length]) hrest2
  have ⟨haE, hbE⟩ := append_eq_of_length_eq (by simp [encodeLE_length]) hrest3
  have htree : t₁.tree = t₂.tree :=
    encodeLE_injective (m := 6) (by have := t₁.hTree; omega) (by have := t₂.hTree; omega) htreeE
  have hleafNat : t₁.leaf.toNat = t₂.leaf.toNat :=
    encodeLE_injective (m := 2) (by have := t₁.leaf.toNat_lt; omega) (by have := t₂.leaf.toNat_lt; omega) hleafE
  have haNat : t₁.a.toNat = t₂.a.toNat :=
    encodeLE_injective (m := 2) (by have := t₁.a.toNat_lt; omega) (by have := t₂.a.toNat_lt; omega) haE
  have hbNat : t₁.b.toNat = t₂.b.toNat :=
    encodeLE_injective (m := 4) (by have := t₁.b.toNat_lt; omega) (by have := t₂.b.toNat_lt; omega) hbE
  have hleaf : t₁.leaf = t₂.leaf := UInt16.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hleafNat)
  have ha : t₁.a = t₂.a := UInt16.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq haNat)
  have hb : t₁.b = t₂.b := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hbNat)
  cases t₁; cases t₂
  simp only at hkind hlayer htree hleaf ha hb
  subst hkind; subst hlayer; subst htree; subst hleaf; subst ha; subst hb
  rfl

-- ---------------------------------------------------------------------------
-- Bounded Length-Framed Application Context (`SPEC.md §7`)
-- ---------------------------------------------------------------------------

/-- Length-prefixed application context encoding `u8(len(ctx)) || ctx`. -/
def frameContext (ctx : List UInt8) : List UInt8 :=
  UInt8.ofNat ctx.length :: ctx

/-- **Prefix-Free Context Framing Theorem:** `frameContext` is unambiguously decodable even when concatenated with arbitrary trailing data. -/
theorem frameContext_prefix_free {c₁ c₂ m₁ m₂ : List UInt8}
    (h₁ : c₁.length ≤ MAX_CONTEXT_LEN) (h₂ : c₂.length ≤ MAX_CONTEXT_LEN)
    (heq : frameContext c₁ ++ m₁ = frameContext c₂ ++ m₂) :
    c₁ = c₂ ∧ m₁ = m₂ := by
  unfold frameContext at heq
  simp only [List.cons_append] at heq
  injection heq with hlenByte htail
  have hlen : c₁.length = c₂.length := by
    have hnat := congrArg UInt8.toNat hlenByte
    simp only [UInt8.toNat_ofNat'] at hnat
    unfold MAX_CONTEXT_LEN at h₁ h₂
    omega
  exact append_eq_of_length_eq hlen htail

theorem frameContext_injective {c₁ c₂ : List UInt8}
    (h₁ : c₁.length ≤ MAX_CONTEXT_LEN) (h₂ : c₂.length ≤ MAX_CONTEXT_LEN)
    (heq : frameContext c₁ = frameContext c₂) : c₁ = c₂ := by
  have h' : frameContext c₁ ++ [] = frameContext c₂ ++ [] := by simpa using heq
  exact (frameContext_prefix_free h₁ h₂ h').1

end Blincs
