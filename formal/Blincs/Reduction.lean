/-
  BLINCS-128-7x5 Machine-Checked Security Reduction: Structural Forgery Dichotomy (`U-FORS`).

  Mechanically proves (ZERO `sorry`, ZERO custom axioms) that for ANY abstract BLAKE3 oracle `H`,
  ANY 32-byte `seed`, ANY transcript `Q` of honest signing queries `(ctx_q, msg_q, draw_q)`,
  and ANY valid forgery `(ctx*, M*, σ*)` passing `verify H (signetId H seed) ctx* M* σ*`
  with `(ctx*, M*) ∉ Q`:

  At least ONE of the following exact cryptographic failure events MUST occur:
    1. `contentHashSecondPreimage`   -- same `(e*, ctx*)`, distinct `M* ≠ M_q`, same `h_msg` under `K_msg`
    2. `messageDigestCollision`      -- distinct `(R*, short*, ctx*)`, same `D` under `K_pub, tweak(MESSAGE)`
    3. `hypertreeNodeSecondPreimage` -- `NODE` collision at explicit hypertree `(ℓ, tree, level, pos)`
    4. `oneTimeKeySecondPreimage`    -- `ONE_TIME_KEY` collision at explicit hypertree `(ℓ, tree, leaf)`
    5. `wotsChainSecondPreimage`     -- `CHAIN` collision at explicit hypertree `(ℓ, tree, leaf, c, step)`
    6. `wotsChainPreimage`           -- inverted chain preimage at explicit hypertree `(ℓ, tree, leaf, c)`
                                        for strictly smaller digit `wotsDigit m* c < wotsDigit m_honest c`
    7. `uforsRootSecondPreimage`     -- `FEW_ROOT` collision at explicit `leaf_addr`
    8. `uforsNodeSecondPreimage`     -- `NODE` collision at explicit U-FORS `(leaf_addr, t, level, pos)`
    9. `uforsLeafSecondPreimage`     -- `ONE_TIME_KEY` collision at explicit U-FORS `(leaf_addr, t, leaf)`
   10. `uforsChainSecondPreimage`    -- `CHAIN` collision at explicit U-FORS `(leaf_addr, t, leaf, c, step)`
   11. `uforsUnrevealedChainPreimage`-- adversary produced the exact honest chain node `x_{d*}` for a
                                        U-FORS coordinate `(leaf_addr*, t, leaf*, c)` that was NEVER
                                        revealed at any depth `≤ d*` in `Q` (inverts `CHAIN` backwards
                                        or predicts `CHAIN_SECRET`!)
   12. `uforsCover`                  -- for EVERY tree `t : Fin 15` and EVERY chain `c : Fin 3`,
                                        some honest query `q ∈ Q` opened `(leaf_addr*, t, leaf*_t)` at a
                                        depth `d_q ≤ d*_c` — literally the exact 3D lattice-meet cover
                                        event `c* ⪰ ∧_j c^(j)` (exact DP probability ≤ 2^{-138.48} at q ≤ 2^{32}).
-/
import Blincs.Scheme

namespace Blincs

/-- An honest signing query recorded in the EUF-CMA transcript. -/
structure SignedQuery where
  ctx  : List UInt8
  hCtx : ctx.length ≤ MAX_CONTEXT_LEN
  msg  : List UInt8
  draw : Bytes 32

/-- Derived public digest values of an honest query `q`. -/
def queryE (H : HashOracle) (k : DerivedKeys) (q : SignedQuery) : Bytes 16 :=
  trunc16 (H.keyed k.k_salt q.draw.toList)

def queryShort (H : HashOracle) (k : DerivedKeys) (q : SignedQuery) : List UInt8 :=
  contentShort H k.k_content (queryE H k q) q.ctx q.msg

def queryR (H : HashOracle) (k : DerivedKeys) (q : SignedQuery) : Bytes 16 :=
  trunc16 (H.keyed k.k_r (queryShort H k q ++ frameContext q.ctx))

def queryDigest (H : HashOracle) (k : DerivedKeys) (q : SignedQuery) : Bytes 32 :=
  messageDigest H k.k_pub (queryR H k q) k.root (queryShort H k q) q.ctx

/-- A query `q` covers U-FORS chain `(leafAddr, t, leaf, c)` at target depth `d` iff its digest
    lands on `(leafAddr, leaf)` in tree `t` AND reveals chain `c` at depth `≤ d` (so hashing
    forward reaches `x_d`). -/
def queryCoversUforsChain (H : HashOracle) (k : DerivedKeys) (q : SignedQuery)
    (leafAddr : Nat) (t : Fin UFORS_TREES) (leaf : Nat) (c : Fin UFORS_CHAINS) (d : Nat) : Prop :=
  let Dq := queryDigest H k q
  extractLeafAddr Dq = leafAddr ∧
  extractUforsLeaf Dq t = leaf ∧
  uforsDigit (extractUforsCode Dq t) c ≤ d

/--
  **Exact Exhaustive Witness Type** for any valid BLINCS (`U-FORS`) forgery `(ctx*, M*, σ*)`
  against `seed` and signing transcript `Q`.
-/
inductive ForgeryWitness (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (ctx M : List UInt8) (σ : Imprint) : Prop where
  /-- (1) Explicit 2nd-preimage of `Keyed(K_msg, ·)`: same `(e, ctx)`, distinct `M ≠ q.msg`, same `h_msg`. -/
  | contentHashSecondPreimage
      (q : SignedQuery) (hq : q ∈ Q)
      (he : σ.e = queryE H (deriveKeys H seed) q)
      (hctx : ctx = q.ctx)
      (hne : M ≠ q.msg)
      (hcol : contentHash H (deriveKeys H seed).k_content σ.e ctx M =
              contentHash H (deriveKeys H seed).k_content (queryE H (deriveKeys H seed) q) q.ctx q.msg)
  /-- (2) Explicit 2nd-preimage/collision of `Keyed(K_pub, tweak(MESSAGE) || ·)`: distinct input, same `D`. -/
  | messageDigestCollision
      (q : SignedQuery) (hq : q ∈ Q)
      (hne : σ.r ≠ queryR H (deriveKeys H seed) q ∨
             contentShort H (deriveKeys H seed).k_content σ.e ctx M ≠ queryShort H (deriveKeys H seed) q ∨
             ctx ≠ q.ctx)
      (hcol : messageDigest H (deriveKeys H seed).k_pub σ.r (deriveKeys H seed).root
                (contentShort H (deriveKeys H seed).k_content σ.e ctx M) ctx =
              queryDigest H (deriveKeys H seed) q)
  /-- (3) Explicit `NODE` 2nd-preimage in hypertree layer `ℓ < 7`. -/
  | hypertreeNodeSecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (level p : Nat)
      (hLvl : 1 ≤ level ∧ level ≤ TREE_HEIGHT)
      (L₁ R₁ L₂ R₂ : Bytes 16)
      (hne : L₁ ≠ L₂ ∨ R₁ ≠ R₂)
      (hcol : treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree level p L₁ R₁ =
              treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree level p L₂ R₂)
  /-- (4) Explicit `ONE_TIME_KEY` 2nd-preimage at hypertree `(ℓ, tree, leaf)`. -/
  | oneTimeKeySecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
      (ends₁ ends₂ : Fin CHAINS → Bytes 16)
      (hne : ends₁ ≠ ends₂)
      (hcol : shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, UInt8.ofNat ℓ.val, tree, hTree, leaf, 0, 0⟩ (flattenBytes16 ends₁) =
              shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, UInt8.ofNat ℓ.val, tree, hTree, leaf, 0, 0⟩ (flattenBytes16 ends₂))
  /-- (5) Explicit `CHAIN` 2nd-preimage at hypertree `(ℓ, tree, leaf, c, s)`. -/
  | wotsChainSecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
      (c : Fin CHAINS) (s : Nat) (hs : s < CHAIN_STEPS)
      (a b : Bytes 16) (hne : a ≠ b)
      (hcol : chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val s a =
              chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val s b)
  /-- (6) Explicit WOTS+ chain preimage inversion: adversary produced honest chain node `x_{d₁}`
          strictly BEFORE the honest signer's digit `d₂` (`d₁ < d₂`) on a distinct message `m* ≠ m_honest`. -/
  | wotsChainPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
      (c : Fin CHAINS) (mForged mHonest : Bytes 16)
      (hne : mForged ≠ mHonest)
      (hlt : wotsDigit mForged c < wotsDigit mHonest c)
      (hpre : (σ.layers ℓ).wots c =
              chainIter (chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val)
                0 (wotsDigit mForged c)
                (chainStart H (deriveKeys H seed).k_sec (UInt8.ofNat ℓ.val) tree hTree leaf c.val))
  /-- (7) Explicit `FEW_ROOT` 2nd-preimage at `leafAddr`. -/
  | uforsRootSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48)
      (roots₁ roots₂ : Fin UFORS_TREES → Bytes 16) (hne : roots₁ ≠ roots₂)
      (hcol : shortHash H (deriveKeys H seed).k_pub ⟨.fewRoot, 0, leafAddr, hAddr, 0, 0, 0⟩ (flattenBytes16 roots₁) =
              shortHash H (deriveKeys H seed).k_pub ⟨.fewRoot, 0, leafAddr, hAddr, 0, 0, 0⟩ (flattenBytes16 roots₂))
  /-- (8) Explicit `NODE` 2nd-preimage in U-FORS tree `t` (`layer = 0x80 + t`). -/
  | uforsNodeSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (t : Fin UFORS_TREES)
      (level p : Nat) (hLvl : 1 ≤ level ∧ level ≤ TREE_HEIGHT)
      (L₁ R₁ L₂ R₂ : Bytes 16) (hne : L₁ ≠ L₂ ∨ R₁ ≠ R₂)
      (hcol : treeCombine H (deriveKeys H seed).k_pub (uforsLayerByte t) leafAddr hAddr level p L₁ R₁ =
              treeCombine H (deriveKeys H seed).k_pub (uforsLayerByte t) leafAddr hAddr level p L₂ R₂)
  /-- (9) Explicit `ONE_TIME_KEY` 2nd-preimage in U-FORS tree `t` at leaf `leaf`. -/
  | uforsLeafSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (t : Fin UFORS_TREES) (leaf : UInt16)
      (ends₁ ends₂ : Fin UFORS_CHAINS → Bytes 16) (hne : ends₁ ≠ ends₂)
      (hcol : shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, uforsLayerByte t, leafAddr, hAddr, leaf, 0, 0⟩ (flattenBytes16 ends₁) =
              shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, uforsLayerByte t, leafAddr, hAddr, leaf, 0, 0⟩ (flattenBytes16 ends₂))
  /-- (10) Explicit `CHAIN` 2nd-preimage in U-FORS tree `t` at `(leaf, c, s)`. -/
  | uforsChainSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (t : Fin UFORS_TREES) (leaf : UInt16)
      (c : Fin UFORS_CHAINS) (s : Nat) (hs : s < UFORS_STEPS)
      (a b : Bytes 16) (hne : a ≠ b)
      (hcol : chainStepFn H (deriveKeys H seed).k_pub (uforsLayerByte t) leafAddr hAddr leaf c.val s a =
              chainStepFn H (deriveKeys H seed).k_pub (uforsLayerByte t) leafAddr hAddr leaf c.val s b)
  /-- (11) Unrevealed U-FORS chain preimage: coordinate `(leafAddr, t, leaf, c)` was NEVER revealed
           at depth `≤ d` in `Q`, yet `(σ.ufors t).chains c` equals the exact honest chain node `x_d`! -/
  | uforsUnrevealedChainPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (t : Fin UFORS_TREES)
      (leaf : Nat) (c : Fin UFORS_CHAINS) (code : Fin 64)
      (hNotCovered : ∀ q ∈ Q, ¬ queryCoversUforsChain H (deriveKeys H seed) q leafAddr t leaf c (uforsDigit code c))
      (hMatch : (σ.ufors t).chains c =
                chainIter (chainStepFn H (deriveKeys H seed).k_pub (uforsLayerByte t) leafAddr hAddr (UInt16.ofNat leaf) c.val)
                  0 (uforsDigit code c)
                  (chainStart H (deriveKeys H seed).k_sec (uforsLayerByte t) leafAddr hAddr (UInt16.ofNat leaf) c.val))
  /-- (12) Exact 3D Lattice-Meet U-FORS cover: for EVERY tree `t : Fin 15` and EVERY chain `c : Fin 3`,
           some honest query `q ∈ Q` landed on `(leafAddr*, t, leaf*_t)` at depth `≤ uforsDigit (code*_t) c`
           (exact DP probability `≤ 2^{-138.48}` per digest query at `q ≤ 2^{32}`). -/
  | uforsCover
      (leafAddr : Nat)
      (leafSel : Fin UFORS_TREES → Nat)
      (codeSel : Fin UFORS_TREES → Fin 64)
      (hCover : ∀ (t : Fin UFORS_TREES) (c : Fin UFORS_CHAINS),
        ∃ q ∈ Q, queryCoversUforsChain H (deriveKeys H seed) q leafAddr t (leafSel t) c (uforsDigit (codeSel t) c))

/-- Helper: extract a WOTS+ or Merkle collision/preimage when a single hypertree layer produces
    the honest tree root from a DIFFERENT input message `mForged ≠ mHonest`. -/
private theorem layer_forgery_extract (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (ctx M : List UInt8) (σ : Imprint)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (ℓ : Fin LAYERS) (mForged : Bytes 16)
    (hne : mForged ≠ honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
    (hRoot : verifyLayerStep H (deriveKeys H seed).k_pub leafAddr hAddr ℓ mForged (σ.layers ℓ) =
             treeRoot H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub
               (UInt8.ofNat ℓ.val) (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr) CHAINS CHAIN_STEPS) :
    ForgeryWitness H seed Q ctx M σ := by
  let k := deriveKeys H seed
  let tree := layerTree leafAddr ℓ.val
  let hTree := layerTree_lt_48 leafAddr ℓ.val hAddr
  let leaf := layerLeaf leafAddr ℓ.val
  let lByte := UInt8.ofNat ℓ.val
  let leafU16 := UInt16.ofNat leaf
  let forgedPk := chainVerifyGeneric H k.k_pub lByte tree hTree leafU16 CHAIN_STEPS (wotsDigit mForged) (σ.layers ℓ).wots
  let honestPk := chainLeafPk H k.k_sec k.k_pub lByte tree hTree leafU16 CHAINS CHAIN_STEPS
  by_cases hpk : forgedPk = honestPk
  · let forgedEnds : Fin CHAINS → Bytes 16 := fun c =>
      chainIter (chainStepFn H k.k_pub lByte tree hTree leafU16 c.val)
        (wotsDigit mForged c) (CHAIN_STEPS - wotsDigit mForged c) ((σ.layers ℓ).wots c)
    let honestEnds : Fin CHAINS → Bytes 16 := fun c =>
      chainEndpoint H k.k_sec k.k_pub lByte tree hTree leafU16 CHAIN_STEPS c.val
    by_cases hends : forgedEnds = honestEnds
    · let mHonest := honestLayerInput H k.k_sec k.k_pub leafAddr hAddr ℓ.val
      rcases wots_dominance hne with ⟨c, hlt⟩
      have hchainEq : forgedEnds c = honestEnds c := congrFun hends c
      have hd1 : wotsDigit mForged c ≤ CHAIN_STEPS := Nat.le_of_lt_succ (wotsDigit_lt_16 mForged c)
      rcases chain_forgery_extract
          (chainStepFn H k.k_pub lByte tree hTree leafU16 c.val)
          (chainStart H k.k_sec lByte tree hTree leafU16 c.val)
          ((σ.layers ℓ).wots c) hd1 hchainEq with hpre | ⟨s, a, b, _, hs2, hab, hcol⟩
      · exact ForgeryWitness.wotsChainPreimage ℓ tree hTree leafU16 c mForged mHonest hne hlt hpre
      · exact ForgeryWitness.wotsChainSecondPreimage ℓ tree hTree leafU16 c s hs2 a b hab hcol
    · exact ForgeryWitness.oneTimeKeySecondPreimage ℓ tree hTree leafU16 forgedEnds honestEnds hends hpk
  · have hLeafEq : honestPk = treeLeaves H k.k_sec k.k_pub lByte tree hTree CHAINS CHAIN_STEPS ⟨leaf, layerLeaf_lt leafAddr ℓ.val⟩ := rfl
    rw [hLeafEq] at hpk
    rcases merkle_forgery_collision (treeCombine H k.k_pub lByte tree hTree) TREE_HEIGHT
        (treeLeaves H k.k_sec k.k_pub lByte tree hTree CHAINS CHAIN_STEPS) leaf (layerLeaf_lt leafAddr ℓ.val)
        forgedPk (List.ofFn (σ.layers ℓ).auth) (by simp) hpk hRoot with
      ⟨lvl, p, L₁, R₁, L₂, R₂, h1, h2, hdiff, hcol⟩
    exact ForgeryWitness.hypertreeNodeSecondPreimage ℓ tree hTree lvl p ⟨h1, h2⟩ L₁ R₁ L₂ R₂ hdiff hcol

/-- Helper: top-down induction on the 7 hypertree layers (`k = 7` down to `0`). -/
private theorem hypertree_top_down_extract (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (ctx M : List UInt8) (σ : Imprint)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS) (uforsNode : Bytes 16) :
    ∀ (k : Nat) (hk : k ≤ LAYERS),
      hypertreeVerifyUpTo H (deriveKeys H seed).k_pub leafAddr hAddr uforsNode σ.layers k hk =
      honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr k →
      uforsNode = uforsRoot H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr
        (by have := params_tree_fits_tweak; omega) ∨
      ForgeryWitness H seed Q ctx M σ
  | 0, _, hEq => Or.inl hEq
  | k + 1, hk, hEq => by
    unfold hypertreeVerifyUpTo at hEq
    let prev := hypertreeVerifyUpTo H (deriveKeys H seed).k_pub leafAddr hAddr uforsNode σ.layers k (by omega)
    let want := honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr k
    by_cases hprev : prev = want
    · exact hypertree_top_down_extract H seed Q ctx M σ leafAddr hAddr uforsNode k (by omega) hprev
    · exact Or.inr (layer_forgery_extract H seed Q ctx M σ leafAddr hAddr ⟨k, hk⟩ prev hprev hEq)

/-- Helper: given `uforsVerify ... = uforsRoot ...`, extract either a U-FORS `FEW_ROOT`/`NODE`/`ONE_TIME_KEY`/`CHAIN`
    2nd-preimage, an unrevealed U-FORS chain preimage, OR the exact 3D lattice-meet `uforsCover` event! -/
private theorem ufors_forgery_extract (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (ctx M : List UInt8) (σ : Imprint)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48)
    (leafSel : Fin UFORS_TREES → Nat) (hLeaf : ∀ t, leafSel t < 2 ^ TREE_HEIGHT)
    (codeSel : Fin UFORS_TREES → Fin 64)
    (hUforsRoot : uforsVerify H (deriveKeys H seed).k_pub leafAddr hAddr leafSel codeSel σ.ufors =
                  uforsRoot H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr) :
    ForgeryWitness H seed Q ctx M σ := by
  let k := deriveKeys H seed
  let forgedRoots : Fin UFORS_TREES → Bytes 16 := fun t =>
    let lByte := uforsLayerByte t
    let leaf := leafSel t
    let digits := fun c : Fin UFORS_CHAINS => uforsDigit (codeSel t) c
    let leafPk := chainVerifyGeneric H k.k_pub lByte leafAddr hAddr (UInt16.ofNat leaf)
      UFORS_STEPS digits (σ.ufors t).chains
    merkleReconstruct (treeCombine H k.k_pub lByte leafAddr hAddr) leaf leafPk (List.ofFn (σ.ufors t).auth)
  let honestRoots : Fin UFORS_TREES → Bytes 16 := fun t =>
    uforsTreeRoot H k.k_sec k.k_pub leafAddr hAddr t
  by_cases hRoots : forgedRoots = honestRoots
  · -- All 15 U-FORS tree roots match! Check whether every chain value matches the honest node `x_d`.
    by_cases hCover : ∀ (t : Fin UFORS_TREES) (c : Fin UFORS_CHAINS),
        ∃ q ∈ Q, queryCoversUforsChain H k q leafAddr t (leafSel t) c (uforsDigit (codeSel t) c)
    · exact ForgeryWitness.uforsCover leafAddr leafSel codeSel hCover
    · -- Some tree `t` and chain `c` was NEVER covered in `Q`!
      have hNotAllT : ∃ t : Fin UFORS_TREES, ¬ ∀ c : Fin UFORS_CHAINS,
          ∃ q ∈ Q, queryCoversUforsChain H k q leafAddr t (leafSel t) c (uforsDigit (codeSel t) c) :=
        Classical.not_forall.mp hCover
      rcases hNotAllT with ⟨t, htNot⟩
      have hNotAllC : ∃ c : Fin UFORS_CHAINS,
          ¬ ∃ q ∈ Q, queryCoversUforsChain H k q leafAddr t (leafSel t) c (uforsDigit (codeSel t) c) :=
        Classical.not_forall.mp htNot
      rcases hNotAllC with ⟨c, hcNot⟩
      have hNever : ∀ q ∈ Q, ¬ queryCoversUforsChain H k q leafAddr t (leafSel t) c (uforsDigit (codeSel t) c) :=
        fun q hq hr => hcNot ⟨q, hq, hr⟩
      let lByte := uforsLayerByte t
      let leaf := leafSel t
      let leafU16 := UInt16.ofNat leaf
      let digits := fun ch : Fin UFORS_CHAINS => uforsDigit (codeSel t) ch
      let forgedPk := chainVerifyGeneric H k.k_pub lByte leafAddr hAddr leafU16 UFORS_STEPS digits (σ.ufors t).chains
      let honestPk := chainLeafPk H k.k_sec k.k_pub lByte leafAddr hAddr leafU16 UFORS_CHAINS UFORS_STEPS
      by_cases hPk : forgedPk = honestPk
      · let forgedEnds : Fin UFORS_CHAINS → Bytes 16 := fun ch =>
          chainIter (chainStepFn H k.k_pub lByte leafAddr hAddr leafU16 ch.val)
            (digits ch) (UFORS_STEPS - digits ch) ((σ.ufors t).chains ch)
        let honestEnds : Fin UFORS_CHAINS → Bytes 16 := fun ch =>
          chainEndpoint H k.k_sec k.k_pub lByte leafAddr hAddr leafU16 UFORS_STEPS ch.val
        by_cases hEnds : forgedEnds = honestEnds
        · have hchainEq : forgedEnds c = honestEnds c := congrFun hEnds c
          have hd : digits c ≤ UFORS_STEPS := uforsDigit_le_9 (codeSel t) c
          rcases chain_forgery_extract
              (chainStepFn H k.k_pub lByte leafAddr hAddr leafU16 c.val)
              (chainStart H k.k_sec lByte leafAddr hAddr leafU16 c.val)
              ((σ.ufors t).chains c) hd hchainEq with hpre | ⟨s, a, b, _, hs2, hab, hcol⟩
          · exact ForgeryWitness.uforsUnrevealedChainPreimage leafAddr hAddr t leaf c (codeSel t) hNever hpre
          · exact ForgeryWitness.uforsChainSecondPreimage leafAddr hAddr t leafU16 c s hs2 a b hab hcol
        · exact ForgeryWitness.uforsLeafSecondPreimage leafAddr hAddr t leafU16 forgedEnds honestEnds hEnds hPk
      · have htRoot : forgedRoots t = honestRoots t := congrFun hRoots t
        have hHonEq : honestPk = treeLeaves H k.k_sec k.k_pub lByte leafAddr hAddr UFORS_CHAINS UFORS_STEPS ⟨leaf, hLeaf t⟩ := rfl
        rw [hHonEq] at hPk
        rcases merkle_forgery_collision (treeCombine H k.k_pub lByte leafAddr hAddr) TREE_HEIGHT
            (treeLeaves H k.k_sec k.k_pub lByte leafAddr hAddr UFORS_CHAINS UFORS_STEPS) leaf (hLeaf t)
            forgedPk (List.ofFn (σ.ufors t).auth) (by simp) hPk htRoot with
          ⟨lvl, p, L₁, R₁, L₂, R₂, h1, h2, hdiff, hcol⟩
        exact ForgeryWitness.uforsNodeSecondPreimage leafAddr hAddr t lvl p ⟨h1, h2⟩ L₁ R₁ L₂ R₂ hdiff hcol
  · exact ForgeryWitness.uforsRootSecondPreimage leafAddr hAddr forgedRoots honestRoots hRoots hUforsRoot

/--
  **Main Machine-Checked Security Decomposition Theorem (`BLINCS-128-7x5` with `U-FORS`):**
  For ANY `HashOracle`, ANY `seed`, ANY honest signing transcript `Q`, and ANY fresh valid forgery
  `(ctx*, M*, σ*)` (`(ctx*, M*) ∉ Q`, `verify H (signetId H seed) ctx* M* σ*`),
  at least ONE of the 12 explicit `ForgeryWitness` events holds!
-/
theorem blincs_forgery_dichotomy (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (ctx M : List UInt8) (σ : Imprint)
    (hFresh : ∀ q ∈ Q, (q.ctx, q.msg) ≠ (ctx, M))
    (hVer : verify H (signetId H seed) ctx M σ) :
    ForgeryWitness H seed Q ctx M σ := by
  rcases hVer with ⟨hCtx, hRootEq⟩
  rcases verifierKeys_match_deriveKeys H seed with ⟨hkpub, hroot, hkcontent⟩
  dsimp only at hRootEq
  rw [hkpub, hroot, hkcontent] at hRootEq
  let k := deriveKeys H seed
  let short := contentShort H k.k_content σ.e ctx M
  let D := messageDigest H k.k_pub σ.r k.root short ctx
  let leafSel := extractUforsLeaf D
  let codeSel := extractUforsCode D
  let leafAddr := extractLeafAddr D
  let hAddr := extractLeafAddr_lt D
  let hAddr48 := extractLeafAddr_lt_48 D
  by_cases hDigestHit : ∃ q ∈ Q, D = queryDigest H k q
  · rcases hDigestHit with ⟨q, hq, hDeq⟩
    by_cases hMsgInput : σ.r = queryR H k q ∧ short = queryShort H k q ∧ ctx = q.ctx
    · rcases hMsgInput with ⟨_, hShortEq, hCtxEq⟩
      have hSplit : σ.e.toList = (queryE H k q).toList ∧
                    (contentHash H k.k_content σ.e ctx M).toList =
                    (contentHash H k.k_content (queryE H k q) q.ctx q.msg).toList := by
        dsimp only [short] at hShortEq
        unfold queryShort at hShortEq
        unfold contentShort at hShortEq
        exact ⟨by simpa using congrArg (List.take 16) hShortEq,
               by simpa using congrArg (List.drop 16) hShortEq⟩
      have heEq : σ.e = queryE H k q := Bytes.toList_injective hSplit.1
      have hhEq : contentHash H k.k_content σ.e ctx M =
                  contentHash H k.k_content (queryE H k q) q.ctx q.msg := Bytes.toList_injective hSplit.2
      have hMne : M ≠ q.msg := by
        intro hMeq
        apply hFresh q hq
        rw [hCtxEq, hMeq]
      exact ForgeryWitness.contentHashSecondPreimage q hq heEq hCtxEq hMne hhEq
    · have hDiff : σ.r ≠ queryR H k q ∨ short ≠ queryShort H k q ∨ ctx ≠ q.ctx := by
        by_cases h1 : σ.r = queryR H k q
        · by_cases h2 : short = queryShort H k q
          · right; right; intro h3; exact hMsgInput ⟨h1, h2, h3⟩
          · right; left; exact h2
        · left; exact h1
      exact ForgeryWitness.messageDigestCollision q hq hDiff hDeq
  · have hTopMatch :
        hypertreeVerifyUpTo H k.k_pub leafAddr hAddr
          (uforsVerify H k.k_pub leafAddr hAddr48 leafSel codeSel σ.ufors) σ.layers LAYERS (Nat.le_refl _) =
        honestLayerInput H k.k_sec k.k_pub leafAddr hAddr LAYERS := by
      have hLeft : hypertreeVerifyUpTo H k.k_pub leafAddr hAddr
          (uforsVerify H k.k_pub leafAddr hAddr48 leafSel codeSel σ.ufors) σ.layers LAYERS (Nat.le_refl _) = k.root := hRootEq
      rw [hLeft]
      have hzero : layerTree leafAddr 6 = 0 := top_layerTree_zero hAddr
      have hRight : honestLayerInput H k.k_sec k.k_pub leafAddr hAddr LAYERS =
          treeRoot H k.k_sec k.k_pub 6 (layerTree leafAddr 6) (layerTree_lt_48 leafAddr 6 hAddr) CHAINS CHAIN_STEPS := rfl
      rw [hRight]
      have hTop : ∀ (t : Nat) (ht : t < 2 ^ 48), t = 0 →
          treeRoot H k.k_sec k.k_pub 6 t ht CHAINS CHAIN_STEPS =
          treeRoot H k.k_sec k.k_pub 6 0 (by decide) CHAINS CHAIN_STEPS := by
        intro t ht h0; subst h0; rfl
      exact (hTop (layerTree leafAddr 6) (layerTree_lt_48 leafAddr 6 hAddr) hzero).symm
    rcases hypertree_top_down_extract H seed Q ctx M σ leafAddr hAddr
        (uforsVerify H k.k_pub leafAddr hAddr48 leafSel codeSel σ.ufors) LAYERS (Nat.le_refl _) hTopMatch with
      hUforsEq | hWitness
    · exact ufors_forgery_extract H seed Q ctx M σ leafAddr hAddr48 leafSel (extractUforsLeaf_lt D) codeSel hUforsEq
    · exact hWitness

/--
  **Two-Stage Salt-Failure Hedged Fallback Theorem (Secondary Security Goal):**
  Even if the salt source (`saltseed`) is completely stuck or leaked so the exact same `draw`
  (and hence the exact same content salt `e`) is reused for two distinct pairs
  `(ctx₁, M₁) ≠ (ctx₂, M₂)` (with valid context lengths), EITHER:
    (a) `ctx₁ = ctx₂`, `M₁ ≠ M₂`, and `h_msg` suffers a 256-bit keyed-BLAKE3 collision under `K_msg`, OR
    (b) the inputs `short₁ || frameContext ctx₁` and `short₂ || frameContext ctx₂` fed into the
        secret-keyed randomizer PRF `Keyed(K_R, ·)` are STRICTLY DISTINCT (so `R` and `D` remain freshly hedged!).
-/
theorem rng_failure_hedged_fallback (H : HashOracle) (seed draw : Bytes 32)
    (ctx₁ M₁ ctx₂ M₂ : List UInt8)
    (hCtx₁ : ctx₁.length ≤ MAX_CONTEXT_LEN) (hCtx₂ : ctx₂.length ≤ MAX_CONTEXT_LEN)
    (hne : (ctx₁, M₁) ≠ (ctx₂, M₂)) :
    let k := deriveKeys H seed
    let e := trunc16 (H.keyed k.k_salt draw.toList)
    let short₁ := contentShort H k.k_content e ctx₁ M₁
    let short₂ := contentShort H k.k_content e ctx₂ M₂
    (ctx₁ = ctx₂ ∧ M₁ ≠ M₂ ∧
      contentHash H k.k_content e ctx₁ M₁ = contentHash H k.k_content e ctx₂ M₂) ∨
    (short₁ ++ frameContext ctx₁ ≠ short₂ ++ frameContext ctx₂) := by
  dsimp only
  let k := deriveKeys H seed
  let e := trunc16 (H.keyed k.k_salt draw.toList)
  by_cases hIn : contentShort H k.k_content e ctx₁ M₁ ++ frameContext ctx₁ =
                 contentShort H k.k_content e ctx₂ M₂ ++ frameContext ctx₂
  · left
    have hShortLen₁ : (contentShort H k.k_content e ctx₁ M₁).length = 48 := by simp [contentShort]
    have hShortLen₂ : (contentShort H k.k_content e ctx₂ M₂).length = 48 := by simp [contentShort]
    have hShortEq : contentShort H k.k_content e ctx₁ M₁ = contentShort H k.k_content e ctx₂ M₂ := by
      have := congrArg (List.take 48) hIn
      simpa [hShortLen₁, hShortLen₂] using this
    have hFrameEq : frameContext ctx₁ = frameContext ctx₂ := by
      have := congrArg (List.drop 48) hIn
      simpa [hShortLen₁, hShortLen₂] using this
    have hCtxEq : ctx₁ = ctx₂ := frameContext_injective hCtx₁ hCtx₂ hFrameEq
    have hHashEq : contentHash H k.k_content e ctx₁ M₁ = contentHash H k.k_content e ctx₂ M₂ := by
      unfold contentShort at hShortEq
      have := congrArg (List.drop 16) hShortEq
      simp only [List.drop_left' (Bytes.toList_length e)] at this
      exact Bytes.toList_injective this
    have hMne : M₁ ≠ M₂ := by
      intro hMeq
      apply hne
      rw [hCtxEq, hMeq]
    exact ⟨hCtxEq, hMne, hHashEq⟩
  · exact Or.inr hIn

end Blincs
