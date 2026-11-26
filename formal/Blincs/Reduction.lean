/-
  BLINCS-128-A2 Machine-Checked Security Reduction: Structural Forgery Dichotomy (`S-WOTS+Z` + `U-PORS`).

  Mechanically proves (ZERO `sorry`, ZERO custom axioms) that for ANY abstract BLAKE3 oracle `H`,
  ANY 32-byte `seed`, ANY transcript `Q` of honest signing queries `(ctx_q, msg_q, draw_q, ctrFt_q)`,
  ANY valid honest hypertree counter table `honestCtr`, and ANY valid forgery `(ctx*, M*, σ*)`
  passing `verify H (signetId H seed) ctx* M* σ*` with `(ctx*, M*) ∉ Q`:

  At least ONE of the following 13 exact cryptographic failure events MUST occur:
    1. `contentHashSecondPreimage`   -- same `(e*, ctx*)`, distinct `M* ≠ M_q`, same `h_msg` under `K_msg`
    2. `messageDigestCollision`      -- distinct `(R*, short*, ctx*)`, same `D_seed` under `K_pub, tweak(MESSAGE)`
    3. `fewSelectCollision`          -- distinct `(D_seed*, ctr_ft*)`, same `D_sel` under `K_pub, tweak(FEW_SELECT)`
    4. `hypertreeNodeSecondPreimage` -- `NODE` collision at explicit hypertree `(ℓ, tree, level, pos)`
    5. `oneTimeKeySecondPreimage`    -- `ONE_TIME_KEY` collision at explicit hypertree `(ℓ, tree, leaf)`
    6. `wotsMsgSecondPreimage`       -- `ONE_TIME_MSG` 128-bit collision at explicit hypertree `(ℓ, tree, leaf)`
                                        for distinct `m* ≠ m_honest` (both satisfying `h[0] = 0`)
    7. `wotsChainSecondPreimage`     -- `CHAIN` collision at explicit hypertree `(ℓ, tree, leaf, c, step)`
    8. `wotsChainPreimage`           -- inverted chain preimage at explicit hypertree `(ℓ, tree, leaf, c)`
                                        for strictly smaller Sperner digit `wotsDigit r* c < wotsDigit r_honest c`
    9. `uporsNodeSecondPreimage`     -- `NODE` collision inside the single height-10 U-PORS Octopus tree
   10. `uporsLeafSecondPreimage`     -- `ONE_TIME_KEY` collision at explicit U-PORS `(leaf_addr, leaf)`
   11. `uporsChainSecondPreimage`    -- `CHAIN` collision at explicit U-PORS `(leaf_addr, leaf, c, step)`
   12. `uporsUnrevealedChainPreimage`-- adversary produced the exact honest chain node `x_{d*}` for a
                                        U-PORS coordinate `(leaf_addr*, leaf*, c)` that was NEVER
                                        revealed at any depth `≤ d*` in `Q`
   13. `uporsCover`                  -- for EVERY opened leaf `j : Fin 10` and EVERY chain `c : Fin 3`,
                                        some honest query `q ∈ Q` opened `(leaf_addr*, leaf*_j)` at a
                                        depth `d_q ≤ d*_c` — literally the exact 3D lattice-meet +
                                        without-replacement subset-resilience cover event
                                        (`≤ 2^{-128.58}` elementary zero-cap-credit / `≤ 2^{-135.37}` true at `q ≤ 2^{32}`).
-/
import Blincs.Scheme

namespace Blincs

/-- An honest signing query recorded in the EUF-CMA transcript. -/
structure SignedQuery where
  ctx   : List UInt8
  hCtx  : ctx.length ≤ MAX_CONTEXT_LEN
  msg   : List UInt8
  draw  : Bytes 32
  ctrFt : UInt32

/-- Derived public digest values of an honest query `q`. -/
def queryE (H : HashOracle) (k : DerivedKeys) (q : SignedQuery) : Bytes 16 :=
  trunc16 (H.keyed k.k_salt q.draw.toList)

def queryShort (H : HashOracle) (k : DerivedKeys) (q : SignedQuery) : List UInt8 :=
  contentShort H k.k_content (queryE H k q) q.ctx q.msg

def queryR (H : HashOracle) (k : DerivedKeys) (q : SignedQuery) : Bytes 16 :=
  trunc16 (H.keyed k.k_r (queryShort H k q ++ frameContext q.ctx))

def querySeedDigest (H : HashOracle) (k : DerivedKeys) (q : SignedQuery) : Bytes 32 :=
  messageDigest H k.k_pub (queryR H k q) k.root (queryShort H k q) q.ctx

def querySelectDigest (H : HashOracle) (k : DerivedKeys) (q : SignedQuery) : Bytes 32 :=
  fewSelectDigest H k.k_pub (querySeedDigest H k q) q.ctrFt

/-- A query `q` covers U-PORS chain `(leafAddr, leaf, c)` at target depth `d` iff its selection digest
    lands on `leafAddr` and opens `leaf` at some slot `i : Fin 10` with depth `≤ d`. -/
def queryCoversUporsChain (H : HashOracle) (k : DerivedKeys) (q : SignedQuery)
    (leafAddr leaf : Nat) (c : Fin UPORS_N) (d : Nat) : Prop :=
  let Dsel := querySelectDigest H k q
  extractLeafAddr Dsel = leafAddr ∧
  ∃ (leaves : List Nat) (hLen : leaves.length = UPORS_K) (i : Fin UPORS_K),
    extractUporsLeaves Dsel = some leaves ∧
    leaves[i.val]'(by omega) = leaf ∧
    uporsDigit (extractUporsCodes H k.k_pub Dsel i) c ≤ d

/--
  **Exact Exhaustive Witness Type** for any valid `BLINCS-128-A2` forgery `(ctx*, M*, σ*)`
  against `seed`, honest signing transcript `Q`, and honest hypertree counter assignment `honestCtr`.
-/
inductive ForgeryWitness (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery)
    (honestCtr : Fin LAYERS → Nat → UInt16)
    (ctx M : List UInt8) (σ : Imprint) : Prop where
  /-- (1) Explicit 2nd-preimage of `Keyed(K_msg, ·)`: same `(e, ctx)`, distinct `M ≠ q.msg`, same `h_msg`. -/
  | contentHashSecondPreimage
      (q : SignedQuery) (hq : q ∈ Q)
      (he : σ.e = queryE H (deriveKeys H seed) q)
      (hctx : ctx = q.ctx)
      (hne : M ≠ q.msg)
      (hcol : contentHash H (deriveKeys H seed).k_content σ.e ctx M =
              contentHash H (deriveKeys H seed).k_content (queryE H (deriveKeys H seed) q) q.ctx q.msg)
  /-- (2) Explicit 2nd-preimage/collision of `Keyed(K_pub, tweak(MESSAGE) || ·)`: distinct input, same `D_seed`. -/
  | messageDigestCollision
      (q : SignedQuery) (hq : q ∈ Q)
      (hne : σ.r ≠ queryR H (deriveKeys H seed) q ∨
             contentShort H (deriveKeys H seed).k_content σ.e ctx M ≠ queryShort H (deriveKeys H seed) q ∨
             ctx ≠ q.ctx)
      (hcol : messageDigest H (deriveKeys H seed).k_pub σ.r (deriveKeys H seed).root
                (contentShort H (deriveKeys H seed).k_content σ.e ctx M) ctx =
              querySeedDigest H (deriveKeys H seed) q)
  /-- (3) Explicit 2nd-preimage/collision of `Keyed(K_pub, tweak(FEW_SELECT) || ·)`: distinct `(D_seed, ctr_ft)`, same `D_sel`. -/
  | fewSelectCollision
      (q : SignedQuery) (hq : q ∈ Q)
      (hne : messageDigest H (deriveKeys H seed).k_pub σ.r (deriveKeys H seed).root
                (contentShort H (deriveKeys H seed).k_content σ.e ctx M) ctx ≠
              querySeedDigest H (deriveKeys H seed) q ∨
              σ.ctrFt ≠ q.ctrFt)
      (hcol : fewSelectDigest H (deriveKeys H seed).k_pub
                (messageDigest H (deriveKeys H seed).k_pub σ.r (deriveKeys H seed).root
                  (contentShort H (deriveKeys H seed).k_content σ.e ctx M) ctx) σ.ctrFt =
              querySelectDigest H (deriveKeys H seed) q)
  /-- (4) Explicit `NODE` 2nd-preimage in hypertree layer `ℓ < 4`. -/
  | hypertreeNodeSecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (level p : Nat)
      (hLvl : 1 ≤ level ∧ level ≤ layerHeightNat ℓ.val)
      (L₁ R₁ L₂ R₂ : Bytes 16)
      (hne : L₁ ≠ L₂ ∨ R₁ ≠ R₂)
      (hcol : treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree level p L₁ R₁ =
              treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree level p L₂ R₂)
  /-- (5) Explicit `ONE_TIME_KEY` 2nd-preimage at hypertree `(ℓ, tree, leaf)`. -/
  | oneTimeKeySecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
      (ends₁ ends₂ : Fin WOTS_N → Bytes 16)
      (hne : ends₁ ≠ ends₂)
      (hcol : shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, UInt8.ofNat ℓ.val, tree, hTree, leaf, 0, 0⟩ (flattenBytes16 ends₁) =
              shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, UInt8.ofNat ℓ.val, tree, hTree, leaf, 0, 0⟩ (flattenBytes16 ends₂))
  /-- (6) Explicit `ONE_TIME_MSG` 128-bit 2nd-preimage at hypertree `(ℓ, tree, leaf)`:
          distinct `(mForged, ctrForged) ≠ (mHonest, ctrHonest)` hashing to the exact same 16-byte digest! -/
  | wotsMsgSecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
      (mForged mHonest : Bytes 16) (ctrForged ctrHonest : UInt16)
      (hne : mForged ≠ mHonest)
      (hcol : wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf mForged ctrForged =
              wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf mHonest ctrHonest)
  /-- (7) Explicit `CHAIN` 2nd-preimage at hypertree `(ℓ, tree, leaf, c, s)`. -/
  | wotsChainSecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
      (c : Fin WOTS_N) (s : Nat) (hs : s < WOTS_STEPS)
      (a b : Bytes 16) (hne : a ≠ b)
      (hcol : chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val s a =
              chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val s b)
  /-- (8) Explicit `S-WOTS+Z` chain preimage inversion: adversary produced honest chain node `x_{d₁}`
          strictly BEFORE the honest signer's Sperner digit `d₂` (`d₁ < d₂`) on a distinct message `m* ≠ m_honest`. -/
  | wotsChainPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
      (c : Fin WOTS_N) (rForged rHonest : Nat)
      (hlt : wotsDigit rForged c < wotsDigit rHonest c)
      (hpre : (σ.layers ℓ).wots c =
              chainIter (chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val)
                0 (wotsDigit rForged c)
                (chainStart H (deriveKeys H seed).k_sec (UInt8.ofNat ℓ.val) tree hTree leaf c.val))
  /-- (9) Explicit `NODE` 2nd-preimage inside the single height-10 U-PORS Octopus tree (`layer = 0x80`). -/
  | uporsNodeSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48)
      (level p : Nat) (hLvl : 1 ≤ level ∧ level ≤ UPORS_HEIGHT)
      (L₁ R₁ L₂ R₂ : Bytes 16) (hne : L₁ ≠ L₂ ∨ R₁ ≠ R₂)
      (hcol : treeCombine H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr level p L₁ R₁ =
              treeCombine H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr level p L₂ R₂)
  /-- (10) Explicit `ONE_TIME_KEY` 2nd-preimage in the U-PORS tree at `(leafAddr, leaf)`. -/
  | uporsLeafSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (leaf : UInt16)
      (ends₁ ends₂ : Fin UPORS_N → Bytes 16) (hne : ends₁ ≠ ends₂)
      (hcol : shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, uporsLayerByte, leafAddr, hAddr, leaf, 0, 0⟩ (flattenBytes16 ends₁) =
              shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, uporsLayerByte, leafAddr, hAddr, leaf, 0, 0⟩ (flattenBytes16 ends₂))
  /-- (11) Explicit `CHAIN` 2nd-preimage in the U-PORS tree at `(leafAddr, leaf, c, s)`. -/
  | uporsChainSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (leaf : UInt16)
      (c : Fin UPORS_N) (s : Nat) (hs : s < UPORS_STEPS)
      (a b : Bytes 16) (hne : a ≠ b)
      (hcol : chainStepFn H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr leaf c.val s a =
              chainStepFn H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr leaf c.val s b)
  /-- (12) Unrevealed U-PORS chain preimage: coordinate `(leafAddr, leaf, c)` was NEVER revealed
           at depth `≤ d` in `Q`, yet `σ.uporsChains j c` equals the exact honest chain node `x_d`! -/
  | uporsUnrevealedChainPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (j : Fin UPORS_K)
      (leaf : Nat) (c : Fin UPORS_N) (code : Fin UPORS_C)
      (hNotCovered : ∀ q ∈ Q, ¬ queryCoversUporsChain H (deriveKeys H seed) q leafAddr leaf c (uporsDigit code c))
      (hMatch : σ.uporsChains j c =
                chainIter (chainStepFn H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr (UInt16.ofNat leaf) c.val)
                  0 (uporsDigit code c)
                  (chainStart H (deriveKeys H seed).k_sec uporsLayerByte leafAddr hAddr (UInt16.ofNat leaf) c.val))
  /-- (13) Exact 3D Lattice-Meet + Without-Replacement U-PORS cover: for EVERY opened leaf `j : Fin 10`
           and EVERY chain `c : Fin 3`, some honest query `q ∈ Q` landed on `(leafAddr*, leaf*_j)` at
           depth `≤ uporsDigit (code*_j) c` (`≤ 2^{-128.58}` elementary / `≤ 2^{-135.37}` true at `q ≤ 2^{32}`). -/
  | uporsCover
      (leafAddr : Nat)
      (leaves : List Nat) (hLen : leaves.length = UPORS_K)
      (codes : Fin UPORS_K → Fin UPORS_C)
      (hCover : ∀ (j : Fin UPORS_K) (c : Fin UPORS_N),
        ∃ q ∈ Q, queryCoversUporsChain H (deriveKeys H seed) q leafAddr (leaves[j.val]'(by omega)) c (uporsDigit (codes j) c))

/-- Helper: extract an `S-WOTS+Z` or Merkle collision/preimage when a single hypertree layer produces
    the honest tree root from a DIFFERENT input message `mForged ≠ mHonest`. -/
private theorem layer_forgery_extract (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (honestCtr : Fin LAYERS → Nat → UInt16)
    (ctx M : List UInt8) (σ : Imprint)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (ℓ : Fin LAYERS) (mForged : Bytes 16)
    (hHonCtrValid : ValidWotsHash
      (wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
        (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
        (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
        (honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
        (honestCtr ℓ leafAddr)))
    (hne : mForged ≠ honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
    (hStepOk : (verifyLayerStep H (deriveKeys H seed).k_pub leafAddr hAddr ℓ mForged (σ.layers ℓ)).1)
    (hRoot : (verifyLayerStep H (deriveKeys H seed).k_pub leafAddr hAddr ℓ mForged (σ.layers ℓ)).2 =
             treeRoot H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub
               (UInt8.ofNat ℓ.val) (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
               (layerHeightNat ℓ.val) WOTS_N WOTS_STEPS) :
    ForgeryWitness H seed Q honestCtr ctx M σ := by
  let k := deriveKeys H seed
  let tree := layerTree leafAddr ℓ.val
  let hTree := layerTree_lt_48 leafAddr ℓ.val hAddr
  let leaf := layerLeaf leafAddr ℓ.val
  let lByte := UInt8.ofNat ℓ.val
  let leafU16 := UInt16.ofNat leaf
  let hForged := wotsMsgHash H k.k_pub lByte tree hTree leafU16 mForged (σ.layers ℓ).ctr
  let rForged := wotsRank hForged
  let forgedPk := chainVerifyGeneric H k.k_pub lByte tree hTree leafU16 WOTS_STEPS (wotsDigit rForged) (σ.layers ℓ).wots
  let honestPk := chainLeafPk H k.k_sec k.k_pub lByte tree hTree leafU16 WOTS_N WOTS_STEPS
  by_cases hpk : forgedPk = honestPk
  · let forgedEnds : Fin WOTS_N → Bytes 16 := fun c =>
      chainIter (chainStepFn H k.k_pub lByte tree hTree leafU16 c.val)
        (wotsDigit rForged c) (WOTS_STEPS - wotsDigit rForged c) ((σ.layers ℓ).wots c)
    let honestEnds : Fin WOTS_N → Bytes 16 := fun c =>
      chainEndpoint H k.k_sec k.k_pub lByte tree hTree leafU16 WOTS_STEPS c.val
    by_cases hends : forgedEnds = honestEnds
    · let mHonest := honestLayerInput H k.k_sec k.k_pub leafAddr hAddr ℓ.val
      let cHon := honestCtr ℓ leafAddr
      let hHonest := wotsMsgHash H k.k_pub lByte tree hTree leafU16 mHonest cHon
      let rHonest := wotsRank hHonest
      by_cases hRankEq : rForged = rHonest
      · have hMsgCol : hForged = hHonest := validWotsHash_eq_of_rank_eq hStepOk hHonCtrValid hRankEq
        exact ForgeryWitness.wotsMsgSecondPreimage ℓ tree hTree leafU16 mForged mHonest (σ.layers ℓ).ctr cHon hne hMsgCol
      · rcases wots_dominance hStepOk.2 hHonCtrValid.2 hRankEq with ⟨c, hlt⟩
        have hchainEq : forgedEnds c = honestEnds c := congrFun hends c
        have hd1 : wotsDigit rForged c ≤ WOTS_STEPS := wotsDigit_le_39 hStepOk.2 c
        rcases chain_forgery_extract
            (chainStepFn H k.k_pub lByte tree hTree leafU16 c.val)
            (chainStart H k.k_sec lByte tree hTree leafU16 c.val)
            ((σ.layers ℓ).wots c) hd1 hchainEq with hpre | ⟨s, a, b, _, hs2, hab, hcol⟩
        · exact ForgeryWitness.wotsChainPreimage ℓ tree hTree leafU16 c rForged rHonest hlt hpre
        · exact ForgeryWitness.wotsChainSecondPreimage ℓ tree hTree leafU16 c s hs2 a b hab hcol
    · exact ForgeryWitness.oneTimeKeySecondPreimage ℓ tree hTree leafU16 forgedEnds honestEnds hends hpk
  · have hLeafEq : honestPk = treeLeaves H k.k_sec k.k_pub lByte tree hTree (layerHeightNat ℓ.val) WOTS_N WOTS_STEPS ⟨leaf, layerLeaf_lt leafAddr ℓ.val⟩ := rfl
    rw [hLeafEq] at hpk
    rcases merkle_forgery_collision (treeCombine H k.k_pub lByte tree hTree) (layerHeightNat ℓ.val)
        (treeLeaves H k.k_sec k.k_pub lByte tree hTree (layerHeightNat ℓ.val) WOTS_N WOTS_STEPS)
        leaf (layerLeaf_lt leafAddr ℓ.val)
        forgedPk (List.ofFn (σ.layers ℓ).auth) (by simp) hpk hRoot with
      ⟨lvl, p, L₁, R₁, L₂, R₂, h1, h2, hdiff, hcol⟩
    exact ForgeryWitness.hypertreeNodeSecondPreimage ℓ tree hTree lvl p ⟨h1, h2⟩ L₁ R₁ L₂ R₂ hdiff hcol

/-- Helper: top-down induction on the 4 hypertree layers (`k = 4` down to `0`). -/
private theorem hypertree_top_down_extract (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (honestCtr : Fin LAYERS → Nat → UInt16)
    (ctx M : List UInt8) (σ : Imprint)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (hHonCtrs : ∀ ℓ : Fin LAYERS, ValidWotsHash
      (wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
        (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
        (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
        (honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
        (honestCtr ℓ leafAddr)))
    (uporsNode : Bytes 16) :
    ∀ (k : Nat) (hk : k ≤ LAYERS),
      let res := hypertreeVerifyUpTo H (deriveKeys H seed).k_pub leafAddr hAddr uporsNode σ.layers k hk
      res.1 →
      res.2 = honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr k →
      uporsNode = uporsRoot H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr
        (by have := params_tree_fits_tweak; omega) ∨
      ForgeryWitness H seed Q honestCtr ctx M σ
  | 0, _, _, hEq => Or.inl hEq
  | k + 1, hk, hOk, hEq => by
    unfold hypertreeVerifyUpTo at hOk hEq
    dsimp only at hOk hEq
    rcases hOk with ⟨hPrevOk, hStepOk⟩
    let prev := (hypertreeVerifyUpTo H (deriveKeys H seed).k_pub leafAddr hAddr uporsNode σ.layers k (by omega)).2
    let want := honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr k
    by_cases hprev : prev = want
    · exact hypertree_top_down_extract H seed Q honestCtr ctx M σ leafAddr hAddr hHonCtrs uporsNode k (by omega) hPrevOk hprev
    · exact Or.inr (layer_forgery_extract H seed Q honestCtr ctx M σ leafAddr hAddr ⟨k, hk⟩ prev
        (hHonCtrs ⟨k, hk⟩) hprev hStepOk hEq)

/-- Helper: given `uporsVerify H k.k_pub D_sel σ.uporsChains σ.uporsSibs = some (uporsRoot ...)`,
    extract a U-PORS Octopus `NODE` / `ONE_TIME_KEY` / `CHAIN` collision, an unrevealed chain preimage,
    OR the exact 3D lattice-meet + without-replacement `uporsCover` event! -/
private theorem upors_forgery_extract (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (honestCtr : Fin LAYERS → Nat → UInt16)
    (ctx M : List UInt8) (σ : Imprint) (D_sel : Bytes 32)
    (hUpors : uporsVerify H (deriveKeys H seed).k_pub D_sel σ.uporsChains σ.uporsSibs =
              some (uporsRoot H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub
                (extractLeafAddr D_sel) (extractLeafAddr_lt_48 D_sel))) :
    ForgeryWitness H seed Q honestCtr ctx M σ := by
  let k := deriveKeys H seed
  let leafAddr := extractLeafAddr D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  let codes := extractUporsCodes H k.k_pub D_sel
  unfold uporsVerify at hUpors
  dsimp only at hUpors
  cases hLeaves : extractUporsLeaves D_sel with
  | none => rw [hLeaves] at hUpors; cases hUpors
  | some leaves =>
    rw [hLeaves] at hUpors
    dsimp only at hUpors
    by_cases hLen : leaves.length = UPORS_K
    · rw [dite_eq_left hLen] at hUpors
      let leafPairs : List (Nat × Bytes 16) :=
        List.ofFn (fun j : Fin UPORS_K =>
          let leaf := leaves[j.val]'(by omega)
          let pk := chainVerifyGeneric H k.k_pub uporsLayerByte leafAddr hAddr48
            (UInt16.ofNat leaf) UPORS_STEPS (fun c => uporsDigit (codes j) c) (σ.uporsChains j)
          (leaf, pk))
      cases hClimb : octopusClimbAux (treeCombine H k.k_pub uporsLayerByte leafAddr hAddr48)
          0 UPORS_HEIGHT leafPairs (List.ofFn σ.uporsSibs) with
      | none => rw [hClimb] at hUpors; cases hUpors
      | some res =>
        rcases res with ⟨top, remSibs⟩
        rw [hClimb] at hUpors
        cases top with
        | nil => cases hUpors
        | cons head tail =>
          rcases head with ⟨idx, rootVal⟩
          cases idx with
          | succ _ => cases hUpors
          | zero =>
            cases tail with
            | cons _ _ => cases hUpors
            | nil =>
              by_cases hAll : remSibs.all (fun z => z.toList == zero16.toList) = true
              · simp only [hAll, ↓reduceIte] at hUpors
                have hRootEq : rootVal = uporsRoot H k.k_sec k.k_pub leafAddr hAddr48 := Option.some.inj hUpors
                rw [hRootEq] at hClimb
                rcases octopus_forgery_collision (treeCombine H k.k_pub uporsLayerByte leafAddr hAddr48)
                    (uporsLeafFn H k.k_sec k.k_pub leafAddr hAddr48) UPORS_HEIGHT leafPairs
                    (List.ofFn σ.uporsSibs) remSibs hClimb with hAllLeaves | ⟨lvl, p, L₁, R₁, L₂, R₂, h1, h2, hdiff, hcol⟩
                · -- Every one of the 10 opened U-PORS leaves matched `uporsLeafFn`!
                  by_cases hCover : ∀ (j : Fin UPORS_K) (c : Fin UPORS_N),
                      ∃ q ∈ Q, queryCoversUporsChain H k q leafAddr (leaves[j.val]'(by omega)) c (uporsDigit (codes j) c)
                  · exact ForgeryWitness.uporsCover leafAddr leaves hLen codes hCover
                  · have hNotAllJ : ∃ j : Fin UPORS_K, ¬ ∀ c : Fin UPORS_N,
                        ∃ q ∈ Q, queryCoversUporsChain H k q leafAddr (leaves[j.val]'(by omega)) c (uporsDigit (codes j) c) :=
                      Classical.not_forall.mp hCover
                    rcases hNotAllJ with ⟨j, hjNot⟩
                    have hNotAllC : ∃ c : Fin UPORS_N,
                        ¬ ∃ q ∈ Q, queryCoversUporsChain H k q leafAddr (leaves[j.val]'(by omega)) c (uporsDigit (codes j) c) :=
                      Classical.not_forall.mp hjNot
                    rcases hNotAllC with ⟨c, hcNot⟩
                    have hNever : ∀ q ∈ Q, ¬ queryCoversUporsChain H k q leafAddr (leaves[j.val]'(by omega)) c (uporsDigit (codes j) c) :=
                      fun q hq hr => hcNot ⟨q, hq, hr⟩
                    let leaf := leaves[j.val]'(by omega)
                    let leafU16 := UInt16.ofNat leaf
                    let digits := fun ch : Fin UPORS_N => uporsDigit (codes j) ch
                    let forgedPk := chainVerifyGeneric H k.k_pub uporsLayerByte leafAddr hAddr48 leafU16 UPORS_STEPS digits (σ.uporsChains j)
                    have hMem : (leaf, forgedPk) ∈ leafPairs := by
                      unfold leafPairs
                      rw [List.mem_ofFn]
                      exact ⟨j, rfl⟩
                    have hPkEq : forgedPk = chainLeafPk H k.k_sec k.k_pub uporsLayerByte leafAddr hAddr48 leafU16 UPORS_N UPORS_STEPS :=
                      hAllLeaves (leaf, forgedPk) hMem
                    let forgedEnds : Fin UPORS_N → Bytes 16 := fun ch =>
                      chainIter (chainStepFn H k.k_pub uporsLayerByte leafAddr hAddr48 leafU16 ch.val)
                        (digits ch) (UPORS_STEPS - digits ch) (σ.uporsChains j ch)
                    let honestEnds : Fin UPORS_N → Bytes 16 := fun ch =>
                      chainEndpoint H k.k_sec k.k_pub uporsLayerByte leafAddr hAddr48 leafU16 UPORS_STEPS ch.val
                    by_cases hEnds : forgedEnds = honestEnds
                    · have hchainEq : forgedEnds c = honestEnds c := congrFun hEnds c
                      have hd : digits c ≤ UPORS_STEPS := uporsDigit_le_23 (codes j) c
                      rcases chain_forgery_extract
                          (chainStepFn H k.k_pub uporsLayerByte leafAddr hAddr48 leafU16 c.val)
                          (chainStart H k.k_sec uporsLayerByte leafAddr hAddr48 leafU16 c.val)
                          (σ.uporsChains j c) hd hchainEq with hpre | ⟨s, a, b, _, hs2, hab, hcol⟩
                      · exact ForgeryWitness.uporsUnrevealedChainPreimage leafAddr hAddr48 j leaf c (codes j) hNever hpre
                      · exact ForgeryWitness.uporsChainSecondPreimage leafAddr hAddr48 leafU16 c s hs2 a b hab hcol
                    · exact ForgeryWitness.uporsLeafSecondPreimage leafAddr hAddr48 leafU16 forgedEnds honestEnds hEnds hPkEq
                · exact ForgeryWitness.uporsNodeSecondPreimage leafAddr hAddr48 lvl p ⟨h1, h2⟩ L₁ R₁ L₂ R₂ hdiff hcol
              · simp only [hAll] at hUpors; cases hUpors
    · rw [dite_eq_right hLen] at hUpors; cases hUpors

/--
  **Main Machine-Checked Security Decomposition Theorem (`BLINCS-128-A2`):**
  For ANY `HashOracle`, ANY `seed`, ANY honest signing transcript `Q`, ANY valid honest hypertree
  counter table `honestCtr`, and ANY fresh valid forgery `(ctx*, M*, σ*)`
  (`(ctx*, M*) ∉ Q`, `verify H (signetId H seed) ctx* M* σ*`),
  at least ONE of the 13 explicit `ForgeryWitness` events holds!
-/
theorem blincs_forgery_dichotomy (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (honestCtr : Fin LAYERS → Nat → UInt16)
    (hHonCtrs : ∀ (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS) (ℓ : Fin LAYERS),
      ValidWotsHash
        (wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
          (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
          (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
          (honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
          (honestCtr ℓ leafAddr)))
    (ctx M : List UInt8) (σ : Imprint)
    (hFresh : ∀ q ∈ Q, (q.ctx, q.msg) ≠ (ctx, M))
    (hVer : verify H (signetId H seed) ctx M σ) :
    ForgeryWitness H seed Q honestCtr ctx M σ := by
  rcases hVer with ⟨hCtx, uporsNode, hUporsVer, hHtOk, hRootEq⟩
  rcases verifierKeys_match_deriveKeys H seed with ⟨hkpub, hroot, hkcontent⟩
  rw [hkpub, hroot, hkcontent] at hUporsVer hHtOk hRootEq
  let k := deriveKeys H seed
  let short := contentShort H k.k_content σ.e ctx M
  let D_seed := messageDigest H k.k_pub σ.r k.root short ctx
  let D_sel := fewSelectDigest H k.k_pub D_seed σ.ctrFt
  let leafAddr := extractLeafAddr D_sel
  let hAddr := extractLeafAddr_lt D_sel
  by_cases hSeedHit : ∃ q ∈ Q, D_seed = querySeedDigest H k q
  · rcases hSeedHit with ⟨q, hq, hDeq⟩
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
  · by_cases hSelHit : ∃ q ∈ Q, D_sel = querySelectDigest H k q
    · rcases hSelHit with ⟨q, hq, hSelEq⟩
      have hSeedNe : D_seed ≠ querySeedDigest H k q := fun h => hSeedHit ⟨q, hq, h⟩
      exact ForgeryWitness.fewSelectCollision q hq (Or.inl hSeedNe) hSelEq
    · have hTopMatch :
          (hypertreeVerifyUpTo H k.k_pub leafAddr hAddr uporsNode σ.layers LAYERS (Nat.le_refl _)).2 =
          honestLayerInput H k.k_sec k.k_pub leafAddr hAddr LAYERS := by
        have hLeft : (hypertreeVerifyUpTo H k.k_pub leafAddr hAddr uporsNode σ.layers LAYERS (Nat.le_refl _)).2 = k.root := hRootEq
        rw [hLeft]
        have hzero : layerTree leafAddr 3 = 0 := top_layerTree_zero hAddr
        have h4 : honestLayerInput H k.k_sec k.k_pub leafAddr hAddr LAYERS =
            treeRoot H k.k_sec k.k_pub 3 (layerTree leafAddr 3) (layerTree_lt_48 leafAddr 3 hAddr)
              (layerHeightNat 3) WOTS_N WOTS_STEPS := rfl
        have hkroot : k.root = treeRoot H k.k_sec k.k_pub 3 0 (by decide) TOP_HEIGHT WOTS_N WOTS_STEPS := rfl
        rw [h4, hkroot]
        have hTop : ∀ (t : Nat) (ht : t < 2 ^ 48), t = 0 →
            treeRoot H k.k_sec k.k_pub 3 0 (by decide) TOP_HEIGHT WOTS_N WOTS_STEPS =
            treeRoot H k.k_sec k.k_pub 3 t ht (layerHeightNat 3) WOTS_N WOTS_STEPS := by
          intro t ht h0; subst h0
          have hh : layerHeightNat 3 = TOP_HEIGHT := rfl
          simp only [hh]
        exact hTop (layerTree leafAddr 3) (layerTree_lt_48 leafAddr 3 hAddr) hzero
      rcases hypertree_top_down_extract H seed Q honestCtr ctx M σ leafAddr hAddr
          (hHonCtrs leafAddr hAddr) uporsNode LAYERS (Nat.le_refl _) hHtOk hTopMatch with
        hUporsEq | hWitness
      · rw [hUporsEq] at hUporsVer
        exact upors_forgery_extract H seed Q honestCtr ctx M σ D_sel hUporsVer
      · exact hWitness

/--
  **Two-Stage Salt-Failure Hedged Fallback Theorem (Secondary Security Goal):**
  Even if the salt source (`saltseed`) is completely stuck or leaked so the exact same `draw`
  (and hence the exact same content salt `e`) is reused for two distinct pairs
  `(ctx₁, M₁) ≠ (ctx₂, M₂)` (with valid context lengths), EITHER:
    (a) `ctx₁ = ctx₂`, `M₁ ≠ M₂`, and `h_msg` suffers a 256-bit keyed-BLAKE3 collision under `K_msg`, OR
    (b) the inputs `short₁ || frameContext ctx₁` and `short₂ || frameContext ctx₂` fed into the
        secret-keyed randomizer PRF `Keyed(K_R, ·)` are STRICTLY DISTINCT (so `R` and `D_seed` remain freshly hedged!).
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
    have hCtxFrameEq : frameContext ctx₁ = frameContext ctx₂ := by
      have := congrArg (List.drop 48) hIn
      simpa [hShortLen₁, hShortLen₂] using this
    have hCtxEq : ctx₁ = ctx₂ := by
      have hpf := frameContext_prefix_free hCtx₁ hCtx₂ (by simpa using hCtxFrameEq : frameContext ctx₁ ++ [] = frameContext ctx₂ ++ [])
      exact hpf.1
    have hHashEq : contentHash H k.k_content e ctx₁ M₁ = contentHash H k.k_content e ctx₂ M₂ := by
      unfold contentShort at hShortEq
      have := congrArg (List.drop 16) hShortEq
      simp only [Bytes.toList_length, List.drop_left'] at this
      exact Bytes.toList_injective this
    have hMne : M₁ ≠ M₂ := by
      intro hMeq
      apply hne
      rw [hCtxEq, hMeq]
    exact ⟨hCtxEq, hMne, hHashEq⟩
  · exact Or.inr hIn

end Blincs
