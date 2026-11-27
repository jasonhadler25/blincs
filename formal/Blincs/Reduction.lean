/-
  BLINCS-128-A2 Machine-Checked Deterministic Forgery Witness Dichotomy (`S-WOTS+Z` + `U-PORS`).

  What this file mechanically proves (ZERO `sorry`, ZERO custom axioms, over an arbitrary
  deterministic `HashOracle`):
    Given ANY 32-byte `seed`, ANY honest signing transcript `Q`, ANY physical-address-indexed
    honest hypertree counter table `honestCtr : Fin LAYERS → Nat → Nat → UInt16` (independent of
    unused lower address bits), and ANY fresh valid forgery `(ctx*, M*, σ*)` passing
    `verify H (signetId H seed) ctx* M* σ*` with `(ctx*, M*) ∉ Q`:

    At least ONE of 13 **provenance-bound, target-bound** `ForgeryWitness` events holds:
      1. `contentHashSecondPreimage`    -- same `(σ.e, ctx)` as `q ∈ Q`, `M ≠ q.msg`, `h_msg` collision
      2. `messageDigestCollision`       -- distinct `(σ.r, short, ctx)` colliding onto `querySeedDigest q`
      3. `fewSelectCollision`           -- fresh `D_seed*` colliding onto `querySelectDigest q`
      4. `hypertreeNodeSecondPreimage`  -- forged child pair distinct from EXACT honest `treeNodeAt` children,
                                           colliding onto EXACT honest hypertree `NODE`
      5. `oneTimeKeySecondPreimage`     -- forged WOTS endpoints distinct from EXACT honest endpoints,
                                           colliding onto EXACT honest `ONE_TIME_KEY`
      6. `wotsMsgSecondPreimage`        -- forged `mForged ≠ honestLayerInput` colliding onto EXACT honest
                                           `wotsMsgHash ... honestLayerInput (honestCtr ℓ tree leaf)`
      7. `wotsChainSecondPreimage`      -- forged value `a` distinct from EXACT honest chain node at step `s`,
                                           colliding onto EXACT honest `chainStepFn s (honestNode s)`
      8. `wotsChainPreimage`            -- `(σ.layers ℓ).wots c` equals EXACT honest chain node at strictly
                                           smaller Sperner digit `wotsDigit rForged c < wotsDigit rHonest c`
      9. `uporsNodeSecondPreimage`      -- forged child pair distinct from EXACT honest U-PORS `treeNodeAt`
                                           children, colliding onto EXACT honest U-PORS `NODE`
     10. `uporsLeafSecondPreimage`      -- forged U-PORS endpoints distinct from EXACT honest endpoints,
                                           colliding onto EXACT honest U-PORS `ONE_TIME_KEY`
     11. `uporsChainSecondPreimage`     -- forged value `a` distinct from EXACT honest U-PORS chain node at `s`,
                                           colliding onto EXACT honest U-PORS `CHAIN` step
     12. `uporsUnrevealedChainPreimage` -- bound to the EXACT parsed `(leafAddr, leaves, codes)` of `(ctx*, M*, σ*)`:
                                           coordinate `(leafAddr, leaves[j], c)` was never covered at depth `≤ d`
                                           in `Q`, yet `σ.uporsChains j c` equals the exact honest node `x_d`
     13. `uporsCover`                   -- bound to the EXACT parsed, FRESH `(leafAddr, leaves, codes)` of
                                           `(ctx*, M*, σ*)` (`leaves.length = 10`, `leaves.Nodup`,
                                           `D_seed* ≠ querySeedDigest q`, `D_sel* ≠ querySelectDigest q`):
                                           every `(leaves[j], c)` is covered at depth `≤ uporsDigit (codes j) c` in `Q`.

  Note on scope: this formalizes deterministic reconstruction and provenance-bound witness extraction
  for the exact `SPEC.md` byte specification; probabilistic / ROM advantage bounds (PRF hybrids,
  query costs, and capped-history `U-PORS` cover probabilities) are analyzed in the accompanying paper.
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
    lands on `leafAddr`, extracts 10 distinct leaves, extracts 10 codewords via `FEW_CODE(D_seed, ctr_ft)`,
    and opens `leaf` at some slot `i : Fin 10` with depth `≤ d`. -/
def queryCoversUporsChain (H : HashOracle) (k : DerivedKeys) (q : SignedQuery)
    (leafAddr leaf : Nat) (c : Fin UPORS_N) (d : Nat) : Prop :=
  let Dseed := querySeedDigest H k q
  let Dsel  := querySelectDigest H k q
  extractLeafAddr Dsel = leafAddr ∧
  ∃ (leaves : List Nat) (hLen : leaves.length = UPORS_K)
    (qCodes : Fin UPORS_K → Fin UPORS_C) (i : Fin UPORS_K),
    extractUporsLeaves Dsel = some leaves ∧
    extractUporsCodes H k.k_pub Dseed q.ctrFt = some qCodes ∧
    leaves[i.val]'(by omega) = leaf ∧
    uporsDigit (qCodes i) c ≤ d

/-- Derived public digests of the candidate forgery `(ctx, M, σ)`. -/
def forgedShort (H : HashOracle) (k : DerivedKeys) (ctx M : List UInt8) (σ : Imprint) : List UInt8 :=
  contentShort H k.k_content σ.e ctx M

def forgedSeedDigest (H : HashOracle) (k : DerivedKeys) (ctx M : List UInt8) (σ : Imprint) : Bytes 32 :=
  messageDigest H k.k_pub σ.r k.root (forgedShort H k ctx M σ) ctx

def forgedSelectDigest (H : HashOracle) (k : DerivedKeys) (ctx M : List UInt8) (σ : Imprint) : Bytes 32 :=
  fewSelectDigest H k.k_pub (forgedSeedDigest H k ctx M σ) σ.ctrFt

/--
  **Exact Target-Bound & Provenance-Bound Witness Type** for any valid `BLINCS-128-A2` forgery
  `(ctx, M, σ)` against `seed`, honest transcript `Q`, and physical-address-indexed counter table
  `honestCtr : Fin LAYERS → Nat → Nat → UInt16` (`ℓ, tree, leaf ↦ ctr`).
-/
inductive ForgeryWitness (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery)
    (honestCtr : Fin LAYERS → Nat → Nat → UInt16)
    (ctx M : List UInt8) (σ : Imprint) : Prop where
  /-- (1) Explicit 2nd-preimage of `Keyed(K_msg, ·)`: same `(e, ctx)`, distinct `M ≠ q.msg`, same `h_msg`. -/
  | contentHashSecondPreimage
      (q : SignedQuery) (hq : q ∈ Q)
      (he : σ.e = queryE H (deriveKeys H seed) q)
      (hctx : ctx = q.ctx)
      (hne : M ≠ q.msg)
      (hcol : contentHash H (deriveKeys H seed).k_content σ.e ctx M =
              contentHash H (deriveKeys H seed).k_content (queryE H (deriveKeys H seed) q) q.ctx q.msg)
  /-- (2) Explicit 2nd-preimage of `Keyed(K_pub, tweak(MESSAGE) || ·)` onto `querySeedDigest q`. -/
  | messageDigestCollision
      (q : SignedQuery) (hq : q ∈ Q)
      (hne : σ.r ≠ queryR H (deriveKeys H seed) q ∨
             forgedShort H (deriveKeys H seed) ctx M σ ≠ queryShort H (deriveKeys H seed) q ∨
             ctx ≠ q.ctx)
      (hcol : forgedSeedDigest H (deriveKeys H seed) ctx M σ = querySeedDigest H (deriveKeys H seed) q)
  /-- (3) Explicit 2nd-preimage of `Keyed(K_pub, tweak(FEW_SELECT) || ·)` onto `querySelectDigest q`. -/
  | fewSelectCollision
      (q : SignedQuery) (hq : q ∈ Q)
      (hne : forgedSeedDigest H (deriveKeys H seed) ctx M σ ≠ querySeedDigest H (deriveKeys H seed) q ∨
             σ.ctrFt ≠ q.ctrFt)
      (hcol : forgedSelectDigest H (deriveKeys H seed) ctx M σ = querySelectDigest H (deriveKeys H seed) q)
  /-- (4) Target-bound hypertree `NODE` 2nd-preimage against the EXACT honest child pair at `(ℓ, tree, level, p)`. -/
  | hypertreeNodeSecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (level p : Nat)
      (hLvl : 1 ≤ level ∧ level ≤ layerHeightNat ℓ.val)
      (L₁ R₁ : Bytes 16)
      (hne : L₁ ≠ treeNodeAt (treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree)
                    (treeLeafFn H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree WOTS_N WOTS_STEPS)
                    (level - 1) (2 * p) ∨
             R₁ ≠ treeNodeAt (treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree)
                    (treeLeafFn H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree WOTS_N WOTS_STEPS)
                    (level - 1) (2 * p + 1))
      (hcol : treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree level p L₁ R₁ =
              treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree level p
                (treeNodeAt (treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree)
                  (treeLeafFn H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree WOTS_N WOTS_STEPS)
                  (level - 1) (2 * p))
                (treeNodeAt (treeCombine H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree)
                  (treeLeafFn H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree WOTS_N WOTS_STEPS)
                  (level - 1) (2 * p + 1)))
  /-- (5) Target-bound hypertree `ONE_TIME_KEY` 2nd-preimage against the EXACT honest WOTS endpoints. -/
  | oneTimeKeySecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
      (ends₁ : Fin WOTS_N → Bytes 16)
      (hne : ends₁ ≠ fun c => chainEndpoint H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub
                                (UInt8.ofNat ℓ.val) tree hTree leaf WOTS_N WOTS_STEPS c.val)
      (hcol : shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, UInt8.ofNat ℓ.val, tree, hTree, leaf, 0, 0⟩ (flattenBytes16 ends₁) =
              chainLeafPk H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub
                (UInt8.ofNat ℓ.val) tree hTree leaf WOTS_N WOTS_STEPS)
  /-- (6) Target-bound `ONE_TIME_MSG` 128-bit 2nd-preimage against the EXACT honest child root and physical-address counter. -/
  | wotsMsgSecondPreimage
      (ℓ : Fin LAYERS) (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
      (mForged : Bytes 16)
      (hne : mForged ≠ honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
      (hcol : wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
                (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
                (UInt16.ofNat (layerLeaf leafAddr ℓ.val)) mForged (σ.layers ℓ).ctr =
              wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
                (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
                (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
                (honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
                (honestCtr ℓ (layerTree leafAddr ℓ.val) (layerLeaf leafAddr ℓ.val)))
  /-- (7) Target-bound hypertree `CHAIN` 2nd-preimage against the EXACT honest chain node at step `s`. -/
  | wotsChainSecondPreimage
      (ℓ : Fin LAYERS) (tree : Nat) (hTree : tree < 2 ^ 48) (leaf : UInt16)
      (c : Fin WOTS_N) (s : Nat) (hs : s < WOTS_STEPS)
      (a : Bytes 16)
      (hne : a ≠ chainIter (chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val)
                   0 s (chainStart H (deriveKeys H seed).k_sec (UInt8.ofNat ℓ.val) tree hTree leaf WOTS_N c.val))
      (hcol : chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val s a =
              chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val s
                (chainIter (chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val) tree hTree leaf c.val)
                  0 s (chainStart H (deriveKeys H seed).k_sec (UInt8.ofNat ℓ.val) tree hTree leaf WOTS_N c.val)))
  /-- (8) Target-bound `S-WOTS+Z` chain preimage inversion strictly before the honest Sperner digit. -/
  | wotsChainPreimage
      (ℓ : Fin LAYERS) (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
      (mForged : Bytes 16)
      (hne : mForged ≠ honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
      (c : Fin WOTS_N)
      (hlt : wotsDigit (wotsRank (wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
                (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
                (UInt16.ofNat (layerLeaf leafAddr ℓ.val)) mForged (σ.layers ℓ).ctr)) c <
             wotsDigit (wotsRank (wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
                (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
                (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
                (honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
                (honestCtr ℓ (layerTree leafAddr ℓ.val) (layerLeaf leafAddr ℓ.val)))) c)
      (hpre : (σ.layers ℓ).wots c =
              chainIter (chainStepFn H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
                  (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
                  (UInt16.ofNat (layerLeaf leafAddr ℓ.val)) c.val)
                0 (wotsDigit (wotsRank (wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
                    (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
                    (UInt16.ofNat (layerLeaf leafAddr ℓ.val)) mForged (σ.layers ℓ).ctr)) c)
                (chainStart H (deriveKeys H seed).k_sec (UInt8.ofNat ℓ.val)
                  (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
                  (UInt16.ofNat (layerLeaf leafAddr ℓ.val)) WOTS_N c.val))
  /-- (9) Target-bound U-PORS Octopus `NODE` 2nd-preimage against the EXACT honest child pair. -/
  | uporsNodeSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48)
      (level p : Nat) (hLvl : 1 ≤ level ∧ level ≤ UPORS_HEIGHT)
      (L₁ R₁ : Bytes 16)
      (hne : L₁ ≠ treeNodeAt (treeCombine H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr)
                    (uporsLeafFn H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr)
                    (level - 1) (2 * p) ∨
             R₁ ≠ treeNodeAt (treeCombine H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr)
                    (uporsLeafFn H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr)
                    (level - 1) (2 * p + 1))
      (hcol : treeCombine H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr level p L₁ R₁ =
              treeCombine H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr level p
                (treeNodeAt (treeCombine H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr)
                  (uporsLeafFn H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr)
                  (level - 1) (2 * p))
                (treeNodeAt (treeCombine H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr)
                  (uporsLeafFn H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr)
                  (level - 1) (2 * p + 1)))
  /-- (10) Target-bound U-PORS `ONE_TIME_KEY` 2nd-preimage against the EXACT honest U-PORS leaf endpoints. -/
  | uporsLeafSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (leaf : UInt16)
      (ends₁ : Fin UPORS_N → Bytes 16)
      (hne : ends₁ ≠ fun c => chainEndpoint H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub
                                uporsLayerByte leafAddr hAddr leaf UPORS_N UPORS_STEPS c.val)
      (hcol : shortHash H (deriveKeys H seed).k_pub ⟨.oneTimeKey, uporsLayerByte, leafAddr, hAddr, leaf, 0, 0⟩ (flattenBytes16 ends₁) =
              chainLeafPk H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub
                uporsLayerByte leafAddr hAddr leaf UPORS_N UPORS_STEPS)
  /-- (11) Target-bound U-PORS `CHAIN` 2nd-preimage against the EXACT honest chain node at step `s`. -/
  | uporsChainSecondPreimage
      (leafAddr : Nat) (hAddr : leafAddr < 2 ^ 48) (leaf : UInt16)
      (c : Fin UPORS_N) (s : Nat) (hs : s < UPORS_STEPS)
      (a : Bytes 16)
      (hne : a ≠ chainIter (chainStepFn H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr leaf c.val)
                   0 s (chainStart H (deriveKeys H seed).k_sec uporsLayerByte leafAddr hAddr leaf UPORS_N c.val))
      (hcol : chainStepFn H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr leaf c.val s a =
              chainStepFn H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr leaf c.val s
                (chainIter (chainStepFn H (deriveKeys H seed).k_pub uporsLayerByte leafAddr hAddr leaf c.val)
                  0 s (chainStart H (deriveKeys H seed).k_sec uporsLayerByte leafAddr hAddr leaf UPORS_N c.val)))
  /-- (12) Provenance-bound unrevealed U-PORS chain preimage: tied to the EXACT parsed `(leafAddr, leaves, codes)`
           of `(ctx, M, σ)`, never covered at depth `≤ d` in `Q`, yet `σ.uporsChains j c` equals `x_d`. -/
  | uporsUnrevealedChainPreimage
      (leaves : List Nat) (hLen : leaves.length = UPORS_K) (hNodup : leaves.Nodup)
      (codes : Fin UPORS_K → Fin UPORS_C)
      (hLeaves : extractUporsLeaves (forgedSelectDigest H (deriveKeys H seed) ctx M σ) = some leaves)
      (hCodes : extractUporsCodes H (deriveKeys H seed).k_pub (forgedSeedDigest H (deriveKeys H seed) ctx M σ) σ.ctrFt = some codes)
      (j : Fin UPORS_K) (c : Fin UPORS_N)
      (hNotCovered : ∀ q ∈ Q, ¬ queryCoversUporsChain H (deriveKeys H seed) q
        (extractLeafAddr (forgedSelectDigest H (deriveKeys H seed) ctx M σ))
        (leaves[j.val]'(by omega)) c (uporsDigit (codes j) c))
      (hMatch : σ.uporsChains j c =
                chainIter (chainStepFn H (deriveKeys H seed).k_pub uporsLayerByte
                    (extractLeafAddr (forgedSelectDigest H (deriveKeys H seed) ctx M σ))
                    (extractLeafAddr_lt_48 (forgedSelectDigest H (deriveKeys H seed) ctx M σ))
                    (UInt16.ofNat (leaves[j.val]'(by omega))) c.val)
                  0 (uporsDigit (codes j) c)
                  (chainStart H (deriveKeys H seed).k_sec uporsLayerByte
                    (extractLeafAddr (forgedSelectDigest H (deriveKeys H seed) ctx M σ))
                    (extractLeafAddr_lt_48 (forgedSelectDigest H (deriveKeys H seed) ctx M σ))
                    (UInt16.ofNat (leaves[j.val]'(by omega))) UPORS_N c.val))
  /-- (13) Provenance-bound, FRESH `U-PORS` cover event: tied directly to the EXACT parsed
           `(leafAddr*, leaves*, codes*)` of the forged `(ctx, M, σ)` with `leaves*.length = 10`,
           `leaves*.Nodup`, and fresh digests `D_seed* ≠ querySeedDigest q`, `D_sel* ≠ querySelectDigest q`! -/
  | uporsCover
      (leaves : List Nat) (hLen : leaves.length = UPORS_K) (hNodup : leaves.Nodup)
      (codes : Fin UPORS_K → Fin UPORS_C)
      (hFreshSeed : ∀ q ∈ Q, forgedSeedDigest H (deriveKeys H seed) ctx M σ ≠ querySeedDigest H (deriveKeys H seed) q)
      (hFreshSel : ∀ q ∈ Q, forgedSelectDigest H (deriveKeys H seed) ctx M σ ≠ querySelectDigest H (deriveKeys H seed) q)
      (hLeaves : extractUporsLeaves (forgedSelectDigest H (deriveKeys H seed) ctx M σ) = some leaves)
      (hCodes : extractUporsCodes H (deriveKeys H seed).k_pub (forgedSeedDigest H (deriveKeys H seed) ctx M σ) σ.ctrFt = some codes)
      (hCover : ∀ (j : Fin UPORS_K) (c : Fin UPORS_N),
        ∃ q ∈ Q, queryCoversUporsChain H (deriveKeys H seed) q
          (extractLeafAddr (forgedSelectDigest H (deriveKeys H seed) ctx M σ))
          (leaves[j.val]'(by omega)) c (uporsDigit (codes j) c))

/-- Helper: extract a target-bound `S-WOTS+Z` or Merkle collision/preimage when layer `ℓ`
    reconstructs the honest tree root from a distinct input `mForged ≠ honestLayerInput`. -/
private theorem layer_forgery_extract (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (honestCtr : Fin LAYERS → Nat → Nat → UInt16)
    (ctx M : List UInt8) (σ : Imprint)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (ℓ : Fin LAYERS) (mForged : Bytes 16)
    (hHonCtrValid : ValidWotsHash
      (wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
        (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
        (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
        (honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
        (honestCtr ℓ (layerTree leafAddr ℓ.val) (layerLeaf leafAddr ℓ.val))))
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
      chainEndpoint H k.k_sec k.k_pub lByte tree hTree leafU16 WOTS_N WOTS_STEPS c.val
    by_cases hends : forgedEnds = honestEnds
    · let mHonest := honestLayerInput H k.k_sec k.k_pub leafAddr hAddr ℓ.val
      let cHon := honestCtr ℓ tree leaf
      let hHonest := wotsMsgHash H k.k_pub lByte tree hTree leafU16 mHonest cHon
      let rHonest := wotsRank hHonest
      by_cases hRankEq : rForged = rHonest
      · have hMsgCol : hForged = hHonest := validWotsHash_eq_of_rank_eq hStepOk hHonCtrValid hRankEq
        exact ForgeryWitness.wotsMsgSecondPreimage ℓ leafAddr hAddr mForged hne hMsgCol
      · rcases wots_dominance (wotsRank_lt_sliceCount hForged) (wotsRank_lt_sliceCount hHonest) hRankEq with ⟨c, hlt⟩
        have hchainEq : forgedEnds c = honestEnds c := congrFun hends c
        have hd1 : wotsDigit rForged c ≤ WOTS_STEPS := wotsDigit_le_39 (wotsRank_lt_sliceCount hForged) c
        rcases chain_forgery_extract
            (chainStepFn H k.k_pub lByte tree hTree leafU16 c.val)
            (chainStart H k.k_sec lByte tree hTree leafU16 WOTS_N c.val)
            ((σ.layers ℓ).wots c) hd1 hchainEq with hpre | ⟨s, a, _, hs2, hne_a, hcol⟩
        · exact ForgeryWitness.wotsChainPreimage ℓ leafAddr hAddr mForged hne c hlt hpre
        · exact ForgeryWitness.wotsChainSecondPreimage ℓ tree hTree leafU16 c s hs2 a hne_a hcol
    · exact ForgeryWitness.oneTimeKeySecondPreimage ℓ tree hTree leafU16 forgedEnds hends hpk
  · have hLeafEq : honestPk = treeLeaves H k.k_sec k.k_pub lByte tree hTree (layerHeightNat ℓ.val) WOTS_N WOTS_STEPS ⟨leaf, layerLeaf_lt leafAddr ℓ.val⟩ := rfl
    rw [hLeafEq] at hpk
    rcases merkle_forgery_collision
        (treeCombine H k.k_pub lByte tree hTree)
        (treeLeafFn H k.k_sec k.k_pub lByte tree hTree WOTS_N WOTS_STEPS)
        (layerHeightNat ℓ.val)
        (treeLeaves H k.k_sec k.k_pub lByte tree hTree (layerHeightNat ℓ.val) WOTS_N WOTS_STEPS)
        (fun _ => rfl)
        leaf (layerLeaf_lt leafAddr ℓ.val)
        forgedPk (List.ofFn (σ.layers ℓ).auth) (by simp) hpk hRoot with
      ⟨lvl, p, L₁, R₁, h1, h2, hdiff, hcol⟩
    exact ForgeryWitness.hypertreeNodeSecondPreimage ℓ tree hTree lvl p ⟨h1, h2⟩ L₁ R₁ hdiff hcol

/-- Helper: top-down induction on the 4 hypertree layers (`k = 4` down to `0`). -/
private theorem hypertree_top_down_extract (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (honestCtr : Fin LAYERS → Nat → Nat → UInt16)
    (ctx M : List UInt8) (σ : Imprint)
    (leafAddr : Nat) (hAddr : leafAddr < 2 ^ HYPER_BITS)
    (hHonCtrs : ∀ ℓ : Fin LAYERS, ValidWotsHash
      (wotsMsgHash H (deriveKeys H seed).k_pub (UInt8.ofNat ℓ.val)
        (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
        (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
        (honestLayerInput H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub leafAddr hAddr ℓ.val)
        (honestCtr ℓ (layerTree leafAddr ℓ.val) (layerLeaf leafAddr ℓ.val))))
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

/-- Helper: given `uporsVerify` matching the honest U-PORS root on fresh `(D_seed*, D_sel*)`,
    extract a target-bound U-PORS Octopus `NODE` / `ONE_TIME_KEY` / `CHAIN` collision,
    a provenance-bound unrevealed chain preimage, OR the provenance-bound fresh `uporsCover` event! -/
private theorem upors_forgery_extract (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (honestCtr : Fin LAYERS → Nat → Nat → UInt16)
    (ctx M : List UInt8) (σ : Imprint)
    (hFreshSeed : ∀ q ∈ Q, forgedSeedDigest H (deriveKeys H seed) ctx M σ ≠ querySeedDigest H (deriveKeys H seed) q)
    (hFreshSel : ∀ q ∈ Q, forgedSelectDigest H (deriveKeys H seed) ctx M σ ≠ querySelectDigest H (deriveKeys H seed) q)
    (hUpors : uporsVerify H (deriveKeys H seed).k_pub
                (forgedSeedDigest H (deriveKeys H seed) ctx M σ) σ.ctrFt σ.uporsChains σ.uporsSibs =
              some (uporsRoot H (deriveKeys H seed).k_sec (deriveKeys H seed).k_pub
                (extractLeafAddr (forgedSelectDigest H (deriveKeys H seed) ctx M σ))
                (extractLeafAddr_lt_48 (forgedSelectDigest H (deriveKeys H seed) ctx M σ)))) :
    ForgeryWitness H seed Q honestCtr ctx M σ := by
  let k := deriveKeys H seed
  let D_seed := forgedSeedDigest H k ctx M σ
  let D_sel  := forgedSelectDigest H k ctx M σ
  let leafAddr := extractLeafAddr D_sel
  let hAddr48 := extractLeafAddr_lt_48 D_sel
  unfold uporsVerify at hUpors
  dsimp only at hUpors
  cases hLeaves : extractUporsLeaves (fewSelectDigest H k.k_pub D_seed σ.ctrFt) with
  | none =>
    rw [hLeaves] at hUpors; cases hUpors
  | some leaves =>
    cases hCodes : extractUporsCodes H k.k_pub D_seed σ.ctrFt with
    | none =>
      rw [hLeaves, hCodes] at hUpors; cases hUpors
    | some codes =>
      rw [hLeaves, hCodes] at hUpors
      dsimp only at hUpors
      have ⟨hLen, hNodup⟩ := extractUporsLeaves_spec hLeaves
      rw [dite_eq_left hLen] at hUpors
      let leafPairs : List (Nat × Bytes 16) :=
        List.ofFn (fun j : Fin UPORS_K =>
          let leaf := leaves[j.val]'(by omega)
          let pk := chainVerifyGeneric H k.k_pub uporsLayerByte leafAddr hAddr48
            (UInt16.ofNat leaf) UPORS_STEPS (fun c => uporsDigit (codes j) c) (σ.uporsChains j)
          (leaf, pk))
      have hUpors' :
          (match octopusClimbAux (treeCombine H k.k_pub uporsLayerByte leafAddr hAddr48)
              0 UPORS_HEIGHT leafPairs (List.ofFn σ.uporsSibs) with
          | some ([(0, root)], remSibs) =>
            if remSibs.all (fun z => z.toList == zero16.toList) then some root else none
          | _ => none) = some (uporsRoot H k.k_sec k.k_pub leafAddr hAddr48) := hUpors
      cases hClimb : octopusClimbAux (treeCombine H k.k_pub uporsLayerByte leafAddr hAddr48)
          0 UPORS_HEIGHT leafPairs (List.ofFn σ.uporsSibs) with
      | none => rw [hClimb] at hUpors'; cases hUpors'
      | some res =>
        rcases res with ⟨top, remSibs⟩
        rw [hClimb] at hUpors'
        cases top with
        | nil => cases hUpors'
        | cons head tail =>
          rcases head with ⟨idx, rootVal⟩
          cases idx with
          | succ _ => cases hUpors'
          | zero =>
            cases tail with
            | cons _ _ => cases hUpors'
            | nil =>
              by_cases hAll : remSibs.all (fun z => z.toList == zero16.toList) = true
              · simp only [hAll, ↓reduceIte] at hUpors'
                have hRootEq : rootVal = uporsRoot H k.k_sec k.k_pub leafAddr hAddr48 := Option.some.inj hUpors'
                rw [hRootEq] at hClimb
                rcases octopus_forgery_collision (treeCombine H k.k_pub uporsLayerByte leafAddr hAddr48)
                    (uporsLeafFn H k.k_sec k.k_pub leafAddr hAddr48) UPORS_HEIGHT leafPairs
                    (List.ofFn σ.uporsSibs) remSibs hClimb with hAllLeaves | ⟨lvl, p, L₁, R₁, h1, h2, hdiff, hcol⟩
                · by_cases hCover : ∀ (j : Fin UPORS_K) (c : Fin UPORS_N),
                      ∃ q ∈ Q, queryCoversUporsChain H k q leafAddr (leaves[j.val]'(by omega)) c (uporsDigit (codes j) c)
                  · exact ForgeryWitness.uporsCover leaves hLen hNodup codes hFreshSeed hFreshSel hLeaves hCodes hCover
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
                      chainEndpoint H k.k_sec k.k_pub uporsLayerByte leafAddr hAddr48 leafU16 UPORS_N UPORS_STEPS ch.val
                    by_cases hEnds : forgedEnds = honestEnds
                    · have hchainEq : forgedEnds c = honestEnds c := congrFun hEnds c
                      have hd : digits c ≤ UPORS_STEPS := uporsDigit_le_23 (codes j) c
                      rcases chain_forgery_extract
                          (chainStepFn H k.k_pub uporsLayerByte leafAddr hAddr48 leafU16 c.val)
                          (chainStart H k.k_sec uporsLayerByte leafAddr hAddr48 leafU16 UPORS_N c.val)
                          (σ.uporsChains j c) hd hchainEq with hpre | ⟨s, a, _, hs2, hne_a, hcol⟩
                      · exact ForgeryWitness.uporsUnrevealedChainPreimage leaves hLen hNodup codes hLeaves hCodes j c hNever hpre
                      · exact ForgeryWitness.uporsChainSecondPreimage leafAddr hAddr48 leafU16 c s hs2 a hne_a hcol
                    · exact ForgeryWitness.uporsLeafSecondPreimage leafAddr hAddr48 leafU16 forgedEnds hEnds hPkEq
                · exact ForgeryWitness.uporsNodeSecondPreimage leafAddr hAddr48 lvl p ⟨h1, h2⟩ L₁ R₁ hdiff hcol
              · simp only [hAll] at hUpors'; cases hUpors'

/--
  **Main Machine-Checked Forgery Witness Dichotomy Theorem (`BLINCS-128-A2`):**
  For ANY `HashOracle`, ANY `seed`, ANY honest signing transcript `Q`, ANY physical-address-indexed
  valid counter assignment `honestCtr` along the forged address `leafAddr*`, and ANY fresh valid
  forgery `(ctx*, M*, σ*)` (`(ctx*, M*) ∉ Q`, `verify H (signetId H seed) ctx* M* σ*`),
  at least ONE of the 13 target-bound, provenance-bound `ForgeryWitness` events holds!

  Notice `hHonCtrs` is required ONLY along the forged signature's leaf address `leafAddr*` (4 layers),
  NOT across all `2^33` unused addresses!
-/
theorem blincs_forgery_dichotomy (H : HashOracle) (seed : Bytes 32)
    (Q : List SignedQuery) (honestCtr : Fin LAYERS → Nat → Nat → UInt16)
    (ctx M : List UInt8) (σ : Imprint)
    (hHonCtrs :
      let k := deriveKeys H seed
      let leafAddr := extractLeafAddr (forgedSelectDigest H k ctx M σ)
      let hAddr := extractLeafAddr_lt (forgedSelectDigest H k ctx M σ)
      ∀ ℓ : Fin LAYERS, ValidWotsHash
        (wotsMsgHash H k.k_pub (UInt8.ofNat ℓ.val)
          (layerTree leafAddr ℓ.val) (layerTree_lt_48 leafAddr ℓ.val hAddr)
          (UInt16.ofNat (layerLeaf leafAddr ℓ.val))
          (honestLayerInput H k.k_sec k.k_pub leafAddr hAddr ℓ.val)
          (honestCtr ℓ (layerTree leafAddr ℓ.val) (layerLeaf leafAddr ℓ.val))))
    (hFresh : ∀ q ∈ Q, (q.ctx, q.msg) ≠ (ctx, M))
    (hVer : verify H (signetId H seed) ctx M σ) :
    ForgeryWitness H seed Q honestCtr ctx M σ := by
  rcases hVer with ⟨hCtx, uporsNode, hUporsVer, hHtOk, hRootEq⟩
  rcases verifierKeys_match_deriveKeys H seed with ⟨hkpub, hroot, hkcontent⟩
  rw [hkpub, hroot, hkcontent] at hUporsVer hHtOk hRootEq
  let k := deriveKeys H seed
  let short := forgedShort H k ctx M σ
  let D_seed := forgedSeedDigest H k ctx M σ
  let D_sel := forgedSelectDigest H k ctx M σ
  let leafAddr := extractLeafAddr D_sel
  let hAddr := extractLeafAddr_lt D_sel
  by_cases hSeedHit : ∃ q ∈ Q, D_seed = querySeedDigest H k q
  · rcases hSeedHit with ⟨q, hq, hDeq⟩
    by_cases hMsgInput : σ.r = queryR H k q ∧ short = queryShort H k q ∧ ctx = q.ctx
    · rcases hMsgInput with ⟨_, hShortEq, hCtxEq⟩
      have hSplit : σ.e.toList = (queryE H k q).toList ∧
                    (contentHash H k.k_content σ.e ctx M).toList =
                    (contentHash H k.k_content (queryE H k q) q.ctx q.msg).toList := by
        dsimp only [short, forgedShort] at hShortEq
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
  · have hFreshSeed : ∀ q ∈ Q, D_seed ≠ querySeedDigest H k q := fun q hq h => hSeedHit ⟨q, hq, h⟩
    by_cases hSelHit : ∃ q ∈ Q, D_sel = querySelectDigest H k q
    · rcases hSelHit with ⟨q, hq, hSelEq⟩
      exact ForgeryWitness.fewSelectCollision q hq (Or.inl (hFreshSeed q hq)) hSelEq
    · have hFreshSel : ∀ q ∈ Q, D_sel ≠ querySelectDigest H k q := fun q hq h => hSelHit ⟨q, hq, h⟩
      have hTopMatch :
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
          hHonCtrs uporsNode LAYERS (Nat.le_refl _) hHtOk hTopMatch with
        hUporsEq | hWitness
      · rw [hUporsEq] at hUporsVer
        exact upors_forgery_extract H seed Q honestCtr ctx M σ hFreshSeed hFreshSel hUporsVer
      · exact hWitness

/--
  **Two-Stage Salt-Failure Hedged Input-Separation Theorem (Deterministic):**
  Even if the exact same `draw` (and hence the exact same content salt `e`) is reused for two
  distinct pairs `(ctx₁, M₁) ≠ (ctx₂, M₂)` (with valid context lengths), EITHER:
    (a) `ctx₁ = ctx₂`, `M₁ ≠ M₂`, and `h_msg` suffers a 256-bit keyed-BLAKE3 collision under `K_msg`, OR
    (b) the inputs `short₁ || frameContext ctx₁` and `short₂ || frameContext ctx₂` fed into `Keyed(K_R, ·)`
        are strictly distinct (leaving pseudorandomness of `R` to the PRF assumption on `Keyed(K_R, ·)`).
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
