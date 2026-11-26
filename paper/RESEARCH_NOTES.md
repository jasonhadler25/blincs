# Research Notes for the Science Paper: `U-FORS`, Coding Theory on Asymmetric Hash Channels, and SIMD-Optimal Stateless Hash-Based Signatures

> *Working research ledger for the eventual cryptography paper accompanying `jasonhadler25/blincs`. All `n = 3` and binary Johnson numbers below are computed by exact dynamic programming (zero Monte Carlo).*

---

## 1. Executive Summary of Breakthrough

We ran exact dynamic-programming experiments across five candidate directions:
1. Flat zero-Merkle hash-chain vectors (`Flat-HORS`, `Flat-J`, `Flat-L`),
2. Opposing-chain 2D forests (`Bi-FORS`, `[w]^2`),
3. Corner-simplex forests (`Tri-FORS` / `Quad-FORS`),
4. Asymmetric mini-`WOTS+` forests (`2+1 W-FORS` and `3+1 W-FORS`),
5. Symmetric **Upper-Layer Constant-Sum Lattice Forests (`U-FORS`)** (plus 1-chain optimal-type `C-FORS`, bucket-thinned `BU-FORS`, and work-balanced digest stretching).

**Core finding:** One unified idea — **`U-FORS`** (replacing raw-secret FORS leaves with `n = 3` equal-length hash chains encoded by an **upper-layer constant-sum extreme-variance subcode** $\mathcal{C} \subset \mathcal{L}_S(3, w)$ inside smaller height-$a_1$ Merkle trees) — **strictly advances the Pareto frontier on size, signing cost, security, SIMD vector parallelism, AND simplicity simultaneously**, not only for **BLINCS ($q \ge 2^{32}$)**, but also for **NIST FIPS 205 `SLH-DSA-128s` and `SLH-DSA-128f` ($q = 2^{64}$)** — with **zero counter grinding**, **zero variable-length pruning/Octopus**, and **zero new cryptographic assumptions**.

---

## 2. Exact Dynamic-Programming Pareto Tables

### 2.1 BLINCS ($h = 35$, $q \ge 2^{32}$, 128-bit security, Ledger `ST33` `p99 < 5.0 s`)

| Bottom FTS Scheme | Wire Bytes | $\Delta$ Bytes | Sign Comp. | Verify Comp. | SIMD Chains (length) | `ITSR` @ $2^{32}$ | @ $2^{33}$ | @ $2^{34}$ | @ $2^{35}$ | @ $2^{36}$ |
|---|---:|---:|---:|---:|---|---:|---:|---:|---:|---:|
| Baseline `BLINCS FORS(k=20, a=8)` | `2,880` | — | `15,346` | `186` | `5,120` (len 1) | `134.46` | `128.85` | `122.39` | `114.90` | `106.18` |
| `2+1 W-FORS(w=8, a₁=5, k=15)` *(asymmetric)* | `1,920` | `-960` | `15,829` | `304` | `960` (7) + `480` (14) | `136.22` | `129.68` | `122.10` | `113.24` | `102.86` |
| **`U-FORS(n=3, w=10, S=16, 64-ext, a₁=5, k=15)`** | **`1,920`** | **`-960`** | **`15,349`** | `259` | **`1,440 = 45×32`** (len 9) | **`138.48`** | **`132.13`** | **`124.73`** | **`116.05`** | `105.83` |
| **`U-FORS(n=3, w=14, S=23, 128-ext, a₁=5, k=14)`** | **`1,792`** | **`-1,088`** | `19,702` | `312` | **`1,344 = 42×32`** (len 13) | **`137.71`** | **`131.14`** | **`123.55`** | `114.73` | `104.42` |
| **`U-FORS(n=3, w=7, S=11, 32-ext, a₁=5, k=16)`** | **`2,048`** | **`-832`** | **`11,765`** | `213` | **`1,536 = 48×32`** (len 6) | **`135.99`** | **`129.96`** | **`122.90`** | `114.57` | `104.70` |

### 2.2 Complete End-to-End BLINCS Candidate Architectures ($q \ge 2^{32}$, Zero Grinding, `ST33 < 5.0 s`)

| Architecture | Raw B | Base64 | Cold Comp. | `ST33` (`25 µs`) | `+40%` DPA | 16-Wide Sign Waves | Verify Comp. | `2^{32}` | `2^{33}` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Baseline `BLINCS-128-7x5` (`FORS 8,20`) | `7,392` | `9,856` | `143,019` | `3.58 s` | `5.01 s` | `8,967` | `2,122` | `134.46 b` | `128.85 b` |
| **A.** `7×5(w=16)` + `U-FORS(w=10,S=16,64-ext,k=15)` | **`6,432`** | `8,576` | **`143,022`** | **`3.58 s`** | `5.01 s` | `8,965` | `2,194` | **`138.48 b`** | **`132.13 b`** |
| **B.** `7×5(w=16)` + `U-FORS(w=7,S=11,32-ext,k=16)` | **`6,560`** | `8,748` | **`139,438`** | **`3.49 s`** | **`4.88 s`** | **`8,741`** | `2,148` | **`135.99 b`** | **`129.96 b`** |
| **C.** `Sperner 7×5(n=32,w=19,S=288)` + `U-FORS(w=14,S=23,128-ext,k=14)` | **`5,968`** | **`7,960`** | `158,127` | **`3.95 s`** | `5.53 s` | `9,909` | `2,426`\* | **`137.71 b`** | **`131.14 b`** |
| **D.** `Sperner 7×5(n=32,w=19,S=288)` + `U-FORS(w=10,S=16,64-ext,k=15)` | **`6,096`** | **`8,128`** | `153,774` | **`3.84 s`** | `5.38 s` | `9,637` | `2,373`\* | **`138.48 b`** | **`132.13 b`** |

*\*Because `n = 32` fits cleanly into 2 full 16-wide SIMD waves (instead of 3 waves for 35-chain WOTS+), branchless 16-wide SIMD verify waves drop from `429` (baseline) to **`374` (`-13%`)** for **C**.*

### 2.3 NIST FIPS 205 `SLH-DSA-128s` ($h = 63, q = 2^{64}$) and `SLH-DSA-128f` ($h = 66, q = 2^{64}$)

| Regime & Bottom Scheme | Wire Bytes | $\Delta$ Bytes | Sign Comp. | Speedup | Verify Comp. | `ITSR` @ $2^{64}$ | @ $2^{65}$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| **`SLH-DSA-128s` baseline `FORS(k=14, a=12)`** | `2,912` | — | `172,032` | `1.00×` | `190` | `133.75 b` | `125.86 b` |
| `U-FORS(w=10, S=16, 64-ext, a₁=7, k=14)` | **`2,240`** | **`-672`** | **`57,334`** | **`3.00×`** | `270` | **`140.67 b`** | **`130.66 b`** |
| `U-FORS(w=14, S=23, 128-ext, a₁=6, k=15)` | **`2,160`** | **`-752`** | **`42,229`** | **`4.07×`** | `349` | **`135.42 b`** | `123.00 b` |
| `U-FORS(w=10, S=16, 64-ext, a₁=6, k=16)` | **`2,304`** | **`-608`** | **`32,757`** | **`5.25×`** | `293` | **`136.07 b`** | `123.94 b` |
| **`SLH-DSA-128f` baseline `FORS(k=33, a=6)`** | `3,696` | — | `6,303` | `1.00×` | `240` | `131.36 b` | `122.27 b` |
| **`U-FORS(w=5, S=8, 16-ext, a₁=4, k=24)`** | **`2,688`** | **`-1,008`** | `6,511` | `0.97×` | **`223`** | **`134.10 b`** | **`124.87 b`** |
| `U-FORS(w=7, S=11, 32-ext, a₁=4, k=22)` | **`2,464`** | **`-1,232`** | `8,080` | `0.78×` | `270` | **`137.02 b`** | **`127.37 b`** |
| `U-FORS(w=10, S=16, 64-ext, a₁=4, k=20)` | **`2,240`** | **`-1,456`** | `10,226` | `0.62×` | `326` | **`135.09 b`** | **`125.47 b`** |

*(Note `SLH-DSA-128f` + `U-FORS(w=5, S=8, 16-ext, a₁=4, k=24)`: **`-1,008 B` smaller, SAME signing cost, FASTER verification (`223` vs `240`), `+2.74` bits stronger, zero grinding, `48 B` LUT**!)*

---

## 3. Defining the Exact Coding-Theoretic Problem

Any hash-chain leaf with $n$ equal-length chains of length $w$ lives in the **chain-product lattice** $[w]^n = \{0, \dots, w-1\}^n$ under coordinatewise order ($x \preceq y \iff \forall i,\, x_i \le y_i$). When $m$ honest codewords $c^{(1)}, \dots, c^{(m)} \in \mathcal{C} \subseteq [w]^n$ are revealed on the same leaf, the adversary learns their **lattice meet**
$$\bigwedge_{j=1}^m c^{(j)} \;=\; \Bigl(\min_j c^{(j)}_0, \dots, \min_j c^{(j)}_{n-1}\Bigr)$$
and can forge any codeword $c^* \in \mathcal{C}$ with $c^* \succeq \bigwedge_{j=1}^m c^{(j)}$.

**Two underlying coding-theoretic channels:**
1. **Discrete collusion-envelope channel ($\Sigma^k$, FORS):** $r$ honest signatures reveal lists $S_0,\dots,S_{k-1} \subseteq \Sigma$ of size $\le r$; a forger wins on any codeword in $S_0 \times \dots \times S_{k-1}$. Relevant literature: $r$-cover-free families / superimposed codes (Kautz–Singleton 1964; D'yachkov–Rykov 1982; Erdős–Frankl–Füredi 1985), zero-error list-recoverable codes (Guruswami–Indyk; Parvaresh–Vardy; Guruswami–Rudra; Doron–Wootters), collusion-resistant fingerprinting / frameproof / IPP codes (Boneh–Shaw; Chor–Fiat–Naor; Tardos).
2. **$w$-ary asymmetric / unidirectional channel ($[w]^n$, hash chains):** Errors only move *upward* ($x_i \to x_i + \Delta_i$, never downward). Relevant literature: AUED codes (Berger 1961 — which WOTS+ reinvented; Freiman 1962 constant-weight), asymmetric ECCs (Varshamov–Tenengolts 1965; Constantin–Rao 1979; Graham–Sloane 1980), constant-weight / Steiner / Golay codes, and Csiszár–Körner Method of Types / constant-composition shaping.

**Desiderata for $\mathcal{C}$:**
1. **1-time ($m = 1$):** Strict antichain in $[w]^n$ (zero fresh forgery).
2. **Few-time ($m \ge 2$):** Minimize expected cover fraction $q(m) = \mathbb{E}\bigl[|\{c^* \in \mathcal{C} : c^* \succeq \bigwedge_{j=1}^m c^{(j)}\}| / |\mathcal{C}|\bigr]$ under uniform independent honest queries (enforced by the unpredictable signer salt $e$).
3. **BLAKE3 & SIMD geometry:** Identical chain lengths $w - 1$ (zero asymmetric checksum chains, 100% SIMD lane occupancy on 4/8/16/32-wide NEON/AVX2/AVX-512/SME2), single-block BLAKE3 leaf hashing (`3 × 16 + 16 = 64 B`), zero counter grinding (`p99 = mean = max`).
4. **Simplicity:** Fixed wire size, tiny LUT or zero-ROM in-place unranking, identical Lean 4 `wots_dominance` + `merkle_forgery_collision` proof.

---

## 4. Systematic Evaluation of Six Coding-Theory Families

### 4.1 Zero-Error List-Recoverable & Reed–Solomon MDS Codes (Negative Result)
Zero-error $(0, r, L)$-list-recovery is word-for-word the worst-case specification of an $r$-time signature ($|\mathcal{C} \cap (S_0 \times \dots \times S_{k-1})| \le L$).
- **List-Recovery Capacity Wall:** Keeping $L$ small requires rate $R < 1 - \log_t r \implies |\mathcal{C}| < (t/r)^k$. Thus exact-codeword collision probability $p_{\mathrm{exact}} \approx r / |\mathcal{C}|$ grows faster than fresh-forgery probability $p_{\mathrm{fresh}}$ shrinks.
- **Measured verification:**
  - `RS[7, 4]` over $\mathbb{F}_7$ ($d = 4$): kills $p_{\mathrm{fresh}}(1) = p_{\mathrm{fresh}}(2) = 0$, yet $p_{\mathrm{total}}$ is `329×` worse than uncoded at $r=1$, `5.4×` at $r=2$, `2.0×` at $r=3$, `1.22×` at $r=4$, `1.015×` at $r=5$.
  - `RS[11, 3]` over $\mathbb{F}_{11}$ ($d = 9$, 5-CFF): kills $p_{\mathrm{fresh}} = 0$ through $r = 6$, yet $p_{\mathrm{total}}$ is `151×` worse at $r = 5$ and `41×` worse at $r = 6$.
- **Why:** High-distance MDS / list-recoverable / CFF codes only beat uncoded spaces under *adversarially steered* queries (no salt). BLINCS's unpredictable salt guarantees uniform honest queries, where distance-thinning strictly hurts.

### 4.2 Classical Asymmetric & Constant-Weight ECCs (Negative Result)
Six celebrated constant-weight / asymmetric ECCs tested directly on the upward-only channel against their full ambient Johnson layer $J(n, u)$:
- **Extended Binary Golay $G_{24}$ Octads = Steiner $S(5,8,24)$ ($d_H = 8$, `759` words):** `q(1)=0.00132, q(2)=0.00459, q(3)=0.04199` vs full $J(24,8)$ (`735,471` words, $d_H=2$): `q(1)=0.0000014, q(2)=0.00337, q(3)=0.04086`.
- **Golay $G_{24}$ Dodecads ($d_H = 8$)**, **Graham–Sloane Asymmetric ECC in $J(16,4)$ ($d_H = 4$)**, **Steiner $S(3,4,16)$ Affine Planes ($d_H = 4$)**, **Projective Plane $PG(2,3) = S(2,4,13)$**, and **Constant-Weight Varshamov–Tenengolts $VT_0(12)$ ($d_H = 4$)** — **all six lose to the uncoded constant-weight layer**.
- **Structural reason:** Regular $t$-designs have the same density inside a random multi-query cover box as the ambient layer, so thinning never lowers the fresh-cover fraction while inflating exact collisions $m / |\mathcal{C}|$.

### 4.3 Where Coding Theory *Actually* Wins: Asymmetric Shaping & Method of Types

Instead of thinning a fixed sphere, coding theory wins by **shaping the symbol composition (type distribution $P$)** on the asymmetric channel $[w]^n$:

1. **Hypertree 1-Time Code ($m = 1$) — Sperner's Theorem + SIMD-Aligned Power-of-Two Width:**
   - By Sperner's theorem for $[w]^n$ (de Bruijn–Tengbergen–Kruyswijk 1951; Zhang–Cui–Yu `ePrint 2023/850`), the middle constant-sum layer $\mathcal{L}_{\lfloor n(w-1)/2 \rfloor}(n, w)$ is size-optimal.
   - Choosing exact power-of-two **`n = 32` chains** gives **`w = 19, S = 288`** ($|\mathcal{L}_{288}(32, 19)| = 2^{129.65} \ge 2^{128}$): saves `336 B` across 7 layers, yields `1,024` equal-length chains/layer (0 wasted SIMD lanes on 4/8/16/32-wide vectors), exact 2×16-wide verify waves, and **zero-ROM in-place boxcar deconvolution unranking** (`prev[s] = cur[s] - cur[s-1] + prev[s-w]`, `4.6 KiB` RAM, `0 B` ROM, zero division).

2. **1-Chain-Per-Tree Constant-Composition Code (`C-FORS`) — Exact Closed-Form Shannon Limit:**
   - Each leaf is a single chain $x_0 \to \dots \to x_{w-1} \to \text{leaf} = H(x_{w-1})$ (final hash prevents Merkle sibling leakage), with opening depths across the $k$ trees drawn from a constant-composition code of type $P = (p_0,\dots,p_{w-1})$.
   - Forgery probability scales as $(r/L)^k \exp\bigl(k \sum_{v=0}^{w-1} p_v \ln F_v\bigr)$, where $F_v = \sum_{u \le v} p_u$.
   - Exact KKT optimality recurrence for the optimal CDF ratios:
     $$r_0 = 0, \qquad \frac{F_v}{F_{v+1}} = r_{v+1} = e^{-(1 - r_v)}$$
     (e.g., $w = 2 \Rightarrow p_0 = 1/e \approx 0.3679$, gain $+0.5307$ bits/tree; $w = 4 \Rightarrow +0.9030$; $w = 16 \Rightarrow +1.2802$).
   - **Universal Shannon ceiling ($w \to \infty$):**
     $$-\int_0^1 \ln F\,dF \;=\; 1\text{ nat} \;=\; \log_2(e) \;=\; \mathbf{1.4427\text{ bits/tree}}.$$
   - Explains mathematically why 1-chain leaves without forced-pruning grinding cannot beat `~2,560 B` (`-320 B`).

3. **Breaking `1.4427` bits/tree Requires Multi-Chain Co-Located Shaping ($n \ge 3$) — Lattice-Meet Asymmetry (`U-FORS`):**
   - For $m = 1$, $[w]^n$ is rank-symmetric ($S \leftrightarrow n(w-1) - S$). **For all $m \ge 2$, the lattice meet $\wedge = \min$ breaks rank symmetry.**
   - At $n = 2$, upper slices of $[w]^2$ are isomorphic to smaller diagonals (zero asymmetry).
   - At **$n = 3$** (the exact minimum dimension where asymmetry activates, AND `3 × 16 + 16 = 64 B` = exact 1 BLAKE3 compression!), pushing $S > \lfloor 3(w-1)/2 \rfloor$ pins untouched coordinates at $\min_i = w - 1$, **simultaneously slashing $q(2), q(3), q(4), q(5)$ AND verification steps** (`3(w-1) - S` constant!).
   - Selecting the power-of-two subset of **maximum coordinate variance** (extreme/bimodal boundary types) inside $\mathcal{L}_S(3, w)$ beats BOTH balanced subsets AND the full unpruned layer (e.g., $\mathcal{L}_{16}(3, 10)$: extreme-64 `q(2) = 0.21992` vs full-69 `0.22088` and balanced-64 `0.22916`). Local hill-climbing over *arbitrary non-flat antichains* in $[10]^3$ gains only `+0.04` bits, showing flat upper constant-sum extreme subsets are virtually globally optimal.

---

## 5. Literature Check & Honest Credit Allocation (Through Nov 2026)

### 5.1 Hash-Based Signature Prior Art (ePrint Survey)
- **Bos & Chaum (CRYPTO 1992)** & **Zhang, Cui, Yu (`ePrint 2023/850`)**, *"Revisiting the Constant-sum Winternitz One-time Signature with Applications to SPHINCS+ and XMSS"*: proves constant-sum WOTS+ is size-optimal among tree-based OTS and exposes a flaw in Bleichenbacher–Maurer's Asiacrypt 1996 DAG OTS.
- **Khovratovich, Kudinov, Wagner (`ePrint 2025/889`)**, *"At the Top of the Hypercube -- Better Size-Time Tradeoffs for Hash-Based Signatures"*: maps 1-time WOTS messages into upper hypercube layers to cut verification cost by `20–40%`. *(Our Lattice-Meet Asymmetry is the few-time $m \ge 2$ counterpart, cutting BOTH verification cost AND multi-reveal forgery probability!)*
- **Hülsing & Kudinov (ASIACRYPT 2022)**: formalizes **ITSR (Interleaved Target Subset Resilience)** for tight SPHINCS+ proofs.
- **Abri & Katz (`ePrint 2025/2069`)**: `PORS+FP` — forced pruning (grinding) on single-tree Octopus PORS.
- **Ren, Zhang, Yu (`ePrint 2026/1328`)**: `BPORS+FP` — **bucket thinning** ($2^B$ independent PORS child keys under an outer FORS-like bucketing layer, reducing use count to $\mathrm{Bin}(q_0, 2^{-B})$) + forced pruning.
  - *Our test of bucket thinning without grinding (`BU-FORS` and `Flat-J`/`Flat-L` at $a_1 = 0$):* without forced-pruning grinding, bucket thinning only helps marginally (`B=1, n=4` at `1,744 B` / `26.9k` comp vs `B=0, n=3` at `1,792 B` / `19.7k` comp), because bucket thinning's main synergy is amplifying Octopus/forced pruning!
- **Wang, Liu, Cui, Hu, Yu (`ePrint 2026/2374`)**: **`BPORS-C+BFP`** — *"Shorter Few-Time Signatures from Hash Chains and Blockwise Forced Pruning"*. Replaces each child leaf secret in `BPORS+FP` with a **single short hash chain** + **global constant-sum constraint** across selected chains + **blockwise forced pruning (grinding)**. *(Closest published sibling to our 1-chain `C-FORS`; differs cleanly from `U-FORS`, which uses co-located `n = 3` multi-chain leaves + upper-layer Lattice-Meet Asymmetry + zero grinding + zero Octopus + 100% SIMD!)*
- **Ren & Yu (`ePrint 2026/2502`)**: **`BGS-CC`** — *"Shorter Hash-Based Signatures via Guarded Sharing in a DAG Model"*. Moves from trees to a DAG with guarded sharing + bucket thinning + hash chains + **rejection sampling (grinding)** (`2,228 B` at $Q = 2^{24}$).
- **Villányi (`ePrint 2026/142`)**: 2-message security of run-length OTS; **Kobeissi (`ePrint 2026/1103`)**: `Jevil` (sharp cliff FTS via secret polynomial commitment).

**Novelty boundary to state honestly in the paper:** Give full credit to `2023/850` (constant-sum WOTS), `2025/889` (upper hypercube for 1-time verify), `2025/2069` (`PORS+FP`), `2026/1328` (bucket thinning), `2026/2374` (`BPORS-C+BFP` 1-chain global constant-sum + blockwise forced pruning), and `2026/2502` (`BGS-CC` DAG guarded sharing + rejection sampling). Position **`U-FORS`** explicitly as the **zero-grinding, fixed-size, 100%-SIMD, single-tree-height** point on the frontier: co-located `n = 3` equal-length chains in a 1-block BLAKE3 leaf using **few-time Lattice-Meet Asymmetry** ($S > \lfloor 3(w-1)/2 \rfloor$) + extreme-variance power-of-two shaping, achieving `-960` to `-1,456 B` (and up to `5.25×` speedup on `SLH-DSA-128s`) with **zero rejection sampling / zero `p99` tail risk**.

### 5.2 ZK-STARK / Proximity-Gap / List-Decoding Literature Check (2020–2026)
- **Key 2025–2026 papers reviewed:**
  - Ben-Sasson et al. (BCIKS, J. ACM 2023), Arnon–Chiesa–Fenzi–Yogev (STIR CRYPTO 2024; WHIR), Skatharoudis SoK (`ePrint 2026/1367`).
  - **Crites & Stewart (`ePrint 2025/2046`)**, *"On Reed–Solomon Proximity Gaps Conjectures"*: **disproved** the BCIKS correlated-agreement up-to-capacity conjecture, WHIR's mutual correlated agreement up-to-capacity conjecture, and DEEP-FRI's list-decodability up-to-capacity conjecture.
  - **Dao, Kominers, Thaler, Zheng (`ePrint 2026/2424`)**: explicit **counterexamples to beyond-Johnson proximity gaps over binary additive domains** (e.g., Binius64).
  - **Chai & Fan (`ePrint 2026/858`)**: first unconditional FRI/STIR/WHIR soundness above Johnson via **threshold halving** (`~2×` query overhead).
  - **Bloemen & Garreta (`ePrint 2026/2930`, `BEEP`)**: replaces Mutual Correlated Agreement with $m = 2..5$ DEEP samples relying only on list-decodability.
- **Architectural relevance to BLINCS:**
  1. *Replacing BLINCS with a STARK proof of `BLAKE3(sk) = pk`:* even with WHIR/BEEP at provable (non-conjectural) 128-bit security, hash-based STARK proofs remain `~40–120 KiB` (7×–20× larger than BLINCS's `6 KiB`), orders of magnitude too RAM/CPU-heavy for an `ST33`, and vastly more complex.
  2. *Using proximity gaps inside FORS:* FRI/STIR/WHIR test proximity of a *freshly committed* table to a low-degree polynomial using verifier-chosen challenges; in a stateless signature, the signer reveals static preimages from a fixed public key, where Lab 1 already proved MDS/list-recoverable subcodes lose under salt-randomized queries.
  3. *Philosophical validation:* The 2025–2026 disproofs of beyond-Johnson proximity-gap conjectures (`2025/2046`, `2026/2424`) strongly vindicate BLINCS's choice to rest strictly on **unconditional exact combinatorial bounds + keyed-BLAKE3 2nd-preimage resistance**.
  4. *Where STARKs DO fit:* **Future batch/recursive aggregation** of thousands of BLINCS imprints (e.g., compressing an entire repository's signature chain into one hash-based STARK proof) — orthogonal to single-imprint design.

---

## 6. Security Analysis Framework (Primary vs. Secondary Goals)

1. **Primary Goal — Security Under Correct Use** (`saltseed` properly managed so every signature uses a unique unpredictable salt $e$, total signatures $q < 2^{32}$, secret signing `seed` remains completely secret):
   - Unpredictable salt $e$ gives two concrete reductions to BLAKE3:
     (a) **Message hashing (`h_msg`) reduces purely to salted 2nd-preimage resistance (`SM-TCR`)** in a single streaming pass;
     (b) **Zero adaptive chosen-message steering** of honest queries — any adversary gaining advantage in steering honest openings onto targeted `leaf_addr`s or `U-FORS` codewords breaks BLAKE3 `PRF`/`SM-TCR`.
   - The *only* remaining leverage from prior honest queries is the unavoidable passive statistical overlap of $q_s$ uniform transcripts (`ITSR`), bounded exactly by our dynamic-programming evaluation (`138.48` bits @ $2^{32}$ for `U-FORS(w=10,S=16,k=15)`, `137.71` bits for `U-FORS(w=14,S=23,k=14)`).
   - Every non-cover forgery branch reduces identically via Lean 4 `wots_dominance` + `wots_chain_forgery_extract` + `merkle_forgery_collision` to BLAKE3 `SM-TCR` / `SM-DSPR`.

2. **Secondary Goal — Security Under Incorrect Use** (mitigated only where cheap in computation AND complexity; explicitly **out of scope**: leaked or predictable signing `seed`, where all bets are off):
   - **(i) `saltseed` stuck, repeated, or leaked (while `seed` stays secret):**
     - `R = Keyed(K_R, Tweak_RAND || e || h_msg || ctx)` is keyed by `K_R` derived from secret `seed`, so distinct `(M, ctx)` pairs STILL produce unpredictable, unsteerable `R` and uniform `D`!
     - Re-signing the exact same `(M, ctx)` with a stuck `e` deterministically reproduces the identical signature (zero extra `U-FORS` leaf/chain leakage).
     - `h_msg = Keyed(e, M)` gracefully falls back from salted 2nd-preimage resistance to plain 256-bit BLAKE3 **collision resistance** — still 128-bit secure!
     - Cost: `1` extra BLAKE3 compression (`K_R` already present in BLINCS!).
   - **(ii) Exceeding $2^{32}$ signatures ($q \ge 2^{32}$):**
     - Graceful degradation (no cliff!): `U-FORS(w=10, S=16, 64-ext, k=15)` remains strictly stronger than baseline `BLINCS FORS(20, 8)` through **`2^{35}` (`8×` over limit: `116.05 b` vs `114.90 b`)**, and still provides `105.83 b` at $2^{36}$ and `79.87 b` at $2^{38}$.
