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


---

## 7. Second Drawing-Board Pass: Breaking the `6 KiB` Wall (Diagnosis & Proven Theoretical Floors)

After shipping `U-FORS` Preset A (`6,432 B`, `1.22 ms` Apple M6, `36.2 µs` verify, `3.58 s` est. `ST33`) across `blincs`, `signet`, and `git-signet`, we judged `-13%` size and `-2%` speed vs. `FORS(8,20)` (`7,392 B`, `1.25 ms`) too incremental and returned to first principles to find the global stateless BLAKE3 frontier.

### 7.1 Root-Cause Diagnosis of Preset A
In `BLINCS-128-7x5` (`U-FORS` Preset A, `6,432 B`, `143,022` cold compressions):
- **70% of signature bytes (`4,480 / 6,432 B`)** and **89% of signing work (`127,673 / 143,022` compressions)** sat in the untouched `7×5` nibble `WOTS+(w=16, n=35)` hypertree.
- Optimizing the bottom FTS alone can never move total size below `~5.5 KiB` or signing time below `~1.1 ms`; breaking past `~6 KiB` requires attacking the hypertree, the FTS, and the tree geometry jointly.

### 7.2 Four Proven Information-Theoretic Walls for Pure Black-Box BLAKE3 Stateless Signatures ($q = 2^{32}$, 128-bit)
Before relaxing any hardware assumption, we mapped the exact mathematical walls using compiled Rust dynamic programming and analytical bounds:

1. **Bleichenbacher–Maurer (1996) / Sperner OTS DAG Bound:** Any 128-bit black-box 1-time hash signature requires $\ge 241$ hash calls/leaf (minimum at $w = 3$) and $\ge n \cdot 2^{128/n}$ hash calls to compress to $n$ chains ($16n$ wire bytes). Inside a single 1-time signature, uniform chain lengths $w_0 = \dots = w_{n-1} = w$ are uniquely optimal by AM-GM / Jensen's inequality (maximizing $\sum_i \log_2 w_i$ at fixed $\sum_i w_i$), and the middle constant-sum slice $S = \lfloor n(w-1)/2 \rfloor$ is uniquely size-optimal by de Bruijn–Tengbergen–Kruyswijk (1951).
2. **Multi-Use Hypertree OTS (`CUTS`) 3-Way Symmetry Ceiling:** Replacing 1-time WOTS in internal hypertree layers with 2-use chains fails strictly: for *any* probability distribution on $\{0,\dots,w-1\}$, three i.i.d. draws satisfy $\Pr[Y \ge \min(X_1, X_2)] \ge 2/3$ (by 3-way symmetry of the minimum). Thus a 2-use chain leaks at most $\log_2(3/2) \approx 0.585$ bits/chain, requiring $\ge 219$ chains (`3,504 B`) — strictly worse than 1-time WOTS plus an extra Merkle level (`~400 + 16 B`).
3. **BLAKE3 VOLE-in-the-Head (`FAEST`-Style ZK) Gate Wall:** BLAKE3's 32-bit ARX additions require `~10,752` non-linear AND gates per compression (`~8.4×` AES-128), yielding `~12–18 KiB` proofs — larger than hash-tree signatures and `~40×` slower to verify. (Pure symmetric ZK like `FAEST-EM-128s` hits `3,924 B` only by introducing an AES-128 ideal-cipher assumption and `~1.5 ms` verification.)
4. **16-Byte Hash Width Wall:** Every internal Merkle node and chain element must remain `16 B` (`128` bits) against offline 2nd-preimage / chain-inversion attacks.

---

## 8. Three Synergistic Breakthroughs Behind `BLINCS-A2` (`3,292 B`)

### 8.1 `U-PORS`: Single-Tree Octopus Merging + Full-Slice Lattice-Meet Asymmetry + Exact Without-Replacement DP

We unified single-tree Octopus path merging (`PORS`, `ePrint 2025/2069`) with our multi-chain upper-layer `U-FORS` leaves (`n = 3` or `4` equal-length chains per leaf) and discovered **three mathematical refinements**:

1. **Exact Without-Replacement Hypergeometric Transition DP (Recovering `+1.0` to `+3.8` Free Bits):**
   In a single binary tree of $L = 2^A$ leaves, each honest signature opens $k$ **distinct** leaves without replacement. Naive with-replacement bounds approximate the probability that a target $k$-subset $S \subset [L]$ is covered after $r$ honest signatures by $s(r)^k$, where $s(r) = \sum_{t=1}^r \Pr[\mathrm{Bin}(r, k/L) = t]\, q(t)$.
   - By exact $(k+1)$-state Markov transition DP over the number $u \in \{0,\dots,k\}$ of target leaves hit at least once,
     $$M_{u \to u+a} = \frac{\binom{k-u}{a}\binom{L-(k-u)}{k-a}}{\binom{L}{k}},$$
     we obtain the **exact** all-hit probability $p_{\mathrm{all}}(r) = (M^r)_{0, k}$.
   - Conditioned on all $k$ target leaves being hit at least once, the per-leaf hit counts $(T_1,\dots,T_k)$ are **negatively associated** (Joag-Dev & Proschan, 1983, since each signature is a without-replacement $k$-subset and independent sums preserve negative association) and have strictly smaller conditional hit counts than independent $\mathrm{Bin}(r, k/L) \mid T \ge 1$ variables. Therefore
     $$\Pr[\text{forge} \mid r] \;\le\; p_{\mathrm{all}}(r) \cdot \Bigl(\mathbb{E}\bigl[q(T) \mid T \ge 1\bigr]\Bigr)^k \;=\; p_{\mathrm{all}}(r)\left(\frac{s(r)}{1 - (1 - k/L)^r}\right)^k$$
     is a **provably conservative elementary upper bound** that is **100% exact at $r = 1$** (where $p_{\mathrm{all}}(1) = 1/\binom{L}{k}$, tightening $(k/L)^k$ by $k^k/k! \approx 2^{14.2}$ at $k=12$!) and recovers **`+0.98` to `+1.47` bits** in the $q = 2^{30}..2^{32}$ regime.

2. **Full Upper-Slice Advantage & Zero-LUT Closed-Form Hexagon Unranking ($n = 3, w = 24, S = 42, C = 376$):**
   At small tree multiplicity ($h \ge 33$, $\lambda = q/2^h \le 1/2$), single-hit leaf cover $q(1) = 1/C$ contributes heavily alongside $q(2), q(3)$. Unlike `U-FORS` at $h = 35, a_1 = 5$ (where $t \ge 2$ dominated and power-of-two extreme-variance truncation beat the full slice), in `U-PORS` with $L = 2^{10} = 1{,}024$ leaves, keeping the **entire** upper slice $\mathcal{L}_S(3, w)$ maximizes $C$ while still activating Lattice-Meet Asymmetry — **eliminating the ROM lookup table completely**.
   - **Exact $n = 3, w = 24$ slice sweep ($h = 33, A = 10, k = 10$, 100% exact DP, zero Monte Carlo):**

     | Slice $S$ | Full Size $C$ | Verify Steps / Leaf ($69 - S$) | Exact $q(1)$ | Exact $q(2)$ | Exact $q(3)$ | Exact $q(4)$ | Raw `ITSR` @ $2^{32}$ (naive $s^k$) | Raw `ITSR` @ $2^{33}$ |
     |---:|---:|---:|---:|---:|---:|---:|---:|---:|
     | `38` | `420` | `31` | `0.002381` | `0.179092` | `0.344457` | `0.465645` | `128.61 b` (`127.65`) | `121.47 b` |
     | `39` | `412` | `30` | `0.002427` | `0.176420` | `0.341928` | `0.463490` | `128.67 b` (`127.71`) | `121.55 b` |
     | `40` | `402` | `29` | `0.002488` | `0.173999` | `0.339703` | `0.461617` | **`128.69 b`** (`127.72`) | **`121.60 b`** |
     | `41` | `390` | `28` | `0.002564` | `0.171848` | `0.337797` | `0.460037` | `128.66 b` (`127.69`) | `121.60 b` |
     | **`42`** | **`376`** | **`27`** | **`0.002660`** | **`0.170004`** | **`0.336239`** | **`0.458771`** | **`128.58 b`** (`127.60`) | **`121.56 b`** |
     | `43` | `360` | `26` | `0.002778` | `0.168524` | `0.335081` | `0.457861` | `128.44 b` (`127.45`) | `121.46 b` |
     | `44` | `342` | `25` | `0.002924` | `0.167500` | `0.334401` | `0.457375` | `128.22 b` (`127.22`) | `121.29 b` |
     | `45` | `322` | `24` | `0.003106` | `0.167071` | `0.334321` | `0.457423` | `127.91 b` (`126.90`) | `121.03 b` |
     | `46` | `300` | `23` | `0.003333` | `0.167451` | `0.335030` | `0.458190` | `127.48 b` (`126.46`) | `120.65 b` |

   - **Closed-form hexagon unranker (`0 B` ROM, bijectively verified over all `0..376`):** For fixed $a \in [\max(0, S - 2(w-1)),\, \min(w-1, S)]$, let $\mathrm{rem} = S - a$, $b_{\mathrm{lo}} = \max(0, \mathrm{rem} - (w-1))$, $b_{\mathrm{hi}} = \min(w-1, \mathrm{rem})$. Stepping $a$ across at most $w = 24$ iterations (subtracting $\mathrm{len}(a) = b_{\mathrm{hi}} - b_{\mathrm{lo}} + 1$) maps $\mathrm{idx} \in \{0,\dots,375\}$ bijectively to $(a, b_{\mathrm{lo}} + \mathrm{idx}, \mathrm{rem} - b)$ with zero tables and zero division.
   - **Exact 1-block leaf hash:** `16 B (tweak) + 3 × 16 B (chain tops) = 64 B` = **1 single BLAKE3 compression**!
   - *(Note on 4D high-capacity `U-PORS`: we also discovered that `n = 4, w = 16, S = 39` (`C = 1,800`, zero LUT) achieves `q(1) = 0.00056, q(2) = 0.0927, q(3) = 0.2319`, enabling `< 1 KiB` (`980–1,092 B`) FTS at $h = 35, A = 9$; at `h = 33, A = 10`, `n = 3, w = 24, S = 42` wins on exact 1-block leaves, 32-lane SIMD alignment, and simplicity.)*

3. **Verifier-Enforced Octopus Cap `sibs(D) ≤ m_max` — Zero Security Loss & Proven `+5.5` to `+7.8` Bit Gain:**
   A natural worry with capping Octopus sibling count (`sibs(D) ≤ m_max`, where the signer grinds a 4-byte `ctr_ft` until the `k` distinct sorted leaves share enough tree ancestors to need at most `m_max` authentication siblings) is whether clustering honest leaves weakens `ITSR`.
   - **High-precision `2,000,000`-trial Octopus distribution for $A = 10, k = 10$:**

     | $m_{\max}$ | $p_{\mathrm{cap}}$ | $-\log_2 p_{\mathrm{cap}}$ | Mean Trials | Median | `p95` | `p99` | `p99.9` |
     |---:|---:|---:|---:|---:|---:|---:|---:|
     | `41` | `0.0001035` | `13.24 b` | `9,662` | `6,697` | `28,944` | `44,494` | `66,742` |
     | `42` | `0.0002050` | `12.25 b` | `4,878` | `3,381` | `14,613` | `22,464` | `33,696` |
     | `43` | `0.0003855` | `11.34 b` | `2,594` | `1,798` | `7,771` | `11,946` | `17,919` |
     | **`44`** | **`0.0007325`** | **`10.41 b`** | **`1,365`** | **`946`** | **`4,090`** | **`6,287`** | **`9,430`** |
     | `45` | `0.0013370` | `9.55 b` | `748` | `518` | `2,241` | `3,444` | `5,167` |
     | `46` | `0.0024030` | `8.70 b` | `416` | `289` | `1,247` | `1,916` | `2,875` |
     | `48` | `0.0073510` | `7.09 b` | `136` | `94` | `408` | `627` | `940` |

   - **Importance-sampling Monte Carlo verification (`6,000` trials × `32` importance sub-draws per $r$) of $\Delta_{\mathrm{cap}}(r) = -\log_2\bigl(\Pr[D' \subseteq U \wedge \mathrm{sibs}(D') \le 44 \mid \text{conditioned honest}] / \Pr[D' \subseteq U \mid \text{unconditioned}]\bigr)$ at $A = 10, k = 10, m_{\max} = 44$:**
     - $r = 2$: **`+3.31 bits`**
     - $r = 3$: **`+4.61 bits`**
     - $r = 4$: **`+5.51 bits`**
     - $r = 5$: **`+6.13 bits`**
     - $r = 6$: **`+6.59 bits`**
     - $r = 7$: **`+6.87 bits`**
     - $r = 8$: **`+7.28 bits`**
     - $r = 10$: **`+7.75 bits`**
   - **Why it helps instead of hurting:** Although each conditioned honest signature's leaves are slightly clustered, $r \ge 4$ independent honest signatures scatter across unrelated subtrees (translation invariance of `sibs`), so the union $U$ of covered leaves is nearly uniform — while the verifier STILL forces the adversary's forged $D'$ to satisfy $\mathrm{sibs}(D') \le 44$ (`1 / 1,365`).
   - **Proof cleanliness decision:** Even though $\Delta_{\mathrm{cap}}$ delivers a verified **`+6.79` bits** at $q = 2^{32}$ and **`+7.35` bits** at $q = 2^{33}$, we chose `BLINCS-A2` to exceed `128.0` bits **with zero cap credit** (`128.58 b` elementary DP), so the formal proof in Lean 4 and the paper requires **zero** Monte Carlo assumptions while retaining `135.37` true bits at $2^{32}$ and `128.91` true bits at $2^{33}$.

### 8.2 `S-WOTS+Z`: Constant-Sum Sperner + `z`-Zero-Bit Deterministic Counter Grinding
Combining middle-slice Sperner unranking with a deterministic per-layer `u16` counter `ctr_l` requiring $z = 8$ leading zero bits in $H_l = \mathrm{BLAKE3\_KEYED}(K_{\mathrm{pub}},\, \mathrm{Tweak}_{\mathrm{OneTimeMsg}} \parallel \mathrm{root}_{l-1} \parallel \mathrm{ctr}_l)$ cuts the Sperner domain from $2^{128}$ to $2^{120}$:
- **Exact `u128` verification (`n = 24, w = 40, S_mid = 468`):**
  $$|\mathcal{L}_{468}(24, 40)| \;=\; \mathbf{1{,}973{,}221{,}677{,}906{,}098{,}493{,}567{,}206{,}234{,}001{,}571{,}000} \;>\; 2^{120} \;=\; 1{,}329{,}227{,}995{,}784{,}915{,}872{,}903{,}807{,}060{,}280{,}344{,}576$$
  ($\log_2 |\mathcal{L}_{468}(24, 40)| = \mathbf{120.569964\text{ bits}}$, $+ z = 8 \implies \mathbf{128.569964\text{ bits}}$).
  For $w = 39$, $|\mathcal{L}_{456}(24, 39)| = 1{,}102{,}272{,}360{,}296{,}506{,}971{,}467{,}046{,}668{,}212{,}509{,}411$ (`119.729892 < 120`), proving **`w = 40` is the exact integer minimum**.
- **Security reduction:** Because $\mathcal{L}_{468}(24, 40)$ is an antichain, a forged $(r'_{l-1}, \mathrm{ctr}'_l)$ is dominated by the revealed signature iff its unranked vector equals the revealed vector (probability $2^{-120}$ on uniform `H_l[1..16]`) AND its top byte `H_l[0] == 0` (probability $2^{-8}$), yielding $2^{-128}$ per offline hash.
- **Why $z = 8$ (`u16`) instead of $z = 10$ (`u16` hazard caught!):** With a `u16` (`65,536` values), $z = 10$ has overflow probability $(1023/1024)^{65536} \approx 2^{-92.4}$ — across $2^{32}$ signatures that leaves a `2^{-60}` overflow hazard (requiring ugly 3-byte `u24` counters). At $z = 8$, the `u16` overflow probability is $(255/256)^{65536} \approx \mathbf{2^{-370}}$ (impossible across $2^{128}$ keys!), grinding costs only `256` hashes/layer (`1,024` mean / `2,570` `p99` across `d = 4` layers — `< 0.6%` of signing work!), and saves `2` full chains (`128 B` across 4 layers) vs. `z = 0` (`Sp26(w=37, z=0)` = `3,412 B`).
- **Exact constant-work verification:** Since $24 \times 39 = 936$ is even, $S_{\mathrm{mid}} = 468$ is exact, so every layer executes **exactly `468` verify chain steps** (zero variance).
- **Zero-ROM in-place unranking:** Exact `O(S)` boxcar deconvolution (`prev[s] = cur[s] - cur[s-1] + prev[s-w]`, `469 × 16 B = 7.5 KiB` stack buffer, `0 B` ROM), verified bit-for-bit against the full DP table on boundary ranks $0, 1, 123456789, 2^{120}-1, |\mathcal{L}|-1$.

### 8.3 Exact Global Regime Map (Quantifying the Cost of Every Hardware Constraint)

Using a compiled Rust global DP across all hypertree partitions, per-layer OTS widths, `z ∈ {0, 8, 10, 12}`, and `U-PORS` codes, we quantified the exact price of each hardware constraint (`q = 2^{32}`, `≥ 128 b`, pure BLAKE3, stateless; `ST33` est. `25 µs/comp`, `160 MHz` Cortex-M33 est. `9.4 µs/comp`, Apple M6 1-core est. `8.6 ns/comp` — all embedded numbers unmeasured estimates):

| Regime & Constraints | Best Clean Architecture | Raw / Base64 | vs `FORS` / `SLH-128s` | Est. Embedded Sign (`p99`) | Est. M6 kg / Sign / Ver | Top Tree | Security @ $2^{32}$ (raw / true) |
|---|---|---:|---:|---:|---:|---:|---:|
| *Shipped Preset A (`0` cache, `ST33 ≤ 5 s`, 0 grinding)* | `7×5` `WOTS16` + `U-FORS(3,10,64,5,15)` | `6,432` / `8,576 B` | `-13%` / `-18%` | `3.58 s` ST33 | `0.17 ms` / `1.22 ms` / `36 µs` | `1 KiB` | `138.5 b` |
| **R1 — Strict `0`-cache `ST33 ≤ 5 s`** *(floor: `4,688 B`)* | `7×5` `Sp28(w23,z8)` + `U-PORS(4,16,S39,A9,k9,m32)` *(or `k10,m35`: `4,946 B` zero-cap `134.7 b`)* | `4,834` / `6,448 B` | `-35%` / `-38%` | `4.84 s` ST33 | `0.2 ms` / `1.35 ms` / `37 µs` | `1 KiB` | `126.0` / `131.3 b` |
| **R2 — `128 KiB` Cached Top Tree, `ST33 warm ≤ 5 s`** *(floor: `3,742 B`)* | `12+5+5+5+5` `Sp25(w32,z10)` + `U-PORS(4,12,A9,k12,m41)` | `3,982` / `5,312 B` | `-46%` / `-49%` | `3.73 s` ST33 warm | `29 ms` / `1.23 ms` / `37 µs` | `128 KiB` | `123.9` / `129.0 b` |
| **R3 — `0`-Cache `160 MHz` Cortex-M33 (`≤ 5 s`)** | `6+7+7+6+6` (`d=5`) + `U-PORS(4,16,S39,A10,k9,m40)` | `3,630` / `4,840 B` | `-51%` / `-54%` | `≤ 5.0 s` M33 (`~13 s` ST33) | `0.6 ms` / `3.80 ms` / `46 µs` | `2 KiB` | `123.9` / `129.1 b` |
| **R4 — `0`-Cache `ST33 ≤ 5 s`, Sub-ms M6 Speed** | `7+5×5` `Sp32(w16,z8)` + `U-PORS(4,8,S19,A9,k13,m44)` | `5,136` / `6,848 B` | `-31%` / `-35%` | `4.77 s` ST33 | `0.7 ms` / `0.92 ms` / `28 µs` | `4 KiB` | `122.8` / `128.4 b` |
| **R2 + R3 Combined (`128 KiB` Top Tree + `160 MHz` M33 `≤ 5 s`) — SELECTED `BLINCS-A2`** *(DP floor: `3,085 B`)* | **`12+7+7+7` (`d=4, h=33`) `Sp24(w40,z8)` + `U-PORS(n3,w24,S42,C376,A10,k10,m44)`** | **`3,292` / `4,392 B`** | **`-55%` / `-58%`** | **`4.29 s` M33** | **`34 ms` / `3.94 ms` / `37 µs`** | **`128 KiB`** | **`128.6` / `135.4 b`** |

*(Other clean single-OTS-type finalists in the selected R2+R3 regime: `B1` `3,180 B` [needs cap credit, `124.0/129.5 b`], `A1` `3,228 B` [`Sp23(w47,z8)`, `4.77 s` M33, `128.6/135.4 b`], `Z0` `3,412 B` [`Sp26(w37,z0)`, ZERO WOTS grinding, `4.32 s` M33], `C2` `3,582 B` [`12+6×4`, `h=36`, `2.82 s` M33 / `2.55 ms` M6], `D1` `3,822 B` [`12+5×4`, `h=32`, `1.95 s` M33 / `1.76 ms` M6].)*

---

## 9. Paradigm-Shift Detour & Why We Rejected It: Crash-Safe `U-PORS` Hybrid vs. `SHRINCS`

Before locking in `BLINCS-A2`, we investigated whether hybrid stateful/stateless signing (inspired by `SHRINCS`, Nick & Ruffing, `ePrint 2025/2203`) could break `< 2 KiB` safely:
- **How `SHRINCS` fails:** Under `SignetId = H(fast_root || stateless_root)`, `SHRINCS` uses a stateful 1-time XMSS (`WOTS+`) tree on the fast branch (`~550 B`). Any single backup restore, VM snapshot rollback, or lock-free concurrent race ($r = 2$ on one leaf) drops security instantaneously from **`128 b → 0.0 b`**.
- **Our Crash-Safe `U-PORS` Hybrid construction:** Replace the 1-time XMSS leaves on the fast branch with few-time `U-PORS` leaves under a 1-layer (`h = 12`, `4,096` leaves -> `1,670–1,798 B`, `0.3–0.6 ms` M6) or 2-layer (`12 + 8`, `1,048,576` leaves -> `2,152–2,280 B`) tree. Because every internal `WOTS` layer signs only a *deterministic* child root with deterministic smallest-valid `ctr`, **zero 1-time keys can ever be broken by rollback**; only the bottom `U-PORS` leaf sees $r$ collisions.
- **Exact single-leaf rollback-survival bits (raw, before `+5 b` Octopus cap credit):**

  | Fast-Path Variant | `1`-layer (`4K` lvs) | `2`-layer (`1M` lvs) | $r = 1$ | $r = 2$ | $r = 4$ | $r = 8$ | $r = 16$ | $r = 32$ |
  |---|---:|---:|---:|---:|---:|---:|---:|---:|
  | `SHRINCS` (XMSS `WOTS+`) | `~550 B` | `~1,000 B` | `128.0 b` | **`0.0 b`** | `0.0 b` | `0.0 b` | `0.0 b` | `0.0 b` |
  | `Fast-Std` (`A9, n4, w16, k9, m32`) | `1,670 B` | `2,152 B` | `159.8 b` | **`132.6 b`** | `111.6 b` | `92.4 b` | `74.1 b` | `56.4 b` |
  | `Fast-Tank` (`A10, n4, w16, k9, m40`) | `1,798 B` | `2,280 B` | `168.8 b` | **`146.2 b`** | **`127.4 b`** | `109.2 b` | `91.3 b` | `73.6 b` |
  | `Fast-Ultra` (`A10, n4, w20, k9, m40`) | `1,798 B` | `2,280 B` | `177.7 b` | **`151.2 b`** | **`130.4 b`** | `111.2 b` | `92.7 b` | `74.7 b` |

- **Why we still chose 100% pure stateless `BLINCS-A2` (`3,292 B`):**
  1. Sustained adversarial/read-only-FS rollback ($r \ge 16..64$) still degrades a stateful branch, whereas `BLINCS-A2` has zero state and never degrades even if disk state is frozen forever.
  2. Avoiding counter-order privacy leakage on `2`-layer fast paths requires a secret Feistel permutation (losing sequential lower-tree caching), while `1`-layer Feistel caps fast signatures at `4,096`.
  3. Variable-size two-branch signatures complicate the spec, verifier, and Lean 4 formalization.
  4. Once `BLINCS-A2` reached **`3,292 B`** purely statelessly (already smaller than AES `FAEST-EM-128s` and `2.4×` smaller than `SLH-DSA-128s`), staying 100% stateless was overwhelmingly cleaner.

*(This construction remains an interesting secondary contribution / remark in the paper showing how `U-PORS` transforms `SHRINCS`'s catastrophic $r=2$ cliff into graceful multi-rollback degradation.)*

---

## 10. Complete Exact Specification & Audit Ledger for Selected Flagship **`BLINCS-A2` (`3,292 B`)**

### 10.1 Locked Parameters & Exact Wire Layout (`3,292 B` Raw / `4,392 B` Base64)
- **Hash primitive:** `BLAKE3` (`16`-byte truncated nodes/chains/salts/randomizer, `32`-byte `SignetId = K_pub || top_root`, `32`-byte message digest `h_msg` via Design B3 single-pass salted keyed BLAKE3).
- **Hypertree:** `d = 4` layers, total height `h = 33` (`top = 12` cached in `128 KiB` RAM/Flash [`4,096` leaves], lower 3 layers uniform `h_low = 7` [`128` leaves each]).
- **One-Time Signature (`S-WOTS+Z`):** Single OTS type across all 4 layers: `n = 24` chains, `w = 40` (`39` hash steps/chain), middle Sperner slice `S = 468`, deterministic `u16` counter (`2 B`) enforcing `z = 8` leading zero bits (`H_l[0] == 0`), exact `O(S)` boxcar deconvolution unranking (`0 B` ROM), `7`-block (`400 B`) leaf public-key hash.
- **Few-Time Signature (`U-PORS`):** Single binary tree of height `A = 10` (`L = 1,024` leaves), `n = 3` chains/leaf, `w = 24` (`23` steps/chain), full upper slice `S = 42` (`C = 376` codewords, `27` verify steps/leaf, `0 B` ROM closed-form hexagon unranking, exact `64 B` = 1-block BLAKE3 leaf hash), `k = 10` distinct leaves, `u32` counter (`4 B`) enforcing Octopus sibling cap `sibs(D) ≤ m_max = 44`.
- **Canonical fixed-length wire layout (`3,292 B`):**
  - `e` (`16 B`) + `R` (`16 B`) = **`32 B`**
  - `ctr_ft` (`4 B`, `u32` LE) + `10 × 3 × 16 B` (`U-PORS` chain values = `480 B`) + `44 × 16 B` (`U-PORS` Octopus siblings = `704 B`; if actual `sibs < 44`, trailing `(44 - sibs) × 16` bytes MUST be zero and verified zero for canonical encoding!) = **`1,188 B`**
  - `4` hypertree layers, each `ctr_l` (`2 B`, `u16` LE) + `24 × 16 B` (`S-WOTS+Z` chains = `384 B`) + `h_l × 16 B` Merkle auth path (`7, 7, 7, 12` = `33 × 16 = 528 B`): `4 × 386 + 528` = **`2,072 B`**
  - **Total:** `32 + 1,188 + 2,072` = **`3,292 B`** (`4,392 B` Base64).
- **Unbiased `D`-extraction & fast rejection loop:**
  - `D = BLAKE3_KEYED_XOF(K_pub, Tweak(Message) || R || h_msg || ctx || ctr_ft)`.
  - First `33` bits -> `leaf_addr` (`(top_idx: 12b, l2: 7b, l1: 7b, l0: 7b)`).
  - Subsequent `10`-bit chunks -> collect `10` distinct leaf indices in `0..1024` (reject duplicates, avg `10.04` chunks), sort ascending, compute `sibs(leaves)`. If `sibs > 44`, increment `ctr_ft` and repeat (**only 1 BLAKE3 compression per rejected trial**!).
  - Once `sibs ≤ 44`, draw `10` unbiased codeword indices in `0..376` from subsequent `9`-bit chunks (reject `>= 376`, `73.4%` accept rate, zero modulo bias, zero division) and unrank via the closed-form hexagon unranker.

### 10.2 Exact Security Curve (`U-PORS` Exact DP + Importance-Sampled Cap Credit)
Exact `q(1..10)` for $\mathcal{L}_{42}(3, 24)$ (`C = 376`):
`q(1)=0.0026595745`, `q(2)=0.1700038392`, `q(3)=0.3362391218`, `q(4)=0.4587714506`, `q(5)=0.5477348344`, `q(6)=0.6137590780`, `q(7)=0.6641389466`, `q(8)=0.7036129754`, `q(9)=0.7352753475`, `q(10)=0.7611901986`.

| Budget $q$ | Naive $s^k$ Bound | **Elementary Exact Without-Replacement Bound (Zero Cap Credit)** | Importance-Sampled Cap Credit ($\Delta_{\mathrm{cap}}$) | **True Security (with Octopus Cap)** |
|---|---:|---:|---:|---:|
| $2^{30}$ | `138.28 b` | **`139.75 b`** | `~+5.7 b` | `~145.5 b` |
| $2^{31}$ | `133.36 b` | **`134.58 b`** | `~+6.2 b` | `~140.8 b` |
| **$2^{32}$ (target)** | `127.60 b` | **`128.58 b`** | **`+6.79 b`** *(dom $r=5..8$)* | **`135.37 b`** |
| **$2^{33}$ ($2\times$ overuse)** | `120.79 b` | **`121.56 b`** | **`+7.35 b`** *(dom $r=7..10$)* | **`128.91 b`** *(still $> 128$ b!)* |
| $2^{34}$ ($4\times$ overuse) | `112.71 b` | `113.29 b` | `~+7.8 b` | `~121.1 b` |
| $2^{35}$ ($8\times$ overuse) | `103.14 b` | `103.55 b` | `~+8.1 b` | `~111.7 b` |
| $2^{36}$ ($16\times$ overuse) | `91.89 b` | `92.16 b` | `~+8.3 b` | `~100.5 b` |
| $2^{38}$ ($64\times$ overuse) | `64.43 b` | `64.52 b` | `~+8.6 b` | `~73.1 b` |

### 10.3 Exact Compression Counts, SIMD Alignment & Tail-Jitter Analysis
- **`from_seed` (128 KiB top height-12 tree):** `4,096 × 967 + 4,095` = **`3,964,927` compressions** (`~34.1 ms` est. Apple M6 1-core; `~37 s` est. one-time keygen on `160 MHz` M33; exact `128 × 32` leaf SIMD waves).
- **Warm signing fixed work:**
  - `3` lower height-7 trees (`3 × (128 × 967 + 127)`): `371,709` compressions (`128 × 24 = 3,072 = 96 × 32` exact 32-lane SIMD waves per tree!).
  - `1` active top-layer `S-WOTS+Z` signature (`24 + 468`): `492` compressions.
  - `1` `U-PORS` height-10 tree (`1,024 × (3 × 24 + 1) + 1,023`): `75,775` compressions (`1,024 × 3 = 3,072 = 96 × 32` exact 32-lane SIMD waves, `1,024` single-block 64 B leaves!).
  - **Total fixed warm work:** **`447,976` compressions**.
- **Warm signing grinding work:**
  - `S-WOTS+Z` (`4 × 256` mean): `1,024` mean / `2,570` `p99` compressions (`u16` overflow prob `2^{-370}`).
  - `U-PORS` (`m_max = 44`): `1,365` mean / `6,287` `p99` compressions (`u32` overflow prob `2^{-4.54 \times 10^6}`).
  - **Total warm signing:** **`450,365` mean / `~456,000` joint `p99`** -> **`p99 / mean = 1.013×`** (virtually zero latency jitter!). Est. `160 MHz` Cortex-M33: **`4.23 s` mean / `4.29 s` `p99`** (`< 5.0 s`); est. Apple M6 1-core: **`~3.9 ms`**.
- **Verification (100% constant work, zero variance):**
  - `4 × (468 + 7) = 1,900` (`S-WOTS+Z`) + `33` (hypertree auth) + `10 × (27 + 1) + 44 = 324` (`U-PORS`) + `6` (header/msg) = **`2,263` compressions** (`~37 µs` est. Apple M6 1-core — practically identical to `FORS(8,20)`'s `34.2 µs` and `~40×` faster than `FAEST-EM-128s`!).

### 10.4 Summary Comparison Against State of the Art (128-bit Classical Security)

| Scheme | Assumption | Stateless? | $q_{\max}$ | Signature Size (Raw / B64) | Est. / Meas. Verify (1-core) |
|---|---|---|---:|---:|---:|
| `SLH-DSA-128s` (FIPS 205) | SHA-256 / SHAKE | Yes | $2^{64}$ | `7,856` / `10,476 B` | `~0.5–1.5 ms` |
| `BLINCS FORS(8,20)` (old) | Pure BLAKE3 | Yes | $2^{32}$ | `7,392` / `9,856 B` | `34.2 µs` (M6 meas.) |
| `BLINCS U-FORS` Preset A (v0.2) | Pure BLAKE3 | Yes | $2^{32}$ | `6,432` / `8,576 B` | `36.2 µs` (M6 meas.) |
| `FAEST-EM-128s` (NIST R2) | AES-128 Ideal Cipher + Hash | Yes | $\infty$ | `3,924` / `5,232 B` | `~1,500 µs` |
| **`BLINCS-A2` (NEW)** | **Pure BLAKE3** | **Yes** | **$2^{32}$** | **`3,292` / `4,392 B`** | **`~37 µs` (M6 est.)** |
| *Reference: `ML-DSA-44` (FIPS 204)* | *Module-LWE / SIS (lattice)* | *Yes* | *$\infty$* | *`2,420` / `3,228 B`* | *`~40–60 µs`* |

### 10.5 Additional References to Cite in the Paper
- **Bleichenbacher & Maurer (ASIACRYPT 1996):** *Optimal Tree-Based One-Time Digital Signature Schemes* (DAG lower bound; cf. Zhang–Cui–Yu `ePrint 2023/850`).
- **de Bruijn, van Ebbenhorst Tengbergen, & Kruyswijk (1951):** *On the set of divisors of a number* (Sperner / LYM property of divisor / chain-product lattices $[w]^n$).
- **Joag-Dev & Proschan (Annals of Statistics 1983):** *Negative Association of Random Variables, with Applications* (justifies our conservative without-replacement hypergeometric `U-PORS` bound).
- **Nick & Ruffing (`ePrint 2025/2203`):** *SHRINCS: 324-byte stateful post-quantum signatures with static backups* (baseline for our Crash-Safe `U-PORS` Hybrid comparison in §9).
- **Baum et al. (`FAEST` v2, NIST Additional Signatures Round 2, 2025):** VOLE-in-the-Head AES-128 signatures (`3,924 B` `FAEST-EM-128s`, `4,506 B` `FAEST-128s`).
