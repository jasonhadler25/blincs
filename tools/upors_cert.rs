//! Exhaustive, zero-Monte-Carlo, deterministic all-orbits upper-bound certifier
//! for `BLINCS-48-X` `U-PORS` (`H=11, K=9, m_max=45, C=L_42(3, 24)`).
//!
//! Compile & run (zero external dependencies):
//!   `rustc --edition 2024 -O tools/upors_cert.rs -o /tmp/upors_cert`
//!   `/tmp/upors_cert --fast`   (< 1s CI check: integer u_3, small-tree BF, trinomial r=2,
//!                               root-merge/symmetry checks, exact BigInt rational certification
//!                               of archived all-orbits S_1..S_44 sums)
//!   `/tmp/upors_cert`          (~11 min full run: recomputes all 1,614,132 Aut(T_11)-orbits from
//!                               scratch, checks bit-exact equality with archived sums, and runs
//!                               exact BigInt rational interval certification with zero f64 reliance)
//!
//! What this program certifies deterministically (ZERO Monte Carlo, ZERO f64 in final bounds):
//!   1. Exact integer certificate of the 3-term exponential upper envelope
//!        `u_3(t) = 1 - (7495/5546)*(79/100)^t + (1949/5546)*(20/100)^t >= q_C(t)`
//!      for ALL integers `t >= 0` (`t=0,1` exact, `t=1..=16` checked in exact 256-bit integers,
//!      and `t >= 16` proved by `(15/376)*(371/376)^t >= (7495/5546)*(79/100)^t`).
//!   2. Small-tree brute-force ground-truth verification (`H=4, K=3, m_max=6`) confirming
//!      agreement between brute-force subset enumeration and `F256` Kronecker evaluation.
//!   3. Exact integer enumerator `|F| = 180,700,154,447,569,471,488`, `p_cap = |F| / C(2048, 9)`,
//!      independent closed-form trinomial `r=2` uncapped check (both `u_3` and exact `q_C`),
//!      and exact pairwise inclusion clustering ratios `Pr[u,v in D] / (9/2048)^2` by LCA height.
//!   4. Complete deterministic enumeration of ALL `1,614,132` isomorphism classes (orbits) of `F`
//!      modulo `Aut(T_11)`, verifying `sum(orbit_size) == |F|`.
//!   5. Deterministic evaluation of the exact 3-term envelope moments `M_k = sum_j c_j (1 - G(z_j))^k`
//!      (`k = 1..=44`) on EVERY SINGLE ONE of the `1,614,132` orbits in 256-bit pure fractional
//!      fixed-point arithmetic (`eps = 2^-256`), accumulating `orbit_size * M_k` in exact 448-bit
//!      signed integers across all orbits.
//!   6. 100% exact arbitrary-precision `BigInt` rational interval certification (ZERO `f64`!):
//!      exact integer `C(q, k)`, exact per-moment F256 error `340,122,240 * 2^-256`, exact
//!      Leibniz alternating remainder with verified `(14990/5546)^9 < 7700`, outward-rounded
//!      decimal upper bounds on `P`, exact Taylor-certified downward-rounded bit lower bounds
//!      `-log2 P`, and exact integer `q_96` comparison `P_UB(q_96) * 2^96 <= 1`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::Instant;

const H: usize = 11;
const L: usize = 1 << H;
const K: usize = 9;
const M_MAX: usize = 45;
const N2: usize = 1 << K;
const N3: usize = 19_683; // 3^9
const K_POW: usize = 44; // Alternating binomial remainder <= 2^-201 even up to lambda = 20!
const STRIDE: usize = (K + 1) * (M_MAX + 1);

// ============================================================================
// 1. Exact 256-bit unsigned integer for the all-t integer certificate of u_3(t)
// ============================================================================
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct U256([u64; 4]);

impl U256 {
    const fn from_u64(x: u64) -> Self { Self([x, 0, 0, 0]) }
    fn cmp_val(&self, o: &Self) -> std::cmp::Ordering {
        for i in (0..4).rev() {
            if self.0[i] != o.0[i] { return self.0[i].cmp(&o.0[i]); }
        }
        std::cmp::Ordering::Equal
    }
    fn add(self, o: Self) -> Self {
        let mut r = [0u64; 4];
        let mut c = 0u128;
        for i in 0..4 {
            let s = self.0[i] as u128 + o.0[i] as u128 + c;
            r[i] = s as u64;
            c = s >> 64;
        }
        assert!(c == 0, "U256 add overflow");
        Self(r)
    }
    fn sub(self, o: Self) -> Self {
        let mut r = [0u64; 4];
        let mut b = 0u64;
        for i in 0..4 {
            let (d1, o1) = self.0[i].overflowing_sub(o.0[i]);
            let (d2, o2) = d1.overflowing_sub(b);
            r[i] = d2;
            b = (o1 as u64) + (o2 as u64);
        }
        assert!(b == 0, "U256 sub underflow");
        Self(r)
    }
    fn mul_u64(self, m: u64) -> Self {
        let mut r = [0u64; 4];
        let mut c = 0u128;
        for i in 0..4 {
            let s = (self.0[i] as u128) * (m as u128) + c;
            r[i] = s as u64;
            c = s >> 64;
        }
        assert!(c == 0, "U256 mul_u64 overflow");
        Self(r)
    }
    fn pow_u64(base: u64, exp: u32) -> Self {
        let mut r = Self::from_u64(1);
        for _ in 0..exp { r = r.mul_u64(base); }
        r
    }
}

/// Exact integer verification of Lemma: u_3(t) >= q_C(t) for ALL integers t >= 0!
/// Also returns exact `(q_C(1), q_C(2))` as rational `(num, den)` for the independent r=2 check.
fn verify_u3_envelope_all_t() -> ((u128, u128), (u128, u128)) {
    let mut codes = Vec::new();
    for a in 0..24usize {
        for b in 0..24usize {
            if a + b <= 42 && 42 - a - b < 24 {
                codes.push([a, b, 42 - a - b]);
            }
        }
    }
    assert_eq!(codes.len(), 376);
    let mut a_cnt = Vec::with_capacity(376 * 3);
    let mut b_cnt = Vec::with_capacity(376 * 3);
    let mut zero_coord_targets = 0usize;
    for &v in &codes {
        if v[0] == 0 || v[1] == 0 || v[2] == 0 {
            zero_coord_targets += 1;
        }
        for i in 0..3 {
            a_cnt.push(codes.iter().filter(|d| d[i] > v[i]).count() as u64);
        }
        for &(i, j) in &[(0, 1), (0, 2), (1, 2)] {
            b_cnt.push(codes.iter().filter(|d| d[i] > v[i] && d[j] > v[j]).count() as u64);
        }
    }
    assert_eq!(zero_coord_targets, 15);
    assert_eq!(codes.iter().filter(|d| d[0] > 0).count(), 371);

    let mut d_t2_u128 = 0u128;
    // Divide both sides by 4^t (100/4=25, 376/4=94) so all values fit in U256 through t=16:
    for t in 1..=16u32 {
        let mut sum_a = U256::from_u64(0);
        for &x in &a_cnt { sum_a = sum_a.add(U256::pow_u64(x, t)); }
        let mut sum_b = U256::from_u64(0);
        for &x in &b_cnt { sum_b = sum_b.add(U256::pow_u64(x, t)); }
        let d_t = sum_a.sub(sum_b);
        if t == 2 {
            assert!(d_t.0[2] == 0 && d_t.0[3] == 0);
            d_t2_u128 = (d_t.0[0] as u128) | ((d_t.0[1] as u128) << 64);
        }
        let mut lhs = d_t.mul_u64(5546);
        for _ in 0..t { lhs = lhs.mul_u64(25); }

        let r1 = U256::pow_u64(79, t).mul_u64(7495);
        let r2 = U256::pow_u64(20, t).mul_u64(1949);
        let mut rhs = r1.sub(r2).mul_u64(376);
        for _ in 0..t { rhs = rhs.mul_u64(94); }

        if t == 1 {
            assert!(lhs == rhs, "u_3(1) != q_C(1)");
        } else {
            assert!(lhs.cmp_val(&rhs) != std::cmp::Ordering::Less, "u_3({t}) < q_C({t})");
        }
    }
    // Analytic tail proof for ALL t >= 16:
    assert!(371u64 * 100 > 376u64 * 79);
    let mut tail_lhs = U256::pow_u64(371, 16).mul_u64(15 * 5546);
    for _ in 0..16 { tail_lhs = tail_lhs.mul_u64(25); }
    let mut tail_rhs = U256::pow_u64(79, 16).mul_u64(376 * 7495);
    for _ in 0..16 { tail_rhs = tail_rhs.mul_u64(94); }
    assert!(tail_lhs.cmp_val(&tail_rhs) == std::cmp::Ordering::Greater);
    // Exact coefficient L1 norm proof: (1 + 7495/5546 + 1949/5546)^9 = (14990/5546)^9 < 7700!
    assert!(14990u128.pow(9) < 7700u128 * 5546u128.pow(9));
    println!("[CERTIFIED] Exact integer proof: u_3(t) >= q_C(t) for ALL integers t >= 0 (exact t=0,1; checked t=1..=16; tail proved t>=16) & ||c||_1 = (14990/5546)^9 < 7700.");
    let qc2_den = 376u128 * 376 * 376;
    ((1, 376), (qc2_den - d_t2_u128, qc2_den))
}

// ============================================================================
// 2. 256-bit pure fractional fixed-point arithmetic (val * 2^256 in [0, 1))
//    and exact 448-bit signed accumulator for global orbit-weighted sums
// ============================================================================
#[derive(Clone, Copy, Default)]
struct F256([u64; 4]);

impl F256 {
    const ZERO: Self = Self([0; 4]);

    /// Bit-exact floor(num * 2^256 / den) for ANY 0 <= num < den <= u128::MAX (zero overflow!).
    fn from_ratio_exact_u128(num: u128, den: u128) -> Self {
        debug_assert!(num < den);
        let mut rem = num;
        let mut out = [0u64; 4];
        for bit in (0..256).rev() {
            let carry = rem >> 127;
            rem <<= 1;
            if carry != 0 || rem >= den {
                rem = rem.wrapping_sub(den);
                out[bit / 64] |= 1u64 << (bit % 64);
            }
        }
        Self(out)
    }

    /// Fast 32-bit chunk floor(num * 2^256 / den) for den < 2^96 (|F| < 2^68, C(2048,9) < 2^81).
    #[inline(always)]
    fn from_ratio_fast_u128(num: u128, den: u128) -> Self {
        let mut rem = num;
        let mut ch = [0u64; 8];
        for c in 0..8 {
            rem <<= 32;
            ch[c] = (rem / den) as u64;
            rem %= den;
        }
        Self([
            ch[7] | (ch[6] << 32),
            ch[5] | (ch[4] << 32),
            ch[3] | (ch[2] << 32),
            ch[1] | (ch[0] << 32),
        ])
    }

    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut r = [0u64; 4];
        let mut c = 0u128;
        for i in 0..4 {
            let s = self.0[i] as u128 + o.0[i] as u128 + c;
            r[i] = s as u64;
            c = s >> 64;
        }
        Self(r)
    }

    #[inline(always)]
    fn mul_small_ratio(self, num: u64, den: u64) -> Self {
        let mut p = [0u64; 5];
        let mut c = 0u128;
        for i in 0..4 {
            let v = (self.0[i] as u128) * (num as u128) + c;
            p[i] = v as u64;
            c = v >> 64;
        }
        p[4] = c as u64;
        let d = den as u128;
        let mut rem = p[4] as u128;
        let mut q = [0u64; 4];
        for i in (0..4).rev() {
            let cur = (rem << 64) | (p[i] as u128);
            q[i] = (cur / d) as u64;
            rem = cur % d;
        }
        Self(q)
    }

    /// Limb-skipping truncated product in [0, 1); error vs exact product strictly in [0, 4 * 2^-256].
    #[inline(always)]
    fn mul_fast(self, o: Self) -> Self {
        let [a0, a1, a2, a3] = self.0;
        let [b0, b1, b2, b3] = o.0;
        if a3 != 0 {
            // Exact limb 3 carry + exact limbs 4, 5, 6, 7:
            let m03 = (a0 as u128) * (b3 as u128);
            let m12 = (a1 as u128) * (b2 as u128);
            let m21 = (a2 as u128) * (b1 as u128);
            let m30 = (a3 as u128) * (b0 as u128);
            let l3_lo = (m03 as u64 as u128) + (m12 as u64 as u128) + (m21 as u64 as u128) + (m30 as u64 as u128);
            let c4 = (m03 >> 64) + (m12 >> 64) + (m21 >> 64) + (m30 >> 64) + (l3_lo >> 64);

            let m13 = (a1 as u128) * (b3 as u128);
            let m22 = (a2 as u128) * (b2 as u128);
            let m31 = (a3 as u128) * (b1 as u128);
            let l4 = c4 + (m13 as u64 as u128) + (m22 as u64 as u128) + (m31 as u64 as u128);
            let c5 = (l4 >> 64) + (m13 >> 64) + (m22 >> 64) + (m31 >> 64);

            let m23 = (a2 as u128) * (b3 as u128);
            let m32 = (a3 as u128) * (b2 as u128);
            let l5 = c5 + (m23 as u64 as u128) + (m32 as u64 as u128);
            let c6 = (l5 >> 64) + (m23 >> 64) + (m32 >> 64);

            let m33 = (a3 as u128) * (b3 as u128);
            let l6 = c6 + (m33 as u64 as u128);
            let l7 = (l6 >> 64) + (m33 >> 64);
            return Self([l4 as u64, l5 as u64, l6 as u64, l7 as u64]);
        }
        if a2 != 0 {
            let m03 = (a0 as u128) * (b3 as u128);
            let m12 = (a1 as u128) * (b2 as u128);
            let m21 = (a2 as u128) * (b1 as u128);
            let l3_lo = (m03 as u64 as u128) + (m12 as u64 as u128) + (m21 as u64 as u128);
            let c4 = (m03 >> 64) + (m12 >> 64) + (m21 >> 64) + (l3_lo >> 64);

            let m13 = (a1 as u128) * (b3 as u128);
            let m22 = (a2 as u128) * (b2 as u128);
            let l4 = c4 + (m13 as u64 as u128) + (m22 as u64 as u128);
            let c5 = (l4 >> 64) + (m13 >> 64) + (m22 >> 64);

            let m23 = (a2 as u128) * (b3 as u128);
            let l5 = c5 + (m23 as u64 as u128);
            let l6 = (l5 >> 64) + (m23 >> 64);
            return Self([l4 as u64, l5 as u64, l6 as u64, 0]);
        }
        if a1 != 0 {
            let m03 = (a0 as u128) * (b3 as u128);
            let m12 = (a1 as u128) * (b2 as u128);
            let l3_lo = (m03 as u64 as u128) + (m12 as u64 as u128);
            let c4 = (m03 >> 64) + (m12 >> 64) + (l3_lo >> 64);
            let m13 = (a1 as u128) * (b3 as u128);
            let l4 = c4 + (m13 as u64 as u128);
            let l5 = (l4 >> 64) + (m13 >> 64);
            return Self([l4 as u64, l5 as u64, 0, 0]);
        }
        let m03 = (a0 as u128) * (b3 as u128);
        Self([(m03 >> 64) as u64, 0, 0, 0])
    }
}

/// Per-orbit signed 320-bit fixed-point accumulator (two's complement, * 2^-256).
#[derive(Clone, Copy, Default)]
struct SAcc320([u64; 5]);

impl SAcc320 {
    #[inline(always)]
    fn add_f256(&mut self, neg: bool, u: F256) {
        if !neg {
            let mut c = 0u128;
            for i in 0..4 {
                let s = self.0[i] as u128 + u.0[i] as u128 + c;
                self.0[i] = s as u64;
                c = s >> 64;
            }
            self.0[4] = self.0[4].wrapping_add(c as u64);
        } else {
            let mut b = 0u64;
            for i in 0..4 {
                let (d1, o1) = self.0[i].overflowing_sub(u.0[i]);
                let (d2, o2) = d1.overflowing_sub(b);
                self.0[i] = d2;
                b = (o1 as u64) + (o2 as u64);
            }
            self.0[4] = self.0[4].wrapping_sub(b);
        }
    }

    #[inline(always)]
    fn add_f256_mul(&mut self, neg: bool, u: F256, mult: u64) {
        if mult == 1 {
            self.add_f256(neg, u);
            return;
        }
        let mut p = [0u64; 5];
        let mut c = 0u128;
        for i in 0..4 {
            let s = (u.0[i] as u128) * (mult as u128) + c;
            p[i] = s as u64;
            c = s >> 64;
        }
        p[4] = c as u64;
        if !neg {
            let mut cc = 0u128;
            for i in 0..5 {
                let s = self.0[i] as u128 + p[i] as u128 + cc;
                self.0[i] = s as u64;
                cc = s >> 64;
            }
        } else {
            let mut b = 0u64;
            for i in 0..5 {
                let (d1, o1) = self.0[i].overflowing_sub(p[i]);
                let (d2, o2) = d1.overflowing_sub(b);
                self.0[i] = d2;
                b = (o1 as u64) + (o2 as u64);
            }
        }
    }
}

/// Global signed 448-bit integer accumulator holding sum_{orbits} orbit_size * SAcc320(orbit)!
#[derive(Clone, Copy, Default)]
struct SAcc448([u64; 7]);

impl SAcc448 {
    fn add_assign(&mut self, o: &Self) {
        let mut c = 0u128;
        for i in 0..7 {
            let s = self.0[i] as u128 + o.0[i] as u128 + c;
            self.0[i] = s as u64;
            c = s >> 64;
        }
    }

    fn add_weighted(&mut self, w: u128, v: SAcc320) {
        let neg = (v.0[4] as i64) < 0;
        let mag = if !neg {
            v.0
        } else {
            let mut r = [0u64; 5];
            let mut c = 1u128;
            for i in 0..5 {
                let s = (!v.0[i]) as u128 + c;
                r[i] = s as u64;
                c = s >> 64;
            }
            r
        };
        let w0 = w as u64 as u128;
        let w1 = w >> 64;
        let mut prod = [0u64; 7];
        let mut c = 0u128;
        for i in 0..5 {
            let p = (mag[i] as u128) * w0 + c;
            prod[i] = p as u64;
            c = p >> 64;
        }
        prod[5] = c as u64;
        if w1 != 0 {
            let mut c2 = 0u128;
            for i in 0..5 {
                let p = (mag[i] as u128) * w1 + (prod[i + 1] as u128) + c2;
                prod[i + 1] = p as u64;
                c2 = p >> 64;
            }
            prod[6] = c2 as u64;
        }
        if !neg {
            let mut cc = 0u128;
            for i in 0..7 {
                let s = self.0[i] as u128 + prod[i] as u128 + cc;
                self.0[i] = s as u64;
                cc = s >> 64;
            }
        } else {
            let mut b = 0u64;
            for i in 0..7 {
                let (d1, o1) = self.0[i].overflowing_sub(prod[i]);
                let (d2, o2) = d1.overflowing_sub(b);
                self.0[i] = d2;
                b = (o1 as u64) + (o2 as u64);
            }
        }
    }

    fn to_f64_scaled(&self, total_f: u128) -> f64 {
        let neg = (self.0[6] as i64) < 0;
        let mag = if !neg {
            self.0
        } else {
            let mut r = [0u64; 7];
            let mut c = 1u128;
            for i in 0..7 {
                let s = (!self.0[i]) as u128 + c;
                r[i] = s as u64;
                c = s >> 64;
            }
            r
        };
        let mut val = 0.0f64;
        for i in (0..7).rev() {
            val = val * 18446744073709551616.0 + (mag[i] as f64);
        }
        let scaled = (val * 16.0 / (total_f as f64)) * 2.0f64.powi(-256);
        if neg { -scaled } else { scaled }
    }
}

// ============================================================================
// 3. Exact tree enumerator, orbit enumeration, and memoized subtree DP
// ============================================================================
fn comb_u128(n: usize, k: usize) -> u128 {
    if k > n { return 0; }
    let k = k.min(n - k);
    let mut r = 1u128;
    for i in 1..=k { r = r * ((n - k + i) as u128) / (i as u128); }
    r
}

fn build_f(h_max: usize, k_max: usize, m_max: usize) -> Vec<Vec<Vec<u128>>> {
    let mut f = vec![vec![vec![0u128; m_max + 1]; k_max + 1]; h_max + 1];
    f[0][0][0] = 1;
    f[0][1][0] = 1;
    for h in 0..h_max {
        f[h + 1][0][0] = 1;
        for k in 1..=k_max {
            for s in 0..m_max { f[h + 1][k][s + 1] += 2 * f[h][k][s]; }
        }
        for kl in 1..=k_max {
            for kr in 1..=(k_max - kl) {
                for sl in 0..=m_max {
                    let fl = f[h][kl][sl];
                    if fl == 0 { continue; }
                    for sr in 0..=(m_max - sl) {
                        let fr = f[h][kr][sr];
                        if fr != 0 { f[h + 1][kl + kr][sl + sr] += fl * fr; }
                    }
                }
            }
        }
    }
    f
}

fn solve_sub_dp(f: &[Vec<Vec<u128>>], h: usize, lo: usize, hi: usize, t: &[u16]) -> Vec<u128> {
    if h == 0 {
        let mut dp = vec![0u128; 2 * STRIDE];
        dp[0] = 1;
        dp[STRIDE + (M_MAX + 1)] = 1;
        return dp;
    }
    let mid = (lo + hi) >> 1;
    let split = t.partition_point(|&x| (x as usize) < mid);
    let tl = &t[..split];
    let tr = &t[split..];
    if tl.is_empty() || tr.is_empty() {
        let sub = if tl.is_empty() { solve_sub_dp(f, h - 1, mid, hi, tr) } else { solve_sub_dp(f, h - 1, lo, mid, tl) };
        let n_sub = sub.len() / STRIDE;
        let mut out = vec![0u128; n_sub * STRIDE];
        let fh = &f[h - 1];
        out[0] = 1;
        for kf in 1..=K {
            for sf in 0..M_MAX {
                let cf = fh[kf][sf];
                if cf != 0 { out[kf * (M_MAX + 1) + sf + 1] += cf; }
            }
        }
        for m in 0..n_sub {
            let mb = m * STRIDE;
            for ks in 1..=K {
                for ss in 0..=M_MAX {
                    let cs = sub[mb + ks * (M_MAX + 1) + ss];
                    if cs == 0 { continue; }
                    if ss < M_MAX { out[mb + ks * (M_MAX + 1) + ss + 1] += cs; }
                    for kf in 1..=(K - ks) {
                        for sf in 0..=(M_MAX - ss) {
                            let cf = fh[kf][sf];
                            if cf != 0 { out[mb + (ks + kf) * (M_MAX + 1) + ss + sf] += cs * cf; }
                        }
                    }
                }
            }
        }
        return out;
    }
    let dpl = solve_sub_dp(f, h - 1, lo, mid, tl);
    let dpr = solve_sub_dp(f, h - 1, mid, hi, tr);
    let nl = dpl.len() / STRIDE;
    let nr = dpr.len() / STRIDE;
    let mut out = vec![0u128; nl * nr * STRIDE];
    // Precompute nonzero (sl_min, sl_max) per (ml, kl) and (sr_min, sr_max) per (mr, kr) to skip 90%+ zero iterations!
    let mut lrng = vec![(M_MAX + 1, 0usize); nl * (K + 1)];
    for ml in 0..nl {
        let bl = ml * STRIDE;
        for kl in 0..=K {
            let p = bl + kl * (M_MAX + 1);
            let mut mn = M_MAX + 1;
            let mut mx = 0;
            for s in 0..=M_MAX {
                if dpl[p + s] != 0 {
                    if mn > M_MAX { mn = s; }
                    mx = s;
                }
            }
            lrng[ml * (K + 1) + kl] = (mn, mx);
        }
    }
    let mut rrng = vec![(M_MAX + 1, 0usize); nr * (K + 1)];
    for mr in 0..nr {
        let br = mr * STRIDE;
        for kr in 0..=K {
            let p = br + kr * (M_MAX + 1);
            let mut mn = M_MAX + 1;
            let mut mx = 0;
            for s in 0..=M_MAX {
                if dpr[p + s] != 0 {
                    if mn > M_MAX { mn = s; }
                    mx = s;
                }
            }
            rrng[mr * (K + 1) + kr] = (mn, mx);
        }
    }
    for ml in 0..nl {
        let bl = ml * STRIDE;
        for mr in 0..nr {
            let br = mr * STRIDE;
            let bo = (ml | (mr << tl.len())) * STRIDE;
            for kl in 0..=K {
                let (sl0, sl1) = lrng[ml * (K + 1) + kl];
                if sl0 > M_MAX { continue; }
                for kr in 0..=(K - kl) {
                    let (sr0, sr1) = rrng[mr * (K + 1) + kr];
                    if sr0 > M_MAX { continue; }
                    let add_sib = usize::from((kl == 0) ^ (kr == 0));
                    if sl0 + sr0 + add_sib > M_MAX { continue; }
                    let ksum = kl + kr;
                    let pl = bl + kl * (M_MAX + 1);
                    let pr = br + kr * (M_MAX + 1);
                    let po = bo + ksum * (M_MAX + 1) + add_sib;
                    let sl_hi = sl1.min(M_MAX - sr0 - add_sib);
                    for sl in sl0..=sl_hi {
                        let cl = dpl[pl + sl];
                        if cl == 0 { continue; }
                        let sr_hi = sr1.min(M_MAX - sl - add_sib);
                        for sr in sr0..=sr_hi {
                            let cr = dpr[pr + sr];
                            if cr != 0 { out[po + sl + sr] += cl * cr; }
                        }
                    }
                }
            }
        }
    }
    out
}

fn make_prefix_r(dpr: &[u128]) -> Vec<u128> {
    let mut pref = dpr.to_vec();
    let nr = pref.len() / STRIDE;
    for mr in 0..nr {
        let br = mr * STRIDE;
        for kr in 0..=K {
            let base = br + kr * (M_MAX + 1);
            let mut run = 0u128;
            for sr in 0..=M_MAX {
                run += pref[base + sr];
                pref[base + sr] = run;
            }
        }
    }
    pref
}

fn merge_root_prefix(dpl: &[u128], nl: usize, kl_bits: usize, pref_r: &[u128], nr: usize) -> [u128; N2] {
    let mut res = [0u128; N2];
    for ml in 0..nl {
        let bl = ml * STRIDE;
        for mr in 0..nr {
            let br = mr * STRIDE;
            let mask = ml | (mr << kl_bits);
            let mut sum = 0u128;
            if ml == 0 { sum += pref_r[br + K * (M_MAX + 1) + (M_MAX - 1)]; }
            if mr == 0 {
                for sl in 0..M_MAX { sum += dpl[bl + K * (M_MAX + 1) + sl]; }
            }
            for kl in 1..K {
                let kr = K - kl;
                let pl = bl + kl * (M_MAX + 1);
                let pr = br + kr * (M_MAX + 1);
                for sl in 0..=M_MAX {
                    let cl = dpl[pl + sl];
                    if cl != 0 { sum += cl * pref_r[pr + (M_MAX - sl)]; }
                }
            }
            res[mask] = sum;
        }
    }
    res
}

fn merge_root_single(f_h1: &[Vec<u128>], pref_r: &[u128], nr: usize) -> [u128; N2] {
    let mut pref_f = vec![vec![0u128; M_MAX + 1]; K + 1];
    for kf in 0..=K {
        let mut run = 0u128;
        for sf in 0..=M_MAX {
            run += f_h1[kf][sf];
            pref_f[kf][sf] = run;
        }
    }
    let mut res = [0u128; N2];
    for mr in 0..nr {
        let br = mr * STRIDE;
        let mut sum = 0u128;
        if mr == 0 { sum += pref_f[K][M_MAX - 1]; }
        sum += pref_r[br + K * (M_MAX + 1) + (M_MAX - 1)];
        for kr in 1..K {
            let kf = K - kr;
            let pr = br + kr * (M_MAX + 1);
            let mut prev = 0u128;
            for sr in 0..=M_MAX {
                let cur = pref_r[pr + sr];
                let cr = cur - prev;
                prev = cur;
                if cr != 0 { sum += cr * pref_f[kf][M_MAX - sr]; }
            }
        }
        res[mr] = sum;
    }
    res
}

#[derive(Clone)]
struct SubOrbit {
    s: u8,
    size: u128,
    leaves: Vec<u16>,
}

fn enum_height_h_minus_1() -> Vec<Vec<SubOrbit>> {
    let mut prev: Vec<Vec<SubOrbit>> = vec![vec![]; K + 1];
    prev[1].push(SubOrbit { s: 0, size: 1, leaves: vec![0] });
    for h in 1..H {
        let half = 1u16 << (h - 1);
        let mut next: Vec<Vec<SubOrbit>> = vec![vec![]; K + 1];
        for k in 1..=K {
            for a in &prev[k] {
                if (a.s as usize) + 1 <= M_MAX {
                    next[k].push(SubOrbit { s: a.s + 1, size: a.size * 2, leaves: a.leaves.clone() });
                }
            }
        }
        for kl in 1..=K / 2 {
            for kr in kl..=(K - kl) {
                let kk = kl + kr;
                let la = &prev[kl];
                let lb = &prev[kr];
                if kl == kr {
                    for i in 0..la.len() {
                        let a = &la[i];
                        for j in i..lb.len() {
                            let b = &lb[j];
                            let ss = (a.s as usize) + (b.s as usize);
                            if ss > M_MAX { continue; }
                            let sz = if i == j { a.size * b.size } else { 2 * a.size * b.size };
                            let mut leaves = Vec::with_capacity(kk);
                            leaves.extend_from_slice(&a.leaves);
                            for &x in &b.leaves { leaves.push(x + half); }
                            next[kk].push(SubOrbit { s: ss as u8, size: sz, leaves });
                        }
                    }
                } else {
                    for a in la {
                        for b in lb {
                            let ss = (a.s as usize) + (b.s as usize);
                            if ss > M_MAX { continue; }
                            let sz = 2 * a.size * b.size;
                            let mut leaves = Vec::with_capacity(kk);
                            leaves.extend_from_slice(&a.leaves);
                            for &x in &b.leaves { leaves.push(x + half); }
                            next[kk].push(SubOrbit { s: ss as u8, size: sz, leaves });
                        }
                    }
                }
            }
        }
        prev = next;
    }
    prev
}

/// Small-tree exhaustive validation (H=4, K=3, m_max=6) checking brute-force vs F256 Kronecker!
fn verify_small_tree_ground_truth() {
    let sh = 4usize;
    let sl = 1usize << sh;
    let sk = 3usize;
    let sm = 6usize;
    fn sibs_small(set: &[usize], h: usize) -> usize {
        let mut nodes = set.to_vec();
        let mut sibs = 0usize;
        for _ in 0..h {
            let mut next = Vec::new();
            let mut i = 0;
            while i < nodes.len() {
                if i + 1 < nodes.len() && (nodes[i] ^ 1) == nodes[i + 1] {
                    next.push(nodes[i] >> 1);
                    i += 2;
                } else {
                    sibs += 1;
                    next.push(nodes[i] >> 1);
                    i += 1;
                }
            }
            nodes = next;
        }
        sibs
    }
    let mut fam = Vec::new();
    for a in 0..sl {
        for b in (a + 1)..sl {
            for c in (b + 1)..sl {
                if sibs_small(&[a, b, c], sh) <= sm { fam.push([a, b, c]); }
            }
        }
    }
    let sf = build_f(sh, sk, sm);
    assert_eq!(fam.len() as u128, sf[sh][sk].iter().sum::<u128>());
    let u3 = |t: usize| -> f64 {
        1.0 - (7495.0 / 5546.0) * 0.79f64.powi(t as i32) + (1949.0 / 5546.0) * 0.20f64.powi(t as i32)
    };
    let n = fam.len() as f64;
    let mut bf_r2 = 0.0f64;
    let zs = [(1u64, 1u64), (79, 100), (20, 100)];
    let cs = [(false, 1u128, 1u128), (true, 7495, 5546), (false, 1949, 5546)];
    let mut kr_acc = SAcc448::default();
    let nf = fam.len() as u128;
    for s_star in &fam {
        let mut cnt = [0u128; 8];
        for d in &fam {
            let mut m = 0usize;
            for i in 0..3 { if d.contains(&s_star[i]) { m |= 1 << i; } }
            cnt[m] += 1;
        }
        let mut e2 = 0.0f64;
        for m1 in 0..8 {
            for m2 in 0..8 {
                let p = (cnt[m1] as f64 / n) * (cnt[m2] as f64 / n);
                let mut prod = 1.0;
                for i in 0..3 { prod *= u3(((m1 >> i) & 1) + ((m2 >> i) & 1)); }
                e2 += p * prod;
            }
        }
        bf_r2 += e2 / n;
        let mut local = SAcc320::default();
        for j0 in 0..3 { for j1 in 0..3 { for j2 in 0..3 {
            let mut g = F256::ZERO;
            for m in 0..8 {
                let mut t = F256::from_ratio_fast_u128(cnt[m], nf);
                if m & 1 != 0 { t = t.mul_small_ratio(zs[j0].0, zs[j0].1); }
                if m & 2 != 0 { t = t.mul_small_ratio(zs[j1].0, zs[j1].1); }
                if m & 4 != 0 { t = t.mul_small_ratio(zs[j2].0, zs[j2].1); }
                g = g.add(t);
            }
            let g2 = g.mul_fast(g);
            let neg = cs[j0].0 ^ cs[j1].0 ^ cs[j2].0;
            let c16 = F256::from_ratio_exact_u128(cs[j0].1 * cs[j1].1 * cs[j2].1, cs[j0].2 * cs[j1].2 * cs[j2].2 * 16);
            local.add_f256(neg, c16.mul_fast(g2));
        }}}
        kr_acc.add_weighted(1, local);
    }
    let kr_r2 = kr_acc.to_f64_scaled(nf);
    assert!(((bf_r2 - kr_r2) / bf_r2).abs() < 1e-13);
    println!("[VERIFIED] Small-tree exhaustive check (H=4, K=3, m_max=6, |F|={}): brute-force r=2 == F256 Kronecker ({bf_r2:.12e}, rel={:.2e}).",
        fam.len(), ((bf_r2 - kr_r2) / bf_r2).abs());
}

/// Depth-1 sibling-pair symmetry table for fast exact tuple deduplication!
/// Given `pair_mask` (bit i set iff leaf i and leaf i+1 are adjacent depth-1 siblings, disjoint pairs),
/// precomputes the exact canonical subset of `(j_idx, mult)` over `1..19,683` (omitting `j=0` where
/// `1 - G(1) = 0`) with `sum(mult) == 19,682`.
fn build_sym_tables() -> Vec<Vec<(u16, u8)>> {
    // Disjoint pair positions in 0..8: mask of bits 0..8 (at most 256 masks, only valid disjoint ones needed).
    let mut tables = vec![Vec::new(); 256];
    let mut pow3 = [1usize; K];
    for i in 1..K { pow3[i] = pow3[i - 1] * 3; }
    // Axis order in Kronecker transform: axis `a` corresponds to bit `K - 1 - a` of `mask` (leaf `K - 1 - a`)!
    // In `cur` after 9 axes, index `j` has base-3 digit for leaf `leaf_idx` at position `leaf_idx`!
    // Check: axis 0 splits bit K-1 (leaf K-1) into 3 big blocks -> stride 3^8? Wait:
    // Let's verify exact digit position of leaf `b` in `cur[j]`:
    //   Start: index = sum_{b=0}^{K-1} bit_b * 2^b.
    //   axis=0 (stride = 2^{K-1} = bit K-1): output has 3 blocks of size 2^{K-1} -> trit of leaf K-1 is at MOST SIGNIFICANT trit (3^{K-1})!
    //   axis=1 (stride = 2^{K-2} = bit K-2): splits each block into 3 -> trit of leaf K-2 is at 3^{K-2}!
    //   ...
    //   axis=K-1 (stride = 1 = bit 0): splits into 3 -> trit of leaf 0 is at 3^0!
    //   So leaf `b`'s trit is ALWAYS `(j / 3^b) % 3`!!
    for pmask in 0..256usize {
        // Check disjointness (no adjacent 1-bits):
        if (pmask & (pmask >> 1)) != 0 { continue; }
        let mut pairs = Vec::new();
        for b in 0..8 {
            if (pmask >> b) & 1 != 0 { pairs.push(b); }
        }
        let mut entries = Vec::new();
        for j in 1..N3 {
            let mut keep = true;
            let mut mult = 1u8;
            for &b in &pairs {
                let t0 = (j / pow3[b]) % 3;
                let t1 = (j / pow3[b + 1]) % 3;
                if t0 > t1 {
                    keep = false;
                    break;
                } else if t0 < t1 {
                    mult <<= 1;
                }
            }
            if keep {
                entries.push((j as u16, mult));
            }
        }
        tables[pmask] = entries;
    }
    tables
}

#[inline]
fn sibling_pair_mask(leaves: &[u16; K]) -> usize {
    let mut mask = 0usize;
    let mut i = 0;
    while i + 1 < K {
        if (leaves[i] ^ 1) == leaves[i + 1] {
            mask |= 1 << i;
            i += 2;
        } else {
            i += 1;
        }
    }
    mask
}

/// Evaluate exact M_k (k=1..=K_POW) for one orbit's exact joint counts in F256 and add weighted to `global_acc`.
#[inline]
fn eval_orbit_into(
    jc: &[u128; N2],
    total_f: u128,
    weight: u128,
    sym_entries: &[(u16, u8)],
    c_neg: &[bool],
    c_mag16: &[F256],
    cur: &mut Vec<F256>,
    nxt: &mut Vec<F256>,
    global_acc: &mut [SAcc448; K_POW + 1],
) {
    for m in 0..N2 {
        cur[m] = F256::from_ratio_fast_u128(jc[m], total_f);
    }
    let mut len = N2;
    for axis in 0..K {
        let stride = 1usize << (K - 1 - axis);
        let blocks = len / (2 * stride);
        let out_len = blocks * 3 * stride;
        for b in 0..blocks {
            let ib = b * 2 * stride;
            let ob = b * 3 * stride;
            for o in 0..stride {
                let p0 = cur[ib + o];
                let p1 = cur[ib + stride + o];
                nxt[ob + o] = p0.add(p1);
                nxt[ob + stride + o] = p0.add(p1.mul_small_ratio(79, 100));
                nxt[ob + 2 * stride + o] = p0.add(p1.mul_small_ratio(20, 100));
            }
        }
        std::mem::swap(cur, nxt);
        len = out_len;
    }
    let mut local = [SAcc320::default(); K_POW + 1];
    for &(j_u16, mult) in sym_entries {
        let j = j_u16 as usize;
        let g = cur[j];
        // u = 1 - g (exact two's complement negate of 256-bit fractional g < 1):
        let mut u_limbs = [0u64; 4];
        let mut borrow = 0u64;
        for i in 0..4 {
            let (d1, o1) = 0u64.overflowing_sub(g.0[i]);
            let (d2, o2) = d1.overflowing_sub(borrow);
            u_limbs[i] = d2;
            borrow = (o1 as u64) + (o2 as u64);
        }
        let u = F256(u_limbs);
        let neg = c_neg[j];
        let m64 = mult as u64;
        let mut term = c_mag16[j].mul_fast(u);
        local[1].add_f256_mul(neg, term, m64);
        for k in 2..=K_POW {
            term = term.mul_fast(u);
            local[k].add_f256_mul(neg, term, m64);
        }
    }
    for k in 1..=K_POW {
        global_acc[k].add_weighted(weight, local[k]);
    }
}

// ============================================================================
// 4. Exact arbitrary-precision BigUint / BigInt rational interval certification
//    (ZERO floating-point reliance in the final binomial sum, rounding, or q_96!)
// ============================================================================
#[derive(Clone, Default, PartialEq, Eq)]
struct BigUint(Vec<u64>);

impl BigUint {
    fn trim(&mut self) { while self.0.last() == Some(&0) { self.0.pop(); } }
    fn zero() -> Self { Self(Vec::new()) }
    fn from_u64(x: u64) -> Self { if x == 0 { Self::zero() } else { Self(vec![x]) } }
    fn from_u128(x: u128) -> Self {
        let v = vec![x as u64, (x >> 64) as u64];
        let mut r = Self(v);
        r.trim();
        r
    }
    fn from_limbs(limbs: &[u64]) -> Self {
        let mut r = Self(limbs.to_vec());
        r.trim();
        r
    }
    fn is_zero(&self) -> bool { self.0.is_empty() }
    fn bit_len(&self) -> usize {
        if let Some(&top) = self.0.last() {
            (self.0.len() - 1) * 64 + (64 - top.leading_zeros() as usize)
        } else { 0 }
    }
    fn cmp_val(&self, o: &Self) -> std::cmp::Ordering {
        if self.0.len() != o.0.len() { return self.0.len().cmp(&o.0.len()); }
        for i in (0..self.0.len()).rev() {
            if self.0[i] != o.0[i] { return self.0[i].cmp(&o.0[i]); }
        }
        std::cmp::Ordering::Equal
    }
    fn add(&self, o: &Self) -> Self {
        let n = self.0.len().max(o.0.len());
        let mut out = Vec::with_capacity(n + 1);
        let mut c = 0u128;
        for i in 0..n {
            let s = (*self.0.get(i).unwrap_or(&0) as u128) + (*o.0.get(i).unwrap_or(&0) as u128) + c;
            out.push(s as u64);
            c = s >> 64;
        }
        if c != 0 { out.push(c as u64); }
        let mut r = Self(out);
        r.trim();
        r
    }
    fn sub(&self, o: &Self) -> Self {
        assert!(self.cmp_val(o) != std::cmp::Ordering::Less, "BigUint sub underflow");
        let mut out = Vec::with_capacity(self.0.len());
        let mut b = 0u64;
        for i in 0..self.0.len() {
            let (d1, o1) = self.0[i].overflowing_sub(*o.0.get(i).unwrap_or(&0));
            let (d2, o2) = d1.overflowing_sub(b);
            out.push(d2);
            b = (o1 as u64) + (o2 as u64);
        }
        assert_eq!(b, 0);
        let mut r = Self(out);
        r.trim();
        r
    }
    fn mul_u64(&self, m: u64) -> Self {
        if m == 0 || self.is_zero() { return Self::zero(); }
        let mut out = Vec::with_capacity(self.0.len() + 1);
        let mut c = 0u128;
        for &a in &self.0 {
            let p = (a as u128) * (m as u128) + c;
            out.push(p as u64);
            c = p >> 64;
        }
        if c != 0 { out.push(c as u64); }
        let mut r = Self(out);
        r.trim();
        r
    }
    fn mul(&self, o: &Self) -> Self {
        if self.is_zero() || o.is_zero() { return Self::zero(); }
        let mut out = vec![0u64; self.0.len() + o.0.len()];
        for (i, &a) in self.0.iter().enumerate() {
            let mut c = 0u128;
            for (j, &b) in o.0.iter().enumerate() {
                let p = (a as u128) * (b as u128) + (out[i + j] as u128) + c;
                out[i + j] = p as u64;
                c = p >> 64;
            }
            out[i + o.0.len()] = c as u64;
        }
        let mut r = Self(out);
        r.trim();
        r
    }
    fn div_exact_u64(&self, d: u64) -> Self {
        assert!(d > 0);
        let mut out = vec![0u64; self.0.len()];
        let mut rem = 0u128;
        for i in (0..self.0.len()).rev() {
            let cur = (rem << 64) | (self.0[i] as u128);
            out[i] = (cur / (d as u128)) as u64;
            rem = cur % (d as u128);
        }
        assert_eq!(rem, 0, "BigUint div_exact_u64 nonzero remainder");
        let mut r = Self(out);
        r.trim();
        r
    }
    fn shl_bits(&self, bits: usize) -> Self {
        if self.is_zero() || bits == 0 { return self.clone(); }
        let words = bits / 64;
        let rem = bits % 64;
        let mut out = vec![0u64; words + self.0.len() + 1];
        if rem == 0 {
            out[words..words + self.0.len()].copy_from_slice(&self.0);
        } else {
            let mut carry = 0u64;
            for (i, &a) in self.0.iter().enumerate() {
                out[words + i] = (a << rem) | carry;
                carry = a >> (64 - rem);
            }
            out[words + self.0.len()] = carry;
        }
        let mut r = Self(out);
        r.trim();
        r
    }
    fn pow_u64(base: u64, exp: u32) -> Self {
        let mut r = Self::from_u64(1);
        let mut b = Self::from_u64(base);
        let mut e = exp;
        while e > 0 {
            if e & 1 != 0 { r = r.mul(&b); }
            e >>= 1;
            if e > 0 { b = b.mul(&b); }
        }
        r
    }
}

#[derive(Clone)]
struct BigInt { neg: bool, mag: BigUint }

impl BigInt {
    fn zero() -> Self { Self { neg: false, mag: BigUint::zero() } }
    fn pos(mag: BigUint) -> Self { Self { neg: false, mag } }
    fn from_sacc448(a: SAcc448) -> Self {
        let neg = (a.0[6] as i64) < 0;
        let mag = if !neg {
            BigUint::from_limbs(&a.0)
        } else {
            let mut r = [0u64; 7];
            let mut c = 1u128;
            for i in 0..7 {
                let s = (!a.0[i]) as u128 + c;
                r[i] = s as u64;
                c = s >> 64;
            }
            BigUint::from_limbs(&r)
        };
        Self { neg: neg && !mag.is_zero(), mag }
    }
    fn negate(&self) -> Self { Self { neg: !self.neg && !self.mag.is_zero(), mag: self.mag.clone() } }
    fn add(&self, o: &Self) -> Self {
        if self.neg == o.neg {
            Self { neg: self.neg, mag: self.mag.add(&o.mag) }
        } else {
            match self.mag.cmp_val(&o.mag) {
                std::cmp::Ordering::Equal => Self::zero(),
                std::cmp::Ordering::Greater => Self { neg: self.neg, mag: self.mag.sub(&o.mag) },
                std::cmp::Ordering::Less => Self { neg: o.neg, mag: o.mag.sub(&self.mag) },
            }
        }
    }
    fn mul_uint(&self, m: &BigUint) -> Self {
        let mag = self.mag.mul(m);
        Self { neg: self.neg && !mag.is_zero(), mag }
    }
    fn shl_bits(&self, bits: usize) -> Self {
        Self { neg: self.neg, mag: self.mag.shl_bits(bits) }
    }
}

/// Exact rational upper bound `num / den` on `E_{R~Bin(q, 2^-h)}[prod u_3(T_i)]` (ZERO f64!).
/// - For Cap+Cap: `denom_c = C(2048, 9)`, `weight_scale = |F|`.
/// - For Unc+Unc: `denom_c = 1`,          `weight_scale = 1`.
fn eval_exact_rational_ub(
    accs: &[SAcc448; K_POW + 1],
    denom_c: u128,
    weight_scale: u128,
    h: usize,
    q: u128,
) -> (BigUint, BigUint) {
    if q == 0 {
        return (BigUint::zero(), BigUint::from_u64(1));
    }
    // Verify Leibniz alternating decrease condition for k >= K_POW + 1:
    //   (q - K_POW - 1) * 81 < (K_POW + 2) * 2048 * 2^h
    let lhs_leib = BigUint::from_u128(q).mul_u64(81);
    let rhs_leib = BigUint::from_u64(((K_POW + 2) * 2048) as u64).shl_bits(h);
    assert!(lhs_leib.cmp_val(&rhs_leib) == std::cmp::Ordering::Less, "Leibniz decrease condition violated");

    // Per-moment proved F256 error bound: 16 * 19683 * 1080 * 2^-256 = 340,122,240 * 2^-256
    let err_num = BigInt::pos(BigUint::from_u128(340_122_240u128).mul(&BigUint::from_u128(weight_scale)));
    let mut b_k = BigUint::from_u64(1);
    let mut total = BigInt::zero();
    let shift_base = 11 * (K_POW + 1); // 2048^(K_POW+1) = 2^(11*(K_POW+1))
    let k_lim = (K_POW as u128).min(q) as usize;
    for k in 1..=k_lim {
        b_k = b_k.mul(&BigUint::from_u128(q - (k - 1) as u128)).div_exact_u64(k as u64);
        let s_k = BigInt::from_sacc448(accs[k]);
        let signed_16s = if k % 2 == 1 { s_k.negate() } else { s_k }.shl_bits(4);
        let term = signed_16s.add(&err_num).mul_uint(&b_k).shl_bits((K_POW + 1 - k) * h + shift_base);
        total = total.add(&term);
    }
    // Alternating-series remainder at k = K_POW + 1 = 45 (zero when q <= K_POW):
    //   <= 7700 * weight_scale * C(q, 45) * 81^45 * 2^256 / (denom_c * 2^(256 + 45*h + 495))
    if q > K_POW as u128 {
        let b_rem = b_k.mul(&BigUint::from_u128(q - K_POW as u128)).div_exact_u64((K_POW + 1) as u64);
        let rem = BigUint::from_u64(7700)
            .mul(&BigUint::from_u128(weight_scale))
            .mul(&b_rem)
            .mul(&BigUint::pow_u64(81, (K_POW + 1) as u32))
            .shl_bits(256);
        total = total.add(&BigInt::pos(rem));
    }
    assert!(!total.neg && !total.mag.is_zero(), "exact rational UB non-positive");
    let den = BigUint::from_u128(denom_c).shl_bits(256 + (K_POW + 1) * h + shift_base);
    (total.mag, den)
}

/// Outward-rounded decimal upper bound `d.dddd e-EE` proved in exact BigUint arithmetic!
fn format_decimal_ub(num: &BigUint, den: &BigUint) -> String {
    // Find smallest integer e >= 0 with num * 10^e >= den:
    let mut e = 0u32;
    let mut p10 = BigUint::from_u64(1);
    while num.mul(&p10).cmp_val(den) == std::cmp::Ordering::Less {
        e += 1;
        p10 = p10.mul_u64(10);
    }
    // Scale by 10^4 so m = ceil(num * 10^(e+4) / den) in [10000, 100000]:
    let scaled = num.mul(&p10.mul_u64(10_000));
    let mut lo = 10_000u64;
    let mut hi = 100_000u64;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if den.mul_u64(mid).cmp_val(&scaled) != std::cmp::Ordering::Less { hi = mid; } else { lo = mid + 1; }
    }
    assert!(den.mul_u64(lo).cmp_val(&scaled) != std::cmp::Ordering::Less);
    if lo == 100_000 { lo = 10_000; e -= 1; }
    format!("{}.{:04}e-{:02}", lo / 10_000, lo % 10_000, e)
}

/// Exact rational Taylor lower bound on `2^(-r/10000) = e^{-(r/10000)*ln 2}` (`0 <= r < 10000`):
/// Uses `L_hi = 69314718055994530942 / 10^20 > ln 2` and odd-truncated `T_19(x) < e^{-x} < 2^{-r/10000}`.
/// Returns `(N, D)` with `0 < N / D < 2^(-r/10000)`!
fn exact_pow2_neg_frac_lb(r: u32) -> (BigUint, BigUint) {
    if r == 0 { return (BigUint::from_u64(1), BigUint::from_u64(1)); }
    // x = (r * L_hi) / 10^24, with 0 < x < 0.7
    const L_HI: u128 = 69_314_718_055_994_530_942; // ceil(ln(2) * 10^20)
    let x_num = BigUint::from_u128((r as u128) * L_HI);
    let x_den = BigUint::pow_u64(10, 24);
    const DEG: usize = 19; // Odd truncation => T_19(x) < e^{-x} strictly for all x in (0, 1)
    let mut fact = vec![BigUint::zero(); DEG + 1];
    fact[0] = BigUint::from_u64(1);
    for j in 1..=DEG { fact[j] = fact[j - 1].mul_u64(j as u64); }
    let mut x_num_pow = vec![BigUint::from_u64(1); DEG + 1];
    let mut x_den_pow = vec![BigUint::from_u64(1); DEG + 1];
    for j in 1..=DEG {
        x_num_pow[j] = x_num_pow[j - 1].mul(&x_num);
        x_den_pow[j] = x_den_pow[j - 1].mul(&x_den);
    }
    let common_den = fact[DEG].mul(&x_den_pow[DEG]);
    let mut sum = BigInt::zero();
    for j in 0..=DEG {
        // fact[DEG] / fact[j] exact:
        let mut ratio = BigUint::from_u64(1);
        for m in (j + 1)..=DEG { ratio = ratio.mul_u64(m as u64); }
        let term = x_num_pow[j].mul(&x_den_pow[DEG - j]).mul(&ratio);
        let st = if j % 2 == 1 { BigInt { neg: true, mag: term } } else { BigInt::pos(term) };
        sum = sum.add(&st);
    }
    assert!(!sum.neg && !sum.mag.is_zero());
    (sum.mag, common_den)
}

/// Proves `num / den <= 2^(-(b_10000 / 10000))` in exact BigUint arithmetic!
fn check_bits_lb(num: &BigUint, den: &BigUint, b_10000: u32) -> bool {
    let n = (b_10000 / 10_000) as usize;
    let r = b_10000 % 10_000;
    let (t_num, t_den) = exact_pow2_neg_frac_lb(r);
    // Check num * 2^n * t_den <= den * t_num
    num.shl_bits(n).mul(&t_den).cmp_val(&den.mul(&t_num)) != std::cmp::Ordering::Greater
}

/// Finds the largest 4-decimal bit lower bound `b = b_10000 / 10000` certified in exact BigUint arithmetic!
fn certify_bits_lb(num: &BigUint, den: &BigUint) -> u32 {
    let approx_n = den.bit_len().saturating_sub(num.bit_len()) as u32;
    let mut lo = approx_n.saturating_sub(2) * 10_000;
    let mut hi = (approx_n + 2) * 10_000;
    assert!(check_bits_lb(num, den, lo), "lower search bracket failed");
    assert!(!check_bits_lb(num, den, hi), "upper search bracket failed");
    while lo + 1 < hi {
        let mid = lo + (hi - lo) / 2;
        if check_bits_lb(num, den, mid) { lo = mid; } else { hi = mid; }
    }
    assert!(check_bits_lb(num, den, lo));
    lo
}

/// Independent closed-form trinomial check for uncapped r=2 (both u_3 envelope and exact q_C)!
fn independent_uncapped_r2(p1: f64, p2: f64, total_all: u128) -> f64 {
    let mut fact = [1u128; K + 1];
    for i in 1..=K { fact[i] = fact[i - 1] * (i as u128); }
    let mut sum = 0.0f64;
    for l in 0..=K {
        for r in 0..=(K - l) {
            let b = K - l - r;
            let trinom = (fact[K] / (fact[l] * fact[r] * fact[b])) as f64;
            let ways = (comb_u128(L - K, r) as f64) * (comb_u128(L - K, l) as f64);
            sum += trinom * ways * p1.powi((l + r) as i32) * p2.powi(b as i32);
        }
    }
    let den = total_all as f64;
    sum / (den * den)
}

/// Rigorous 8-state Markov fixed-point certification (scale 2^96, zero floating-point reliance)
/// proving the exact discrete 99th percentile of sum_{i=1}^6 Geom(p_wots) + Geom(alpha * p_cap)
/// is `t = 75,533`: `CDF(75,532) < 0.99 <= CDF(75,533)`.
fn verify_discrete_grind_p99(total_f: u128, total_all: u128) {
    // 1. Exact BigUint proof that 1 - alpha < 2^-72 for 18 draws of 9 distinct leaves in [0..2048):
    let mut dp = vec![BigUint::zero(); K + 1];
    dp[0] = BigUint::from_u64(1);
    for _ in 0..18 {
        let mut ndp = vec![BigUint::zero(); K + 1];
        for c in 0..K {
            ndp[c] = ndp[c].add(&dp[c].mul_u64(c as u64));
            ndp[c + 1] = ndp[c + 1].add(&dp[c].mul_u64((L - c) as u64));
        }
        ndp[K] = ndp[K].add(&dp[K].mul_u64(L as u64));
        dp = ndp;
    }
    let denom_alpha = BigUint::from_u64(1).shl_bits(18 * H); // 2048^18 = 2^198
    let fail_alpha = denom_alpha.sub(&dp[K]);
    assert!(fail_alpha.shl_bits(72).cmp_val(&denom_alpha) == std::cmp::Ordering::Less);

    // 2. Exact u128 scale-2^96 brackets [p_lo, p_hi] for p_wots and [a_lo, a_hi] for alpha * p_cap:
    const WOTS_N_VALID: u128 = 83_261_328_062_314_682_436_358_950_675_433_803;
    let p_lo = WOTS_N_VALID >> 32; // exact floor(p_wots * 2^96)
    let p_hi = p_lo + 1;
    // floor(|F| * 2^96 / C(2048, 9)) via binary search in BigUint (a < 2^-13 => fits in u128 < 2^83):
    let target = BigUint::from_u128(total_f).shl_bits(96);
    let den_all = BigUint::from_u128(total_all);
    let mut lo = 0u128;
    let mut hi = 1u128 << 84;
    while lo + 1 < hi {
        let mid = lo + (hi - lo) / 2;
        if den_all.mul(&BigUint::from_u128(mid)).cmp_val(&target) != std::cmp::Ordering::Greater { lo = mid; } else { hi = mid; }
    }
    let a_lo = lo - (lo >> 71) - 1; // strictly <= alpha * p_cap * 2^96 since 1 - alpha < 2^-72
    let a_hi = lo + 1;              // strictly >= alpha * p_cap * 2^96

    // Multiply two scale-2^96 u128 values (< 2^96) and return floor((x * y) / 2^96):
    fn mul_q96_floor(x: u128, y: u128) -> u128 {
        // Split into 48-bit limbs: x = x1*2^48 + x0, y = y1*2^48 + y0
        let x0 = x & ((1u128 << 48) - 1);
        let x1 = x >> 48;
        let y0 = y & ((1u128 << 48) - 1);
        let y1 = y >> 48;
        let p00 = x0 * y0;
        let mid = x0 * y1 + x1 * y0 + (p00 >> 48);
        x1 * y1 + (mid >> 48)
    }

    const ONE: u128 = 1u128 << 96;
    let mut s_lo = [0u128; 8]; s_lo[0] = ONE;
    let mut s_hi = [0u128; 8]; s_hi[0] = ONE;
    let mut cdf_hi_75532 = 0u128;
    let mut cdf_lo_75533 = 0u128;

    for t in 1..=75_533u128 {
        // Lower bound chain: floor every advance and ceil-sub every stay so total mass can only drop
        // and each state's upward transition rate is <= exact rate => s_lo[7] / 2^96 <= true CDF(t)!
        let mut n_lo = [0u128; 8];
        n_lo[7] = s_lo[7];
        for i in 0..7 {
            let r = if i < 6 { p_lo } else { a_lo };
            let adv = mul_q96_floor(s_lo[i], r);
            let stay = s_lo[i].saturating_sub(adv + 1); // <= s_lo[i] * (1 - r / 2^96)
            n_lo[i] += stay;
            n_lo[i + 1] += adv;
        }
        s_lo = n_lo;

        // Upper bound chain: ceil every advance (adv+1) and floor-sub every stay with (p_hi, a_hi),
        // strictly dominating true CDF(t): s_hi[7] / 2^96 >= true CDF(t)!
        let mut n_hi = [0u128; 8];
        n_hi[7] = s_hi[7];
        for i in 0..7 {
            let r = if i < 6 { p_hi } else { a_hi };
            let adv = mul_q96_floor(s_hi[i], r) + 1;
            let stay = s_hi[i].saturating_sub(adv.saturating_sub(1));
            n_hi[i] += stay;
            n_hi[i + 1] += adv;
        }
        s_hi = n_hi;

        if t == 75_532 { cdf_hi_75532 = s_hi[7]; }
        if t == 75_533 { cdf_lo_75533 = s_lo[7]; }
    }
    // Exact integer comparison against 99 / 100 (multiply by 100 in BigUint to avoid u128 overflow):
    let thr99 = BigUint::from_u64(99).shl_bits(96);
    assert!(BigUint::from_u128(cdf_hi_75532).mul_u64(100).cmp_val(&thr99) == std::cmp::Ordering::Less,
        "discrete p99 upper bound at 75532 >= 0.99!");
    assert!(BigUint::from_u128(cdf_lo_75533).mul_u64(100).cmp_val(&thr99) != std::cmp::Ordering::Less,
        "discrete p99 lower bound at 75533 < 0.99!");
    println!("[CERTIFIED] Exact discrete grinding p99 = 75,533 proved in scale-2^96 integer Markov arithmetic: exact integer assertions verify CDF(75532) < 99/100 <= CDF(75533) (brackets approx {:.8} / {:.8}).",
        (cdf_hi_75532 as f64) / (ONE as f64), (cdf_lo_75533 as f64) / (ONE as f64));
}

/// Exact archived 448-bit signed global accumulators `S_1 .. S_44` from the exhaustive
/// all-1,614,132-orbits evaluation (populated after full run; verified bit-for-bit on full runs
/// and certified in exact BigInt rational interval arithmetic on `--fast` CI runs).
const HAS_ARCHIVED_S: bool = true;
const ARCHIVED_CAP_S: [[u64; 7]; K_POW + 1] = [
    /* k= 0 */ [0, 0, 0, 0, 0, 0, 0],
    /* k= 1 */ [0xf33c9eed4020b800, 0xa90deb08425411b1, 0xffff7f39cab5451e, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k= 2 */ [0x2826e71aef36f800, 0x03a463ae880cfba1, 0x26bfdab8c7dfb110, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k= 3 */ [0xaf2fc582ea4d8800, 0xd9d3525345d9bab5, 0x85aa6ef99d481def, 0xffffffffffffffe1, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k= 4 */ [0x675278061f01e000, 0xc1e6e8558117dc5f, 0xc8a50a450a22f856, 0x0000000000000458, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k= 5 */ [0x4b17a3f60370a000, 0x6aab0da35877bb26, 0xa846926bae09a996, 0xffffffffffffc49f, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k= 6 */ [0xdd0d43058a3fb800, 0x856833b040be1be0, 0xbdae14211f15354f, 0x0000000000019b24, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k= 7 */ [0x7f86c8bd4064f800, 0xf98fed695bec52a1, 0x2b210fad04849672, 0xfffffffffff96931, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k= 8 */ [0xfc6a29bd30f68800, 0x06e2efee7bd8f14c, 0x47199e3890605e7b, 0x0000000000118205, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k= 9 */ [0xc88cb95a1c0dc000, 0x89e3b83fc37c963c, 0x91c902017041fec2, 0xffffffffffe03e29, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k=10 */ [0x31c009c359086800, 0x1e7370b297b521e6, 0x0716231256bd60ec, 0x0000000000288296, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=11 */ [0x8c029ae9afde7800, 0xd9a4cc91de66a5e4, 0x79686453e0000dc9, 0xffffffffffdb30fd, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k=12 */ [0xce3bf3bad7741800, 0x980fe78e08273a15, 0x98a423c4ab998f7c, 0x000000000017c309, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=13 */ [0xd9d073be901c4800, 0x1288ddbd205973fc, 0xbb5bf90f00bec6b2, 0xfffffffffff55351, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k=14 */ [0x47b06f979bb48800, 0xdb8db393c49ad9a2, 0x01246b15dfc49af5, 0x0000000000032c5b, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=15 */ [0x3155cf44e5a2b800, 0xa35c5906e7c94681, 0x48e2cb779e48fd42, 0xffffffffffff7278, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k=16 */ [0xb3db46d02343d000, 0x92843d49f805bad7, 0x2575c38e51aeab67, 0x0000000000000915, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=17 */ [0xde0936311f44b000, 0xecb7be3602810ef5, 0x3675c9225db7c225, 0x00000000000000e2, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=18 */ [0x84717add60d0c800, 0x9941c426a04af78f, 0xf6e16017933bdf99, 0xffffffffffffffea, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k=19 */ [0x8e6f2e5cc1588800, 0xff22ff53b6803115, 0x00f2007f97ea62e0, 0xfffffffffffffffd, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k=20 */ [0x4f8bd3b23f5a4000, 0xe654bc03aa78739c, 0xf25d94534f729ba3, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
    /* k=21 */ [0x9ab439ffa7aa2800, 0x918683f27753d676, 0x05156339d17fddb8, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=22 */ [0xbe6363421406d000, 0x85de739f25aed457, 0x00c2c6421de5368f, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=23 */ [0xe783af8ecdb6a800, 0xeb25c00bcfa2bdb7, 0x0011a3d65f84406e, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=24 */ [0xca144de5cc60f800, 0xe9505a2ce32df215, 0x0001418699024d05, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=25 */ [0x49ef625076c52000, 0x05db947d31bc91ce, 0x000013a2408bb369, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=26 */ [0xc267e5a17af72800, 0xa1d743109636a7ec, 0x00000112ed7e0fc7, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=27 */ [0xce251189d1c87800, 0x76732d69b21bb7cc, 0x0000000dd3891129, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=28 */ [0xb53ef1fe6fa64000, 0x53ff6a7c09009b09, 0x00000000a687b2bf, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=29 */ [0x88fe29ece8121800, 0x5665d60f35ec5385, 0x00000000076bccff, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=30 */ [0xb041182384b43000, 0x9ac326ee3142070e, 0x000000000050ee48, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=31 */ [0x667b097913ee2800, 0x63dd34eaab1abeb0, 0x00000000000351b6, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=32 */ [0x12d4692f7d9a8000, 0x4ab8f1cb63fa0936, 0x00000000000021bd, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=33 */ [0xef0b5c0937cac800, 0x8b3beebcf7ef0e6d, 0x000000000000014d, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=34 */ [0x4965b62377759800, 0x92bbd6ee939613e4, 0x000000000000000c, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=35 */ [0xce467a1b3f3a5800, 0x76cd915b48194d0c, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=36 */ [0xf1b957145e521800, 0x044dfe42057835d1, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=37 */ [0xa1e7d84c35008800, 0x002748836a3b99b0, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=38 */ [0x5ea5d40afdab0800, 0x000161590c1f1bc4, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=39 */ [0xca1b17400e426800, 0x00000c41c32d10bc, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=40 */ [0xc6378ef7d13d8800, 0x0000006b9a45cc4a, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=41 */ [0x722415fbee678000, 0x00000003a701f541, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=42 */ [0xeed5931d0d7d9000, 0x000000001f7267e8, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=43 */ [0x336403643688f000, 0x00000000010c7ef8, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    /* k=44 */ [0x5d0034990df02800, 0x000000000008e540, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
];

fn main() {
    let fast_mode = std::env::args().any(|a| a == "--fast");
    let t_start = Instant::now();
    let ((qc1_n, qc1_d), (qc2_n, qc2_d)) = verify_u3_envelope_all_t();
    verify_small_tree_ground_truth();

    let f = build_f(H, K, M_MAX);
    let total_f: u128 = f[H][K].iter().sum();
    let total_all = comb_u128(L, K);
    let p_cap = (total_f as f64) / (total_all as f64);
    println!("|F|        = {total_f}");
    println!("C(2048, 9) = {total_all}");
    println!("p_cap      = {p_cap:.10e} (1/p_cap = {:.3}, -log2 = {:.4} b)", 1.0 / p_cap, -p_cap.log2());

    // Precompute bit-exact c_neg and c_mag16 = |c_j|/16 in F256
    let c_num: [(bool, u128, u128); 3] = [(false, 1, 1), (true, 7495, 5546), (false, 1949, 5546)];
    let mut c_neg = vec![false; N3];
    let mut c_mag16 = vec![F256::ZERO; N3];
    for idx in 0..N3 {
        let mut t = idx;
        let mut neg = false;
        let mut num = 1u128;
        let mut den = 1u128;
        for _ in 0..K {
            let (cn, n, d) = c_num[t % 3];
            neg ^= cn;
            num *= n;
            den *= d;
            t /= 3;
        }
        c_neg[idx] = neg;
        c_mag16[idx] = F256::from_ratio_exact_u128(num, den * 16);
    }
    let sym_tables = build_sym_tables();

    // 1. Deterministic uncapped envelope upper bound (Unc+Unc, zero MC!)
    let mut uncap_jc = [0u128; N2];
    for mask in 0..N2 {
        let a = mask.count_ones() as usize;
        uncap_jc[mask] = comb_u128(L - K, K - a);
    }
    let mut uncap_acc = [SAcc448::default(); K_POW + 1];
    let mut cur0 = vec![F256::ZERO; N3];
    let mut nxt0 = vec![F256::ZERO; N3];
    eval_orbit_into(&uncap_jc, total_all, 1, &sym_tables[0], &c_neg, &c_mag16, &mut cur0, &mut nxt0, &mut uncap_acc);
    let mut m_uncap = [0.0f64; K_POW + 1];
    for k in 1..=K_POW { m_uncap[k] = uncap_acc[k].to_f64_scaled(1); }
    let exact_r1 = 376.0f64.powi(-(K as i32)) / (total_all as f64);
    assert!(((-m_uncap[1] - exact_r1) / exact_r1).abs() < 1e-13, "uncapped r=1: {:.12e} vs {:.12e}", -m_uncap[1], exact_r1);
    let s1_bi = BigInt::from_sacc448(uncap_acc[1]);
    let s2_bi = BigInt::from_sacc448(uncap_acc[2]);
    let r2_bi = s1_bi.negate().shl_bits(1).add(&s2_bi);
    assert!(!r2_bi.neg);
    // Exact check against closed-form trinomial sum (zero cancellation in r2_bi!):
    let mut r2_f64 = 0.0f64;
    for &limb in r2_bi.mag.0.iter().rev() { r2_f64 = r2_f64 * 18446744073709551616.0 + (limb as f64); }
    let uncap_r2 = r2_f64 * 16.0 * 2.0f64.powi(-256);
    let u3_1 = 1.0 / 376.0;
    let u3_2 = (55_460_000i64 - 7495 * 6241 + 1949 * 400) as f64 / 55_460_000.0;
    let indep_u3_r2 = independent_uncapped_r2(u3_1, u3_2, total_all);
    let indep_qc_r2 = independent_uncapped_r2(qc1_n as f64 / qc1_d as f64, qc2_n as f64 / qc2_d as f64, total_all);
    assert!(((uncap_r2 - indep_u3_r2) / indep_u3_r2).abs() < 1e-13, "uncapped r=2 mismatch: {uncap_r2:.12e} vs {indep_u3_r2:.12e}");
    println!("[VERIFIED] Independent uncapped r=1 & r=2 checks: r=1 ({:.4} b == exact {:.4} b), r=2 u_3 ({:.4} b == trinomial {:.4} b, rel={:.2e}; exact q_C = {:.4} b).",
        -(-m_uncap[1]).log2(), -exact_r1.log2(), -uncap_r2.log2(), -indep_u3_r2.log2(),
        ((uncap_r2 - indep_u3_r2) / indep_u3_r2).abs(), -indep_qc_r2.log2());

    // 2. Pairwise clustering ratios vs (9/2048)^2 by LCA height d = 1..=11
    let p_marg = (K as f64) / (L as f64);
    let base_pair = p_marg * p_marg;
    print!("Pairwise clustering vs (9/2048)^2 (d=1..11):");
    for d in 1..=H {
        let u = 0u16;
        let v = 1u16 << (d - 1);
        let mut tgt: [u16; K] = std::array::from_fn(|i| if i == 0 { u } else if i == 1 { v } else { (L - 1 - i) as u16 });
        tgt.sort_unstable();
        let root = solve_sub_dp(&f, H, 0, L, &tgt);
        let iu = tgt.iter().position(|&x| x == u).unwrap();
        let iv = tgt.iter().position(|&x| x == v).unwrap();
        let need = (1usize << iu) | (1usize << iv);
        let mut both = 0u128;
        for m in 0..N2 {
            if (m & need) == need {
                let base = m * STRIDE + K * (M_MAX + 1);
                both += root[base..=base + M_MAX].iter().sum::<u128>();
            }
        }
        print!(" d{d}={:.2}x", (both as f64 / total_f as f64) / base_pair);
    }
    println!();

    // 3. Enumerate ALL sub-orbits at height H-1 = 10, precompute dpl for k=1..=4 (341 sub-orbits)
    let t_enum = Instant::now();
    let sub10 = enum_height_h_minus_1();
    let mut dpl_cache: Vec<Vec<Vec<u128>>> = vec![vec![]; 5];
    for kl in 1..=4 {
        dpl_cache[kl] = sub10[kl].iter().map(|o| solve_sub_dp(&f, H - 1, 0, L / 2, &o.leaves)).collect();
    }
    let mut tasks: Vec<(usize, usize)> = Vec::new();
    for kr in 5..=K {
        for idx in 0..sub10[kr].len() { tasks.push((kr, idx)); }
    }
    println!("Precomputed {} small dpl tables (k<=4) and {} right-subtree tasks in {:.3}s.",
        (1..=4).map(|k| sub10[k].len()).sum::<usize>(), tasks.len(), t_enum.elapsed().as_secs_f64());

    // Self-check fast prefix-sum root merges AND sibling-pair symmetry dedup!
    for kr in 5..=K {
        let b = &sub10[kr][0];
        let dpr = solve_sub_dp(&f, H - 1, 0, L / 2, &b.leaves);
        let pref_r = make_prefix_r(&dpr);
        let mut full_leaves = [0u16; K];
        let fast = if kr == K {
            for i in 0..K { full_leaves[i] = b.leaves[i] + (L / 2) as u16; }
            merge_root_single(&f[H - 1], &pref_r, 1 << K)
        } else {
            let kl = K - kr;
            let a = &sub10[kl][0];
            for i in 0..kl { full_leaves[i] = a.leaves[i]; }
            for i in 0..kr { full_leaves[kl + i] = b.leaves[i] + (L / 2) as u16; }
            merge_root_prefix(&dpl_cache[kl][0], 1 << kl, kl, &pref_r, 1 << kr)
        };
        let root = solve_sub_dp(&f, H, 0, L, &full_leaves);
        for m in 0..N2 {
            let base = m * STRIDE + K * (M_MAX + 1);
            assert_eq!(fast[m], root[base..=base + M_MAX].iter().sum::<u128>());
        }
        let pmask = sibling_pair_mask(&full_leaves);
        if pmask != 0 {
            let mut a0 = [SAcc448::default(); K_POW + 1];
            let mut a1 = [SAcc448::default(); K_POW + 1];
            eval_orbit_into(&fast, total_f, 1, &sym_tables[0], &c_neg, &c_mag16, &mut cur0, &mut nxt0, &mut a0);
            eval_orbit_into(&fast, total_f, 1, &sym_tables[pmask], &c_neg, &c_mag16, &mut cur0, &mut nxt0, &mut a1);
            for k in 1..=4 {
                let d_int = BigInt::from_sacc448(a0[k]).add(&BigInt::from_sacc448(a1[k]).negate());
                // Difference between unreduced and reduced sums is bounded by 2 * (340_122_240 / 16) = 42_515_280!
                assert!(d_int.mag.cmp_val(&BigUint::from_u64(42_515_280)) != std::cmp::Ordering::Greater,
                    "sym dedup integer error bound exceeded at k={k}");
            }
        }
    }
    println!("[VERIFIED] Fast prefix-sum root merges (kr=5..=9) & depth-1 sibling-pair symmetry dedup (within proved integer F256 error bound).");

    // 4. Exhaustive parallel evaluation across ALL 1,614,132 orbits (or load archived exact sums in --fast mode)
    let mut global_acc = [SAcc448::default(); K_POW + 1];
    if fast_mode {
        assert!(HAS_ARCHIVED_S, "--fast mode requires archived exact S_1..S_44 sums");
        for k in 1..=K_POW { global_acc[k] = SAcc448(ARCHIVED_CAP_S[k]); }
        println!("[FAST MODE] Loaded exact archived 448-bit S_1..S_44 accumulators from full all-1,614,132-orbits run.");
    } else {
        let n_threads = thread::available_parallelism().map(|n| n.get()).unwrap_or(8);
        let next_task = AtomicUsize::new(0);
        let total_orbits_done = AtomicUsize::new(0);
        let f_ref = &f;
        let sub10_ref = &sub10;
        let dpl_ref = &dpl_cache;
        let tasks_ref = &tasks;
        let sym_ref = &sym_tables;
        let c_neg_ref = &c_neg;
        let c_mag_ref = &c_mag16;

        let t_eval = Instant::now();
        let thread_results: Vec<([SAcc448; K_POW + 1], u128)> = thread::scope(|scope| {
            let mut handles = Vec::with_capacity(n_threads);
            for _ in 0..n_threads {
                handles.push(scope.spawn(|| {
                    let mut acc = [SAcc448::default(); K_POW + 1];
                    let mut cur = vec![F256::ZERO; N3];
                    let mut nxt = vec![F256::ZERO; N3];
                    let mut w_sum = 0u128;
                    let mut full_leaves = [0u16; K];
                    loop {
                        let start = next_task.fetch_add(64, Ordering::Relaxed);
                        if start >= tasks_ref.len() { break; }
                        let end = (start + 64).min(tasks_ref.len());
                        let mut chunk_orbs = 0usize;
                        for &(kr, idx_b) in &tasks_ref[start..end] {
                            let b = &sub10_ref[kr][idx_b];
                            if kr == K {
                                if (b.s as usize) + 1 > M_MAX { continue; }
                                let dpr = solve_sub_dp(f_ref, H - 1, 0, L / 2, &b.leaves);
                                let pref_r = make_prefix_r(&dpr);
                                let jc = merge_root_single(&f_ref[H - 1], &pref_r, 1 << K);
                                for i in 0..K { full_leaves[i] = b.leaves[i] + (L / 2) as u16; }
                                let pmask = sibling_pair_mask(&full_leaves);
                                let w = b.size * 2;
                                eval_orbit_into(&jc, total_f, w, &sym_ref[pmask], c_neg_ref, c_mag_ref, &mut cur, &mut nxt, &mut acc);
                                w_sum += w;
                                chunk_orbs += 1;
                            } else {
                                let kl = K - kr;
                                let mut has_any = false;
                                for a in &sub10_ref[kl] {
                                    if (a.s as usize) + (b.s as usize) <= M_MAX { has_any = true; break; }
                                }
                                if !has_any { continue; }
                                let dpr = solve_sub_dp(f_ref, H - 1, 0, L / 2, &b.leaves);
                                let pref_r = make_prefix_r(&dpr);
                                let nl = 1usize << kl;
                                let nr = 1usize << kr;
                                for i in 0..kr { full_leaves[kl + i] = b.leaves[i] + (L / 2) as u16; }
                                for (idx_a, a) in sub10_ref[kl].iter().enumerate() {
                                    if (a.s as usize) + (b.s as usize) > M_MAX { continue; }
                                    for i in 0..kl { full_leaves[i] = a.leaves[i]; }
                                    let pmask = sibling_pair_mask(&full_leaves);
                                    let jc = merge_root_prefix(&dpl_ref[kl][idx_a], nl, kl, &pref_r, nr);
                                    let w = 2 * a.size * b.size;
                                    eval_orbit_into(&jc, total_f, w, &sym_ref[pmask], c_neg_ref, c_mag_ref, &mut cur, &mut nxt, &mut acc);
                                    w_sum += w;
                                    chunk_orbs += 1;
                                }
                            }
                        }
                        let done = total_orbits_done.fetch_add(chunk_orbs, Ordering::Relaxed) + chunk_orbs;
                        if done / 200_000 != (done - chunk_orbs) / 200_000 {
                            eprintln!("  progress: {:7} / 1614132 orbits ({:.1}s)", done, t_eval.elapsed().as_secs_f64());
                        }
                    }
                    (acc, w_sum)
                }));
            }
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });

        let mut sum_weights = 0u128;
        for (acc, w) in thread_results {
            for k in 1..=K_POW { global_acc[k].add_assign(&acc[k]); }
            sum_weights += w;
        }
        let total_orbits = total_orbits_done.load(Ordering::Relaxed);
        assert_eq!(total_orbits, 1_614_132, "orbit count mismatch!");
        assert_eq!(sum_weights, total_f, "orbit weight sum != |F|!");
        println!("\n[CERTIFIED] Evaluated ALL {total_orbits} Aut(T_11)-orbits (sum = {sum_weights} == |F|) in {:.2}s on {n_threads} threads!",
            t_eval.elapsed().as_secs_f64());
        if HAS_ARCHIVED_S {
            for k in 1..=K_POW {
                assert_eq!(global_acc[k].0, ARCHIVED_CAP_S[k], "recomputed S_{k} differs from archived constant!");
            }
            println!("[VERIFIED] All 44 recomputed 448-bit S_k accumulators match ARCHIVED_CAP_S bit-for-bit!");
        }
        println!("--- EXACT 448-BIT SIGNED ACCUMULATORS S_1..S_44 (CAP+CAP) ---");
        for k in 1..=K_POW {
            let a = global_acc[k].0;
            println!("    /* k={:2} */ [0x{:016x}, 0x{:016x}, 0x{:016x}, 0x{:016x}, 0x{:016x}, 0x{:016x}, 0x{:016x}],",
                k, a[0], a[1], a[2], a[3], a[4], a[5], a[6]);
        }
        println!("--- END EXACT ACCUMULATORS ---");
    }

    let mut m_cap = [0.0f64; K_POW + 1];
    for k in 1..=K_POW { m_cap[k] = global_acc[k].to_f64_scaled(total_f); }
    let cap_r1 = -p_cap * m_cap[1];
    assert!(((cap_r1 - exact_r1) / exact_r1).abs() < 1e-13, "capped r=1 mismatch: {cap_r1:.12e} vs {exact_r1:.12e}");
    let cap_r2 = p_cap * (2.0 * (-m_cap[1]) + m_cap[2]);
    println!("[VERIFIED] All-1,614,132-orbits checks: r=1 ({:.6} b == exact {:.6} b), r=2 ({:.4} b).",
        -cap_r1.log2(), -exact_r1.log2(), -cap_r2.log2());

    println!("\n=== EXACT RATIONAL INTERVAL ALL-ORBITS 3-TERM ENVELOPE UPPER BOUND (ZERO MC, ZERO f64) ===");
    println!("  (h, q)                | Cap+Cap Certified LB / UB         | Unc+Unc Certified LB / UB");
    for &(h_bits, q_exact, label, exp_cb, exp_cs, exp_ub, exp_us) in &[
        (48usize, 1u128 << 46, "h=48, q=2^46 (0.25x)", 141_7220u32, "2.1748e-43", 138_8182u32, "1.6276e-42"),
        (48,      1u128 << 47, "h=48, q=2^47 (0.50x)", 137_1012,    "5.3506e-42", 133_8571,    "5.0697e-41"),
        (48,      1u128 << 48, "h=48, q=2^48 (1.00x)", 131_7076,    "2.2493e-40", 127_9743,    "2.9914e-39"),
        (48,      1u128 << 49, "h=48, q=2^49 (2.00x)", 125_3590,    "1.8330e-38", 120_9424,    "3.9148e-37"),
        (48,      1u128 << 50, "h=48, q=2^50 (4.00x)", 117_8522,    "3.3338e-36", 112_5196,    "1.3434e-34"),
        (48,      1u128 << 51, "h=48, q=2^51 (8.00x)", 108_9894,    "1.5521e-33", 102_4964,    "1.3980e-31"),
        (64,      1u128 << 64, "h=64, q=2^64 (1.00x)", 131_7076,    "2.2493e-40", 127_9743,    "2.9914e-39"),
    ] {
        let (cn, cd) = eval_exact_rational_ub(&global_acc, total_all, total_f, h_bits, q_exact);
        let (un, ud) = eval_exact_rational_ub(&uncap_acc, 1, 1, h_bits, q_exact);
        let cb = certify_bits_lb(&cn, &cd);
        let ub = certify_bits_lb(&un, &ud);
        let cs = format_decimal_ub(&cn, &cd);
        let us = format_decimal_ub(&un, &ud);
        assert_eq!(cb, exp_cb, "Cap+Cap bits mismatch on {label}");
        assert_eq!(cs, exp_cs, "Cap+Cap decimal UB mismatch on {label}");
        assert_eq!(ub, exp_ub, "Unc+Unc bits mismatch on {label}");
        assert_eq!(us, exp_us, "Unc+Unc decimal UB mismatch on {label}");
        println!("  {label:<21} | >= {:3}.{:04} b (P <= {cs}) | >= {:3}.{:04} b (P <= {us})",
            cb / 10_000, cb % 10_000, ub / 10_000, ub % 10_000);
    }

    // Exact integer q_96 certification: verify P_UB^rat(q_96) * 2^96 <= 1 and P_UB^rat(q_96 + 1) * 2^96 > 1!
    let mut lo = 1u128 << 48;
    let mut hi = 20u128 * (1u128 << 48);
    while lo + 1 < hi {
        let mid = lo + (hi - lo) / 2;
        let (cn, cd) = eval_exact_rational_ub(&global_acc, total_all, total_f, 48, mid);
        if cn.shl_bits(96).cmp_val(&cd) != std::cmp::Ordering::Greater { lo = mid; } else { hi = mid; }
    }
    assert_eq!(lo, 5_291_482_952_600_082u128, "certified q_96 mismatch!");
    let (cn96, cd96) = eval_exact_rational_ub(&global_acc, total_all, total_f, 48, lo);
    assert!(cn96.shl_bits(96).cmp_val(&cd96) != std::cmp::Ordering::Greater);
    let (cn96p1, cd96p1) = eval_exact_rational_ub(&global_acc, total_all, total_f, 48, lo + 1);
    assert!(cn96p1.shl_bits(96).cmp_val(&cd96p1) == std::cmp::Ordering::Greater);
    let lam96 = (lo as f64) / ((1u128 << 48) as f64);
    let eb96 = (lo as f64) * 3990.0 / 1e18;
    println!("\n[CERTIFIED] Exact integer q_96 = {lo} (lambda = {lam96:.6}, {eb96:.2} Exabytes): P_UB(q_96) <= 2^-96 PROVED in exact BigUint arithmetic (q_96 + 1 exceeds 2^-96).");
    verify_discrete_grind_p99(total_f, total_all);
    println!("Total wall time: {:.2}s", t_start.elapsed().as_secs_f64());
}
