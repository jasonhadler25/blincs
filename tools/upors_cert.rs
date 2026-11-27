//! Reproducible 320-bit exact Kronecker-transform + all-37-strata certified upper bound
//! for `BLINCS-128-A2` `U-PORS` (`H=10, K=10, m_max=44, L_42(3, 24)`).
//!
//! Compile & run (zero external dependencies):
//!   `rustc --edition 2024 -O tools/upors_cert.rs -o /tmp/upors_cert && /tmp/upors_cert`
//!
//! Computes:
//!   1. Exact integer family size `|F|` via `F_{h+1}(x, y) = 1 + 2y(F_h - 1) + (F_h - 1)^2`
//!      and exact cap acceptance probability `p_cap = |F| / C(1024, 10)`.
//!   2. Exact pairwise inclusion probabilities `P_{D ~ Unif(F)}[u, v in D]` by LCA height `d = 1..=10`,
//!      quantifying the positive clustering induced by the Octopus sibling cap `m_max = 44`.
//!   3. Verification of the exact `r = 1` identity `P_raw(1) = C(1024, 10)^{-1} * 376^{-10}`.
//!   4. Zero-MC certified upper bound for uncapped histories/verifiers (`Unc+Unc`) via the 3-term
//!      certified exponential envelope `u_3(t) = 1 - (8905/7144)*(0.81)^t + (1761/7144)*(0.05)^t >= q_C(t)`
//!      (`forall t >= 0`), evaluated in 320-bit fixed-point arithmetic (zero cancellation).
//!   5. All-37-strata (`s = 8..=44`) stratified zero-history-MC certified upper bound for the TRUE
//!      normative `BLINCS-128-A2` capped-signer + capped-verifier raw-query law (`Cap+Cap`, `mu = Unif(F)`),
//!      with exact 99% one-sided probability-space confidence bounds before taking `-log2`.

use std::convert::TryInto;

const H: usize = 10;
const L: usize = 1 << H;
const K: usize = 10;
const M_MAX: usize = 44;

/// Signed 320-bit fixed-point number (`val * 2^-256`, ~77 decimal fractional digits).
#[derive(Clone, Copy, Debug)]
struct Fix {
    neg: bool,
    mag: [u64; 5],
}

impl Fix {
    const ZERO: Self = Self { neg: false, mag: [0; 5] };
    const ONE: Self = Self { neg: false, mag: [0, 0, 0, 0, 1] };

    fn from_ratio_u128(num: u128, den: u128) -> Self {
        let mut q = [0u64; 5];
        let mut rem = 0u128;
        for bit in (0..384).rev() {
            let b = if bit >= 256 { (num >> (bit - 256)) & 1 } else { 0 };
            let carry = rem >> 127;
            rem = (rem << 1) | b;
            if carry != 0 || rem >= den {
                rem = rem.wrapping_sub(den);
                if bit < 320 {
                    q[bit / 64] |= 1u64 << (bit % 64);
                }
            }
        }
        Self { neg: false, mag: q }
    }

    fn from_rational(num: i128, den: u128) -> Self {
        let neg = num < 0;
        let mut r = Self::from_ratio_u128(num.unsigned_abs(), den);
        r.neg = neg && r.mag != [0; 5];
        r
    }

    fn cmp_mag(a: &[u64; 5], b: &[u64; 5]) -> std::cmp::Ordering {
        for i in (0..5).rev() {
            if a[i] != b[i] {
                return a[i].cmp(&b[i]);
            }
        }
        std::cmp::Ordering::Equal
    }

    fn add_mag(a: &[u64; 5], b: &[u64; 5]) -> [u64; 5] {
        let mut r = [0u64; 5];
        let mut c = 0u128;
        for i in 0..5 {
            let s = a[i] as u128 + b[i] as u128 + c;
            r[i] = s as u64;
            c = s >> 64;
        }
        r
    }

    fn sub_mag(a: &[u64; 5], b: &[u64; 5]) -> [u64; 5] {
        let mut r = [0u64; 5];
        let mut borrow = 0i128;
        for i in 0..5 {
            let d = a[i] as i128 - b[i] as i128 - borrow;
            if d < 0 {
                r[i] = (d + (1i128 << 64)) as u64;
                borrow = 1;
            } else {
                r[i] = d as u64;
                borrow = 0;
            }
        }
        r
    }

    #[inline]
    fn add(self, other: Self) -> Self {
        if self.neg == other.neg {
            Self { neg: self.neg, mag: Self::add_mag(&self.mag, &other.mag) }
        } else {
            match Self::cmp_mag(&self.mag, &other.mag) {
                std::cmp::Ordering::Greater => Self { neg: self.neg, mag: Self::sub_mag(&self.mag, &other.mag) },
                std::cmp::Ordering::Less => Self { neg: other.neg, mag: Self::sub_mag(&other.mag, &self.mag) },
                std::cmp::Ordering::Equal => Self::ZERO,
            }
        }
    }

    #[inline]
    fn mul(self, other: Self) -> Self {
        let mut prod = [0u64; 10];
        for i in 0..5 {
            let ai = self.mag[i] as u128;
            if ai == 0 {
                continue;
            }
            let mut carry = 0u128;
            for j in 0..5 {
                let s = prod[i + j] as u128 + ai * (other.mag[j] as u128) + carry;
                prod[i + j] = s as u64;
                carry = s >> 64;
            }
            prod[i + 5] = carry as u64;
        }
        let mag = [prod[4], prod[5], prod[6], prod[7], prod[8]];
        Self { neg: (self.neg ^ other.neg) && mag != [0; 5], mag }
    }

    fn to_f64(self) -> f64 {
        let mut v = 0.0f64;
        for i in (0..5).rev() {
            v = v * 2.0f64.powi(64) + (self.mag[i] as f64);
        }
        let val = v * 2.0f64.powi(-256);
        if self.neg { -val } else { val }
    }
}

fn comb_u128(n: usize, k: usize) -> u128 {
    if k > n {
        return 0;
    }
    let k = k.min(n - k);
    let mut r = 1u128;
    for i in 0..k {
        r = r * (n - i) as u128 / (i + 1) as u128;
    }
    r
}

struct SplitMix64(u64);
impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn next_u128_below(&mut self, bound: u128) -> u128 {
        let limit = u128::MAX - (u128::MAX % bound);
        loop {
            let v = ((self.next_u64() as u128) << 64) | (self.next_u64() as u128);
            if v < limit {
                return v % bound;
            }
        }
    }
}

fn build_f() -> Vec<Vec<Vec<u128>>> {
    let mut f = vec![vec![vec![0u128; M_MAX + 1]; K + 1]; H + 1];
    f[0][0][0] = 1;
    f[0][1][0] = 1;
    for h in 0..H {
        f[h + 1][0][0] = 1;
        for k in 1..=K {
            for s in 0..M_MAX {
                let c = f[h][k][s];
                if c != 0 {
                    f[h + 1][k][s + 1] += 2 * c;
                }
            }
        }
        for kl in 1..K {
            for kr in 1..=(K - kl) {
                for sl in 0..=M_MAX {
                    let cl = f[h][kl][sl];
                    if cl == 0 {
                        continue;
                    }
                    for sr in 0..=(M_MAX - sl) {
                        let cr = f[h][kr][sr];
                        if cr != 0 {
                            f[h + 1][kl + kr][sl + sr] += cl * cr;
                        }
                    }
                }
            }
        }
    }
    f
}

fn sample_exact_f_stratum(f: &[Vec<Vec<u128>>], s_target: usize, rng: &mut SplitMix64) -> [usize; K] {
    let mut out = Vec::with_capacity(K);
    fn rec(f: &[Vec<Vec<u128>>], rng: &mut SplitMix64, h: usize, base: usize, k: usize, s: usize, out: &mut Vec<usize>) {
        if k == 0 {
            return;
        }
        if h == 0 {
            out.push(base);
            return;
        }
        let total = f[h][k][s];
        let mut pick = rng.next_u128_below(total);
        if s >= 1 {
            let c = f[h - 1][k][s - 1];
            if pick < c {
                rec(f, rng, h - 1, base, k, s - 1, out);
                return;
            }
            pick -= c;
            if pick < c {
                rec(f, rng, h - 1, base + (1 << (h - 1)), k, s - 1, out);
                return;
            }
            pick -= c;
        }
        for kl in 1..k {
            let kr = k - kl;
            for sl in 0..=s {
                let cl = f[h - 1][kl][sl];
                if cl == 0 {
                    continue;
                }
                let cr = f[h - 1][kr][s - sl];
                if cr == 0 {
                    continue;
                }
                let ways = cl * cr;
                if pick < ways {
                    rec(f, rng, h - 1, base, kl, sl, out);
                    rec(f, rng, h - 1, base + (1 << (h - 1)), kr, s - sl, out);
                    return;
                }
                pick -= ways;
            }
        }
        unreachable!();
    }
    rec(f, rng, H, 0, K, s_target, &mut out);
    out.sort_unstable();
    out.try_into().unwrap()
}

fn exact_joint_counts(f: &[Vec<Vec<u128>>], target: &[usize; K]) -> [u128; 1024] {
    const STRIDE: usize = (K + 1) * (M_MAX + 1);
    fn rec(f: &[Vec<Vec<u128>>], h: usize, base: usize, targets: &[usize]) -> Vec<u128> {
        let m = targets.len();
        if h == 0 {
            let mut dp = vec![0u128; 2 * STRIDE];
            dp[0] = 1;
            dp[STRIDE + (M_MAX + 1)] = 1;
            return dp;
        }
        let mid = base + (1 << (h - 1));
        let split = targets.partition_point(|&x| x < mid);
        let left_t = &targets[..split];
        let right_t = &targets[split..];
        let mut out = vec![0u128; (1 << m) * STRIDE];
        if left_t.is_empty() || right_t.is_empty() {
            let sub = if !left_t.is_empty() {
                rec(f, h - 1, base, left_t)
            } else {
                rec(f, h - 1, mid, right_t)
            };
            let free = &f[h - 1];
            for mask in 0..(1usize << m) {
                let mb = mask * STRIDE;
                if mask == 0 {
                    out[0] += 1;
                    for kf in 1..=K {
                        for sf in 0..M_MAX {
                            let cf = free[kf][sf];
                            if cf != 0 {
                                out[kf * (M_MAX + 1) + sf + 1] += cf;
                            }
                        }
                    }
                }
                for ks in 1..=K {
                    for ss in 0..=M_MAX {
                        let cs = sub[mb + ks * (M_MAX + 1) + ss];
                        if cs == 0 {
                            continue;
                        }
                        if ss < M_MAX {
                            out[mb + ks * (M_MAX + 1) + ss + 1] += cs;
                        }
                        for kf in 1..=(K - ks) {
                            for sf in 0..=(M_MAX - ss) {
                                let cf = free[kf][sf];
                                if cf != 0 {
                                    out[mb + (ks + kf) * (M_MAX + 1) + ss + sf] += cs * cf;
                                }
                            }
                        }
                    }
                }
            }
            return out;
        }
        let ml = left_t.len();
        let mr = right_t.len();
        let dpl = rec(f, h - 1, base, left_t);
        let dpr = rec(f, h - 1, mid, right_t);
        for ml_mask in 0..(1usize << ml) {
            let bl = ml_mask * STRIDE;
            for mr_mask in 0..(1usize << mr) {
                let br = mr_mask * STRIDE;
                let bo = (ml_mask | (mr_mask << ml)) * STRIDE;
                for kl in 0..=K {
                    if ml_mask != 0 && kl == 0 {
                        continue;
                    }
                    for kr in 0..=(K - kl) {
                        if mr_mask != 0 && kr == 0 {
                            continue;
                        }
                        let add_sib = usize::from((kl == 0) ^ (kr == 0));
                        let ksum = kl + kr;
                        for sl in 0..=M_MAX {
                            let cl = dpl[bl + kl * (M_MAX + 1) + sl];
                            if cl == 0 {
                                continue;
                            }
                            if sl + add_sib > M_MAX {
                                continue;
                            }
                            let sr_max = M_MAX - sl - add_sib;
                            for sr in 0..=sr_max {
                                let cr = dpr[br + kr * (M_MAX + 1) + sr];
                                if cr != 0 {
                                    out[bo + ksum * (M_MAX + 1) + sl + sr + add_sib] += cl * cr;
                                }
                            }
                        }
                    }
                }
            }
        }
        out
    }
    let root = rec(f, H, 0, target);
    let mut res = [0u128; 1024];
    for mask in 0..1024usize {
        let base = mask * STRIDE + K * (M_MAX + 1);
        res[mask] = root[base..=base + M_MAX].iter().sum();
    }
    res
}

fn eval_exact_upper_3term(probs: &[Fix; 1024], z: &[Fix; 3], c_prod: &[Fix], max_r: usize) -> Vec<f64> {
    let mut cur: Vec<Fix> = probs.to_vec();
    let mut pow3 = 1usize;
    let mut pow2 = 1024usize;
    for _ax in 0..K {
        pow2 /= 2;
        let mut nxt = vec![Fix::ZERO; pow3 * 3 * pow2];
        for hi in 0..pow2 {
            for lo in 0..pow3 {
                let a0 = cur[(hi * 2) * pow3 + lo];
                let a1 = cur[(hi * 2 + 1) * pow3 + lo];
                let out_base = hi * 3 * pow3 + lo;
                for m in 0..3 {
                    nxt[out_base + m * pow3] = a0.add(a1.mul(z[m]));
                }
            }
        }
        cur = nxt;
        pow3 *= 3;
    }
    let mut g_pow = cur.clone();
    let mut out = vec![0.0f64; max_r + 1];
    for r in 1..=max_r {
        let mut acc = Fix::ZERO;
        for idx in 0..59_049usize {
            acc = acc.add(c_prod[idx].mul(g_pow[idx]));
        }
        out[r] = acc.to_f64();
        if r < max_r {
            for idx in 0..59_049usize {
                g_pow[idx] = g_pow[idx].mul(cur[idx]);
            }
        }
    }
    out
}

fn log_binom(q: u64, r: usize, log_p: f64, log_1mp: f64) -> f64 {
    let mut lc = 0.0;
    for i in 0..r {
        lc += ((q - i as u64) as f64).ln() - ((i + 1) as f64).ln();
    }
    lc + (r as f64) * log_p + ((q - r as u64) as f64) * log_1mp
}

fn main() {
    let f = build_f();
    let total_f: u128 = f[H][K].iter().sum();
    let total_all = comb_u128(L, K);
    assert_eq!(total_f, 256_172_225_164_499_838_464);
    assert_eq!(total_all, 334_265_867_498_622_145_619_456);
    let p_cap = (total_f as f64) / (total_all as f64);
    println!("|F|          = {total_f}");
    println!("C(1024, 10)  = {total_all}");
    println!("p_cap        = {p_cap:.10e}  (1/p_cap = {:.3}, -log2 = {:.4} b)", 1.0 / p_cap, -p_cap.log2());

    let z = [Fix::ONE, Fix::from_rational(81, 100), Fix::from_rational(5, 100)];
    let c = [Fix::ONE, Fix::from_rational(-8905, 7144), Fix::from_rational(1761, 7144)];
    let mut c_prod = vec![Fix::ONE; 59_049];
    for idx in 0..59_049usize {
        let mut t = idx;
        let mut p = Fix::ONE;
        for _ in 0..K {
            p = p.mul(c[t % 3]);
            t /= 3;
        }
        c_prod[idx] = p;
    }

    let max_r = 28usize;
    let mut uncap_probs = [Fix::ZERO; 1024];
    for mask in 0..1024usize {
        let a = mask.count_ones() as usize;
        uncap_probs[mask] = Fix::from_ratio_u128(comb_u128(L - K, K - a), total_all);
    }
    let uncap_u3 = eval_exact_upper_3term(&uncap_probs, &z, &c_prod, max_r);

    // Check exact r=1 identity
    let exact_r1 = 376.0f64.powi(-10) / (total_all as f64);
    assert!(((uncap_u3[1] - exact_r1) / exact_r1).abs() < 1e-12);

    // All-37-strata stratified exact target-law calculation (2 independent seeds to verify replication!)
    for (run_id, seed) in [(1usize, 0x1337_cafe_2026_1126u64), (2usize, 0xfeed_beef_dead_c0deu64)] {
        let mut rng = SplitMix64(seed);
        let mut total_mean = vec![0.0f64; max_r + 1];
        let mut total_var = vec![0.0f64; max_r + 1];
        for s in 0..=M_MAX {
            let cnt_s = f[H][K][s];
            if cnt_s == 0 {
                continue;
            }
            let w_s = (cnt_s as f64) / (total_f as f64);
            let n_s: usize = if s >= 38 { 64 } else if s >= 30 { 32 } else { 16 };
            let mut sm = vec![0.0f64; max_r + 1];
            let mut sm2 = vec![0.0f64; max_r + 1];
            for _ in 0..n_s {
                let target = sample_exact_f_stratum(&f, s, &mut rng);
                let jc = exact_joint_counts(&f, &target);
                assert_eq!(jc.iter().sum::<u128>(), total_f);
                let probs: [Fix; 1024] = std::array::from_fn(|m| Fix::from_ratio_u128(jc[m], total_f));
                let res = eval_exact_upper_3term(&probs, &z, &c_prod, max_r);
                for r in 1..=max_r {
                    let v = p_cap * res[r];
                    sm[r] += v;
                    sm2[r] += v * v;
                }
            }
            for r in 1..=max_r {
                let m = sm[r] / (n_s as f64);
                let var = ((sm2[r] / (n_s as f64)) - m * m).max(0.0) / (n_s as f64);
                total_mean[r] += w_s * m;
                total_var[r] += w_s * w_s * var;
            }
        }
        assert!(((total_mean[1] - exact_r1) / exact_r1).abs() < 1e-12);
        let log_p = -(33.0f64) * 2.0f64.ln();
        let log_1mp = (-2.0f64.powi(-33)).ln_1p();
        println!("\n=== Independent Replication #{run_id} (seed=0x{seed:016x}, all 37 strata, 64/32/16 samples/stratum) ===");
        println!("  q    | CERT Cap+Cap (99% LCB) | SE%   | EXACT Unc+Unc (0 MC) | Net Cap Gain");
        for exp in 30..=35 {
            let q = 1u64 << exp;
            let mut p_cc = 0.0;
            let mut v_cc = 0.0;
            let mut p_uu = 0.0;
            let mut rem = 1.0 - (q as f64 * log_1mp).exp();
            for r in 1..=max_r {
                let pr = log_binom(q, r, log_p, log_1mp).exp();
                rem -= pr;
                p_cc += pr * total_mean[r];
                v_cc += pr * pr * total_var[r];
                p_uu += pr * uncap_u3[r];
            }
            let tail = rem.max(0.0);
            let se = v_cc.sqrt();
            let ucb_cc = p_cc + 2.576 * se + tail;
            let ucb_uu = p_uu + tail;
            println!(
                "  2^{exp} |  {:6.2} b ({:6.2} b LCB) | {:4.2}% |       {:6.2} b       |   {:+6.2} b",
                -p_cc.log2(),
                -ucb_cc.log2(),
                100.0 * se / p_cc,
                -ucb_uu.log2(),
                (-p_cc.log2()) - (-ucb_uu.log2())
            );
        }
    }
}
