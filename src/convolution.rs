use cargo_snippet::snippet;

// https://github.com/atcoder/ac-library/blob/master/atcoder/convolution.hpp
use crate::integer::IntegerOperation;
#[snippet("convolution")]
#[snippet(include = "IntegerOperation")]
#[snippet(include = "ModIntTrait")]
pub fn convolution<Mint>(arga: &[Mint], argb: &[Mint]) -> Vec<Mint>
where
    Mint: Clone
        + ModIntTrait
        + std::ops::Add<Output = Mint>
        + std::ops::Mul<Output = Mint>
        + std::ops::Sub<Output = Mint>
        + std::ops::MulAssign
        + std::ops::Div<Output = Mint>
        + Copy,
{
    let n = arga.len();
    let m = argb.len();
    let z = 1 << ceil_pow2(n + m - 1);
    let mut a = vec![Mint::new(0usize); z];
    let mut b = vec![Mint::new(0usize); z];
    for (a, &arga) in a.iter_mut().zip(arga.iter()) {
        *a = arga;
    }
    butterfly(&mut a);
    for (b, &argb) in b.iter_mut().zip(argb.iter()) {
        *b = argb;
    }
    butterfly(&mut b);
    for (a, b) in a.iter_mut().zip(b.into_iter()) {
        *a *= b;
    }
    butterfly_inv(&mut a);
    while a.len() > n + m - 1 {
        a.pop();
    }
    let iz = Mint::new(1usize) / Mint::new(z);
    for a in a.iter_mut() {
        *a *= iz;
    }
    a
}
#[snippet("convolution")]
// returns 'r' s.t. 'r^(m - 1) == 1 (mod m)'
fn primitive_root(m: i64) -> i64 {
    debug_assert!(m.is_prime());
    if m == 2 {
        return 1;
    }
    if m == 167772161 {
        return 3;
    }
    if m == 469762049 {
        return 3;
    }
    if m == 754974721 {
        return 11;
    }
    if m == 998244353 {
        return 3;
    }
    if m == 1000000007 {
        return 5;
    }
    let divs = ((m - 1) / 2).into_primes();

    for g in 2.. {
        let mut ok = true;
        for (&div, _) in divs.iter() {
            fn pow_mod(x: i64, mut p: i64, m: i64) -> i64 {
                let mut ret = 1;
                let mut mul = x % m;
                while p > 0 {
                    if p & 1 != 0 {
                        ret *= mul;
                        ret %= m;
                    }
                    p >>= 1;
                    mul *= mul;
                    mul %= m;
                }
                ret
            }

            if pow_mod(g, (m - 1) / div, m) == 1 {
                ok = false;
                break;
            }
        }
        if ok {
            return g;
        }
    }
    unreachable!();
}
#[snippet("convolution")]
struct FFTinfo<Mint> {
    root: Vec<Mint>,  // root[i]^(2^i) == 1
    iroot: Vec<Mint>, // root[i] * iroot[i] == 1
    rate2: Vec<Mint>,
    irate2: Vec<Mint>,
    rate3: Vec<Mint>,
    irate3: Vec<Mint>,
}
// returns minimum non-negative `x` s.t. `(n & (1 << x)) != 0`
#[snippet("convolution")]
fn bsf(n: usize) -> usize {
    let mut x = 0;
    while (n & (1 << x)) == 0 {
        x += 1;
    }
    x
}
#[snippet("convolution")]
impl<Mint> FFTinfo<Mint>
where
    Mint: Clone
        + ModIntTrait
        + std::ops::Mul<Output = Mint>
        + std::ops::MulAssign
        + std::ops::Div<Output = Mint>
        + std::ops::Div<Output = Mint>
        + Copy,
{
    fn new() -> Self {
        let rank2 = bsf(Mint::get_mod() - 1);
        let mut root = vec![Mint::new(0usize); rank2 + 1];
        let mut iroot = vec![Mint::new(0usize); rank2 + 1];
        let mut rate2 = vec![Mint::new(0usize); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
        let mut irate2 = vec![Mint::new(0usize); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
        let mut rate3 = vec![Mint::new(0usize); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];
        let mut irate3 = vec![Mint::new(0usize); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];

        let g = primitive_root(Mint::get_mod() as i64);
        root[rank2] = Mint::new(g as usize).pow((Mint::get_mod() - 1) >> rank2);
        iroot[rank2] = Mint::new(1usize) / root[rank2];
        for i in (0..rank2).rev() {
            root[i] = root[i + 1] * root[i + 1];
            iroot[i] = iroot[i + 1] * iroot[i + 1];
        }

        {
            let mut prod = Mint::new(1usize);
            let mut iprod = Mint::new(1usize);
            for i in 0..=(rank2 - 2) {
                rate2[i] = root[i + 2] * prod;
                irate2[i] = iroot[i + 2] * iprod;
                prod *= iroot[i + 2];
                iprod *= root[i + 2];
            }
        }
        {
            let mut prod = Mint::new(1usize);
            let mut iprod = Mint::new(1usize);
            for i in 0..=(rank2 - 3) {
                rate3[i] = root[i + 3] * prod;
                irate3[i] = iroot[i + 3] * iprod;
                prod *= iroot[i + 3];
                iprod *= root[i + 3];
            }
        }

        Self {
            root,
            iroot,
            rate2,
            irate2,
            rate3,
            irate3,
        }
    }
}
#[snippet("convolution")]
fn ceil_pow2(n: usize) -> usize {
    let mut x = 0;
    while (1 << x) < n {
        x += 1;
    }
    x
}
#[snippet("convolution")]
fn butterfly<Mint>(a: &mut [Mint])
where
    Mint: Clone
        + ModIntTrait
        + std::ops::Add<Output = Mint>
        + std::ops::Mul<Output = Mint>
        + std::ops::MulAssign
        + std::ops::Sub<Output = Mint>
        + std::ops::Div<Output = Mint>
        + Copy,
{
    let n = a.len();
    let h = ceil_pow2(n);

    let info = FFTinfo::new();

    let mut len = 0; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
    while len < h {
        if h - len == 1 {
            let p = 1 << (h - len - 1);
            let mut rot = Mint::new(1usize);
            for s in 0..(1 << len) {
                let offset = s << (h - len);
                for i in 0..p {
                    let l = a[i + offset];
                    let r = a[i + offset + p] * rot;
                    a[i + offset] = l + r;
                    a[i + offset + p] = l - r;
                }
                if s + 1 != (1 << len) {
                    rot *= info.rate2[bsf(!s)];
                }
            }
            len += 1;
        } else {
            // 4-base
            let p = 1 << (h - len - 2);
            let mut rot = Mint::new(1usize);
            let imag = info.root[2];
            for s in 0..(1 << len) {
                let rot2 = rot * rot;
                let rot3 = rot2 * rot;
                let offset = s << (h - len);
                for i in 0..p {
                    let mod2 = Mint::get_mod() * Mint::get_mod();
                    let a0 = a[i + offset].val();
                    let a1 = a[i + offset + p].val() * rot.val();
                    let a2 = a[i + offset + 2 * p].val() * rot2.val();
                    let a3 = a[i + offset + 3 * p].val() * rot3.val();
                    let a1na3imag = Mint::new(a1 + mod2 - a3).val() * imag.val();
                    let na2 = mod2 - a2;
                    a[i + offset] = Mint::new(a0 + a2 + a1 + a3);
                    a[i + offset + p] = Mint::new(a0 + a2 + (2 * mod2 - (a1 + a3)));
                    a[i + offset + 2 * p] = Mint::new(a0 + na2 + a1na3imag);
                    a[i + offset + 3 * p] = Mint::new(a0 + na2 + (mod2 - a1na3imag));
                }
                if s + 1 != (1 << len) {
                    rot *= info.rate3[bsf(!s)];
                }
            }
            len += 2;
        }
    }
}
#[snippet("convolution")]
fn butterfly_inv<Mint>(a: &mut [Mint])
where
    Mint: Clone
        + ModIntTrait
        + std::ops::Add<Output = Mint>
        + std::ops::Mul<Output = Mint>
        + std::ops::MulAssign
        + std::ops::Sub<Output = Mint>
        + std::ops::Div<Output = Mint>
        + Copy,
{
    let n = a.len();
    let h = ceil_pow2(n);

    let info = FFTinfo::<Mint>::new();

    let mut len = h; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
    while len > 0 {
        if len == 1 {
            let p = 1 << (h - len);
            let mut irot = Mint::new(1usize);
            for s in 0..(1 << (len - 1)) {
                let offset = s << (h - len + 1);
                for i in 0..p {
                    let l = a[i + offset];
                    let r = a[i + offset + p];
                    a[i + offset] = l + r;
                    a[i + offset + p] =
                        Mint::new((Mint::get_mod() + l.val() - r.val()) * irot.val());
                }
                if s + 1 != (1 << (len - 1)) {
                    irot *= info.irate2[bsf(!s)];
                }
            }
            len -= 1;
        } else {
            // 4-base
            let p = 1 << (h - len);
            let mut irot = Mint::new(1usize);
            let iimag = info.iroot[2];
            for s in 0..(1 << (len - 2)) {
                let irot2 = irot * irot;
                let irot3 = irot2 * irot;
                let offset = s << (h - len + 2);
                for i in 0..p {
                    let a0 = a[i + offset].val();
                    let a1 = a[i + offset + p].val();
                    let a2 = a[i + offset + 2 * p].val();
                    let a3 = a[i + offset + 3 * p].val();
                    let a2na3iimag = Mint::new((Mint::get_mod() + a2 - a3) * iimag.val()).val();
                    a[i + offset] = Mint::new(a0 + a1 + a2 + a3);
                    a[i + offset + p] =
                        Mint::new((a0 + (Mint::get_mod() - a1) + a2na3iimag) * irot.val());
                    a[i + offset + 2 * p] = Mint::new(
                        (a0 + a1 + (Mint::get_mod() - a2) + (Mint::get_mod() - a3)) * irot2.val(),
                    );
                    a[i + offset + 3 * p] = Mint::new(
                        (a0 + (Mint::get_mod() - a1) + (Mint::get_mod() - a2na3iimag))
                            * irot3.val(),
                    );
                }
                if s + 1 != (1 << (len - 2)) {
                    irot *= info.irate3[bsf(!s)];
                }
            }
            len -= 2;
        }
    }
}

use crate::modint::{DynModInt, ModIntTrait};
#[snippet("convolution_i64")]
#[snippet(include = "DynModInt")]
#[snippet(include = "convolution")]
pub fn convolution_i64(a: &[i64], b: &[i64]) -> Vec<i64> {
    let n = a.len();
    let m = b.len();
    if n == 0 || m == 0 {
        return vec![];
    }

    const M1: u64 = 754974721; // 2^24
    const M2: u64 = 167772161; // 2^25
    const M3: u64 = 469762049; // 2^26
    const M2M3: u64 = M2 * M3;
    const M1M3: u64 = M1 * M3;
    const M1M2: u64 = M1 * M2;
    const M1M2M3: u64 = M1M2.wrapping_mul(M3);

    const I1: i64 = 190329765; //ext_gcd(M2 * M3, M1).0;
    const I2: i64 = 58587104; //ext_gcd(M3 * M1, M2).0;
    const I3: i64 = 187290749; //ext_gcd(M1 * M2, M3).0;

    const MAX_AB_BIT: usize = 24;
    debug_assert_eq!(1, M1 % (1u64 << MAX_AB_BIT));
    debug_assert_eq!(1, M2 % (1u64 << MAX_AB_BIT));
    debug_assert_eq!(1, M3 % (1u64 << MAX_AB_BIT));
    debug_assert!(n + m - 1 <= (1 << MAX_AB_BIT));

    DynModInt::set_mod(M1 as usize);
    let c1 = convolution(
        &a.iter()
            .map(|&x| DynModInt::new(x as usize))
            .collect::<Vec<_>>(),
        &b.iter()
            .map(|&x| DynModInt::new(x as usize))
            .collect::<Vec<_>>(),
    )
    .into_iter()
    .map(|x| x.val())
    .collect::<Vec<_>>();
    DynModInt::set_mod(M2 as usize);
    let c2 = convolution(
        &a.iter()
            .map(|&x| DynModInt::new(x as usize))
            .collect::<Vec<_>>(),
        &b.iter()
            .map(|&x| DynModInt::new(x as usize))
            .collect::<Vec<_>>(),
    )
    .into_iter()
    .map(|x| x.val())
    .collect::<Vec<_>>();
    DynModInt::set_mod(M3 as usize);
    let c3 = convolution(
        &a.iter()
            .map(|&x| DynModInt::new(x as usize))
            .collect::<Vec<_>>(),
        &b.iter()
            .map(|&x| DynModInt::new(x as usize))
            .collect::<Vec<_>>(),
    )
    .into_iter()
    .map(|x| x.val())
    .collect::<Vec<_>>();

    c1.into_iter()
        .zip(c2)
        .zip(c3)
        .map(|((c1, c2), c3)| {
            const OFFSET: &[u64] = &[0, 0, M1M2M3, 2 * M1M2M3, 3 * M1M2M3];

            let mut x = [(c1, I1, M1, M2M3), (c2, I2, M2, M1M3), (c3, I3, M3, M1M2)]
                .iter()
                .map(|&(c, i, m1, m2)| {
                    (c as i64)
                        .wrapping_mul(i)
                        .rem_euclid(m1 as _)
                        .wrapping_mul(m2 as _)
                })
                .fold(0, i64::wrapping_add);

            // B = 2^63, -B <= x, r(real value) < B
            // (x, x - M, x - 2M, or x - 3M) = r (mod 2B)
            // r = c1[i] (mod MOD1)
            // focus on MOD1
            // r = x, x - M', x - 2M', x - 3M' (M' = M % 2^64) (mod 2B)
            // r = x,
            //     x - M' + (0 or 2B),
            //     x - 2M' + (0, 2B or 4B),
            //     x - 3M' + (0, 2B, 4B or 6B) (without mod!)
            // (r - x) = 0, (0)
            //           - M' + (0 or 2B), (1)
            //           -2M' + (0 or 2B or 4B), (2)
            //           -3M' + (0 or 2B or 4B or 6B) (3) (mod MOD1)
            // we checked that
            //   ((1) mod MOD1) mod 5 = 2
            //   ((2) mod MOD1) mod 5 = 3
            //   ((3) mod MOD1) mod 5 = 4
            fn safe_mod(mut x: i64, m: i64) -> i64 {
                x %= m;
                if x < 0 {
                    x += m;
                }
                x
            }

            let mut diff = c1 as i64 - safe_mod(x, M1 as _);
            if diff < 0 {
                diff += M1 as i64;
            }
            x = x.wrapping_sub(OFFSET[diff.rem_euclid(5) as usize] as _);
            x
        })
        .collect()
}
