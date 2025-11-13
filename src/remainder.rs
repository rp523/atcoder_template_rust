use cargo_snippet::snippet;

use std::cmp::{PartialEq, PartialOrd};
use std::ops::{Add, AddAssign, Div, Mul, Neg, Rem, RemAssign, Sub, SubAssign};
#[snippet("gcd")]
pub fn gcd<T: Copy + Rem<Output = T> + PartialEq + From<u8>>(a: T, b: T) -> T {
    let zero = T::from(0u8);
    if b == zero {
        a
    } else {
        gcd(b, a % b)
    }
}

#[snippet("ext_gcd")]
#[inline(always)]
// returns (p, q) s. t. ap + bq = gcd(a, b)
pub fn ext_gcd<
    T: Eq + Copy + Sub<Output = T> + Mul<Output = T> + Div<Output = T> + Rem<Output = T> + From<u8>,
>(
    a: T,
    b: T,
) -> (T, T) {
    let zero = T::from(0u8);
    let one = T::from(1u8);
    if a == zero {
        return (zero, one);
    }
    // (b % a) * x + a * y = gcd(a, b)
    // b % a = b - (b / a) * a
    // ->
    // (b - (b / a) * a) * x + a * y = gcd(a, b)
    // a * (y - (b / a) * x) + b * x = gcd(a, b)
    let (x, y) = ext_gcd(b % a, a);
    (y - b / a * x, x)
}

// Chinese Remainder Theorem
#[snippet("chinese_rem")]
#[snippet(include = "gcd")]
#[snippet(include = "ext_gcd")]
// when exists, returns (lcm(mods), x) s.t. x = r_i (mod  m_i) for all i.
pub fn chinese_rem<
    T: Eq
        + Copy
        + Neg<Output = T>
        + PartialOrd
        + Add<Output = T>
        + AddAssign
        + Sub<Output = T>
        + SubAssign
        + Mul<Output = T>
        + Div<Output = T>
        + Rem<Output = T>
        + RemAssign
        + From<u8>,
>(
    mods: &[T],
    rems: &[T],
) -> Option<(T, T)> {
    // when exists, returns (lcm(m1, m2), x) s.t. x = r1 (mod  m1) and x = r2 (mod m2)
    fn chinese_rem_elem2<
        T: Eq
            + Copy
            + Neg<Output = T>
            + PartialOrd
            + Add<Output = T>
            + AddAssign
            + Sub<Output = T>
            + SubAssign
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + RemAssign
            + From<u8>,
    >(
        m1: T,
        r1: T,
        m2: T,
        r2: T,
    ) -> Option<(T, T)> {
        let zero = T::from(0u8);
        let one = T::from(1u8);
        let (p, _q) = ext_gcd(m1, m2);
        let g = gcd(m1, m2);
        if (r2 - r1) % g != zero {
            None
        } else {
            let lcm = m1 * (m2 / g);
            let mut r = r1 + m1 * ((r2 - r1) / g) * p;
            if r < zero {
                let dv = (-r + lcm - one) / lcm;
                r += dv * lcm;
            }
            r %= lcm;
            Some((lcm, r))
        }
    }
    let zero = T::from(0u8);
    let one = T::from(1u8);
    debug_assert!(mods.len() == rems.len());
    let mut lcm = one;
    let mut rem = zero;
    for (m, r) in mods.iter().copied().zip(rems.iter().copied()) {
        if let Some((nlcm, nrem)) = chinese_rem_elem2(lcm, rem, m, r) {
            lcm = nlcm;
            rem = nrem;
        } else {
            return None;
        }
    }
    Some((lcm, rem))
}
mod test {
    #[test]
    fn gcd() {
        const N: usize = 1000;
        for a in 1..=N {
            for b in 1..=N {
                for expected in (1..=std::cmp::min(a, b)).rev() {
                    if a % expected == 0 && b % expected == 0 {
                        assert_eq!(expected, super::gcd(a, b));
                        break;
                    }
                }
            }
        }
    }
}
