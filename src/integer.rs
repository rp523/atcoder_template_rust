use cargo_snippet::snippet;

#[snippet("IntegerOperation")]
pub trait IntegerOperation {
    fn into_primes(self) -> std::collections::BTreeMap<Self, usize>
    where
        Self: Sized;
    fn into_divisors(self) -> Vec<Self>
    where
        Self: Sized;
    fn squared_length(&self, rhs: Self) -> Self;
    fn is_prime(&self) -> bool;
}
#[snippet("IntegerOperation")]
impl<
        T: Copy
            + Ord
            + std::ops::AddAssign
            + std::ops::MulAssign
            + std::ops::DivAssign
            + std::ops::Add<Output = T>
            + std::ops::Mul<Output = T>
            + std::ops::Div<Output = T>
            + std::ops::Rem<Output = T>
            + From<u8>,
    > IntegerOperation for T
{
    fn into_primes(self) -> std::collections::BTreeMap<T, usize> // O(N^0.5 x logN)
    {
        let zero = T::from(0u8);
        let one = T::from(1u8);
        let two = one + one;
        let three = two + one;
        #[allow(clippy::eq_op)]
        if self == zero {
            panic!("Zero has no divisors.");
        }
        #[allow(clippy::eq_op)]
        let mut n = self;
        let mut ans = std::collections::BTreeMap::new();
        while n % two == zero {
            *ans.entry(two).or_insert(0) += 1;
            n /= two;
        }
        {
            let mut i = three;
            while i * i <= n {
                while n % i == zero {
                    *ans.entry(i).or_insert(0) += 1;
                    n /= i;
                }
                i += two;
            }
        }
        if n != one {
            *ans.entry(n).or_insert(0) += 1;
        }
        ans
    }
    fn into_divisors(self) -> Vec<T> // O(N^0.5)
    {
        let zero = T::from(0u8);
        let one = T::from(1u8);
        if self == zero {
            panic!("Zero has no primes.");
        }
        let n = self;
        let mut ret: Vec<T> = Vec::new();
        {
            let mut i = one;
            while i * i <= n {
                if n % i == zero {
                    ret.push(i);
                    if i * i != n {
                        ret.push(n / i);
                    }
                }
                i += one;
            }
        }
        ret.sort();
        ret
    }
    fn squared_length(&self, rhs: Self) -> Self {
        *self * *self + rhs * rhs
    }
    fn is_prime(&self) -> bool // O(N^0.5 x logN)
    {
        let primes = self.into_primes();
        primes.len() == 1 && primes.iter().next().unwrap().1 == &1
    }
}
#[snippet("IntegerOperation")]
pub fn is_prime(n: u64) -> bool {
    fn mulmod(a: u64, b: u64, n: u64) -> u64 {
        ((a as u128) * (b as u128) % (n as u128)) as u64
    }
    fn powmod(mut b: u64, mut p: u64, n: u64) -> u64 {
        let mut r = if (p & 1) == 0 { 1 } else { b };
        loop {
            p >>= 1;
            if p == 0 {
                return r;
            }
            b = mulmod(b, b, n);
            if p & 1 != 0 {
                r = mulmod(r, b, n);
            }
        }
    }
    if n == 2 {
        return true;
    }
    if n < 2 || n & 1 == 0 {
        return false;
    }
    let n1 = n - 1;
    let s = n1.trailing_zeros();
    let d = n1 >> s;
    [2, 325, 9375, 28178, 450775, 9780504, 1795265022]
        .iter()
        .all(|&base| {
            let a = if base < n { base } else { base % n };
            if a == 0 {
                return true;
            }
            let mut t = powmod(a, d, n);
            if t == 1 || t == n1 {
                return true;
            }
            for _ in 1..s {
                t = mulmod(t, t, n);
                if t == n1 {
                    return true;
                }
            }
            false
        })
}

#[cfg(test)]
mod test {
    #[test]
    fn is_prime() {
        for x in 1..100_000u64 {
            let expected = (x >= 2) && (2..x).all(|px| x % px != 0);
            let actual = super::is_prime(x);
            assert_eq!(expected, actual);
        }
    }
}
