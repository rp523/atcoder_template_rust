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
    fn is_prime(&self) -> bool // O(N^0.5 x logN)
    {
        let primes = self.into_primes();
        primes.len() == 1 && primes.iter().next().unwrap().1 == &1
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
}

#[cfg(test)]
mod test {
    use super::IntegerOperation;
    #[test]
    fn is_prime() {
        for x in 2..1e5 as usize {
            let expected = (2..x).all(|px| x % px != 0);
            let actual = x.is_prime();
            assert_eq!(expected, actual);
        }
    }
}
