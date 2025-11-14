use crate::remainder::ext_gcd;
use cargo_snippet::snippet;

#[snippet("ModIntTrait")]
pub trait ModIntTrait {
    fn get_mod() -> usize;
    fn val(&self) -> usize;
    fn raw(x: usize) -> Self;
    fn new<T>(x: T) -> Self
    where
        T: Into<usize>,
        Self: Sized,
    {
        Self::raw(x.into() % Self::get_mod())
    }
    fn inverse(&self) -> Self
    where
        Self: Sized,
    {
        // x * inv_x + M * _ = gcd(x, M) = 1
        // x * inv_x = 1 (mod M)
        let v = ext_gcd(self.val() as i64, Self::get_mod() as i64).0;
        let m = Self::get_mod();
        let seed = if v >= 0 {
            v as usize
        } else {
            m - (-v % m as i64) as usize
        };
        Self::new(seed)

        // [Fermat's little theorem]
        // if p is prime, for any integer a, a^p = a (mod p)
        // especially when a and b is coprime, a^(p-1) = 1 (mod p).
        // -> inverse of a is a^(p-2).

        //let mut ret = Self { x: 1 };
        //let mut mul: Self = *self;
        //let mut p = MOD() - 2;
        //while p > 0 {
        //    if p & 1 != 0 {
        //        ret *= mul;
        //    }
        //    p >>= 1;
        //    mul *= mul;
        //}
        //ret
    }
    fn pow(self, p: usize) -> Self
    where
        Self: Sized,
    {
        Self::raw(Self::powmod(self.val(), p, Self::get_mod()))
    }
    #[inline(always)]
    fn powmod(x: usize, mut p: usize, m: usize) -> usize {
        let mut ret = 1;
        let mut mul = x;
        while p > 0 {
            if p & 1 != 0 {
                ret = (ret * mul) % m;
            }
            p >>= 1;
            mul = (mul * mul) % m;
        }
        ret
    }
}

#[snippet("StaticModInt")]
#[snippet(include = "ModIntTrait")]
#[snippet(include = "ext_gcd")]
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct StaticModInt<const MOD: usize> {
    x: usize,
}
#[snippet("StaticModInt")]
impl<const MOD: usize> ModIntTrait for StaticModInt<MOD> {
    fn get_mod() -> usize {
        MOD
    }
    fn raw(x: usize) -> Self {
        Self { x }
    }
    fn val(&self) -> usize {
        self.x
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::ops::Add<Self> for StaticModInt<MOD> {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.x + rhs.x)
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::ops::Sub<Self> for StaticModInt<MOD> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output {
        let m = Self::get_mod();
        Self::new(m + self.x - rhs.x)
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::ops::Mul<Self> for StaticModInt<MOD> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.x * rhs.x)
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::ops::Div<Self> for StaticModInt<MOD> {
    type Output = Self;
    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        Self::new(self.x * rhs.inverse().x)
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::ops::AddAssign<Self> for StaticModInt<MOD> {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = Self::new(self.x + rhs.x);
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::ops::SubAssign<Self> for StaticModInt<MOD> {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Self) {
        let m = Self::get_mod();
        *self = Self::new(m + self.x - rhs.x);
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::ops::MulAssign<Self> for StaticModInt<MOD> {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = Self::new(self.x * rhs.x);
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::ops::DivAssign<Self> for StaticModInt<MOD> {
    #[inline(always)]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn div_assign(&mut self, rhs: Self) {
        *self = Self::new(self.x * rhs.inverse().x);
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> From<usize> for StaticModInt<MOD> {
    fn from(value: usize) -> Self {
        Self::new(value)
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> From<u8> for StaticModInt<MOD> {
    fn from(value: u8) -> Self {
        Self::new(value as usize)
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::str::FromStr for StaticModInt<MOD> {
    type Err = std::num::ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.parse::<usize>() {
            Ok(x) => Ok(Self::new(x)),
            Err(e) => Err(e),
        }
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::iter::Sum for StaticModInt<MOD> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new(0usize), |cum, v| cum + v)
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::fmt::Display for StaticModInt<MOD> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.x)
    }
}
#[snippet("StaticModInt")]
impl<const MOD: usize> std::fmt::Debug for StaticModInt<MOD> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.x)
    }
}

#[snippet("DynModInt")]
static mut MOD: usize = 2;
#[snippet("DynModInt")]
#[snippet(include = "ModIntTrait")]
#[snippet(include = "ext_gcd")]
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct DynModInt {
    x: usize,
}
#[snippet("DynModInt")]
impl ModIntTrait for DynModInt {
    fn get_mod() -> usize {
        unsafe { MOD }
    }
    fn raw(x: usize) -> Self {
        Self { x }
    }
    fn val(&self) -> usize {
        self.x
    }
}
#[snippet("DynModInt")]
impl DynModInt {
    pub fn set_mod(val: usize) {
        unsafe {
            MOD = val;
        }
    }
}
#[snippet("DynModInt")]
impl std::ops::Add<Self> for DynModInt {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.x + rhs.x)
    }
}
#[snippet("DynModInt")]
impl std::ops::Sub<Self> for DynModInt {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output {
        let m = Self::get_mod();
        Self::new(m + self.x - rhs.x)
    }
}
#[snippet("DynModInt")]
impl std::ops::Mul<Self> for DynModInt {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.x * rhs.x)
    }
}
#[snippet("DynModInt")]
impl std::ops::Div<Self> for DynModInt {
    type Output = Self;
    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        Self::new(self.x * rhs.inverse().x)
    }
}
#[snippet("DynModInt")]
impl std::ops::AddAssign<Self> for DynModInt {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = Self::new(self.x + rhs.x);
    }
}
#[snippet("DynModInt")]
impl std::ops::SubAssign<Self> for DynModInt {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Self) {
        let m = Self::get_mod();
        *self = Self::new(m + self.x - rhs.x);
    }
}
#[snippet("DynModInt")]
impl std::ops::MulAssign<Self> for DynModInt {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = Self::new(self.x * rhs.x);
    }
}
#[snippet("DynModInt")]
impl std::ops::DivAssign<Self> for DynModInt {
    #[inline(always)]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn div_assign(&mut self, rhs: Self) {
        *self = Self::new(self.x * rhs.inverse().x)
    }
}
#[snippet("DynModInt")]
impl From<u8> for DynModInt {
    fn from(value: u8) -> Self {
        Self::new(value as usize)
    }
}
#[snippet("DynModInt")]
impl From<usize> for DynModInt {
    fn from(value: usize) -> Self {
        Self::new(value)
    }
}
#[snippet("DynModInt")]
impl std::str::FromStr for DynModInt {
    type Err = std::num::ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.parse::<usize>() {
            Ok(x) => Ok(Self::new(x)),
            Err(e) => Err(e),
        }
    }
}
#[snippet("DynModInt")]
impl std::iter::Sum for DynModInt {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new(0usize), |cum, v| cum + v)
    }
}
#[snippet("DynModInt")]
impl std::fmt::Display for DynModInt {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.x)
    }
}
#[snippet("DynModInt")]
impl std::fmt::Debug for DynModInt {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.x)
    }
}

#[snippet("HashNode")]
type Mint0 = StaticModInt<1000010029>;
#[snippet("HashNode")]
type Mint1 = StaticModInt<1000010051>;
#[snippet("HashNode")]
type Mint2 = StaticModInt<1000010069>;
#[snippet("HashNode")]
type Mint3 = StaticModInt<1000010101>;
#[snippet("HashNode")]
type Mint4 = StaticModInt<1000010153>;
#[snippet("HashNode")]
type Mint5 = StaticModInt<1000010173>;
#[snippet("HashNode")]
type Mint6 = StaticModInt<1000010189>;
#[snippet("HashNode")]
type Mint7 = StaticModInt<1000010197>;
#[snippet("HashNode")]
type Mint8 = StaticModInt<1000010233>;
#[snippet("HashNode")]
type Mint9 = StaticModInt<1000010243>;
#[snippet("HashNode")]
#[snippet(include = "DnyModInt")]
#[snippet(include = "StaticModInt")]
#[snippet(include = "ModIntTrait")]
#[snippet(include = "ext_gcd")]
#[derive(Clone, Debug, Copy, Eq, Hash, PartialEq)]
pub struct HashNode {
    x0: Mint0,
    x1: Mint1,
    x2: Mint2,
    x3: Mint3,
    x4: Mint4,
    x5: Mint5,
    x6: Mint6,
    x7: Mint7,
    x8: Mint8,
    x9: Mint9,
}
#[snippet("HashNode")]
impl HashNode {
    pub fn new(x: usize) -> Self {
        Self {
            x0: Mint0::new(x),
            x1: Mint1::new(x),
            x2: Mint2::new(x),
            x3: Mint3::new(x),
            x4: Mint4::new(x),
            x5: Mint5::new(x),
            x6: Mint6::new(x),
            x7: Mint7::new(x),
            x8: Mint8::new(x),
            x9: Mint9::new(x),
        }
    }
}
#[snippet("HashNode")]
impl std::ops::Add<Self> for HashNode {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            x0: self.x0 + rhs.x0,
            x1: self.x1 + rhs.x1,
            x2: self.x2 + rhs.x2,
            x3: self.x3 + rhs.x3,
            x4: self.x4 + rhs.x4,
            x5: self.x5 + rhs.x5,
            x6: self.x6 + rhs.x6,
            x7: self.x7 + rhs.x7,
            x8: self.x8 + rhs.x8,
            x9: self.x9 + rhs.x9,
        }
    }
}
#[snippet("HashNode")]
impl std::ops::Sub<Self> for HashNode {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            x0: self.x0 - rhs.x0,
            x1: self.x1 - rhs.x1,
            x2: self.x2 - rhs.x2,
            x3: self.x3 - rhs.x3,
            x4: self.x4 - rhs.x4,
            x5: self.x5 - rhs.x5,
            x6: self.x6 - rhs.x6,
            x7: self.x7 - rhs.x7,
            x8: self.x8 - rhs.x8,
            x9: self.x9 - rhs.x9,
        }
    }
}
#[snippet("HashNode")]
impl std::ops::Mul<Self> for HashNode {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            x0: self.x0 * rhs.x0,
            x1: self.x1 * rhs.x1,
            x2: self.x2 * rhs.x2,
            x3: self.x3 * rhs.x3,
            x4: self.x4 * rhs.x4,
            x5: self.x5 * rhs.x5,
            x6: self.x6 * rhs.x6,
            x7: self.x7 * rhs.x7,
            x8: self.x8 * rhs.x8,
            x9: self.x9 * rhs.x9,
        }
    }
}
#[snippet("HashNode")]
impl std::ops::Div<Self> for HashNode {
    type Output = Self;
    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        Self {
            x0: self.x0 / rhs.x0,
            x1: self.x1 / rhs.x1,
            x2: self.x2 / rhs.x2,
            x3: self.x3 / rhs.x3,
            x4: self.x4 / rhs.x4,
            x5: self.x5 / rhs.x5,
            x6: self.x6 / rhs.x6,
            x7: self.x7 / rhs.x7,
            x8: self.x8 / rhs.x8,
            x9: self.x9 / rhs.x9,
        }
    }
}
#[snippet("HashNode")]
impl std::ops::AddAssign<Self> for HashNode {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
#[snippet("HashNode")]
impl std::ops::SubAssign<Self> for HashNode {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}
#[snippet("HashNode")]
impl std::ops::MulAssign<Self> for HashNode {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}
#[snippet("HashNode")]
impl std::ops::DivAssign<Self> for HashNode {
    #[inline(always)]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}
#[snippet("HashNode")]
impl std::str::FromStr for HashNode {
    type Err = std::num::ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.parse::<usize>() {
            Ok(x) => Ok(Self::new(x)),
            Err(e) => Err(e),
        }
    }
}
#[snippet("HashNode")]
impl std::iter::Sum for HashNode {
    fn sum<I: Iterator<Item = HashNode>>(iter: I) -> Self {
        iter.fold(Self::new(0), |cum, v| cum + v)
    }
}

#[snippet("Fact")]
#[allow(dead_code)]
struct Fact<T>
where
    T: Clone + Copy + std::ops::Mul<T, Output = T> + std::ops::Div<T, Output = T> + From<usize>,
{
    fact: Vec<T>,
    ifact: Vec<T>,
}
#[snippet("Fact")]
#[allow(dead_code)]
impl<T> Fact<T>
where
    T: Clone + Copy + std::ops::Mul<T, Output = T> + std::ops::Div<T, Output = T> + From<usize>,
{
    pub fn new() -> Self {
        let one = T::from(1usize);
        Self {
            fact: vec![one],
            ifact: vec![one],
        }
    }
    pub fn factorial(&mut self, n: usize) -> T {
        while self.fact.len() <= n {
            self.fact
                .push(self.fact[self.fact.len() - 1] * T::from(self.fact.len()))
        }
        self.fact[n]
    }
    pub fn factorial_inv(&mut self, n: usize) -> T {
        while self.ifact.len() <= n {
            self.ifact
                .push(self.ifact[self.ifact.len() - 1] / T::from(self.ifact.len()))
        }
        self.ifact[n]
    }
    pub fn combination(&mut self, n: usize, k: usize) -> T {
        self.factorial(n) * self.factorial_inv(n - k) * self.factorial_inv(k)
    }
    pub fn permutation(&mut self, n: usize, k: usize) -> T {
        self.factorial(n) * self.factorial_inv(n - k)
    }
}
#[cfg(test)]
mod test {
    use super::Fact;
    use super::ModIntTrait;
    use super::StaticModInt;
    fn fact_raw(n: usize) -> usize {
        (1..=n).fold(1, |cum, x| cum * x)
    }
    #[test]
    fn factorial() {
        const N: usize = 10;
        type Mint = StaticModInt<1000000007>;
        let mut fact = Fact::<Mint>::new();
        for n in 0..=N {
            let actual = fact.factorial(n);
            let expected = fact_raw(n);
            assert_eq!(expected, actual.val());
        }
    }
    #[test]
    fn combination() {
        const N: usize = 10;
        type Mint = StaticModInt<1000000007>;
        let mut fact = Fact::<Mint>::new();
        for n in 0..=N {
            for k in 0..=n {
                let actual = fact.combination(n, k);
                let expected = fact_raw(n) / fact_raw(n - k) / fact_raw(k);
                assert_eq!(expected, actual.val());
            }
        }
    }
    #[test]
    fn permutation() {
        const N: usize = 10;
        type Mint = StaticModInt<1000000007>;
        let mut fact = Fact::<Mint>::new();
        for n in 0..=N {
            for k in 0..=n {
                let actual = fact.permutation(n, k);
                let expected = fact_raw(n) / fact_raw(n - k);
                assert_eq!(expected, actual.val());
            }
        }
    }
}
