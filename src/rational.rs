use crate::remainder::gcd;
use cargo_snippet::snippet;

#[snippet("Rational")]
#[snippet(include = "gcd")]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rational {
    pub num: i64,
    pub denom: i64,
}
#[snippet("Rational")]
impl Rational {
    pub fn new(num: i64, denom: i64) -> Self {
        if num == 0 {
            if denom == 0 {
                panic!("0/0 is indefinite.")
            } else {
                Self { num: 0, denom: 1 }
            }
        } else if denom == 0 {
            Self { num: 1, denom: 0 }
        } else {
            let (num, denom) = {
                if denom < 0 {
                    (-num, -denom)
                } else {
                    (num, denom)
                }
            };
            let g = gcd(num.abs(), denom.abs());
            debug_assert!(denom >= 0);
            Self {
                num: num / g,
                denom: denom / g,
            }
        }
    }
    pub fn abs(&self) -> Self {
        if self < &Self::new(0, 1) {
            -*self
        } else {
            *self
        }
    }
}
#[snippet("Rational")]
impl std::ops::AddAssign<Self> for Rational {
    fn add_assign(&mut self, rhs: Self) {
        let d0 = self.denom.abs();
        let d1 = rhs.denom.abs();
        let denom = d0 * (d1 / gcd(d0, d1));
        let n0 = self.num * (denom / d0);
        let n1 = rhs.num * (denom / d1);
        *self = Self::new(n0 + n1, denom);
    }
}
#[snippet("Rational")]
impl std::ops::Add<Self> for Rational {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let mut ret = self;
        ret += rhs;
        ret
    }
}
#[snippet("Rational")]
impl std::ops::SubAssign<Self> for Rational {
    fn sub_assign(&mut self, rhs: Self) {
        *self += Self::new(-rhs.num, rhs.denom);
    }
}
#[snippet("Rational")]
impl std::ops::Sub<Self> for Rational {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let mut ret = self;
        ret -= rhs;
        ret
    }
}
#[snippet("Rational")]
impl std::ops::MulAssign<Self> for Rational {
    fn mul_assign(&mut self, rhs: Self) {
        *self = Self::new(self.num * rhs.num, self.denom * rhs.denom);
    }
}
#[snippet("Rational")]
impl std::ops::Mul<Self> for Rational {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let mut ret = self;
        ret *= rhs;
        ret
    }
}
#[snippet("Rational")]
impl std::ops::DivAssign<Self> for Rational {
    fn div_assign(&mut self, rhs: Self) {
        *self = Self::new(self.num * rhs.denom, rhs.num * self.denom);
    }
}
#[snippet("Rational")]
impl std::ops::Div<Self> for Rational {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        let mut ret = self;
        ret /= rhs;
        ret
    }
}
#[snippet("Rational")]
impl std::ops::Neg for Rational {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self::new(-self.num, self.denom)
    }
}
#[snippet("Rational")]
impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(i64::cmp(
            &(self.num * other.denom),
            &(self.denom * other.num),
        ))
    }
}
#[snippet("Rational")]
impl Ord for Rational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Self::partial_cmp(self, other).unwrap()
    }
}
#[snippet("Rational")]
impl std::fmt::Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.num as f64 / self.denom as f64)
    }
}
#[snippet("Rational")]
impl std::fmt::Debug for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.num as f64 / self.denom as f64)
    }
}
