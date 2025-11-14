use cargo_snippet::snippet;

#[snippet("Matrix")]
#[derive(Clone)]
pub struct Matrix<T> {
    h: usize,
    w: usize,
    vals: Vec<Vec<T>>,
}
#[snippet("Matrix")]
impl<
        T: Clone
            + Copy
            + std::ops::Sub<Output = T>
            + std::ops::Mul
            + std::iter::Sum<<T as std::ops::Mul>::Output>
            + From<u8>,
    > Matrix<T>
{
    pub fn new(h: usize, w: usize) -> Self {
        let zero = T::from(0u8);
        Self {
            h,
            w,
            vals: vec![vec![zero; w]; h],
        }
    }
    pub fn identity(h: usize, w: usize) -> Self {
        let zero = T::from(0u8);
        let one = T::from(1u8);
        debug_assert!(h == w);
        let mut vals = vec![vec![zero; w]; h];
        for (y, line) in vals.iter_mut().enumerate() {
            for (x, val) in line.iter_mut().enumerate() {
                *val = if y == x { one } else { zero };
            }
        }
        Self { h, w, vals }
    }
    pub fn pow(&self, mut p: usize) -> Self {
        let mut ret = Self::identity(self.h, self.w);
        let mut mul = self.clone();
        while p > 0 {
            if p & 1 != 0 {
                ret = ret.clone() * mul.clone();
            }
            p >>= 1;
            mul = mul.clone() * mul.clone();
        }
        ret
    }
}
#[snippet("Matrix")]
impl<T, Idx: std::slice::SliceIndex<[Vec<T>]>> std::ops::Index<Idx> for Matrix<T> {
    type Output = Idx::Output;
    fn index(&self, i: Idx) -> &Self::Output {
        &self.vals[i]
    }
}
#[snippet("Matrix")]
impl<T, Idx: std::slice::SliceIndex<[Vec<T>]>> std::ops::IndexMut<Idx> for Matrix<T> {
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.vals[index]
    }
}
#[snippet("Matrix")]
impl<
        T: Clone
            + Copy
            + std::ops::Sub<Output = T>
            + std::ops::Mul
            + std::iter::Sum<<T as std::ops::Mul>::Output>
            + From<u8>,
    > std::ops::Mul<Matrix<T>> for Matrix<T>
{
    type Output = Matrix<T>;
    fn mul(self, rhs: Matrix<T>) -> Self::Output {
        debug_assert!(self.w == rhs.h);
        let mut ret = Self::new(self.h, rhs.w);
        for y in 0..ret.h {
            for x in 0..ret.w {
                ret[y][x] = (0..self.w).map(|i| self[y][i] * rhs[i][x]).sum::<T>();
            }
        }
        ret
    }
}
#[snippet("Matrix")]
impl<
        T: Clone
            + Copy
            + std::ops::Sub<Output = T>
            + std::ops::Mul
            + std::iter::Sum<<T as std::ops::Mul>::Output>,
    > std::ops::MulAssign<Matrix<T>> for Matrix<T>
{
    fn mul_assign(&mut self, rhs: Matrix<T>) {
        let self0 = self.clone();
        for i in 0..self.h {
            for j in 0..self.w {
                self[i][j] = (0..self.h).map(|k| self0[i][k] * rhs[k][j]).sum::<T>();
            }
        }
    }
}
#[snippet("Matrix")]
impl<T: Clone + Copy + std::ops::Mul + std::iter::Sum<<T as std::ops::Mul>::Output>>
    std::ops::Mul<Vec<T>> for Matrix<T>
{
    type Output = Vec<T>;
    fn mul(self, rhs: Vec<T>) -> Self::Output {
        debug_assert!(self.w == rhs.len());
        (0..self.h)
            .map(|y| (0..self.w).map(|x| self[y][x] * rhs[x]).sum::<T>())
            .collect::<Vec<_>>()
    }
}
#[snippet("Matrix")]
impl<T: Clone + Copy + std::ops::Mul + std::iter::Sum<<T as std::ops::Mul>::Output>>
    std::ops::Mul<Matrix<T>> for Vec<T>
{
    type Output = Vec<T>;
    fn mul(self, rhs: Matrix<T>) -> Self::Output {
        debug_assert!(self.len() == rhs.h);
        (0..rhs.w)
            .map(|x| (0..rhs.h).map(|y| self[y] * rhs[y][x]).sum::<T>())
            .collect::<Vec<_>>()
    }
}
#[snippet("Matrix")]
impl<
        T: Clone
            + Copy
            + std::ops::Add<Output = T>
            + std::ops::Sub<Output = T>
            + std::ops::Mul
            + std::iter::Sum<<T as std::ops::Mul>::Output>
            + From<u8>,
    > std::ops::Add<Matrix<T>> for Matrix<T>
{
    type Output = Matrix<T>;
    fn add(self, rhs: Self) -> Self::Output {
        let mut ret = Matrix::<T>::new(self.h, self.w);
        for y in 0..self.h {
            for x in 0..self.w {
                ret[y][x] = self[y][x] + rhs[y][x];
            }
        }
        ret
    }
}
