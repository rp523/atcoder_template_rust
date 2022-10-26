#![allow(unused_macros, unused_imports, dead_code)]
use proconio::input;
use proconio::marker::{Chars, Usize1};
use std::any::TypeId;
use std::cmp::{max, min, Reverse};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque};
use std::mem::swap;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};

fn main() {
    
}

/*************************************************************************************/
/*************************************************************************************/

macro_rules! dbg {
    ($($xs:expr),+) => {
        if cfg!(debug_assertions) {
            std::dbg!($($xs),+)
        } else {
            ($($xs),+)
        }
    }
}

pub trait ChangeMinMax {
    fn chmin(&mut self, rhs: Self) -> bool;
    fn chmax(&mut self, rhs: Self) -> bool;
}
impl<T: PartialOrd + Copy> ChangeMinMax for T {
    fn chmin(&mut self, rhs: Self) -> bool {
        if *self > rhs {
            *self = rhs;
            true
        } else {
            false
        }
    }
    fn chmax(&mut self, rhs: Self) -> bool {
        if *self < rhs {
            *self = rhs;
            true
        } else {
            false
        }
    }
}

pub trait RepeatedSquaring {
    fn power(self, p: i64) -> Self;
}
impl<T: std::ops::MulAssign + From<usize> + Copy> RepeatedSquaring for T {
    fn power(self, mut p: i64) -> Self {
        #[allow(clippy::eq_op)]
        let mut ret: Self = T::from(1_usize);
        let mut mul: Self = self;
        while p > 0 {
            if p & 1 != 0 {
                ret *= mul;
            }
            p >>= 1;
            mul *= mul;
        }
        ret
    }
}

fn factorial_impl<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T>,
>(
    p: usize,
    memo: &mut Vec<usize>,
    update_op: fn(T, T) -> T,
) -> T {
    while memo.len() < 2_usize {
        memo.push(1_usize);
    }
    while memo.len() <= p + 1 {
        let last_val: T = T::from(*memo.last().unwrap());
        memo.push(update_op(last_val, T::from(memo.len())).into());
    }
    T::from(memo[p])
}

fn factorial<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    p: usize,
) -> T {
    static mut MEMO: Vec<usize> = Vec::<usize>::new();
    unsafe { factorial_impl(p, &mut MEMO, |x: T, y: T| x * y) }
}

fn factorial_inv<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    p: usize,
) -> T {
    static mut MEMO: Vec<usize> = Vec::<usize>::new();
    unsafe { factorial_impl(p, &mut MEMO, |x: T, y: T| x / y) }
}

fn combination<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if k == 0 {
        return T::from(1_usize);
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return (T::from(n) * T::from(n - 1)) / T::from(2);
    }

    if TypeId::of::<mint>() == TypeId::of::<T>() {
        factorial::<T>(n) * factorial_inv::<T>(k) * factorial_inv::<T>(n - k)
    } else {
        factorial::<T>(n) / (factorial::<T>(k) * factorial::<T>(n - k))
    }
}

fn permutation<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if k == 0 {
        return T::from(1_usize);
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return T::from(n) * T::from(n - 1);
    }

    if TypeId::of::<mint>() == TypeId::of::<T>() {
        factorial::<T>(n) * factorial_inv::<T>(n - k)
    } else {
        factorial::<T>(n) / factorial::<T>(n - k)
    }
}

mod union_find {
    #[derive(Clone)]
    pub struct UnionFind {
        pub graph: Vec<Vec<usize>>,
        parents: Vec<usize>,
        grp_sz: Vec<usize>,
        grp_num: usize,
    }

    impl UnionFind {
        pub fn new(sz: usize) -> Self {
            Self {
                graph: vec![vec![]; sz],
                parents: (0..sz).collect::<Vec<usize>>(),
                grp_sz: vec![1; sz],
                grp_num: sz,
            }
        }
        pub fn root(&mut self, v: usize) -> usize {
            if v == self.parents[v] {
                v
            } else {
                self.parents[v] = self.root(self.parents[v]);
                self.parents[v]
            }
        }
        pub fn same(&mut self, a: usize, b: usize) -> bool {
            self.root(a) == self.root(b)
        }
        pub fn unite(&mut self, into: usize, from: usize) {
            self.graph[into].push(from);
            self.graph[from].push(into);
            let r_into = self.root(into);
            let r_from = self.root(from);
            if r_into != r_from {
                self.parents[r_from] = r_into;
                self.grp_sz[r_into] += self.grp_sz[r_from];
                self.grp_sz[r_from] = 0;
                self.grp_num -= 1;
            }
        }
        pub fn group_num(&self) -> usize {
            self.grp_num
        }
        pub fn group_size(&mut self, a: usize) -> usize {
            let ra = self.root(a);
            self.grp_sz[ra]
        }
    }
}
use union_find::UnionFind;

mod segment_tree {
    #[derive(Clone)]
    pub struct SegmentTree<T> {
        n2: usize,   // implemented leaf num (2^n)
        neff: usize, // effective vector length
        dat: Vec<T>,
        pair_op: fn(T, T) -> T,
    }
    impl<T: Copy> SegmentTree<T> {
        pub fn new(n: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut s = Self {
                n2,
                neff: n,
                pair_op,
                dat: vec![ini_val; 2 * n2 - 1],
            };

            for i in 0..n {
                s.set(i, ini_val);
            }
            s
        }
        pub fn new_from(pair_op: fn(T, T) -> T, ini_values: &Vec<T>) -> Self {
            let n = ini_values.len();
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut st = Self {
                n2,
                neff: n,
                pair_op,
                dat: vec![ini_values[0]; 2 * n2 - 1],
            };

            for (i, ini_val) in ini_values.iter().enumerate() {
                st.set(i, *ini_val);
            }
            st
        }
        pub fn set(&mut self, mut pos: usize, val: T) {
            pos += self.n2 - 1;
            self.dat[pos] = val;
            while pos > 0 {
                pos = (pos - 1) / 2; // parent
                self.dat[pos] = (self.pair_op)(self.dat[pos * 2 + 1], self.dat[pos * 2 + 2]);
            }
        }
        pub fn get(&self, pos: usize) -> T {
            self.dat[pos + self.n2 - 1]
        }
        // get query value of [a, b]
        pub fn query(&self, a: usize, b: usize) -> T {
            self.query_sub(a, b + 1, 0, 0, self.n2)
        }
        // get query value of [a, b)
        fn query_sub(&self, a: usize, b: usize, node: usize, node_l: usize, node_r: usize) -> T {
            if (node_r <= a) || (b <= node_l) {
                panic!("invalid query range, ({a}, {b})");
            } else if (a <= node_l) && (node_r <= b) {
                // this not is covered by given interval.
                self.dat[node]
            } else if a < (node_l + node_r) / 2 {
                let vl = self.query_sub(a, b, node * 2 + 1, node_l, (node_l + node_r) / 2);
                if (node_l + node_r) / 2 < b {
                    let vr = self.query_sub(a, b, node * 2 + 2, (node_l + node_r) / 2, node_r);
                    (self.pair_op)(vl, vr)
                } else {
                    vl
                }
            } else if (node_l + node_r) / 2 < b {
                self.query_sub(a, b, node * 2 + 2, (node_l + node_r) / 2, node_r)
            } else {
                panic!("invalid query range, ({a}, {b})");
            }
        }
    }
}
use segment_tree::SegmentTree;

mod lazy_segment_tree {
    pub struct LazySegmentTree<X, M> {
        // https://algo-logic.info/segment-tree/#toc_id_3
        n2: usize,                    // num of node(integer power of 2)
        pair_op: fn(X, X) -> X,       // node_val x node_val -> node_val
        update_op: fn(X, M) -> X,     // node_val x update_val -> node
        update_concat: fn(M, M) -> M, // update_val x update_val -> update_val
        dat: Vec<X>,                  // node values
        lazy_ops: Vec<Option<M>>,     // reserved operations
        built: bool,
    }
    impl<X: Copy, M: Copy> LazySegmentTree<X, M> {
        pub fn new(
            n: usize,
            pair_op: fn(X, X) -> X,
            update_op: fn(X, M) -> X,
            update_concat: fn(M, M) -> M,
            ini_val: X,
        ) -> Self {
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut ret = Self {
                n2,
                pair_op,
                update_op,
                update_concat,
                dat: vec![ini_val; n * 4],
                lazy_ops: vec![None; n * 4],
                built: false,
            };
            ret.init_all(ini_val);
            ret
        }
        pub fn new_from(
            n: usize,
            pair_op: fn(X, X) -> X,
            update_op: fn(X, M) -> X,
            update_concat: fn(M, M) -> M,
            init_vals: &[X],
        ) -> Self {
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut ret = Self {
                n2,
                pair_op,
                update_op,
                update_concat,
                dat: vec![init_vals[0]; n * 4],
                lazy_ops: vec![None; n * 4],
                built: false,
            };
            for (i, init_val) in init_vals.iter().enumerate() {
                ret.set(i, *init_val);
            }
            ret
        }
        pub fn query(&mut self, a: usize, b: usize) -> X // closed interval
        {
            self.query_sub(a, b + 1, 0, 0, self.n2) // half_open interval
        }
        pub fn reserve(&mut self, a: usize, b: usize, m: M) // closed interval
        {
            self.reserve_sub(a, b + 1, m, 0, 0, self.n2); // half_open interval
        }
        pub fn set(&mut self, i: usize, val: X) {
            self.dat[i + self.n2 - 1] = val;
        }
        fn init_all(&mut self, ini_val: X) {
            for i in 0..self.n2 {
                self.set(i, ini_val);
            }
        }
        fn build(&mut self) {
            for k in (0..=(self.n2 - 2)).rev() {
                self.dat[k] = (self.pair_op)(self.dat[2 * k + 1], self.dat[2 * k + 2]);
            }
        }
        fn lazy_eval(&mut self, node: usize) {
            if !self.built {
                self.build();
                self.built = true;
            }
            if let Some(lazy_val) = self.lazy_ops[node] {
                if node < self.n2 - 1 {
                    // 葉でなければ子に伝搬
                    for d in 1..=2_usize {
                        let nc = node * 2 + d;
                        if let Some(nc_lazy_val) = self.lazy_ops[nc] {
                            self.lazy_ops[nc] = Some((self.update_concat)(nc_lazy_val, lazy_val));
                        } else {
                            self.lazy_ops[nc] = Some(lazy_val);
                        }
                    }
                }
                // 自身を更新
                self.dat[node] = (self.update_op)(self.dat[node], lazy_val);
                self.lazy_ops[node] = None;
            }
        }
        fn reserve_sub(
            &mut self,
            a: usize,
            b: usize,
            m: M,
            node: usize,
            node_l: usize,
            node_r: usize,
        ) {
            self.lazy_eval(node);
            if (a <= node_l) && (node_r <= b) {
                // 完全に内側の時
                if let Some(lazy_val) = self.lazy_ops[node] {
                    self.lazy_ops[node] = Some((self.update_concat)(lazy_val, m));
                } else {
                    self.lazy_ops[node] = Some(m);
                }
                self.lazy_eval(node);
            } else if (a < node_r) && (node_l < b) {
                // 一部区間が被る時
                self.reserve_sub(a, b, m, node * 2 + 1, node_l, (node_l + node_r) / 2); // 左の子
                self.reserve_sub(a, b, m, node * 2 + 2, (node_l + node_r) / 2, node_r); // 右の子
                self.dat[node] = (self.pair_op)(self.dat[node * 2 + 1], self.dat[node * 2 + 2]);
            }
        }
        fn query_sub(
            &mut self,
            a: usize,
            b: usize,
            node: usize,
            node_l: usize,
            node_r: usize,
        ) -> X {
            self.lazy_eval(node);
            if (a <= node_l) && (node_r <= b) {
                // this node is inside query range.
                self.dat[node]
            } else if (node_r > a) && (b > node_l) {
                // this node and query range overlap partly.
                let n0 = node * 2 + 1;
                let l0 = node_l;
                let r0 = (node_l + node_r) / 2;
                let n1 = node * 2 + 2;
                let l1 = (node_l + node_r) / 2;
                let r1 = node_r;
                if (a < r0) && (l0 < b) {
                    if (a < r1) && (l1 < b) {
                        (self.pair_op)(
                            self.query_sub(a, b, n0, l0, r0),
                            self.query_sub(a, b, n1, l1, r1),
                        )
                    } else {
                        self.query_sub(a, b, n0, l0, r0)
                    }
                } else if (a < r1) && (l1 < b) {
                    self.query_sub(a, b, n1, l1, r1)
                } else {
                    panic!("invalid arg range {}, {}", a, b);
                }
            } else {
                panic!(
                    "this node and query range have no common area, {}, {}",
                    a, b
                );
            }
        }
    }
}
use lazy_segment_tree::LazySegmentTree;

mod modint {
    use std::fmt;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};
    static mut MOD: i64 = 2;

    #[derive(Clone, Copy)]
    pub struct ModInt {
        x: i64,
    }
    impl ModInt {
        pub fn set_prime(val: i64) {
            unsafe {
                MOD = val;
            }
        }
        fn get_prime() -> i64 {
            unsafe { MOD }
        }
        pub fn new(sig: i64) -> Self {
            if sig < 0 {
                Self {
                    x: sig % Self::get_prime() + Self::get_prime(),
                }
            } else {
                Self {
                    x: sig % Self::get_prime(),
                }
            }
        }
        pub fn get(&self) -> i64 {
            self.x
        }
        fn inverse(&self) -> Self {
            // [Fermat's little theorem]
            // when p is prime number, a^(p-1) = 1
            let mut ret = Self { x: 1 };
            let mut mul: Self = Self { x: self.get() };
            let mut p = Self::get_prime() - 2;
            while p > 0 {
                if p & 1 != 0 {
                    ret *= mul;
                }
                p >>= 1;
                mul *= mul;
            }
            ret
        }
    }
    impl AddAssign<Self> for ModInt {
        fn add_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x + rhs.get());
        }
    }
    impl AddAssign<i64> for ModInt {
        fn add_assign(&mut self, rhs: i64) {
            *self = ModInt::new(self.x + rhs);
        }
    }
    impl Add<ModInt> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x + rhs.get())
        }
    }
    impl Add<i64> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: i64) -> Self::Output {
            ModInt::new(self.x + rhs)
        }
    }
    impl Add<ModInt> for i64 {
        type Output = ModInt;
        fn add(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self + rhs.get())
        }
    }
    impl SubAssign<Self> for ModInt {
        fn sub_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x - rhs.get());
        }
    }
    impl SubAssign<i64> for ModInt {
        fn sub_assign(&mut self, rhs: i64) {
            *self = ModInt::new(self.x - rhs);
        }
    }
    impl Sub<ModInt> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x - rhs.get())
        }
    }
    impl Sub<i64> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: i64) -> Self::Output {
            ModInt::new(self.x - rhs)
        }
    }
    impl Sub<ModInt> for i64 {
        type Output = ModInt;
        fn sub(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self - rhs.get())
        }
    }
    impl MulAssign<Self> for ModInt {
        fn mul_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x * rhs.get());
        }
    }
    impl MulAssign<i64> for ModInt {
        fn mul_assign(&mut self, rhs: i64) {
            *self = ModInt::new(self.x * rhs);
        }
    }
    impl Mul<ModInt> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x * rhs.get())
        }
    }
    impl Mul<i64> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: i64) -> Self::Output {
            ModInt::new(self.x * rhs)
        }
    }
    impl Mul<ModInt> for i64 {
        type Output = ModInt;
        fn mul(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self * rhs.get())
        }
    }
    impl DivAssign<Self> for ModInt {
        fn div_assign(&mut self, rhs: Self) {
            *self = *self / rhs;
        }
    }
    impl DivAssign<i64> for ModInt {
        fn div_assign(&mut self, rhs: i64) {
            *self = *self / ModInt::new(rhs);
        }
    }
    impl Div<ModInt> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: Self) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * rhs.inverse().get())
        }
    }
    impl Div<i64> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: i64) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * ModInt::new(rhs).inverse().get())
        }
    }
    impl Div<ModInt> for i64 {
        type Output = ModInt;
        fn div(self, rhs: ModInt) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self * rhs.inverse().get())
        }
    }
    impl From<usize> for ModInt {
        fn from(x: usize) -> Self {
            ModInt::new(x as i64)
        }
    }
    #[allow(clippy::from_over_into)]
    impl Into<usize> for ModInt {
        fn into(self) -> usize {
            self.x as usize
        }
    }
    impl fmt::Display for ModInt {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.x)
        }
    }
}
use modint::ModInt as mint;

pub trait ToPrimes {
    fn to_primes(&self) -> BTreeMap<Self, usize>
    where
        Self: Sized;
}
impl<T: Copy + Ord + From<i32> + AddAssign + DivAssign + Mul<Output = T> + Rem<Output = T>> ToPrimes
    for T
{
    fn to_primes(&self) -> BTreeMap<T, usize> // O(N^0.5 x logN)
    {
        let zero = T::from(0_i32);
        let one = T::from(1_i32);
        let mut n = *self;
        let mut ans = BTreeMap::<T, usize>::new();
        {
            let mut i = T::from(2_i32);
            while i * i <= n {
                while n % i == zero {
                    let v = ans.entry(i).or_insert(0_usize);
                    *v += 1_usize;
                    n /= i;
                }
                i += one;
            }
        }
        if n != one {
            let v = ans.entry(n).or_insert(0);
            *v += 1_usize;
        }
        ans
    }
}

pub trait ToDivisors {
    fn to_divisors(&self) -> Vec<Self>
    where
        Self: Sized;
}
impl<
        T: Copy + Ord + Div<Output = T> + From<i32> + Mul<Output = T> + Rem<Output = T> + AddAssign,
    > ToDivisors for T
{
    fn to_divisors(&self) -> Vec<T> // O(N^0.5)
    {
        let zero = T::from(0_i32);
        let one = T::from(1_i32);
        let n = *self;
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
}

pub trait CoordinateCompress {
    fn compress(self) -> Vec<usize>;
}
impl<T: Copy + Ord> CoordinateCompress for Vec<T> {
    fn compress(self) -> Vec<usize> {
        let mut keys = BTreeSet::<T>::new();
        for x in self.iter() {
            keys.insert(*x);
        }
        let mut dict = BTreeMap::<T, usize>::new();
        for (i, key) in keys.into_iter().enumerate() {
            dict.insert(key, i);
        }
        self.into_iter().map(|x| dict[&x]).collect::<Vec<usize>>()
    }
}

mod xor_shift_64 {
    pub struct XorShift64(u64);
    impl XorShift64 {
        pub fn new() -> Self {
            XorShift64(
                88172645463325252_u64
            )
        }
        pub fn next_u64(&mut self) -> u64
        {
            self.0 = self.0 ^ (self.0 << 7);
            self.0 = self.0 ^ (self.0 >> 9);
            self.0
        }
        pub fn next_f64(&mut self) -> f64
        {
            self.0 = self.0 ^ (self.0 << 7);
            self.0 = self.0 ^ (self.0 >> 9);
            self.0 as f64 * 5.421_010_862_427_522e-20
        }
    }
}
use xor_shift_64::XorShift64;