#![allow(unused_macros, unused_imports, dead_code)]
use fixedbitset::FixedBitSet;
use ordered_float::OrderedFloat;
use permutohedron::LexicalPermutation;
use proconio::fastout;
use std::any::TypeId;
use std::cmp::{max, min, Ordering, Reverse};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::mem::swap;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use std::time::Instant;

macro_rules! __debug_impl {
    ($x:expr) => {
        eprint!("{}={:?}  ", stringify!($x), &$x);
    };
    ($x:expr, $($y:expr),+) => (
        __debug_impl!($x);
        __debug_impl!($($y),+);
    );
}
macro_rules! __debug_line {
    () => {
        eprint!("L{}  ", line!());
    };
}
macro_rules! __debug_select {
    () => {
        eprintln!();
    };
    ($x:expr) => {
        __debug_line!();
        __debug_impl!($x);
        eprintln!();
    };
    ($x:expr, $($y:expr),+) => (
        __debug_line!();
        __debug_impl!($x);
        __debug_impl!($($y),+);
        eprintln!();
    );
}
macro_rules! debug {
    () => {
        if cfg!(debug_assertions) {
            __debug_select!();
        }
    };
    ($($xs:expr),+) => {
        if cfg!(debug_assertions) {
            __debug_select!($($xs),+);
        }
    };
}

mod change_min_max {
    pub trait ChangeMinMax<T> {
        fn chmin(&mut self, rhs: T) -> bool;
        fn chmax(&mut self, rhs: T) -> bool;
    }
    impl<T: PartialOrd> ChangeMinMax<T> for T {
        #[inline(always)]
        fn chmin(&mut self, rhs: T) -> bool {
            if *self > rhs {
                *self = rhs;
                true
            } else {
                false
            }
        }
        #[inline(always)]
        fn chmax(&mut self, rhs: T) -> bool {
            if *self < rhs {
                *self = rhs;
                true
            } else {
                false
            }
        }
    }
    impl<T: Clone + PartialOrd> ChangeMinMax<T> for Option<T> {
        #[inline(always)]
        fn chmin(&mut self, rhs: T) -> bool {
            if let Some(val) = self.clone() {
                if val > rhs {
                    *self = Some(rhs);
                    true
                } else {
                    false
                }
            } else {
                *self = Some(rhs);
                true
            }
        }
        #[inline(always)]
        fn chmax(&mut self, rhs: T) -> bool {
            if let Some(val) = self.clone() {
                if val < rhs {
                    *self = Some(rhs);
                    true
                } else {
                    false
                }
            } else {
                *self = Some(rhs);
                true
            }
        }
    }
}
use change_min_max::ChangeMinMax;

mod lazy_segment_tree {
    #[derive(Clone)]
    pub struct LazySegmentTree<X, M> {
        n: usize,
        n2: usize,
        height: usize,
        width: Vec<usize>,
        pair_op: fn(X, X) -> X,
        update_op: fn(X, M) -> X,
        update_concat: fn(M, M) -> M,
        dat: Vec<X>,
        lazy_ops: Vec<Option<M>>,
    }
    impl<X: Clone, M: Clone> LazySegmentTree<X, M> {
        pub fn from_vec(
            pair_op: fn(X, X) -> X,
            update_op: fn(X, M) -> X,
            update_concat: fn(M, M) -> M,
            ini_vals: Vec<X>,
        ) -> Self {
            let n = ini_vals.len();
            let mut n2 = 1;
            let mut height = 1;
            while n2 < n {
                n2 *= 2;
                height += 1;
            }
            let width = (0..height)
                .scan(2 * n, |cum, _| {
                    *cum = (*cum).div_ceil(2);
                    Some(*cum)
                })
                .collect::<Vec<_>>();
            let mut dat = vec![ini_vals[0].clone(); n2 + n];
            dat.iter_mut()
                .skip(n2)
                .zip(ini_vals)
                .for_each(|(dat, ini)| {
                    *dat = ini;
                });
            for hi in 1..height {
                let beg = n2 >> hi;
                let cend = (n2 >> (hi - 1)) + width[hi - 1];
                for p in (beg..).take(width[hi]) {
                    let l = p * 2;
                    let r = l + 1;
                    dat[p] = if r < cend {
                        pair_op(dat[l].clone(), dat[r].clone())
                    } else {
                        dat[l].clone()
                    };
                }
            }
            let lazy_ops = vec![None; n2];
            Self {
                n,
                n2,
                height,
                width,
                pair_op,
                update_op,
                update_concat,
                dat,
                lazy_ops,
            }
        }
        #[inline(always)]
        fn eval_down(&mut self, hi: usize, v: usize) {
            if hi == 0 {
                // bottom
                return;
            }
            // not bottom, has childs.
            let Some(lazy) = self.lazy_ops[v].clone() else {
                return;
            };
            self.lazy_ops[v] = None;
            let x0 = self.dat[v].clone();
            self.dat[v] = (self.update_op)(x0, lazy.clone());
            let l = v * 2;
            let r = l + 1;
            let cend = (self.n2 >> (hi - 1)) + self.width[hi - 1];
            if l < self.n2 {
                self.lazy_ops[l] = if let Some(m0) = self.lazy_ops[l].clone() {
                    Some((self.update_concat)(m0, lazy.clone()))
                } else if l < cend {
                    Some(lazy.clone())
                } else {
                    None
                };
                self.lazy_ops[r] = if let Some(m0) = self.lazy_ops[r].clone() {
                    Some((self.update_concat)(m0, lazy))
                } else if r < cend {
                    Some(lazy)
                } else {
                    None
                };
            } else {
                // bottom, no childs.
                if l < self.n2 + self.n {
                    self.dat[l] = (self.update_op)(self.dat[l].clone(), lazy.clone());
                    if r < self.n2 + self.n {
                        self.dat[r] = (self.update_op)(self.dat[r].clone(), lazy);
                    }
                }
            }
        }
        #[inline(always)]
        fn sum_up(&mut self, hi: usize, v: usize) {
            if hi == 0 {
                return;
            }
            self.eval_down(hi, v);
            let l = v * 2;
            let r = l + 1;
            if hi > 0 {
                self.eval_down(hi - 1, l);
                self.eval_down(hi - 1, r);
            }
            let cend = (self.n2 >> (hi - 1)) + self.width[hi - 1];
            self.dat[v] = if l < cend {
                if r < cend {
                    (self.pair_op)(self.dat[l].clone(), self.dat[r].clone())
                } else {
                    self.dat[l].clone()
                }
            } else {
                self.dat[r].clone()
            };
        }
        pub fn get(&mut self, mut i: usize) -> X {
            i += self.n2;
            for hi in (0..self.height).rev() {
                self.eval_down(hi, i >> hi);
            }
            self.dat[i].clone()
        }
        pub fn set(&mut self, mut i: usize, x: X) {
            i += self.n2;
            for hi in (0..self.height).rev() {
                self.eval_down(hi, i >> hi);
            }
            self.dat[i] = x;
            for hi in 0..self.height {
                self.sum_up(hi, i >> hi);
            }
        }
        pub fn query(&mut self, mut l: usize, mut r: usize) -> X {
            l += self.n2;
            r += self.n2 + 1;
            for hi in (0..self.height).rev() {
                self.eval_down(hi, l >> hi);
                self.eval_down(hi, (r - 1) >> hi);
            }
            let mut lcum = None;
            let mut rcum = None;
            for hi in 0..self.height {
                let end = (self.n2 >> hi) + self.width[hi];
                if l % 2 == 1 {
                    debug_assert!(l < end);
                    self.eval_down(hi, l);
                    lcum = if let Some(lv) = lcum {
                        Some((self.pair_op)(lv, self.dat[l].clone()))
                    } else {
                        Some(self.dat[l].clone())
                    };
                    l += 1;
                }
                if r % 2 == 1 {
                    r -= 1;
                    debug_assert!(r < end);
                    self.eval_down(hi, r);
                    rcum = if let Some(rv) = rcum {
                        Some((self.pair_op)(self.dat[r].clone(), rv))
                    } else {
                        Some(self.dat[r].clone())
                    };
                }
                l /= 2;
                r /= 2;
                if l >= r {
                    break;
                }
            }
            if let Some(lcum) = lcum {
                if let Some(rcum) = rcum {
                    (self.pair_op)(lcum, rcum)
                } else {
                    lcum
                }
            } else {
                rcum.unwrap()
            }
        }
        pub fn reserve(&mut self, mut l: usize, mut r: usize, m: M) {
            if l > r {
                debug_assert!(false);
                return;
            }
            l += self.n2;
            r += self.n2 + 1;
            for hi in (0..self.height).rev() {
                self.eval_down(hi, l >> hi);
                self.eval_down(hi, (r - 1) >> hi);
            }
            {
                let (mut l2, mut r2) = (l, r);
                for hi in 0..self.height {
                    if l2 % 2 == 1 {
                        debug_assert!(l2 < (self.n2 >> hi) + self.width[hi]);
                        if hi > 0 {
                            self.eval_down(hi, l2);
                            self.lazy_ops[l2] = Some(m.clone());
                        } else {
                            self.dat[l2] = (self.update_op)(self.dat[l2].clone(), m.clone());
                        }
                        l2 += 1;
                    }
                    if r2 % 2 == 1 {
                        r2 -= 1;
                        debug_assert!(r2 < (self.n2 >> hi) + self.width[hi]);
                        if hi > 0 {
                            self.eval_down(hi, r2);
                            self.lazy_ops[r2] = Some(m.clone());
                        } else {
                            self.dat[r2] = (self.update_op)(self.dat[r2].clone(), m.clone());
                        }
                    }
                    l2 /= 2;
                    r2 /= 2;
                    if l2 >= r2 {
                        break;
                    }
                }
            }
            for hi in 0..self.height {
                self.sum_up(hi, l >> hi);
                self.sum_up(hi, (r - 1) >> hi);
            }
        }
        pub fn right_rise(&mut self, l: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            self.right_fall(l, |x| !jdg(x))
        }
        pub fn right_fall(&mut self, l: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            let mut v = l + self.n2;
            for hi in (1..self.height).rev() {
                self.eval_down(hi, v >> hi);
            }
            if !jdg(self.dat[v].clone()) {
                return Some(l);
            }
            if jdg(self.query(l, self.n - 1)) {
                return None;
            }
            let mut true_fix = None;
            let mut hi = 0;
            while hi < self.height {
                self.eval_down(hi, v);
                let ev = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(true_fix, self.dat[v].clone())
                } else {
                    self.dat[v].clone()
                };
                if !jdg(ev.clone()) {
                    break;
                }
                if v & 1 != 0 {
                    v += 1;
                    true_fix = Some(ev);
                }
                while v & 1 == 0 {
                    v /= 2;
                    hi += 1;
                }
            }
            while hi > 0 {
                let lc = v * 2;
                let rc = lc + 1;
                self.eval_down(hi - 1, lc);
                let ev_lc = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(true_fix, self.dat[lc].clone())
                } else {
                    self.dat[lc].clone()
                };
                if !jdg(ev_lc.clone()) {
                    v = lc;
                } else {
                    self.eval_down(hi - 1, rc);
                    v = rc;
                    true_fix = Some(ev_lc);
                }
                hi -= 1;
            }
            Some(v - self.n2)
        }
        pub fn left_rise(&mut self, r: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            self.left_fall(r, |x| !jdg(x))
        }
        pub fn left_fall(&mut self, r: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            let mut v = r + self.n2 + 1;
            for hi in (1..self.height).rev() {
                self.eval_down(hi, (v - 1) >> hi);
            }
            if !jdg(self.dat[v - 1].clone()) {
                return Some(r);
            }
            if jdg(self.query(0, r)) {
                return None;
            }
            let mut true_fix = None;
            let mut hi = 0;
            while hi < self.height {
                self.eval_down(hi, v - 1);
                let ev = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(self.dat[v - 1].clone(), true_fix)
                } else {
                    self.dat[v - 1].clone()
                };
                if !jdg(ev.clone()) {
                    break;
                }
                if v & 1 != 0 {
                    v -= 1;
                    true_fix = Some(ev);
                }
                while v & 1 == 0 {
                    v /= 2;
                    hi += 1;
                }
            }
            while hi > 0 {
                let lc = (v - 1) * 2;
                let rc = lc + 1;
                self.eval_down(hi - 1, rc);
                let ev_rc = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(self.dat[rc].clone(), true_fix)
                } else {
                    self.dat[rc].clone()
                };
                if !jdg(ev_rc.clone()) {
                    v = rc + 1;
                } else {
                    self.eval_down(hi - 1, lc);
                    v = lc + 1;
                    true_fix = Some(ev_rc);
                }
                hi -= 1;
            }
            Some(v - self.n2 - 1)
        }
        pub fn right_true_max(&mut self, l: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            if let Some(r) = self.right_fall(l, jdg) {
                if l == r {
                    None
                } else {
                    Some(r - 1)
                }
            } else {
                Some(self.n - 1)
            }
        }
        pub fn right_false_max(&mut self, l: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            if let Some(r) = self.right_rise(l, jdg) {
                if l == r {
                    None
                } else {
                    Some(r - 1)
                }
            } else {
                Some(self.n - 1)
            }
        }
        pub fn left_true_max(&mut self, r: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            if let Some(l) = self.left_fall(r, jdg) {
                if l == r {
                    None
                } else {
                    Some(l + 1)
                }
            } else {
                Some(0)
            }
        }
        pub fn left_false_max(&mut self, r: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            if let Some(l) = self.left_rise(r, jdg) {
                if l == r {
                    None
                } else {
                    Some(l + 1)
                }
            } else {
                Some(0)
            }
        }
        fn fmt_base(
            &self,
            f: &mut std::fmt::Formatter,
            x_to_string: fn(&X) -> String,
            m_to_string: fn(&M) -> String,
        ) -> std::fmt::Result {
            let mut now = 1;
            let mut delta = 1;
            for hi in (0..self.height).rev() {
                for x in (now..).take(self.width[hi]) {
                    write!(
                        f,
                        "{}{} ",
                        x_to_string(&self.dat[x]),
                        if x < self.lazy_ops.len() {
                            if let Some(l) = &self.lazy_ops[x] {
                                m_to_string(l)
                            } else {
                                String::new()
                            }
                        } else {
                            String::new()
                        }
                    )?;
                }
                writeln!(f)?;
                now += delta;
                delta *= 2;
            }
            Ok(())
        }
    }
    impl<X: Clone + std::fmt::Display, M: Clone + std::fmt::Display> std::fmt::Display
        for LazySegmentTree<X, M>
    {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            self.fmt_base(f, |x: &X| format!("{}", x), |m: &M| format!("{}", m))
        }
    }
    impl<X: Clone + std::fmt::Debug, M: Clone + std::fmt::Debug> std::fmt::Debug
        for LazySegmentTree<X, M>
    {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            self.fmt_base(f, |x: &X| format!("{:?}", x), |m: &M| format!("{:?}", m))
        }
    }
    #[cfg(test)]
    mod test {
        use super::LazySegmentTree;
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaChaRng;
        #[test]
        fn random() {
            const N: usize = 100;
            const T: usize = 1000;
            let mut rng = ChaChaRng::from_seed([0; 32]);
            for n in 1..=N {
                let mut a = (0..n).map(|_| rng.random_range(0..2)).collect::<Vec<_>>();
                #[derive(Clone, Debug)]
                struct Node {
                    n0: usize,
                    n1: usize,
                    inner_swap: usize,
                }
                let mut seg = LazySegmentTree::<Node, bool>::from_vec(
                    |x, y| {
                        let n0 = x.n0 + y.n0;
                        let n1 = x.n1 + y.n1;
                        let inner_swap = x.inner_swap + y.inner_swap + x.n1 * y.n0;
                        Node { n0, n1, inner_swap }
                    },
                    |x, b| {
                        if !b {
                            return x;
                        }
                        let tot = x.n0 + x.n1;
                        let n0 = x.n1;
                        let n1 = x.n0;
                        let mut inner_swap = (tot * (tot - 1)) / 2;
                        inner_swap -= if n0 == 0 { 0 } else { (n0 * (n0 - 1)) / 2 };
                        inner_swap -= if n1 == 0 { 0 } else { (n1 * (n1 - 1)) / 2 };
                        inner_swap -= x.inner_swap;
                        Node { n0, n1, inner_swap }
                    },
                    |b0, b1| (b0 != b1),
                    a.iter()
                        .map(|&a| {
                            if a == 0 {
                                Node {
                                    n0: 1,
                                    n1: 0,
                                    inner_swap: 0,
                                }
                            } else {
                                Node {
                                    n0: 0,
                                    n1: 1,
                                    inner_swap: 0,
                                }
                            }
                        })
                        .collect::<Vec<_>>(),
                );
                for _ in 0..T {
                    let mut l = rng.random_range(0..n);
                    let mut r = rng.random_range(0..n);
                    if l >= r {
                        std::mem::swap(&mut l, &mut r);
                    }
                    let op = rng.random_range(0..2);
                    if op == 0 {
                        seg.reserve(l, r, true);
                        a.iter_mut().take(r + 1).skip(l).for_each(|a| {
                            *a = 1 - *a;
                        });
                    } else {
                        let actual = seg.query(l, r).inner_swap;
                        let mut cnt = vec![0; 2];
                        let mut expected = 0;
                        for i in l..=r {
                            if a[i] == 0 {
                                expected += cnt[1];
                            }
                            cnt[a[i]] += 1;
                        }
                        assert_eq!(expected, actual);
                    }
                }
            }
        }
        #[test]
        fn binary_search() {
            const NMAX: usize = 100;
            const T: usize = 100;
            const OP: usize = 1000;
            const V: usize = 10;
            let mut rng = ChaChaRng::from_seed([0; 32]);
            for n in 1..=NMAX {
                for _ in 0..T {
                    let mut a = (0..n).map(|_| rng.random_range(0..V)).collect::<Vec<_>>();
                    let mut seg = LazySegmentTree::<(usize, usize), usize>::from_vec(
                        |x, y| (x.0 + y.0, x.1 + y.1),
                        |x, m| (x.0 + x.1 * m, x.1),
                        |m0, m1| m0 + m1,
                        a.iter().map(|&a| (a, 1)).collect::<Vec<_>>(),
                    );
                    let mut ops = vec![];
                    for _ in 0..OP {
                        let mut l = rng.random_range(0..n);
                        let mut r = rng.random_range(0..n);
                        if l > r {
                            (l, r) = (r, l);
                        }
                        let op = rng.random_range(0..3);
                        let v = rng.random_range(0..V);
                        ops.push((op, l, r, v));
                        match op {
                            0 => {
                                (l..=r).for_each(|i| {
                                    a[i] += v;
                                });
                                seg.reserve(l, r, v);
                            }
                            1 => {
                                let mut expected_fall = None;
                                let mut cum = 0;
                                for i in l..n {
                                    cum += a[i];
                                    if cum >= v {
                                        expected_fall = Some(i);
                                        break;
                                    }
                                }
                                assert_eq!(expected_fall, seg.right_fall(l, |(x, _)| x < v));
                                assert_eq!(expected_fall, seg.right_rise(l, |(x, _)| x >= v));
                            }
                            2 => {
                                let mut expected_fall = None;
                                let mut cum = 0;
                                for i in (0..=r).rev() {
                                    cum += a[i];
                                    if cum >= v {
                                        expected_fall = Some(i);
                                        break;
                                    }
                                }
                                assert_eq!(expected_fall, seg.left_fall(r, |(x, _)| x < v));
                                assert_eq!(expected_fall, seg.left_rise(r, |(x, _)| x >= v));
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }
    }
}
use lazy_segment_tree::LazySegmentTree;

mod integer_operation {
    use std::collections::BTreeMap;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem};
    pub trait IntegerOperation {
        fn into_primes(self) -> BTreeMap<Self, usize>
        where
            Self: Sized;
        fn into_divisors(self) -> Vec<Self>
        where
            Self: Sized;
        fn squared_length(&self, rhs: Self) -> Self;
        fn is_prime(&self) -> bool;
    }
    impl<
            T: Copy
                + Ord
                + AddAssign
                + MulAssign
                + DivAssign
                + Add<Output = T>
                + Mul<Output = T>
                + Div<Output = T>
                + Rem<Output = T>
                + From<u8>,
        > IntegerOperation for T
    {
        fn into_primes(self) -> BTreeMap<T, usize> // O(N^0.5 x logN)
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
            let mut ans = BTreeMap::new();
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
}
use integer_operation::IntegerOperation;

pub trait CoordinateCompress<T> {
    fn compress_encoder(&self) -> HashMap<T, usize>;
    fn compress_decoder(&self) -> Vec<T>;
    fn compress(self) -> Vec<usize>;
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for Vec<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = BTreeSet::new();
        for &x in self.iter() {
            dict.insert(x);
        }
        let mut ret = HashMap::new();
        for (i, value) in dict.into_iter().enumerate() {
            ret.insert(value, i);
        }
        ret
    }
    fn compress_decoder(&self) -> Vec<T> {
        let mut keys = BTreeSet::<T>::new();
        for &x in self.iter() {
            keys.insert(x);
        }
        keys.into_iter().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        let dict = self.compress_encoder();
        self.into_iter().map(|x| dict[&x]).collect::<Vec<usize>>()
    }
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for BTreeSet<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = HashMap::new();
        for (i, &key) in self.iter().enumerate() {
            dict.insert(key, i);
        }
        dict
    }
    fn compress_decoder(&self) -> Vec<T> {
        self.iter().copied().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        (0..self.len()).collect::<Vec<usize>>()
    }
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for HashSet<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = BTreeSet::new();
        for &x in self.iter() {
            dict.insert(x);
        }
        let mut ret = HashMap::new();
        for (i, value) in dict.into_iter().enumerate() {
            ret.insert(value, i);
        }
        ret
    }
    fn compress_decoder(&self) -> Vec<T> {
        let mut keys = BTreeSet::<T>::new();
        for &x in self.iter() {
            keys.insert(x);
        }
        keys.into_iter().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        let dict = self.compress_encoder();
        self.into_iter().map(|x| dict[&x]).collect::<Vec<usize>>()
    }
}

mod xor_shift_64 {
    pub struct XorShift64(usize);
    impl XorShift64 {
        pub fn new() -> Self {
            Self(88172645463325252_usize)
        }
        fn next(&mut self) {
            self.0 ^= self.0 << 7;
            self.0 ^= self.0 >> 9;
        }
        pub fn next_usize(&mut self) -> usize {
            self.next();
            self.0
        }
        pub fn next_f64(&mut self) -> f64 {
            self.next();
            self.0 as f64 * 5.421_010_862_427_522e-20
        }
    }
    pub trait Shuffle {
        fn shuffle(&mut self, rand: &mut XorShift64);
    }
    impl<T> Shuffle for Vec<T> {
        fn shuffle(&mut self, rand: &mut XorShift64) {
            let n = self.len();
            for i in (1..n).rev() {
                let j = rand.next_usize() % (i + 1);
                self.swap(i, j);
            }
        }
    }
}
use xor_shift_64::{Shuffle, XorShift64};

mod rooted_tree {
    use std::mem::swap;

    use atcoder::union_find::UnionFind;
    pub struct RootedTree {
        n: usize,
        doubling_bit_width: usize,
        root: usize,
        rise_tbl: Vec<Vec<Option<usize>>>,
        dist: Vec<Option<i64>>,
        step: Vec<Option<usize>>,
        pub graph: Vec<Vec<(i64, usize)>>,
        edge_cnt: usize,
        uf: UnionFind,
    }
    impl RootedTree {
        pub fn new(n: usize, root: usize) -> RootedTree {
            let mut doubling_bit_width = 1;
            while (1 << doubling_bit_width) < n {
                doubling_bit_width += 1;
            }
            RootedTree {
                n,
                doubling_bit_width,
                root,
                rise_tbl: vec![vec![None; n]; doubling_bit_width],
                dist: vec![None; n],
                step: vec![None; n],
                graph: vec![vec![]; n],
                edge_cnt: 0,
                uf: UnionFind::new(n),
            }
        }
        pub fn unite(&mut self, a: usize, b: usize) {
            self.unite_with_distance(a, b, 1);
        }
        pub fn unite_with_distance(&mut self, a: usize, b: usize, delta: i64) {
            self.graph[a].push((delta, b));
            self.graph[b].push((delta, a));
            self.edge_cnt += 1;
            self.uf.unite(a, b);
            if self.edge_cnt >= self.n - 1 {
                if self.uf.group_num() != 1 {
                    panic!("nodes are NOT connected into one union.")
                }
                self.analyze(self.root);
            }
        }
        pub fn stepback(&self, from: usize, step: usize) -> usize {
            let mut v = from;
            for d in (0..self.doubling_bit_width - 1).rev() {
                if ((step >> d) & 1) != 0 {
                    v = self.rise_tbl[d][v].unwrap();
                }
            }
            v
        }
        fn dfs(
            v: usize,
            pre: Option<usize>,
            graph: &Vec<Vec<(i64, usize)>>,
            dist: &mut Vec<Option<i64>>,
            step: &mut Vec<Option<usize>>,
            rise_tbl: &mut Vec<Vec<Option<usize>>>,
        ) {
            for (delta, nv) in graph[v].iter() {
                if let Some(pre) = pre {
                    if *nv == pre {
                        continue;
                    }
                }
                if dist[*nv].is_none() {
                    dist[*nv] = Some(dist[v].unwrap() + *delta);
                    step[*nv] = Some(step[v].unwrap() + 1);
                    rise_tbl[0][*nv] = Some(v);
                    Self::dfs(*nv, Some(v), graph, dist, step, rise_tbl);
                }
            }
        }
        fn analyze(&mut self, root: usize) {
            self.dist[root] = Some(0);
            self.step[root] = Some(0);
            self.rise_tbl[0][root] = Some(root);
            Self::dfs(
                root,
                None,
                &self.graph,
                &mut self.dist,
                &mut self.step,
                &mut self.rise_tbl,
            );
            // doubling
            for d in (0..self.doubling_bit_width).skip(1) {
                for v in 0_usize..self.n {
                    self.rise_tbl[d][v] = self.rise_tbl[d - 1][self.rise_tbl[d - 1][v].unwrap()];
                }
            }
        }
        pub fn lca(&self, mut a: usize, mut b: usize) -> usize {
            if self.step[a] > self.step[b] {
                swap(&mut a, &mut b);
            }
            assert!(self.step[a] <= self.step[b]);
            // bring up the deeper one to the same level of the shallower one.
            for d in (0..self.doubling_bit_width).rev() {
                let rise_v = self.rise_tbl[d][b].unwrap();
                if self.step[rise_v] >= self.step[a] {
                    b = rise_v;
                }
            }
            assert!(self.step[a] == self.step[b]);
            if a != b {
                // simultaneously rise to the previous level of LCA.
                for d in (0..self.doubling_bit_width).rev() {
                    if self.rise_tbl[d][a] != self.rise_tbl[d][b] {
                        a = self.rise_tbl[d][a].unwrap();
                        b = self.rise_tbl[d][b].unwrap();
                    }
                }
                // 1-step higher level is LCA.
                a = self.rise_tbl[0][a].unwrap();
                b = self.rise_tbl[0][b].unwrap();
            }
            assert!(a == b);
            a
        }
        pub fn distance(&self, a: usize, b: usize) -> i64 {
            let lca_v = self.lca(a, b);
            self.dist[a].unwrap() + self.dist[b].unwrap() - 2 * self.dist[lca_v].unwrap()
        }
    }
}
use rooted_tree::RootedTree;

mod sort_vec_binary_search {
    static mut VEC_IS_SORTED_ONCE: bool = false;
    #[allow(clippy::type_complexity)]
    fn sorted_binary_search<'a, T: PartialOrd>(
        vec: &'a [T],
        key: &T,
        earlier: fn(&T, &T) -> bool,
    ) -> (Option<(usize, &'a T)>, Option<(usize, &'a T)>) {
        unsafe {
            if !VEC_IS_SORTED_ONCE {
                for i in 1..vec.len() {
                    assert!(vec[i - 1] <= vec[i]);
                }
                VEC_IS_SORTED_ONCE = true;
            }
        }
        if vec.is_empty() {
            return (None, None);
        }

        if !earlier(&vec[0], key) {
            (None, Some((0, &vec[0])))
        } else if earlier(vec.last().unwrap(), key) {
            (Some((vec.len() - 1, &vec[vec.len() - 1])), None)
        } else {
            let mut l = 0;
            let mut r = vec.len() - 1;
            while r - l > 1 {
                let m = (l + r) / 2;
                if earlier(&vec[m], key) {
                    l = m;
                } else {
                    r = m;
                }
            }
            (Some((l, &vec[l])), Some((r, &vec[r])))
        }
    }
    pub trait SortVecBinarySearch<T> {
        #[allow(clippy::type_complexity)]
        fn greater_equal(&self, key: &T) -> Option<(usize, &T)>;
        fn greater_than(&self, key: &T) -> Option<(usize, &T)>;
        fn less_equal(&self, key: &T) -> Option<(usize, &T)>;
        fn less_than(&self, key: &T) -> Option<(usize, &T)>;
    }
    impl<T: Ord> SortVecBinarySearch<T> for Vec<T> {
        fn greater_equal(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x < y).1
        }
        fn greater_than(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x <= y).1
        }
        fn less_equal(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x <= y).0
        }
        fn less_than(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x < y).0
        }
    }
}
use sort_vec_binary_search::SortVecBinarySearch;

mod map_counter {
    use std::cmp::Ord;
    use std::collections::{BTreeMap, HashMap};
    use std::hash::Hash;
    pub trait MapCounter<T> {
        fn incr(&mut self, key: T) -> bool;
        fn incr_by(&mut self, key: T, delta: usize) -> bool;
        fn decr(&mut self, key: &T) -> bool;
        fn decr_by(&mut self, key: &T, delta: usize) -> bool;
    }
    impl<T: Ord + Clone> MapCounter<T> for BTreeMap<T, usize> {
        fn incr(&mut self, key: T) -> bool {
            let stat0 = self.contains_key(&key);
            self.incr_by(key.clone(), 1);
            stat0 != self.contains_key(&key)
        }
        fn incr_by(&mut self, key: T, delta: usize) -> bool {
            let stat0 = self.contains_key(&key);
            *self.entry(key.clone()).or_insert(0) += delta;
            stat0 != self.contains_key(&key)
        }
        fn decr(&mut self, key: &T) -> bool {
            let stat0 = self.contains_key(key);
            self.decr_by(key, 1);
            stat0 != self.contains_key(key)
        }
        fn decr_by(&mut self, key: &T, delta: usize) -> bool {
            let stat0 = self.contains_key(key);
            let v = self.entry(key.clone()).or_insert(0);
            debug_assert!(*v >= delta);
            *v -= delta;
            if *v == 0 {
                self.remove(key);
            }
            stat0 != self.contains_key(key)
        }
    }
    impl<T: Clone + Hash + Eq> MapCounter<T> for HashMap<T, usize> {
        fn incr(&mut self, key: T) -> bool {
            let stat0 = self.contains_key(&key);
            self.incr_by(key.clone(), 1);
            stat0 != self.contains_key(&key)
        }
        fn incr_by(&mut self, key: T, delta: usize) -> bool {
            let stat0 = self.contains_key(&key);
            *self.entry(key.clone()).or_insert(0) += delta;
            stat0 != self.contains_key(&key)
        }
        fn decr(&mut self, key: &T) -> bool {
            let stat0 = self.contains_key(key);
            self.decr_by(key, 1);
            stat0 != self.contains_key(key)
        }
        fn decr_by(&mut self, key: &T, delta: usize) -> bool {
            let stat0 = self.contains_key(key);
            let v = self.entry(key.clone()).or_insert(0);
            debug_assert!(*v >= delta);
            *v -= delta;
            if *v == 0 {
                self.remove(key);
            }
            stat0 != self.contains_key(key)
        }
    }
}
use map_counter::MapCounter;

mod usize_move_delta {
    pub trait MoveDelta<T> {
        fn move_delta(self, delta: T, lim_lo: usize, lim_hi: usize) -> Option<usize>;
    }
    impl<T: Copy + Into<i64>> MoveDelta<T> for usize {
        fn move_delta(self, delta: T, lim_lo: usize, lim_hi: usize) -> Option<usize> {
            let delta: i64 = delta.into();
            let added: i64 = self as i64 + delta;
            let lim_lo: i64 = lim_lo as i64;
            let lim_hi: i64 = lim_hi as i64;
            if (lim_lo <= added) && (added <= lim_hi) {
                Some(added as usize)
            } else {
                None
            }
        }
    }
}
use usize_move_delta::MoveDelta;

fn exit_by<T: std::fmt::Display>(msg: T) {
    println!("{}", msg);
    std::process::exit(0);
}

pub struct PermutationIterator<T> {
    v: Vec<T>,
    is_first: bool,
}
impl<T: Copy + Ord + Clone> PermutationIterator<T> {
    pub fn new(mut v: Vec<T>) -> PermutationIterator<T> {
        v.sort();
        PermutationIterator { v, is_first: true }
    }
}
impl<T: Copy + Ord + Clone> Iterator for PermutationIterator<T> {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_first {
            self.is_first = false;
            Some(self.v.clone())
        } else if self.v.next_permutation() {
            Some(self.v.clone())
        } else {
            None
        }
    }
}

pub trait IntoPermutations<T: Copy + Ord + Clone> {
    fn into_permutations(self) -> PermutationIterator<T>;
}
// implement for ones that has IntoIterator.
impl<T: Copy + Ord + Clone, I: IntoIterator<Item = T>> IntoPermutations<T> for I {
    fn into_permutations(self) -> PermutationIterator<T> {
        PermutationIterator::new(self.into_iter().collect())
    }
}
mod add_header {
    pub trait AddHeader<T> {
        fn add_header(&mut self, add_val: T);
    }
    impl<T> AddHeader<T> for Vec<T>
    where
        Vec<T>: Clone,
    {
        fn add_header(&mut self, add_val: T) {
            let cpy = self.clone();
            self.clear();
            self.push(add_val);
            for cpy_val in cpy {
                self.push(cpy_val);
            }
        }
    }
}
use add_header::AddHeader;

mod my_string {
    use std::ops::{Index, IndexMut};
    use std::slice::SliceIndex;
    #[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
    pub struct Str {
        vc: Vec<char>,
    }
    impl Str {
        pub fn new() -> Self {
            Self { vc: vec![] }
        }
        pub fn from(s: &str) -> Self {
            Self {
                vc: s.to_string().chars().collect::<Vec<char>>(),
            }
        }
        pub fn len(&self) -> usize {
            self.vc.len()
        }
        pub fn clear(&mut self) {
            self.vc.clear()
        }
        pub fn is_empty(&self) -> bool {
            self.vc.is_empty()
        }
        pub fn first(&self) -> Option<&char> {
            self.vc.first()
        }
        pub fn last(&self) -> Option<&char> {
            self.vc.last()
        }
        pub fn push(&mut self, c: char) {
            self.vc.push(c);
        }
        pub fn push_str(&mut self, s: &str) {
            for c in s.to_string().chars().collect::<Vec<char>>().into_iter() {
                self.push(c);
            }
        }
        pub fn pop(&mut self) -> Option<char> {
            self.vc.pop()
        }
        pub fn into_iter(self) -> std::vec::IntoIter<char> {
            self.vc.into_iter()
        }
        pub fn iter(&self) -> std::slice::Iter<'_, char> {
            self.vc.iter()
        }
        pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, char> {
            self.vc.iter_mut()
        }
        pub fn swap(&mut self, a: usize, b: usize) {
            self.vc.swap(a, b);
        }
        pub fn reverse(&mut self) {
            self.vc.reverse();
        }
        pub fn find(&self, p: &Str) -> Option<usize> {
            let s: String = self.vc.iter().collect::<String>();
            let p: String = p.vc.iter().collect::<String>();
            s.find(&p)
        }
        pub fn rfind(&self, p: &Str) -> Option<usize> {
            let s: String = self.vc.iter().collect::<String>();
            let p: String = p.vc.iter().collect::<String>();
            s.rfind(&p)
        }
        pub fn into_usize(self, base: char, offset: usize) -> Vec<usize> {
            self.vc
                .into_iter()
                .map(|c| (c as u8 - base as u8) as usize + offset)
                .collect::<Vec<usize>>()
        }
        pub fn sort(&mut self) {
            self.vc.sort();
        }
        pub fn remove(&mut self, index: usize) -> char {
            self.vc.remove(index)
        }
    }
    impl std::str::FromStr for Str {
        type Err = ();
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(Str {
                vc: s.to_string().chars().collect::<Vec<char>>(),
            })
        }
    }
    impl<Idx: SliceIndex<[char]>> Index<Idx> for Str {
        type Output = Idx::Output;
        fn index(&self, i: Idx) -> &Self::Output {
            &self.vc[i]
        }
    }
    impl<Idx: SliceIndex<[char]>> IndexMut<Idx> for Str {
        fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
            &mut self.vc[index]
        }
    }
    impl std::ops::Add<Str> for Str {
        type Output = Str;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            for c in rhs.into_iter() {
                ret.vc.push(c);
            }
            ret
        }
    }
    impl std::ops::AddAssign<Str> for Str {
        fn add_assign(&mut self, rhs: Self) {
            for c in rhs.into_iter() {
                self.vc.push(c);
            }
        }
    }
    impl std::ops::Add<char> for Str {
        type Output = Str;
        fn add(self, rhs: char) -> Self::Output {
            let mut ret = self;
            ret.vc.push(rhs);
            ret
        }
    }
    impl std::ops::AddAssign<char> for Str {
        fn add_assign(&mut self, rhs: char) {
            self.vc.push(rhs);
        }
    }
    impl std::fmt::Display for Str {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.vc.iter().collect::<String>())
        }
    }
    impl std::fmt::Debug for Str {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.vc.iter().collect::<String>())
        }
    }
}
use my_string::Str;

mod rational {
    use atcoder::remainder::gcd;
    use std::cmp::Ordering;
    use std::fmt;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Rational {
        pub num: i64,
        pub denom: i64,
    }
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
    impl AddAssign<Self> for Rational {
        fn add_assign(&mut self, rhs: Self) {
            let d0 = self.denom.abs();
            let d1 = rhs.denom.abs();
            let denom = d0 * (d1 / gcd(d0, d1));
            let n0 = self.num * (denom / d0);
            let n1 = rhs.num * (denom / d1);
            *self = Self::new(n0 + n1, denom);
        }
    }
    impl Add<Self> for Rational {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret += rhs;
            ret
        }
    }
    impl SubAssign<Self> for Rational {
        fn sub_assign(&mut self, rhs: Self) {
            *self += Self::new(-rhs.num, rhs.denom);
        }
    }
    impl Sub<Self> for Rational {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret -= rhs;
            ret
        }
    }
    impl MulAssign<Self> for Rational {
        fn mul_assign(&mut self, rhs: Self) {
            *self = Self::new(self.num * rhs.num, self.denom * rhs.denom);
        }
    }
    impl Mul<Self> for Rational {
        type Output = Self;
        fn mul(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret *= rhs;
            ret
        }
    }
    impl DivAssign<Self> for Rational {
        fn div_assign(&mut self, rhs: Self) {
            *self = Self::new(self.num * rhs.denom, rhs.num * self.denom);
        }
    }
    impl Div<Self> for Rational {
        type Output = Self;
        fn div(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret /= rhs;
            ret
        }
    }
    impl Neg for Rational {
        type Output = Self;
        fn neg(self) -> Self::Output {
            Self::new(-self.num, self.denom)
        }
    }
    impl PartialOrd for Rational {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(i64::cmp(
                &(self.num * other.denom),
                &(self.denom * other.num),
            ))
        }
    }
    impl Ord for Rational {
        fn cmp(&self, other: &Self) -> Ordering {
            Self::partial_cmp(self, other).unwrap()
        }
    }
    impl fmt::Display for Rational {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.num as f64 / self.denom as f64)
        }
    }
    impl fmt::Debug for Rational {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.num as f64 / self.denom as f64)
        }
    }
}
use rational::Rational;

fn z_algo(s: &[usize]) -> Vec<usize> {
    // https://www.youtube.com/watch?v=f6ct5PQHqM0
    let n = s.len();
    let mut last_match = None;
    let mut ret = vec![0; n];
    ret[0] = n;
    for i in 1..n {
        let mut match_delta = 0;
        if let Some((m0, m1)) = last_match {
            if i < m1 {
                // reuse calculated info.
                if i + ret[i - m0] != m1 {
                    // built from old one, and finish.
                    ret[i] = min(ret[i - m0], m1 - i);
                    continue;
                } else {
                    // skip known range, and continues.
                    match_delta = m1 - i;
                }
            }
        }
        // expand until unmatch is found.
        while i + match_delta < n {
            if s[match_delta] == s[i + match_delta] {
                match_delta += 1;
            } else {
                break;
            }
        }
        // set header-match lentgh.
        ret[i] = match_delta;
        // update last match range for future use.
        if let Some((_m0, m1)) = last_match {
            if i + match_delta <= m1 {
                continue;
            }
        }
        last_match = Some((i, i + match_delta));
    }
    ret
}

mod convex_hull {
    use super::{ChangeMinMax, Rational};
    use std::collections::{BTreeMap, BTreeSet, VecDeque};
    use std::ops::{Add, Div, Mul, Neg, Sub};
    pub struct ConvexHull {
        x_ys: BTreeMap<i64, Vec<i64>>,
    }
    impl ConvexHull {
        pub fn new() -> Self {
            Self {
                x_ys: BTreeMap::new(),
            }
        }
        pub fn add(&mut self, y: i64, x: i64) {
            self.x_ys.entry(x).or_default().push(y);
        }
        pub fn convex_hull(&self) -> Vec<(i64, i64)> {
            let mut x_ys = self
                .x_ys
                .iter()
                .map(|(x, ys)| (*x, ys.clone()))
                .collect::<Vec<_>>();
            // lower
            x_ys.iter_mut().for_each(|(_x, ys)| {
                ys.sort();
            });
            let lower_yx = Self::weakly_monotone_tangents(&x_ys);
            // upper
            x_ys.iter_mut().for_each(|(_x, ys)| {
                ys.reverse();
            });
            x_ys.reverse();
            let upper_yx = Self::weakly_monotone_tangents(&x_ys);
            let mut ret = vec![];
            let mut seen = BTreeSet::new();
            for (y, x) in lower_yx.into_iter().chain(upper_yx.into_iter()) {
                if seen.contains(&(y, x)) {
                    continue;
                }
                ret.push((y, x));
                seen.insert((y, x));
            }
            ret
        }
        fn weakly_monotone_tangents(x_ys: &[(i64, Vec<i64>)]) -> VecDeque<(i64, i64)> {
            let mut vs = VecDeque::new();
            for (x, ys) in x_ys.iter() {
                let x = *x;
                let y = ys[0];
                if vs.is_empty() {
                    vs.push_back((y, x));
                    continue;
                }
                while vs.len() >= 2 {
                    let (y0, x0) = vs.pop_back().unwrap();
                    let (y1, x1) = vs.pop_back().unwrap();
                    let t0 = Rational::new(y0 - y, x0 - x);
                    let t1 = Rational::new(y1 - y, x1 - x);
                    if t0 < t1 {
                        vs.push_back((y1, x1));
                    } else {
                        vs.push_back((y1, x1));
                        vs.push_back((y0, x0));
                        break;
                    }
                }
                vs.push_back((y, x));
            }
            if let Some((x, ys)) = x_ys.last() {
                let x = *x;
                for &y in ys.iter().skip(1) {
                    vs.push_back((y, x))
                }
            }
            if let Some((x, ys)) = x_ys.first() {
                let x = *x;
                for &y in ys.iter().skip(1) {
                    vs.push_front((y, x))
                }
            }
            vs
        }
    }
    #[derive(Clone, Debug)]
    pub struct ConvexHullTrickMaxImpl<T> {
        lines: BTreeMap<T, T>,   // slope, intercept
        borders: BTreeMap<T, T>, // x, slope
    }
    impl<T> ConvexHullTrickMaxImpl<T>
    where
        T: Clone
            + Copy
            + PartialEq
            + Eq
            + PartialOrd
            + Ord
            + Add<Output = T>
            + Sub<Output = T>
            + Mul<Output = T>
            + Div<Output = T>
            + std::fmt::Debug,
    {
        pub fn new() -> Self {
            Self {
                lines: BTreeMap::new(),
                borders: BTreeMap::new(),
            }
        }
        fn cross(a0: T, b0: T, a1: T, b1: T) -> (T, T) {
            let x = (b0 - b1) / (a1 - a0);
            let y = a0 * x + b0;
            (y, x)
        }
        fn need_center(a0: T, b0: T, a1: T, b1: T, a2: T, b2: T) -> bool {
            (a2 - a1) * (b1 - b0) > (a1 - a0) * (b2 - b1)
        }
        pub fn get_max(&self, x: T) -> T {
            if let Some((_, &a)) = self.borders.range(..=x).next_back() {
                let b = self.lines[&a];
                a * x + b
            } else if let Some((&a, &b)) = self.lines.iter().next() {
                a * x + b
            } else {
                unreachable!()
            }
        }
        pub fn add(&mut self, a: T, b: T) {
            if let Some((&a0, &b0)) = self.lines.range(..a).next_back() {
                if let Some((&a2, &b2)) = self.lines.range(a..).next() {
                    if !Self::need_center(a0, b0, a, b, a2, b2) {
                        return;
                    }
                }
            };
            let mut del_lines = VecDeque::new();
            // left remove
            if let Some((a1, b1)) = self.lines.range(..a).next_back() {
                let mut a1 = *a1;
                let mut b1 = *b1;
                while let Some((a0, b0)) = self.lines.range(..a1).next_back() {
                    let a0 = *a0;
                    let b0 = *b0;
                    if Self::need_center(a0, b0, a1, b1, a, b) {
                        break;
                    }
                    assert_eq!(Some(b1), self.lines.remove(&a1));
                    del_lines.push_front((a1, b1));
                    a1 = a0;
                    b1 = b0;
                }
            }
            // right remove
            if let Some((a1, b1)) = self.lines.range(a..).next() {
                let mut a1 = *a1;
                let mut b1 = *b1;
                while let Some((a2, b2)) = self.lines.range(a1..).next() {
                    let a2 = *a2;
                    let b2 = *b2;
                    if Self::need_center(a, b, a1, b1, a2, b2) {
                        break;
                    }
                    assert_eq!(Some(b1), self.lines.remove(&a1));
                    del_lines.push_back((a1, b1));
                    a1 = a2;
                    b1 = b2;
                }
            }
            // remove left-end border.
            if let Some(&(ar, br)) = del_lines.front() {
                if let Some((&al, &bl)) = self.lines.range(..ar).next_back() {
                    let (_, x) = Self::cross(al, bl, ar, br);
                    assert_eq!(Some(ar), self.borders.remove(&x));
                }
            }
            // remove right-end border.
            if let Some(&(al, bl)) = del_lines.back() {
                if let Some((&ar, &br)) = self.lines.range(al..).next() {
                    let (_, x) = Self::cross(al, bl, ar, br);
                    assert_eq!(Some(ar), self.borders.remove(&x));
                }
            }
            // remove intermediate border.
            for ir in 1..del_lines.len() {
                let il = ir - 1;
                let (al, bl) = del_lines[il];
                let (ar, br) = del_lines[ir];
                let (_, x) = Self::cross(al, bl, ar, br);
                assert_eq!(Some(ar), self.borders.remove(&x));
            }
            // add left border.
            if let Some((&al, &bl)) = self.lines.range(..a).next_back() {
                let (_, x) = Self::cross(al, bl, a, b);
                assert!(self.borders.insert(x, a).is_none());
            }
            // add right border.
            if let Some((&ar, &br)) = self.lines.range(a..).next() {
                let (_, x) = Self::cross(a, b, ar, br);
                assert!(self.borders.insert(x, ar).is_none());
            }
            // add line.
            assert!(self.lines.insert(a, b).is_none());
        }
    }
    pub struct ConvexHullTrickMinImpl<T> {
        cht: ConvexHullTrickMaxImpl<T>,
    }
    impl<T> ConvexHullTrickMinImpl<T>
    where
        T: Clone
            + Copy
            + PartialEq
            + Eq
            + PartialOrd
            + Ord
            + Add<Output = T>
            + Sub<Output = T>
            + Mul<Output = T>
            + Div<Output = T>
            + Neg<Output = T>
            + std::fmt::Debug,
    {
        pub fn new() -> Self {
            Self {
                cht: ConvexHullTrickMaxImpl::new(),
            }
        }
        pub fn add(&mut self, a: T, b: T) {
            self.cht.add(-a, -b)
        }
        pub fn get_min(&self, x: T) -> T {
            -self.cht.get_max(x)
        }
    }
    pub struct ConvexHullTrickMax {
        cht: ConvexHullTrickMaxImpl<Rational>,
    }
    impl ConvexHullTrickMax {
        pub fn new() -> Self {
            Self {
                cht: ConvexHullTrickMaxImpl::new(),
            }
        }
        pub fn add(&mut self, a: i64, b: i64) {
            self.cht.add(Rational::new(a, 1), Rational::new(b, 1))
        }
        pub fn get_max(&self, x: i64) -> Rational {
            self.cht.get_max(Rational::new(x, 1))
        }
    }
    pub struct ConvexHullTrickMin {
        cht: ConvexHullTrickMinImpl<Rational>,
    }
    impl ConvexHullTrickMin {
        pub fn new() -> Self {
            Self {
                cht: ConvexHullTrickMinImpl::new(),
            }
        }
        pub fn add(&mut self, a: i64, b: i64) {
            self.cht.add(Rational::new(a, 1), Rational::new(b, 1))
        }
        pub fn get_min(&self, x: i64) -> Rational {
            self.cht.get_min(Rational::new(x, 1))
        }
    }
}
use convex_hull::{ConvexHull, ConvexHullTrickMax, ConvexHullTrickMin};

mod matrix {
    use std::iter::Sum;
    use std::ops::{Add, Index, IndexMut, Mul, MulAssign, Sub};
    use std::slice::SliceIndex;
    #[derive(Clone)]
    pub struct Matrix<T> {
        h: usize,
        w: usize,
        vals: Vec<Vec<T>>,
    }
    impl<T: Clone + Copy + Sub<Output = T> + Mul + Sum<<T as Mul>::Output> + From<u8>> Matrix<T> {
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
    impl<T, Idx: SliceIndex<[Vec<T>]>> Index<Idx> for Matrix<T> {
        type Output = Idx::Output;
        fn index(&self, i: Idx) -> &Self::Output {
            &self.vals[i]
        }
    }
    impl<T, Idx: SliceIndex<[Vec<T>]>> IndexMut<Idx> for Matrix<T> {
        fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
            &mut self.vals[index]
        }
    }
    impl<T: Clone + Copy + Sub<Output = T> + Mul + Sum<<T as Mul>::Output> + From<u8>>
        Mul<Matrix<T>> for Matrix<T>
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
    impl<T: Clone + Copy + Sub<Output = T> + Mul + Sum<<T as Mul>::Output>> MulAssign<Matrix<T>>
        for Matrix<T>
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
    impl<T: Clone + Copy + Mul + Sum<<T as Mul>::Output>> Mul<Vec<T>> for Matrix<T> {
        type Output = Vec<T>;
        fn mul(self, rhs: Vec<T>) -> Self::Output {
            debug_assert!(self.w == rhs.len());
            (0..self.h)
                .map(|y| (0..self.w).map(|x| self[y][x] * rhs[x]).sum::<T>())
                .collect::<Vec<_>>()
        }
    }
    impl<T: Clone + Copy + Mul + Sum<<T as Mul>::Output>> Mul<Matrix<T>> for Vec<T> {
        type Output = Vec<T>;
        fn mul(self, rhs: Matrix<T>) -> Self::Output {
            debug_assert!(self.len() == rhs.h);
            (0..rhs.w)
                .map(|x| (0..rhs.h).map(|y| self[y] * rhs[y][x]).sum::<T>())
                .collect::<Vec<_>>()
        }
    }
    impl<
            T: Clone
                + Copy
                + Add<Output = T>
                + Sub<Output = T>
                + Mul
                + Sum<<T as Mul>::Output>
                + From<u8>,
        > Add<Matrix<T>> for Matrix<T>
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
}
use matrix::Matrix;

mod suffix_array {
    use std::cmp::Ordering;
    use std::mem::swap;
    fn compare(pos_to_ord: &[i64], i: usize, j: usize, k: usize, n: usize) -> Ordering {
        let ri0 = pos_to_ord[i];
        let rj0 = pos_to_ord[j];
        let ri1 = if i + k <= n { pos_to_ord[i + k] } else { -1 };
        let rj1 = if j + k <= n { pos_to_ord[j + k] } else { -1 };
        (ri0, ri1).cmp(&(rj0, rj1))
    }
    fn construct_suffix_array(s: &[usize]) -> Vec<usize> {
        let n = s.len();
        let mut ord_to_pos = vec![0usize; n + 1];
        let mut pos_to_ord = vec![0i64; n + 1];
        let mut pos_to_ord_nxt = vec![0i64; n + 1];
        for i in 0..=n {
            ord_to_pos[i] = i;
            pos_to_ord[i] = if i < n { s[i] as i64 } else { -1 };
        }
        let mut k = 1;
        while k <= n {
            ord_to_pos.sort_by(|&i, &j| compare(&pos_to_ord, i, j, k, n));
            pos_to_ord_nxt[ord_to_pos[0]] = 0;
            for ord in 1..=n {
                pos_to_ord_nxt[ord_to_pos[ord]] = pos_to_ord_nxt[ord_to_pos[ord - 1]]
                    + if compare(&pos_to_ord, ord_to_pos[ord - 1], ord_to_pos[ord], k, n)
                        == Ordering::Less
                    {
                        1
                    } else {
                        0
                    };
            }
            //
            k *= 2;
            swap(&mut pos_to_ord, &mut pos_to_ord_nxt);
        }
        ord_to_pos
    }
    fn construct_longest_common_prefix(s: &[usize], ord_to_pos: &[usize]) -> Vec<usize> {
        let n = s.len();
        debug_assert_eq!(ord_to_pos.len(), n + 1);
        let pos_to_ord = {
            let mut pos_to_ord = vec![0; ord_to_pos.len()];
            for (ord, &pos) in ord_to_pos.iter().enumerate() {
                pos_to_ord[pos] = ord;
            }
            pos_to_ord
        };
        let mut lcp_now = 0usize;
        let mut lcp = vec![0; n];
        for pos in 0..n {
            let pre_ord = pos_to_ord[pos] - 1;
            let pre_ord_pos = ord_to_pos[pre_ord];
            lcp_now = lcp_now.saturating_sub(1);
            while pre_ord_pos + lcp_now < n && pos + lcp_now < n {
                if s[pre_ord_pos + lcp_now] == s[pos + lcp_now] {
                    lcp_now += 1;
                } else {
                    break;
                }
            }
            lcp[pre_ord] = lcp_now;
        }
        lcp
    }
    pub trait ToSuffixArray {
        fn suffix_array(&self) -> (Vec<usize>, Vec<usize>);
    }
    impl ToSuffixArray for Vec<usize> {
        fn suffix_array(&self) -> (Vec<usize>, Vec<usize>) {
            let ord_to_pos = construct_suffix_array(self);
            let lcp = construct_longest_common_prefix(self, &ord_to_pos);
            (ord_to_pos, lcp)
        }
    }
    #[cfg(test)]
    mod test {
        const T: usize = 100;
        const N: usize = 100;
        const C: usize = 26;
        use super::ToSuffixArray;
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaChaRng;
        #[test]
        fn suffix_array() {
            let mut rng = ChaChaRng::from_seed([0; 32]);
            for n in 1..=N {
                for _ in 0..T {
                    let a = (0..n).map(|_| rng.random_range(0..C)).collect::<Vec<_>>();
                    let sa_expected = {
                        let mut sa_expected = (0..=n).collect::<Vec<_>>();
                        sa_expected.sort_by(|&i, &j| a[i..].cmp(&a[j..]));
                        sa_expected
                    };
                    let lcp_expected = (0..n)
                        .map(|i| {
                            (0..)
                                .take_while(|&d| {
                                    (sa_expected[i] + d < n)
                                        && (sa_expected[i + 1] + d < n)
                                        && a[sa_expected[i] + d] == a[sa_expected[i + 1] + d]
                                })
                                .count()
                        })
                        .collect::<Vec<_>>();
                    let (sa_actual, lcp_actual) = a.suffix_array();
                    assert_eq!(sa_expected, sa_actual);
                    assert_eq!(lcp_expected, lcp_actual);
                }
            }
        }
    }
}
use suffix_array::ToSuffixArray;

mod flow {
    use crate::change_min_max::ChangeMinMax;
    use std::cmp::Reverse;
    use std::collections::{BinaryHeap, VecDeque};
    #[derive(Clone, Copy)]
    pub struct Edge {
        pub to: usize,
        pub rev_idx: usize, // index of paired edge at node "to".
        pub cap: i64,       // immutable capacity, s.t. flow <= cap
        pub flow: i64,      // flow can be negative.
        pub cost: i64,      // for min-cost flow
    }
    #[derive(Clone)]
    pub struct Flow {
        pub g: Vec<Vec<Edge>>,
        flow_lb_sum: i64,
        neg_cost_any: bool,
    }
    impl Flow {
        pub fn new(n: usize) -> Self {
            Self {
                g: vec![vec![]; n + 2],
                flow_lb_sum: 0,
                neg_cost_any: false,
            }
        }
        pub fn add_edge(&mut self, from: usize, to: usize, cap: i64) {
            self.add_cost_edge(from, to, cap, 0);
        }
        pub fn add_flowbound_edge(&mut self, from: usize, to: usize, cap_min: i64, cap_max: i64) {
            self.add_flowbound_cost_edge(from, to, cap_min, cap_max, 0);
        }
        pub fn add_flowbound_cost_edge(
            &mut self,
            from: usize,
            to: usize,
            cap_min: i64,
            cap_max: i64,
            cost: i64,
        ) {
            self.add_cost_edge(from, to, cap_max - cap_min, cost);
            if cap_min > 0 {
                self.flow_lb_sum += cap_min;
                let dummy_src = self.g.len() - 2;
                self.add_cost_edge(dummy_src, to, cap_min, cost);
                let dummy_dst = self.g.len() - 1;
                self.add_cost_edge(from, dummy_dst, cap_min, cost);
            }
        }
        pub fn add_cost_edge(&mut self, from: usize, to: usize, cap: i64, cost: i64) {
            let rev_idx = self.g[to].len();
            self.g[from].push(Edge {
                to,
                rev_idx,
                cap,
                flow: 0,
                cost,
            });
            let rev_idx = self.g[from].len() - 1;
            self.g[to].push(Edge {
                to: from,
                rev_idx,
                cap: 0,
                flow: 0,
                cost: -cost,
            });
            if cost < 0 {
                self.neg_cost_any = true;
            }
        }
        fn bfs(g: &[Vec<Edge>], source: usize) -> Vec<Option<usize>> {
            let mut level = vec![None; g.len()];
            level[source] = Some(0);
            let mut que = std::collections::VecDeque::new();
            que.push_back(source);
            while let Some(v) = que.pop_front() {
                let nxt_level = level[v].unwrap() + 1;
                for edge in g[v].iter().copied() {
                    if level[edge.to].is_none() && (edge.flow < edge.cap) {
                        level[edge.to] = Some(nxt_level);
                        que.push_back(edge.to);
                    }
                }
            }
            level
        }
        fn dfs(
            g: &mut [Vec<Edge>],
            v: usize,
            sink: usize,
            flow: i64,
            search_cnt: &mut [usize],
            level: &[Option<usize>],
        ) -> i64 {
            if v == sink {
                return flow;
            }
            while search_cnt[v] < g[v].len() {
                let (to, rev_idx, remain_capacity) = {
                    let edge = g[v][search_cnt[v]];
                    (edge.to, edge.rev_idx, edge.cap - edge.flow)
                };
                if let Some(nxt_level) = level[to] {
                    if (level[v].unwrap() < nxt_level) && (remain_capacity > 0) {
                        let additional_flow = Self::dfs(
                            g,
                            to,
                            sink,
                            std::cmp::min(flow, remain_capacity),
                            search_cnt,
                            level,
                        );
                        if additional_flow > 0 {
                            g[v][search_cnt[v]].flow += additional_flow;
                            g[to][rev_idx].flow -= additional_flow;
                            return additional_flow;
                        }
                    }
                }
                search_cnt[v] += 1;
            }
            0
        }
        pub fn max_flow(&mut self, src: usize, dst: usize) -> Option<i64> {
            if self.flow_lb_sum == 0 {
                return Some(self.max_flow_impl(src, dst));
            }
            let dummy_src = self.g.len() - 2;
            let dummy_dst = self.g.len() - 1;
            // cyclic flow
            self.add_edge(dst, src, 1 << 60);
            if self.max_flow_impl(dummy_src, dummy_dst) != self.flow_lb_sum {
                return None;
            }
            Some(self.max_flow_impl(src, dst))
        }
        pub fn min_cut_split(&self, src: usize) -> Vec<bool> {
            let nm = self.g.len() - 2;
            let mut split = vec![false; nm];
            let mut que = VecDeque::new();
            que.push_back(src);
            while let Some(v) = que.pop_front() {
                for e in self.g[v].iter() {
                    if e.flow >= e.cap || split[e.to] {
                        continue;
                    }
                    split[e.to] = true;
                    que.push_back(e.to);
                }
            }
            split
        }
        fn max_flow_impl(&mut self, source: usize, sink: usize) -> i64 {
            let inf = 1i64 << 60;
            let mut flow = 0;
            loop {
                let level = Self::bfs(&self.g, source);
                if level[sink].is_none() {
                    break;
                }
                let mut search_cnt = vec![0; self.g.len()];
                loop {
                    let additional_flow =
                        Self::dfs(&mut self.g, source, sink, inf, &mut search_cnt, &level);
                    if additional_flow > 0 {
                        flow += additional_flow;
                    } else {
                        break;
                    }
                }
            }
            flow
        }
        pub fn min_cost_flow(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64,
            flow_ub: i64,
        ) -> Option<(i64, i64)> {
            if self.flow_lb_sum == 0 {
                return self.min_cost_flow_impl(src, dst, flow_lb, flow_ub);
            }
            let dummy_src = self.g.len() - 2;
            let dummy_dst = self.g.len() - 1;
            // cyclic flow
            self.add_edge(dst, src, 1 << 60);
            let (dcost, _ds_to_dt) =
                self.min_cost_flow_impl(dummy_src, dummy_dst, self.flow_lb_sum, self.flow_lb_sum)?;
            let (cost, s_to_t) = self.min_cost_flow_impl(src, dst, flow_lb, flow_ub)?;
            Some((cost + dcost, s_to_t))
        }
        fn min_cost_flow_impl(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Option<(i64, i64)> {
            if self.neg_cost_any {
                self.min_negcost_flow(src, dst, flow_lb, flow_ub)
            } else {
                self.min_poscost_flow(src, dst, flow_lb)
            }
        }
        fn min_negcost_flow(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Option<(i64, i64)> {
            let mut flow_now = 0;
            let mut min_cost = 0;
            let mut dist = vec![None; self.g.len()];
            let mut prev = vec![None; self.g.len()];
            loop {
                dist[source] = Some(0);
                let mut update = true;
                while update {
                    update = false;
                    for (v, to) in self.g.iter().enumerate() {
                        if dist[v].is_none() {
                            continue;
                        }
                        for (ei, e) in to.iter().enumerate() {
                            if e.flow >= e.cap {
                                continue;
                            }
                            let nd = dist[v].unwrap() + e.cost;
                            if dist[e.to].chmin(nd) {
                                prev[e.to] = Some((v, ei));
                                update = true;
                            }
                        }
                    }
                }

                if let Some(dist_sink) = dist[sink] {
                    if (flow_now >= flow_lb) && (dist_sink > 0) {
                        break;
                    }
                    let mut delta_flow = flow_ub - flow_now;
                    {
                        let mut v = sink;
                        while let Some((pv, pei)) = prev[v] {
                            let e = &self.g[pv][pei];
                            delta_flow.chmin(e.cap - e.flow);
                            v = pv;
                        }
                    }
                    if delta_flow == 0 {
                        break;
                    }
                    min_cost += delta_flow * dist_sink;
                    flow_now += delta_flow;
                    {
                        let mut v = sink;
                        while let Some((pv, pei)) = prev[v] {
                            self.g[pv][pei].flow += delta_flow;
                            let rev_idx = self.g[pv][pei].rev_idx;
                            self.g[v][rev_idx].flow -= delta_flow;
                            v = pv;
                        }
                    }
                } else if flow_now >= flow_lb {
                    break;
                } else {
                    return None;
                }

                dist.iter_mut().for_each(|x| *x = None);
                prev.iter_mut().for_each(|x| *x = None);
            }
            Some((min_cost, flow_now))
        }
        fn min_poscost_flow(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow;
        ) -> Option<(i64, i64)> {
            let mut flow_now = 0;
            let mut min_cost = 0;
            let mut h = vec![0; self.g.len()];
            let mut dist = vec![None; self.g.len()];
            let mut prev = vec![None; self.g.len()];
            while flow_now < flow_lb {
                let mut que = BinaryHeap::new();
                que.push((Reverse(0), source));
                dist[source] = Some(0);
                while let Some((Reverse(d), v)) = que.pop() {
                    if dist[v].unwrap() != d {
                        continue;
                    }
                    for (ei, e) in self.g[v].iter().enumerate() {
                        if e.flow >= e.cap {
                            continue;
                        }
                        let nd = d + e.cost + h[v] - h[e.to];
                        if dist[e.to].chmin(nd) {
                            prev[e.to] = Some((v, ei));
                            que.push((Reverse(nd), e.to));
                        }
                    }
                }
                dist[sink]?;
                h.iter_mut().zip(dist.iter()).for_each(|(h, d)| {
                    if let Some(d) = d {
                        *h += d
                    }
                });
                let mut delta_flow = flow_lb - flow_now;
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        let e = &self.g[pv][pei];
                        delta_flow.chmin(e.cap - e.flow);
                        v = pv;
                    }
                }
                min_cost += delta_flow * h[sink];
                flow_now += delta_flow;
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        self.g[pv][pei].flow += delta_flow;
                        let rev_idx = self.g[pv][pei].rev_idx;
                        self.g[v][rev_idx].flow -= delta_flow;
                        v = pv;
                    }
                }

                dist.iter_mut().for_each(|dist| *dist = None);
                prev.iter_mut().for_each(|dist| *dist = None);
            }
            Some((min_cost, flow_now))
        }
        pub fn min_cost_slope(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Vec<(i64, i64)> {
            if self.neg_cost_any {
                self.min_negcost_slope(src, dst, flow_lb, flow_ub)
            } else {
                self.min_poscost_slope(src, dst, flow_lb)
            }
        }
        fn min_negcost_slope(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Vec<(i64, i64)> {
            let mut slope = vec![];
            let mut flow_now = 0;
            let mut min_cost = 0;
            let mut dist = vec![None; self.g.len()];
            let mut prev = vec![None; self.g.len()];
            loop {
                dist[source] = Some(0);
                let mut update = true;
                while update {
                    update = false;
                    for (v, to) in self.g.iter().enumerate() {
                        if dist[v].is_none() {
                            continue;
                        }
                        for (ei, e) in to.iter().enumerate() {
                            if e.flow >= e.cap {
                                continue;
                            }
                            let nd = dist[v].unwrap() + e.cost;
                            if dist[e.to].chmin(nd) {
                                prev[e.to] = Some((v, ei));
                                update = true;
                            }
                        }
                    }
                }

                if let Some(dist_sink) = dist[sink] {
                    if (flow_now >= flow_lb) && (dist_sink > 0) {
                        break;
                    }
                    let mut delta_flow = flow_ub - flow_now;
                    {
                        let mut v = sink;
                        while let Some((pv, pei)) = prev[v] {
                            let e = &self.g[pv][pei];
                            delta_flow.chmin(e.cap - e.flow);
                            v = pv;
                        }
                    }
                    if delta_flow == 0 {
                        break;
                    }
                    min_cost += delta_flow * dist_sink;
                    flow_now += delta_flow;
                    slope.push((min_cost, flow_now));
                    {
                        let mut v = sink;
                        while let Some((pv, pei)) = prev[v] {
                            self.g[pv][pei].flow += delta_flow;
                            let rev_idx = self.g[pv][pei].rev_idx;
                            self.g[v][rev_idx].flow -= delta_flow;
                            v = pv;
                        }
                    }
                } else {
                    break;
                }

                dist.iter_mut().for_each(|x| *x = None);
                prev.iter_mut().for_each(|x| *x = None);
            }
            slope
        }
        fn min_poscost_slope(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow;
        ) -> Vec<(i64, i64)> {
            let mut slope = vec![];
            let mut flow_now = 0;
            let mut min_cost = 0;
            let mut h = vec![0; self.g.len()];
            let mut dist = vec![None; self.g.len()];
            let mut prev = vec![None; self.g.len()];
            while flow_now < flow_lb {
                let mut que = BinaryHeap::new();
                que.push((Reverse(0), source));
                dist[source] = Some(0);
                while let Some((Reverse(d), v)) = que.pop() {
                    if dist[v].unwrap() != d {
                        continue;
                    }
                    for (ei, e) in self.g[v].iter().enumerate() {
                        if e.flow >= e.cap {
                            continue;
                        }
                        let nd = d + e.cost + h[v] - h[e.to];
                        if dist[e.to].chmin(nd) {
                            prev[e.to] = Some((v, ei));
                            que.push((Reverse(nd), e.to));
                        }
                    }
                }
                if dist[sink].is_none() {
                    break;
                }
                h.iter_mut().zip(dist.iter()).for_each(|(h, d)| {
                    if let Some(d) = d {
                        *h += d
                    }
                });
                let mut delta_flow = flow_lb - flow_now;
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        let e = &self.g[pv][pei];
                        delta_flow.chmin(e.cap - e.flow);
                        v = pv;
                    }
                }
                min_cost += delta_flow * h[sink];
                flow_now += delta_flow;
                slope.push((min_cost, flow_now));
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        self.g[pv][pei].flow += delta_flow;
                        let rev_idx = self.g[pv][pei].rev_idx;
                        self.g[v][rev_idx].flow -= delta_flow;
                        v = pv;
                    }
                }

                dist.iter_mut().for_each(|dist| *dist = None);
                prev.iter_mut().for_each(|dist| *dist = None);
            }
            slope
        }
    }
}
use flow::Flow;

mod convolution {
    // https://github.com/atcoder/ac-library/blob/master/atcoder/convolution.hpp
    use crate::IntegerOperation;
    use atcoder::modint::{DynModInt, ModIntTrait};
    use atcoder::remainder::ext_gcd;
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
    // returns 'r' s.t. 'r^(m - 1) == 1 (mod m)'
    fn primitive_root(m: i64) -> i64 {
        debug_assert!(is_prime(m));
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
    fn is_prime(x: i64) -> bool {
        if x == 1 {
            return false;
        }
        for i in 2.. {
            if i * i > x {
                return true;
            }
            if x % i == 0 {
                return false;
            }
        }
        unreachable!();
    }
    struct FFTinfo<Mint> {
        root: Vec<Mint>,  // root[i]^(2^i) == 1
        iroot: Vec<Mint>, // root[i] * iroot[i] == 1
        rate2: Vec<Mint>,
        irate2: Vec<Mint>,
        rate3: Vec<Mint>,
        irate3: Vec<Mint>,
    }
    // returns minimum non-negative `x` s.t. `(n & (1 << x)) != 0`
    fn bsf(n: usize) -> usize {
        let mut x = 0;
        while (n & (1 << x)) == 0 {
            x += 1;
        }
        x
    }
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
            let mut rate2 =
                vec![Mint::new(0usize); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
            let mut irate2 =
                vec![Mint::new(0usize); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
            let mut rate3 =
                vec![Mint::new(0usize); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];
            let mut irate3 =
                vec![Mint::new(0usize); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];

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
    fn ceil_pow2(n: usize) -> usize {
        let mut x = 0;
        while (1 << x) < n {
            x += 1;
        }
        x
    }
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
                            (a0 + a1 + (Mint::get_mod() - a2) + (Mint::get_mod() - a3))
                                * irot2.val(),
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
}
use convolution::{convolution, convolution_i64};

mod manhattan_mst {
    use crate::change_min_max::ChangeMinMax;
    use crate::CoordinateCompress;
    use atcoder::segment_tree::SegmentTree;
    use atcoder::union_find::UnionFind;
    use std::cmp::{min, Reverse};
    use std::collections::BinaryHeap;
    pub struct ManhattanMST {
        points: Vec<(usize, (i64, i64))>,
    }
    impl ManhattanMST {
        pub fn new() -> Self {
            Self { points: vec![] }
        }
        pub fn push(&mut self, pt: (i64, i64)) {
            self.points.push((self.points.len(), pt));
        }
        fn mst(mut edges: Vec<(i64, usize, usize)>, n: usize) -> Vec<Vec<(i64, usize)>> {
            let mut uf = UnionFind::new(n);
            let mut g = vec![vec![]; n];
            edges.sort();
            for (delta, i, j) in edges {
                if !uf.same(i, j) {
                    uf.unite(i, j);
                    g[i].push((delta, j));
                    g[j].push((delta, i));
                }
            }
            g
        }
        pub fn minimum_spanning_tree(&mut self) -> Vec<Vec<(i64, usize)>> {
            let n = self.points.len();
            let mut edges = vec![];
            let inf = 1i64 << 60;
            for h0 in 0..2 {
                for h1 in 0..2 {
                    let y_enc = self
                        .points
                        .iter()
                        .map(|&(_i, (y, _x))| y)
                        .collect::<Vec<_>>()
                        .compress_encoder();
                    for h2 in 0..2 {
                        let mut st = SegmentTree::<(usize, i64)>::new(
                            n,
                            |(i0, ypx0), (i1, ypx1)| {
                                if ypx0 < ypx1 {
                                    (i0, ypx0)
                                } else {
                                    (i1, ypx1)
                                }
                            },
                            (0, inf),
                        );
                        self.points
                            .sort_by(|(_i0, (y0, x0)), (_i1, (y1, x1))| (y0 - x0).cmp(&(y1 - x1)));
                        for &(i, (y, x)) in self.points.iter() {
                            let ey = y_enc[&y];
                            let q = st.query(ey, n - 1);
                            if q.1 != inf {
                                let delta = q.1 - (y + x);
                                debug_assert!(delta >= 0);
                                edges.push((delta, i, q.0));
                            }
                            //
                            if st.get(ey).1 > y + x {
                                st.set(ey, (i, y + x));
                            }
                        }
                        if h2 == 0 {
                            self.points.iter_mut().for_each(|(_i, (_y, x))| *x = -(*x));
                        }
                    }
                    if h1 == 0 {
                        self.points.iter_mut().for_each(|(_i, (y, _x))| *y = -(*y));
                    }
                }
                if h0 == 0 {
                    self.points
                        .iter_mut()
                        .for_each(|(_i, (y, x))| std::mem::swap(x, y));
                }
            }
            Self::mst(edges, n)
        }
    }
}
use manhattan_mst::ManhattanMST;

mod mo {
    use std::iter::{Chain, Rev};
    use std::ops::{Range, RangeInclusive};
    use std::vec::IntoIter;
    pub struct Mo {
        ls: Vec<usize>,
        rs: Vec<usize>,
    }
    pub struct MoIterator {
        index_iter: IntoIter<usize>,
        ls: Vec<usize>,
        rs: Vec<usize>,
    }
    impl Mo {
        pub fn new() -> Self {
            Self {
                ls: vec![],
                rs: vec![],
            }
        }
        pub fn add_range_queue(&mut self, l: usize, r: usize) {
            self.ls.push(l);
            self.rs.push(r);
        }
        pub fn into_iter(self) -> MoIterator {
            let n = self.rs.iter().max().unwrap() + 1;
            let q = self.rs.len();
            let d = n / ((q as f64).sqrt() as usize + 1) + 1;
            let mut indexes = (0..q).collect::<Vec<_>>();
            indexes.sort_by_cached_key(|&i| {
                let div = self.ls[i] / d;
                if div % 2 == 0 {
                    (div, self.rs[i])
                } else {
                    (div, n - self.rs[i])
                }
            });
            MoIterator {
                index_iter: indexes.into_iter(),
                ls: self.ls,
                rs: self.rs,
            }
        }
        pub fn add_chain(
            l0: usize,
            r0: usize,
            l1: usize,
            r1: usize,
        ) -> Chain<Rev<Range<usize>>, RangeInclusive<usize>> {
            (l1..l0).rev().chain(r0 + 1..=r1)
        }
        pub fn remove_chain(
            l0: usize,
            r0: usize,
            l1: usize,
            r1: usize,
        ) -> Chain<Range<usize>, Rev<RangeInclusive<usize>>> {
            (l0..l1).chain(((r1 + 1)..=r0).rev())
        }
    }
    impl Iterator for MoIterator {
        type Item = (usize, (usize, usize));
        fn next(&mut self) -> Option<Self::Item> {
            if let Some(i) = self.index_iter.next() {
                Some((i, (self.ls[i], self.rs[i])))
            } else {
                None
            }
        }
    }
}
use mo::*;

// construct XOR basis.
// Some XOR combination of these can make every element of the array.
// When msb of a[i] is b-th, b-th bit of all the other element is zero.
fn xor_basis(a: &[usize]) -> Vec<usize> {
    let mut basis: Vec<usize> = vec![];
    for mut a in a.iter().copied() {
        for &base in basis.iter() {
            a.chmin(a ^ base);
        }
        for base in basis.iter_mut() {
            base.chmin(a ^ *base);
        }
        if a > 0 {
            basis.push(a);
        }
    }
    basis.sort();
    basis
}

mod transpose {
    pub trait Transpose<T> {
        fn transpose(self) -> Vec<Vec<T>>;
    }
    impl<T: Clone> Transpose<T> for Vec<Vec<T>> {
        fn transpose(self) -> Vec<Vec<T>> {
            (0..self[0].len())
                .map(|x| {
                    (0..self.len())
                        .map(|y| self[y][x].clone())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        }
    }
}
use transpose::Transpose;

fn show1d<T>(line: &[T])
where
    T: std::fmt::Debug,
{
    #[cfg(debug_assertions)]
    {
        use std::collections::VecDeque;
        let ln = line.len();
        let mx = line
            .iter()
            .map(|val| format!("{:?}", val).len())
            .max()
            .unwrap()
            + 2;
        fn to_string<X>(x: X, mx: usize) -> String
        where
            X: std::fmt::Debug,
        {
            let mut s = format!("{:?}", x).chars().collect::<VecDeque<char>>();
            let mut sw = 0;
            while s.len() < mx {
                if sw == 0 {
                    s.push_back(' ');
                } else {
                    s.push_front(' ');
                }
                sw ^= 1;
            }
            s.into_iter().collect::<String>()
        }
        let eprintln_split = || {
            eprint!("+");
            for _ in 0..ln {
                for _ in 0..mx {
                    eprint!("=");
                }
                eprint!("+");
            }
            eprintln!();
        };
        eprintln_split();
        {
            eprint!("|");
            for x in 0..ln {
                eprint!("{}", to_string::<usize>(x, mx));
                eprint!("|");
            }
            eprintln!();
        }
        eprintln_split();
        eprint!("|");
        for val in line {
            eprint!("{}|", to_string(val, mx));
        }
        eprintln!();
        eprintln_split();
    }
}

fn show2d<T>(table2d: &[Vec<T>])
where
    T: std::fmt::Debug,
{
    #[cfg(debug_assertions)]
    {
        use std::collections::VecDeque;
        let w = table2d[0].len();
        let mx = table2d
            .iter()
            .map(|line| {
                line.iter()
                    .map(|val| format!("{:?}", val).len())
                    .max()
                    .unwrap()
            })
            .max()
            .unwrap()
            + 2;
        fn to_string<X>(x: X, mx: usize) -> String
        where
            X: std::fmt::Debug,
        {
            let mut s = format!("{:?}", x).chars().collect::<VecDeque<char>>();
            let mut sw = 0;
            while s.len() < mx {
                if sw == 0 {
                    s.push_back(' ');
                } else {
                    s.push_front(' ');
                }
                sw ^= 1;
            }
            s.into_iter().collect::<String>()
        }
        let eprintln_split = |doubled: bool| {
            eprint!("+");
            for _ in 0..=w {
                for _ in 0..mx {
                    eprint!("{}", if doubled { '=' } else { '-' });
                }
                eprint!("+");
            }
            eprintln!();
        };
        eprintln_split(false);
        {
            eprint!("|");
            for x in 0..=w {
                let s = if x > 0 {
                    to_string::<usize>(x - 1, mx)
                } else {
                    (0..mx).map(|_| ' ').collect::<String>()
                };
                eprint!("{s}");
                eprint!("|");
            }
            eprintln!();
        }
        eprintln_split(true);
        for (y, line) in table2d.iter().enumerate() {
            eprint!("|");
            eprint!("{}", to_string(y, mx));
            eprint!("|");
            for val in line {
                eprint!("{}|", to_string(val, mx));
            }
            eprintln!();
            eprintln_split(false);
        }
    }
}

mod procon_reader {
    use std::fmt::Debug;
    use std::io::Read;
    use std::str::FromStr;
    pub fn read<T: FromStr>() -> T
    where
        <T as FromStr>::Err: Debug,
    {
        let stdin = std::io::stdin();
        let mut stdin_lock = stdin.lock();
        let mut u8b: [u8; 1] = [0];
        loop {
            let mut buf: Vec<u8> = Vec::with_capacity(16);
            loop {
                let res = stdin_lock.read(&mut u8b);
                if res.unwrap_or(0) == 0 || u8b[0] <= b' ' {
                    break;
                } else {
                    buf.push(u8b[0]);
                }
            }
            if !buf.is_empty() {
                let ret = String::from_utf8(buf).unwrap();
                return ret.parse().unwrap();
            }
        }
    }
    pub fn read_vec<T: std::str::FromStr>(n: usize) -> Vec<T>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..n).map(|_| read::<T>()).collect::<Vec<T>>()
    }
    pub fn read_mat<T: std::str::FromStr>(h: usize, w: usize) -> Vec<Vec<T>>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..h).map(|_| read_vec::<T>(w)).collect::<Vec<_>>()
    }
}
use procon_reader::*;
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////

#[fastout]
fn main() {
    read::<usize>();
}
