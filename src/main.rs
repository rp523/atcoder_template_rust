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
