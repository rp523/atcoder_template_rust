#![allow(unused_macros, unused_imports, dead_code)]
use proconio::input;
use proconio::marker::Usize1;
use std::cmp::{max, min, Reverse};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::mem::swap;
use std::ops::Div;

fn main() {
}

/*************************************************************************************/
/*************************************************************************************/

pub trait ChangeMinMax {
    fn chmin(&mut self, rhs: Self) -> bool;
    fn chmax(&mut self, rhs: Self) -> bool;
}
impl<T: PartialOrd + Copy> ChangeMinMax for T {
    fn chmin(&mut self, rhs: Self) -> bool {
        let mut ret = false;
        if *self > rhs {
            *self = rhs;
            ret = true;
        }
        ret
    }
    fn chmax(&mut self, rhs: Self) -> bool {
        let mut ret = false;
        if *self < rhs {
            *self = rhs;
            ret = true;
        }
        ret
    }
}

pub trait RepeatedSquaring {
    fn power(self, p: i32) -> Self;
}
impl<T: std::ops::MulAssign + std::ops::Div<Output = T> + Copy> RepeatedSquaring for T {
    fn power(self, mut p: i32) -> Self {
        #[allow(clippy::eq_op)]
        let mut ret: Self = self / self;
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

struct UnionFind {
    pub graph: Vec<Vec<usize>>,
    parents: Vec<usize>,
    grp_sz: Vec<usize>,
    grp_num: usize,
}
impl UnionFind {
    fn new(sz: usize) -> Self {
        Self {
            graph: vec![vec![]; sz],
            parents: (0..sz).collect::<Vec<usize>>(),
            grp_sz: vec![1; sz],
            grp_num: sz,
        }
    }
    fn root(&mut self, v: usize) -> usize {
        if v == self.parents[v] {
            v
        } else {
            self.parents[v] = self.root(self.parents[v]);
            self.parents[v]
        }
    }
    fn same(&mut self, a: usize, b: usize) -> bool {
        self.root(a) == self.root(b)
    }
    fn unite(&mut self, into: usize, from: usize) {
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
    fn group_num(&self) -> usize {
        self.grp_num
    }
    fn group_size(&mut self, a: usize) -> usize {
        let ra = self.root(a);
        self.grp_sz[ra]
    }
}

struct SegmentTree<T> {
    n2: usize,   // implemented leaf num (2^n)
    neff: usize, // effective vector length
    dat: Vec<T>,
    pair_op: fn(T, T) -> T,
}
impl<T: Copy> SegmentTree<T> {
    fn new(n: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
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
    fn set(&mut self, mut pos: usize, val: T) {
        pos += self.n2 - 1;
        self.dat[pos] = val;
        while pos > 0 {
            pos = (pos - 1) / 2; // parent
            self.dat[pos] = (self.pair_op)(self.dat[pos * 2 + 1], self.dat[pos * 2 + 2]);
        }
    }
    fn get(&self, pos: usize) -> T {
        self.dat[pos + self.n2 - 1]
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
    // get query value of [a, b]
    fn query(&self, a: usize, b: usize) -> T {
        self.query_sub(a, b + 1, 0, 0, self.n2)
    }
}
