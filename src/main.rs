#![allow(unused_macros, unused_imports)]
use proconio::input;
use proconio::marker::Usize1;
use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
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
