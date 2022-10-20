#![allow(unused_macros, unused_imports)]
use proconio::input;
use proconio::marker::Usize1;

macro_rules! dbg {
    ($($xs:expr),+) => {
        if cfg!(debug_assertions) {
            std::dbg!($($xs),+)
        } else {
            ($($xs),+)
        }
    }
}

fn main() {
}
