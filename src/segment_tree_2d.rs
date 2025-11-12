use crate::segment_tree::SegmentTree;
use cargo_snippet::snippet;

#[snippet("SegmentTree2D")]
#[derive(Clone)]
pub struct SegmentTree2D<T: Clone> {
    h: usize,
    w: usize,
    segs: Vec<SegmentTree<T>>,
    pair_op: fn(T, T) -> T,
}
#[snippet("SegmentTree2D")]
#[snippet(include = "SegmentTree")]
impl<T: Clone> SegmentTree2D<T> {
    pub fn new(h: usize, w: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
        Self {
            h,
            w,
            pair_op,
            segs: vec![SegmentTree::new(w, pair_op, ini_val); 2 * h],
        }
    }
    pub fn set(&mut self, mut y: usize, x: usize, val: T) {
        y += self.h;
        self.segs[y].set(x, val);
        let mut par = y / 2;
        while par >= 1 {
            let l = par * 2;
            let r = l + 1;
            let lv = self.segs[l].get(x);
            let rv = self.segs[r].get(x);
            let v = (self.pair_op)(lv, rv);
            self.segs[par].set(x, v);
            par /= 2;
        }
    }
    pub fn get(&self, y: usize, x: usize) -> T {
        self.segs[y + self.h].get(x)
    }
    // get query value of [a, b]
    pub fn query(&self, mut y0: usize, mut y1: usize, x0: usize, x1: usize) -> T {
        y0 += self.h;
        y1 += self.h + 1;
        let mut y0val = None;
        let mut bval = None;
        while y0 < y1 {
            if y0 % 2 == 1 {
                y0val = if let Some(aval0) = y0val {
                    Some((self.pair_op)(aval0, self.segs[y0].query(x0, x1)))
                } else {
                    Some(self.segs[y0].query(x0, x1))
                };
                y0 += 1;
            }
            if y1 % 2 == 1 {
                y1 -= 1;
                bval = if let Some(bval0) = bval {
                    Some((self.pair_op)(self.segs[y1].query(x0, x1), bval0))
                } else {
                    Some(self.segs[y1].query(x0, x1))
                };
            }
            y0 /= 2;
            y1 /= 2;
        }
        if let Some(y0val) = y0val {
            if let Some(bval) = bval {
                (self.pair_op)(y0val, bval)
            } else {
                y0val
            }
        } else {
            bval.unwrap()
        }
    }
}
impl<T: Copy + std::ops::Add<Output = T> + std::ops::Sub<Output = T>> SegmentTree2D<T> {
    pub fn add(&mut self, y: usize, x: usize, add_val: T) {
        self.set(y, x, self.get(y, x) + add_val);
    }
    pub fn sub(&mut self, y: usize, x: usize, sub_val: T) {
        self.set(y, x, self.get(y, x) - sub_val);
    }
}
mod tests {
    use super::SegmentTree2D;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    #[test]
    fn random_test() {
        use std::cmp::{max, min};
        const N: usize = 10;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for &f in [min, max, |x, y| x + y].iter() {
            let mut raw = vec![vec![0; N]; N];
            let mut seg = SegmentTree2D::<i64>::new(N, N, f, 0);
            for y in 0..N {
                for x in 0..N {
                    let v = rng.random_range(0..100) as i64;
                    seg.set(y, x, v);
                    raw[y][x] = v;
                }
            }
            for y0 in 0..N {
                for y1 in y0..N {
                    for x0 in 0..N {
                        for x1 in x0..N {
                            let seg_v = seg.query(y0, y1, x0, x1);
                            let mut raw_v = raw[y0][x0];
                            for y in y0..=y1 {
                                for x in x0..=x1 {
                                    if (y, x) == (y0, x0) {
                                        continue;
                                    }
                                    raw_v = f(raw_v, raw[y][x]);
                                }
                            }
                            assert_eq!(seg_v, raw_v);
                        }
                    }
                }
            }
        }
    }
}
