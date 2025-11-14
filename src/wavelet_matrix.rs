use cargo_snippet::snippet;

#[snippet("BitVector")]
#[derive(Clone)]
pub struct BitVector {
    bits: Vec<u64>,
    cum_ones: Vec<u32>,
    zero_num: usize,
}
#[snippet("BitVector")]
const W: usize = 64;
#[snippet("BitVector")]
const LOG_W: usize = 6;
#[snippet("BitVector")]
impl BitVector {
    pub fn from_vec(a: &[u64], di: usize) -> Self {
        let ln = a.len() / W + 1;
        let mut bits = vec![0; ln];
        for (i, &a) in a.iter().enumerate() {
            let d = i >> LOG_W;
            let r = i & (W - 1);
            bits[d] |= ((a >> di) & 1) << r;
        }
        let cum_ones = bits
            .iter()
            .map(|&bit| bit.count_ones())
            .scan(0, |cum: &mut u32, x: u32| {
                *cum += x;
                Some(*cum)
            })
            .collect::<Vec<_>>();
        let zero_num = a.len() - cum_ones[ln - 1] as usize;
        Self {
            bits,
            cum_ones,
            zero_num,
        }
    }
    // count 1 in 0..i
    #[inline(always)]
    pub fn rank1(&self, i: usize) -> usize {
        let d = i >> LOG_W;
        let r = i & (W - 1);
        (if d == 0 {
            (self.bits[d] & ((1u64 << r) - 1)).count_ones()
        } else {
            self.cum_ones[d - 1] + (self.bits[d] & ((1u64 << r) - 1)).count_ones()
        }) as usize
    }
    #[inline(always)]
    pub fn zero_num(&self) -> usize {
        self.zero_num
    }
    // count 0 in 0..i
    #[inline(always)]
    pub fn rank0(&self, i: usize) -> usize {
        i - self.rank1(i)
    }
    #[inline(always)]
    pub fn get(&self, i: usize) -> bool {
        let d = i >> LOG_W;
        let r = i & (W - 1);
        (self.bits[d] >> r) & 1 != 0
    }
}

#[cfg(test)]
mod test {
    use super::BitVector;
    use super::W;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    #[test]
    fn random_test() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        const D: usize = 10;
        for n in 1..W * 5 {
            let a = (0..n)
                .map(|_| rng.random_range(0..(1u64 << D)))
                .collect::<Vec<_>>();
            let bit_vectors = (0..D)
                .map(|di| BitVector::from_vec(&a, di))
                .collect::<Vec<_>>();
            let mut rank0 = vec![0; D];
            let mut rank1 = vec![0; D];
            for i in 0..n {
                for di in 0..D {
                    if ((a[i] >> di) & 1) != 0 {
                        rank1[di] += 1;
                    } else {
                        rank0[di] += 1;
                    }
                    assert_eq!(((a[i] >> di) & 1) != 0, bit_vectors[di].get(i));
                    assert_eq!(0, bit_vectors[di].rank0(0));
                    assert_eq!(0, bit_vectors[di].rank1(0));
                    assert_eq!(rank0[di], bit_vectors[di].rank0(i + 1));
                    assert_eq!(rank1[di], bit_vectors[di].rank1(i + 1));
                }
            }
        }
    }
}

#[snippet("WaveletMatrix")]
#[snippet(include = "BitVector")]
#[derive(Clone)]
pub struct WaveletMatrix {
    bit_vectors: Vec<BitVector>,
}
#[snippet("WaveletMatrix")]
impl WaveletMatrix {
    // construct. O(N * log(ValueMax))
    pub fn new(mut a: Vec<u64>) -> Self {
        let &mx = a.iter().max().unwrap();
        let mut d = 0;
        while mx & !((1u64 << d) - 1) != 0 {
            d += 1;
        }
        let mut bit_vectors = vec![];
        for di in (0..d).rev() {
            // calc
            let bit_vector = BitVector::from_vec(&a, di);
            // sort a
            a = a
                .iter()
                .filter(|&a| ((a >> di) & 1) == 0)
                .copied()
                .chain(a.iter().filter(|&a| ((a >> di) & 1) != 0).copied())
                .collect::<Vec<_>>();
            // record
            bit_vectors.push(bit_vector);
        }
        bit_vectors.reverse();
        Self { bit_vectors }
    }
    // get a[i]. O(log(ValueMax))
    pub fn get(&self, mut i: usize) -> u64 {
        let mut val = 0;
        for (di, bit_vector) in self.bit_vectors.iter().enumerate().rev() {
            if bit_vector.get(i) {
                val |= 1u64 << di;
                i = bit_vector.zero_num() + bit_vector.rank1(i);
            } else {
                i = bit_vector.rank0(i);
            }
        }
        val
    }
    // count value s.t. lower <= value < upper, in a[l..r]. O(log(ValueMax))
    pub fn range_freq(&self, lower: u64, upper: u64, l: usize, r: usize) -> usize {
        self.low_freq(upper, l, r) - self.low_freq(lower, l, r)
    }
    // count value s.t. value < upper, in a[l..r]. O(log(ValueMax))
    fn low_freq(&self, upper: u64, mut l: usize, mut r: usize) -> usize {
        if upper & !((1u64 << self.bit_vectors.len()) - 1) != 0 {
            return r - l;
        }
        let mut lows = 0;
        for (di, bit_vector) in self.bit_vectors.iter().enumerate().rev() {
            let c0_left = bit_vector.rank0(l);
            let c1_left = bit_vector.rank1(l);
            let c0_in = bit_vector.rank0(r) - c0_left;
            let c1_in = bit_vector.rank1(r) - c1_left;
            if ((upper >> di) & 1) == 0 {
                // next0
                l = c0_left;
                r = c0_left + c0_in;
            } else {
                lows += c0_in;
                // next 1
                let zero_num = bit_vector.zero_num();
                l = zero_num + c1_left;
                r = zero_num + c1_left + c1_in;
            }
            if l >= r {
                break;
            }
        }
        lows
    }
    // get k-th smallest value in a[l..r]. O(log(ValueMax))
    pub fn range_kth_smallest(&self, mut l: usize, mut r: usize, mut k: usize) -> u64 {
        let mut val = 0;
        for (di, bit_vector) in self.bit_vectors.iter().enumerate().rev() {
            let c0_left = bit_vector.rank0(l);
            let c1_left = bit_vector.rank1(l);
            let c0_in = bit_vector.rank0(r) - c0_left;
            let c1_in = bit_vector.rank1(r) - c1_left;
            if c0_in > k {
                // next0
                l = c0_left;
                r = c0_left + c0_in;
            } else {
                // next 1
                let zero_num = bit_vector.zero_num();
                l = zero_num + c1_left;
                r = zero_num + c1_left + c1_in;
                k -= c0_in;
                val |= 1u64 << di;
            }
            if l >= r {
                break;
            }
        }
        val
    }
}

#[cfg(test)]
mod wavelet_matrix_test {
    use super::*;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    const T: usize = 300;
    const N: usize = 30;
    const UPPER: u64 = 30;
    #[test]
    fn get() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for _ in 0..T {
            let a = (0..N)
                .map(|_| rng.random_range(0..UPPER))
                .collect::<Vec<_>>();
            let wm = WaveletMatrix::new(a.clone());
            for (i, a) in a.into_iter().enumerate() {
                let chk = wm.get(i);
                assert_eq!(a, chk);
            }
        }
    }
    #[test]
    fn low_freq() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for _ in 0..T {
            let a = (0..N)
                .map(|_| rng.random_range(0..UPPER))
                .collect::<Vec<_>>();
            let wm = WaveletMatrix::new(a.clone());
            for l in 0..N {
                for r in l..=N {
                    for upper in 0..=UPPER {
                        let exp = (l..r).map(|i| a[i]).filter(|&a| a < upper).count();
                        let act = wm.low_freq(upper, l, r);
                        assert_eq!(act, exp);
                    }
                }
            }
        }
    }
    #[test]
    fn range_freq() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for _ in 0..T {
            let a = (0..N)
                .map(|_| rng.random_range(0..UPPER))
                .collect::<Vec<_>>();
            let wm = WaveletMatrix::new(a.clone());
            for l in 0..N {
                for r in l..N {
                    for lower in 0..UPPER {
                        for upper in lower..=UPPER {
                            let exp = (l..r)
                                .map(|i| a[i])
                                .filter(|&a| lower <= a && a < upper)
                                .count();
                            let act = wm.range_freq(lower, upper, l, r);
                            assert_eq!(act, exp);
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn range_kth_smallest() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for _ in 0..T {
            let a = (0..N)
                .map(|_| rng.random_range(0..UPPER))
                .collect::<Vec<_>>();
            let wm = WaveletMatrix::new(a.clone());
            for l in 0..N {
                for r in l..=N {
                    let mut sub = (l..r).map(|i| a[i]).collect::<Vec<_>>();
                    sub.sort();
                    for (k, exp) in sub.into_iter().enumerate() {
                        let act = wm.range_kth_smallest(l, r, k);
                        assert_eq!(act, exp);
                    }
                }
            }
        }
    }
}

#[snippet("WaveletMatrix2D")]
#[snippet(include = "WaveletMatrix")]
#[derive(Clone)]
pub struct WaveletMatrix2D {
    h: usize,
    w: usize,
    pos_vectors: Vec<WaveletMatrix>,
}
#[snippet("WaveletMatrix2D")]
impl WaveletMatrix2D {
    pub fn new(a: Vec<Vec<u64>>) -> Self {
        let h = a.len();
        let w = a[0].len();
        let &mx = a.iter().map(|org| org.iter().max().unwrap()).max().unwrap();
        let mut d = 0;
        while mx & !((1u64 << d) - 1) != 0 {
            d += 1;
        }
        let mut xa = vec![];
        for a in a {
            for (x1, val) in a.into_iter().enumerate() {
                xa.push((x1, val));
            }
        }
        let mut pos_vectors = vec![];
        for di in (0..d).rev() {
            // calc
            let wm1 = WaveletMatrix::new(
                xa.iter()
                    .map(|&(x, a)| if ((a >> di) & 1) == 0 { x } else { w } as u64)
                    .collect::<Vec<_>>(),
            );
            // sort a
            xa = xa
                .iter()
                .filter(|(_x, a)| ((a >> di) & 1) == 0)
                .copied()
                .chain(xa.iter().filter(|(_x, a)| ((a >> di) & 1) != 0).copied())
                .collect::<Vec<_>>();
            // record
            pos_vectors.push(wm1);
        }
        pos_vectors.reverse();
        Self { h, w, pos_vectors }
    }
    // get k-th smallest value in a[y0..y1][x0..x1]. O(log(ValueMax) * log(W))
    pub fn range_kth_smallest(
        &self,
        y0: usize,
        y1: usize,
        x0: usize,
        x1: usize,
        mut k: usize,
    ) -> u64 {
        let mut val = 0;
        let mut l = y0 * self.w;
        let mut r = y1 * self.w;
        for (di, pos_vector) in self.pos_vectors.iter().enumerate().rev() {
            let c0_left = pos_vector.range_freq(0, self.w as u64, 0, l);
            let c0val_left = pos_vector.range_freq(x0 as u64, x1 as u64, 0, l);
            let c1_left = l - c0_left;
            debug_assert!(c0val_left <= c0_left);
            let c0_in = pos_vector.range_freq(0, self.w as u64, l, r);
            let c0val_in = pos_vector.range_freq(x0 as u64, x1 as u64, l, r);
            debug_assert!(c0val_in <= c0_in);
            let c1_in = (r - l) - c0_in;
            if c0val_in > k {
                // next0
                l = c0_left;
                r = c0_left + c0_in;
            } else {
                // next 1
                k -= c0val_in;
                let zero_num = pos_vector.range_freq(0, self.w as u64, 0, self.h * self.w);
                l = zero_num + c1_left;
                r = zero_num + c1_left + c1_in;
                val |= 1u64 << di;
            }
            if l >= r {
                break;
            }
        }
        val
    }
    // count value s.t. lower <= value < upper, in a[y0..y1][x0..x1]. O(log(ValueMax) * log(W))
    pub fn range_freq(
        &self,
        y0: usize,
        y1: usize,
        x0: usize,
        x1: usize,
        lower: u64,
        upper: u64,
    ) -> usize {
        self.low_freq(y0, y1, x0, x1, upper) - self.low_freq(y0, y1, x0, x1, lower)
    }
    // count value s.t. value < upper, in a[y0..y1][x0..x1]. O(log(ValueMax) * log(W))
    fn low_freq(&self, y0: usize, y1: usize, x0: usize, x1: usize, upper: u64) -> usize {
        if upper & !((1u64 << self.pos_vectors.len()) - 1) != 0 {
            return (y1 - y0) * (x1 - x0);
        }
        let area = self.h * self.w;
        let mut cnt = 0;
        let mut l = y0 * self.w;
        let mut r = y1 * self.w;
        for (di, pos_vector) in self.pos_vectors.iter().enumerate().rev() {
            let c0_left = pos_vector.range_freq(0, self.w as u64, 0, l);
            let c1_left = l - c0_left;
            let c0_in = pos_vector.range_freq(0, self.w as u64, l, r);
            let c0val_in = pos_vector.range_freq(x0 as u64, x1 as u64, l, r);
            debug_assert!(c0val_in <= c0_in);
            let c1_in = (r - l) - c0_in;
            if ((upper >> di) & 1) == 0 {
                // next0
                l = c0_left;
                r = c0_left + c0_in;
            } else {
                cnt += c0val_in;
                // next 1
                let zero_num = pos_vector.range_freq(0, self.w as u64, 0, area);
                l = zero_num + c1_left;
                r = zero_num + c1_left + c1_in;
            }
            if l >= r {
                break;
            }
        }
        cnt
    }
}

#[cfg(test)]
mod wavelet_matrix_2d_test {
    use super::WaveletMatrix2D;
    use crate::segment_tree::SegmentTree;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    const HMAX: usize = 8;
    const WMAX: usize = 8;
    const UPPER: u64 = 8;
    #[test]
    fn range_kth_smallest() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for h in 1..=HMAX {
            for w in 1..=WMAX {
                let a = (0..h)
                    .map(|_| {
                        (0..w)
                            .map(|_| rng.random_range(0..UPPER))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                let wm = WaveletMatrix2D::new(a.clone());
                for y0 in 0..h {
                    for y1 in y0..=h {
                        for x0 in 0..w {
                            for x1 in x0..=w {
                                let mut v = vec![];
                                for y in y0..y1 {
                                    for x in x0..x1 {
                                        v.push(a[y][x]);
                                    }
                                }
                                v.sort();
                                for (k, expected) in v.into_iter().enumerate() {
                                    let actual = wm.range_kth_smallest(y0, y1, x0, x1, k);
                                    assert_eq!(expected, actual);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn range_freq() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for h in 1..=HMAX {
            for w in 1..=WMAX {
                let a = (0..h)
                    .map(|_| {
                        (0..w)
                            .map(|_| rng.random_range(0..UPPER))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                let wm = WaveletMatrix2D::new(a.clone());
                for y0 in 0..h {
                    for y1 in y0..=h {
                        for x0 in 0..w {
                            for x1 in x0..=w {
                                let mut seg =
                                    SegmentTree::<usize>::new(UPPER as usize, |x, y| x + y, 0);
                                for y in y0..y1 {
                                    for x in x0..x1 {
                                        seg.add(a[y][x] as usize, 1);
                                    }
                                }
                                for lower in 0..UPPER {
                                    for upper in lower..=UPPER {
                                        let low_expected = if upper == 0 {
                                            0
                                        } else {
                                            seg.query(0, upper as usize - 1)
                                        };
                                        let low_actual = wm.low_freq(y0, y1, x0, x1, upper);
                                        assert_eq!(low_actual, low_expected);
                                        let range_expected = if lower == upper {
                                            0
                                        } else {
                                            seg.query(lower as usize, upper as usize - 1)
                                        };
                                        let range_actual =
                                            wm.range_freq(y0, y1, x0, x1, lower, upper);
                                        assert_eq!(range_actual, range_expected);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
