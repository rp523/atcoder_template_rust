use cargo_snippet::snippet;

#[snippet("SegmentTree")]
#[derive(Clone)]
pub struct SegmentTree<T> {
    n: usize,
    n2: usize,
    height: usize,
    width: Vec<usize>,
    dat: Vec<T>,
    pair_op: fn(T, T) -> T,
}
#[snippet("SegmentTree")]
impl<T: Clone> SegmentTree<T> {
    pub fn new(n: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
        Self::from_vec(pair_op, vec![ini_val; n])
    }
    pub fn from_vec(pair_op: fn(T, T) -> T, ini_values: Vec<T>) -> Self {
        let n = ini_values.len();
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
        let mut dat = vec![ini_values[0].clone(); n2 + n];
        dat.iter_mut()
            .skip(n2)
            .zip(ini_values)
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
        Self {
            n,
            n2,
            height,
            width,
            pair_op,
            dat,
        }
    }
    pub fn set(&mut self, mut i: usize, val: T) {
        i += self.n2;
        self.dat[i] = val;
        for hi in 1..self.height {
            let p = i >> hi;
            let l = p * 2;
            let r = l + 1;
            let cend = (self.n2 >> (hi - 1)) + self.width[hi - 1];
            self.dat[p] = if r < cend {
                (self.pair_op)(self.dat[l].clone(), self.dat[r].clone())
            } else {
                self.dat[l].clone()
            };
        }
    }
    pub fn get(&self, pos: usize) -> T {
        self.dat[pos + self.n2].clone()
    }
    pub fn query_all(&mut self) -> T {
        self.query(0, self.n - 1)
    }
    pub fn query_left(&self, r: usize) -> T {
        self.query(0, r)
    }
    pub fn query_right(&self, l: usize) -> T {
        self.query(l, self.n - 1)
    }
    // get query value of [a, b]
    pub fn query(&self, mut l: usize, mut r: usize) -> T {
        l += self.n2;
        r += self.n2 + 1;
        let mut lcum = None;
        let mut rcum = None;
        for hi in 0..self.height {
            let end = (self.n2 >> hi) + self.width[hi];
            if l % 2 == 1 {
                debug_assert!(l < end);
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
    pub fn right_rise(&self, l: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
        self.right_fall(l, |x| !jdg(x))
    }
    pub fn right_fall(&self, l: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
        let mut v = l + self.n2;
        if !jdg(self.dat[v].clone()) {
            return Some(l);
        }
        if jdg(self.query(l, self.n - 1)) {
            return None;
        }
        let mut true_fix = None;
        loop {
            let ev = if let Some(true_fix) = true_fix.clone() {
                (self.pair_op)(true_fix, self.dat[v].clone())
            } else {
                self.dat[v].clone()
            };
            if jdg(ev.clone()) {
                if v & 1 != 0 {
                    v += 1;
                    true_fix = Some(ev);
                }
                v /= 2;
            } else {
                break;
            }
        }
        while v < self.n2 {
            let lc = v * 2;
            let rc = lc + 1;
            let ev_lc = if let Some(true_fix) = true_fix.clone() {
                (self.pair_op)(true_fix, self.dat[lc].clone())
            } else {
                self.dat[lc].clone()
            };
            if !jdg(ev_lc.clone()) {
                v = lc;
            } else {
                v = rc;
                true_fix = Some(ev_lc);
            }
        }
        Some(v - self.n2)
    }
    pub fn left_rise(&self, r: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
        self.left_fall(r, |x| !jdg(x))
    }
    pub fn left_fall(&self, r: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
        let mut v = r + self.n2 + 1;
        if !jdg(self.dat[v - 1].clone()) {
            return Some(r);
        }
        if jdg(self.query(0, r)) {
            return None;
        }
        let mut true_fix = None;
        loop {
            let ev = if let Some(true_fix) = true_fix.clone() {
                (self.pair_op)(self.dat[v - 1].clone(), true_fix)
            } else {
                self.dat[v - 1].clone()
            };
            if jdg(ev.clone()) {
                if v & 1 != 0 {
                    v -= 1;
                    true_fix = Some(ev);
                }
                v /= 2;
            } else {
                break;
            }
        }
        v -= 1;
        while v < self.n2 {
            let lc = v * 2;
            let rc = lc + 1;
            let ev_rc = if let Some(true_fix) = true_fix.clone() {
                (self.pair_op)(self.dat[rc].clone(), true_fix)
            } else {
                self.dat[rc].clone()
            };
            if !jdg(ev_rc.clone()) {
                v = rc;
            } else {
                v = lc;
                true_fix = Some(ev_rc);
            }
        }
        Some(v - self.n2)
    }
    pub fn right_true_max(&self, l: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
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
    pub fn right_false_max(&self, l: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
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
    pub fn left_true_max(&self, r: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
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
    pub fn left_false_max(&self, r: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
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
        x_to_string: fn(&T) -> String,
    ) -> std::fmt::Result {
        let mut now = 1;
        let mut delta = 1;
        for hi in (0..self.height).rev() {
            for x in (now..).take(self.width[hi]) {
                write!(f, "{} ", x_to_string(&self.dat[x]),)?;
            }
            writeln!(f)?;
            now += delta;
            delta *= 2;
        }
        Ok(())
    }
}
impl<T: Copy + std::ops::Add<Output = T> + std::ops::Sub<Output = T>> SegmentTree<T> {
    pub fn add(&mut self, pos: usize, add_val: T) {
        self.set(pos, self.get(pos) + add_val);
    }
    pub fn sub(&mut self, pos: usize, sub_val: T) {
        self.set(pos, self.get(pos) - sub_val);
    }
}
impl<T: Clone + std::fmt::Display> std::fmt::Display for SegmentTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.fmt_base(f, |x: &T| format!("{}", x))
    }
}
impl<T: Clone + std::fmt::Debug> std::fmt::Debug for SegmentTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.fmt_base(f, |x: &T| format!("{:?}", x))
    }
}
pub mod test {
    #[test]
    pub fn query() {
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaChaRng;
        const T: usize = 100;
        const N: usize = 100;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for n in 1..=N {
            let mut a = vec![0; n];
            let mut seg = super::SegmentTree::<usize>::from_vec(std::cmp::max, a.clone());
            for _ in 0..T {
                a.iter_mut().enumerate().for_each(|(i, a)| {
                    *a = rng.random_range(0..N);
                    seg.set(i, *a);
                });
                for l in 0..n {
                    for r in l..n {
                        let &expected = a[l..=r].iter().max().unwrap();
                        let actual = seg.query(l, r);
                        assert_eq!(expected, actual);
                    }
                }
            }
        }
    }
    #[test]
    fn binary_search() {
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaChaRng;
        const T: usize = 100;
        const N: usize = 100;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for n in 1..=N {
            let mut a = vec![0; n];
            let mut seg = super::SegmentTree::<usize>::from_vec(std::cmp::max, a.clone());
            for _ in 0..T {
                a.iter_mut().enumerate().for_each(|(i, a)| {
                    *a = rng.random_range(0..N);
                    seg.set(i, *a);
                });
                for v in 0..=N {
                    let lower = |x| x < v;
                    let upper = |x| x >= v;
                    for l in 0..n {
                        let actural = seg.right_fall(l, lower);
                        assert_eq!(actural, seg.right_rise(l, upper));
                        let mut expected = None;
                        for r in l..n {
                            if upper(seg.query(l, r)) {
                                expected = Some(r);
                                break;
                            }
                        }
                        assert_eq!(expected, actural);
                    }
                    for r in 0..n {
                        let actural = seg.left_fall(r, lower);
                        assert_eq!(actural, seg.left_rise(r, upper));
                        let mut expected = None;
                        for l in (0..=r).rev() {
                            if upper(seg.query(l, r)) {
                                expected = Some(l);
                                break;
                            }
                        }
                        assert_eq!(expected, actural);
                    }
                }
            }
        }
    }
}
