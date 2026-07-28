use cargo_snippet::snippet;

#[snippet("LazySegmentTree")]
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
#[snippet("LazySegmentTree")]
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
#[snippet("LazySegmentTree")]
impl<X: Clone + std::fmt::Display, M: Clone + std::fmt::Display> std::fmt::Display
    for LazySegmentTree<X, M>
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.fmt_base(f, |x: &X| format!("{}", x), |m: &M| format!("{}", m))
    }
}
#[snippet("LazySegmentTree")]
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
