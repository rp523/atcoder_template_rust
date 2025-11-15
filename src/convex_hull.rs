use cargo_snippet::snippet;
use crate::rational::Rational;

#[snippet("ConvexHull")]
#[snippet(include = "Rational")]
pub struct ConvexHull {
    x_ys: std::collections::BTreeMap<i64, Vec<i64>>,
}
#[snippet("ConvexHull")]
impl ConvexHull {
    pub fn new() -> Self {
        Self {
            x_ys: std::collections::BTreeMap::new(),
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
        let mut seen = std::collections::BTreeSet::new();
        for (y, x) in lower_yx.into_iter().chain(upper_yx.into_iter()) {
            if seen.contains(&(y, x)) {
                continue;
            }
            ret.push((y, x));
            seen.insert((y, x));
        }
        ret
    }
    fn weakly_monotone_tangents(x_ys: &[(i64, Vec<i64>)]) -> std::collections::VecDeque<(i64, i64)> {
        let mut vs = std::collections::VecDeque::new();
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
#[snippet("ConvexHull")]
#[derive(Clone, Debug)]
pub struct ConvexHullTrickMaxImpl<T> {
    lines: std::collections::BTreeMap<T, T>,   // slope, intercept
    borders: std::collections::BTreeMap<T, T>, // x, slope
}
#[snippet("ConvexHull")]
impl<T> ConvexHullTrickMaxImpl<T>
where
    T: Clone
        + Copy
        + PartialEq
        + Eq
        + PartialOrd
        + Ord
        + std::ops::Add<Output = T>
        + std::ops::Sub<Output = T>
        + std::ops::Mul<Output = T>
        + std::ops::Div<Output = T>
        + std::fmt::Debug,
{
    pub fn new() -> Self {
        Self {
            lines: std::collections::BTreeMap::new(),
            borders: std::collections::BTreeMap::new(),
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
        let mut del_lines = std::collections::VecDeque::new();
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
#[snippet("ConvexHull")]
pub struct ConvexHullTrickMinImpl<T> {
    cht: ConvexHullTrickMaxImpl<T>,
}
#[snippet("ConvexHull")]
impl<T> ConvexHullTrickMinImpl<T>
where
    T: Clone
        + Copy
        + PartialEq
        + Eq
        + PartialOrd
        + Ord
        + std::ops::Add<Output = T>
        + std::ops::Sub<Output = T>
        + std::ops::Mul<Output = T>
        + std::ops::Div<Output = T>
        + std::ops::Neg<Output = T>
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
#[snippet("ConvexHull")]
pub struct ConvexHullTrickMax {
    cht: ConvexHullTrickMaxImpl<Rational>,
}
#[snippet("ConvexHull")]
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
#[snippet("ConvexHull")]
pub struct ConvexHullTrickMin {
    cht: ConvexHullTrickMinImpl<Rational>,
}
#[snippet("ConvexHull")]
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