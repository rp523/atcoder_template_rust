use cargo_snippet::snippet;

#[snippet("PersistentSegmentTree")]
#[derive(Clone)]
pub struct PersistentNode<T: Clone> {
    l: usize,
    r: usize,
    val: T,
}
#[snippet("PersistentSegmentTree")]
#[derive(Clone)]
pub struct PersistentSegmentTree<T: Clone> {
    n: usize,
    n2: usize,
    nodes: Vec<PersistentNode<T>>,
    ver_roots: Vec<usize>,
    pair_op: fn(T, T) -> T,
}
#[snippet("PersistentSegmentTree")]
impl<T: Clone> PersistentSegmentTree<T> {
    pub fn from_vec(pair_op: fn(T, T) -> T, ini_values: Vec<T>) -> Self {
        let n = ini_values.len();
        let mut n2 = 1;
        while n2 < n {
            n2 *= 2;
        }
        let temp_val = ini_values[0].clone();
        let mut nodes = vec![
            PersistentNode::<T> {
                l: 0,
                r: 0,
                val: temp_val.clone(),
            };
            n2
        ];
        for val in ini_values {
            nodes.push(PersistentNode::<T> { l: 0, r: 0, val });
        }
        for i in (1..n2).rev() {
            let l = 2 * i;
            let r = 2 * i + 1;
            nodes[i] = PersistentNode::<T> {
                l: if l >= nodes.len() { 0 } else { l },
                r: if r >= nodes.len() { 0 } else { r },
                val: if l >= nodes.len() {
                    temp_val.clone()
                } else if r >= nodes.len() {
                    nodes[l].val.clone()
                } else {
                    (pair_op)(nodes[l].val.clone(), nodes[r].val.clone())
                },
            };
        }
        Self {
            n,
            n2,
            ver_roots: vec![1],
            nodes,
            pair_op,
        }
    }
    pub fn set(&mut self, ver: usize, i: usize, new_val: T) -> usize {
        let ver_toot_new = self.set_impl(self.ver_roots[ver], self.n2, i, &new_val);
        self.ver_roots.push(ver_toot_new);
        self.ver_roots.len() - 1
    }
    fn set_impl(&mut self, now: usize, node_size: usize, i: usize, new_val: &T) -> usize {
        if node_size == 1 {
            self.nodes.push(PersistentNode {
                l: 0,
                r: 0,
                val: new_val.clone(),
            });
            self.nodes.len() - 1
        } else {
            let half = node_size / 2;
            let (l, r) = if i < half {
                (
                    self.set_impl(self.nodes[now].l, half, i, new_val),
                    self.nodes[now].r,
                )
            } else {
                (
                    self.nodes[now].l,
                    self.set_impl(self.nodes[now].r, half, i - half, new_val),
                )
            };
            self.nodes.push(PersistentNode {
                l,
                r,
                val: (self.pair_op)(self.nodes[l].val.clone(), self.nodes[r].val.clone()),
            });
            self.nodes.len() - 1
        }
    }
    pub fn query(&self, ver: usize, l: usize, r: usize) -> T {
        self.query_impl(self.ver_roots[ver], self.n2, l, r + 1)
    }
    fn query_impl(&self, now: usize, node_size: usize, l: usize, r: usize) -> T {
        debug_assert!(r - l <= node_size);
        if r - l == node_size {
            self.nodes[now].val.clone()
        } else {
            let half = node_size / 2;
            debug_assert!(half > 0);
            debug_assert!(self.nodes[now].l > 0);
            if r == 0 || r <= half {
                // only left half
                self.query_impl(self.nodes[now].l, half, l, r)
            } else if half <= l {
                // only right half
                self.query_impl(self.nodes[now].r, half, l - half, r - half)
            } else {
                // split
                (self.pair_op)(
                    self.query_impl(self.nodes[now].l, half, l, half),
                    self.query_impl(self.nodes[now].r, half, 0, r - half),
                )
            }
        }
    }
    pub fn get(&self, ver: usize, i: usize) -> T {
        self.get_impl(self.ver_roots[ver], self.n2, i)
    }
    fn get_impl(&self, now: usize, node_size: usize, i: usize) -> T {
        debug_assert!(now < self.nodes.len());
        if node_size == 1 {
            return self.nodes[now].val.clone();
        }
        let half = node_size / 2;
        debug_assert!(half > 0);
        if i < half {
            self.get_impl(self.nodes[now].l, half, i)
        } else {
            self.get_impl(self.nodes[now].r, half, i - half)
        }
    }
}
#[snippet("PersistentSegmentTree")]
impl<T: Clone + std::fmt::Debug> std::fmt::Debug for PersistentSegmentTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "[")?;
        for ver in 0..self.ver_roots.len() {
            write!(f, "[")?;
            for i in 0..self.n {
                write!(f, "{:?}", self.get(ver, i))?;
                if i < self.n - 1 {
                    write!(f, ", ")?
                }
            }
            writeln!(f, "]")?;
        }
        write!(f, "]")
    }
}
#[snippet("PersistentSegmentTree")]
impl<T: Clone + std::fmt::Display> std::fmt::Display for PersistentSegmentTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "[")?;
        for ver in 0..self.ver_roots.len() {
            write!(f, "[")?;
            for i in 0..self.n {
                write!(f, "{}", self.get(ver, i))?;
                if i < self.n - 1 {
                    write!(f, ", ")?
                }
            }
            writeln!(f, "]")?;
        }
        write!(f, "]")
    }
}

mod test {
    #[test]
    pub fn random() {
        use super::PersistentSegmentTree;
        use crate::segment_tree::SegmentTree;
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaChaRng;
        const T: usize = 64;
        const N: usize = 32;
        const V: i32 = 100;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for f in [std::cmp::max, std::cmp::min, |x, y| x + y] {
            for _ in 0..T {
                let n = rng.random_range(1..=N);
                let mut pseg = PersistentSegmentTree::<i32>::from_vec(f, vec![0; n]);
                let mut segs = vec![SegmentTree::<i32>::from_vec(f, vec![0; n])];
                for _ in 0..T {
                    let pver = rng.random_range(0..segs.len());
                    let at = rng.random_range(0..n);
                    let val = rng.random_range(-V..=V);
                    let mut nseg = segs[pver].clone();
                    nseg.set(at, val);
                    segs.push(nseg);
                    assert_eq!(segs.len() - 1, pseg.set(pver, at, val));
                    for (ver, seg) in segs.iter().enumerate() {
                        for i in 0..n {
                            for j in i..n {
                                let expected = seg.query(i, j);
                                let actual = pseg.query(ver, i, j);
                                assert_eq!(expected, actual);
                            }
                            assert_eq!(seg.get(i), pseg.get(ver, i));
                        }
                    }
                }
            }
        }
    }
}
