use crate::segment_tree::SegmentTree;
use crate::union_find::UnionFind;
use cargo_snippet::snippet;

#[snippet("ManhattanMST")]
#[snippet(include = "SegmentTree")]
#[snippet(include = "UnionFind")]
pub struct ManhattanMST {
    points: Vec<(usize, (i64, i64))>,
}
#[snippet("ManhattanMST")]
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
                    .collect::<std::collections::BTreeSet<_>>()
                    .into_iter()
                    .enumerate()
                    .map(|(i, v)| (v, i))
                    .collect::<std::collections::BTreeMap<_, _>>();
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
