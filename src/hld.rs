use crate::union_find::UnionFind;
use cargo_snippet::snippet;

#[snippet("Hld")]
#[snippet(include = "UnionFind")]
// use entry order as inclusive array range, for segment-tree.
#[derive(Clone, Debug)]
pub struct Hld {
    root: usize,
    g: Vec<Vec<usize>>,
    uf: UnionFind,
    order: Vec<(usize, usize)>,
    head: Vec<usize>,
    par: Vec<usize>,
}
#[snippet("Hld")]
impl Hld {
    pub fn new(n: usize, root: usize) -> Self {
        Self {
            root,
            g: vec![vec![]; n],
            uf: UnionFind::new(n),
            order: vec![(0, 0); n],
            head: vec![root; n],
            par: vec![root; n],
        }
    }
    pub fn unite(&mut self, a: usize, b: usize) {
        debug_assert!(!self.g[a].contains(&b));
        debug_assert!(!self.g[b].contains(&a));
        debug_assert!(!self.uf.same(a, b));
        self.g[a].push(b);
        self.g[b].push(a);
        self.uf.unite(a, b);
        if self.uf.group_num() == 1 {
            self.build();
        }
    }
    fn build(&mut self) {
        let n = self.g.len();
        debug_assert_eq!(self.root, self.par[self.root]);
        dfs1(self.root, n, &mut self.g, &mut self.par, &mut vec![1; n]);
        dfs2(
            self.root,
            n,
            &self.g,
            &mut self.order,
            &mut self.head,
            &mut 0,
        );
        fn dfs1(
            v: usize,
            p: usize,
            g: &mut [Vec<usize>],
            par: &mut [usize],
            sz: &mut [usize],
        ) -> usize {
            let first_ei = if g[v][0] == p { 1 } else { 0 };
            for ei in 0..g[v].len() {
                let nv = g[v][ei];
                if nv == p {
                    continue;
                }
                par[nv] = v;
                sz[v] += dfs1(nv, v, g, par, sz);
                if ei != first_ei && sz[g[v][first_ei]] < sz[nv] {
                    g[v].swap(first_ei, ei);
                }
            }
            sz[v]
        }
        fn dfs2(
            v: usize,
            p: usize,
            g: &[Vec<usize>],
            order: &mut [(usize, usize)],
            head: &mut [usize],
            now: &mut usize,
        ) {
            order[v].0 = *now;
            *now += 1;
            for (ei, &nv) in g[v].iter().enumerate() {
                if nv == p {
                    continue;
                }
                head[nv] = if ei == 0 { head[v] } else { nv };
                dfs2(nv, v, g, order, head, now);
            }
            order[v].1 = *now - 1;
        }
    }
    pub fn iter_vertex(&self, a: usize, b: usize) -> VertexIterator<'_> {
        VertexIterator::new(a, b, self)
    }
    pub fn iter_edges(&self, a: usize, b: usize) -> EdgeIterator<'_> {
        EdgeIterator::new(a, b, self)
    }
    pub fn lca(&self, mut a: usize, mut b: usize) -> usize {
        loop {
            match self.order[self.head[a]].0.cmp(&self.order[self.head[b]].0) {
                std::cmp::Ordering::Less => {
                    b = self.par[self.head[b]];
                }
                std::cmp::Ordering::Greater => {
                    a = self.par[self.head[a]];
                }
                std::cmp::Ordering::Equal => {
                    if self.order[a].0 > self.order[b].0 {
                        a = b;
                    }
                    break;
                }
            }
        }
        a
    }
    pub fn subtree_vertex(&self, subroot: usize) -> (usize, usize) {
        self.order[subroot]
    }
}
#[snippet("Hld")]
pub struct VertexIterator<'a> {
    ab: Option<(usize, usize)>,
    hld: &'a Hld,
}
#[snippet("Hld")]
impl<'a> VertexIterator<'a> {
    pub fn new(a: usize, b: usize, hld: &'a Hld) -> Self {
        Self {
            ab: Some((a, b)),
            hld,
        }
    }
}
#[snippet("Hld")]
impl<'a> Iterator for VertexIterator<'a> {
    type Item = (usize, usize);
    fn next(&mut self) -> Option<Self::Item> {
        let (mut a, mut b) = self.ab?;
        if self.hld.head[a] == self.hld.head[b] {
            let (ea, eb) = (self.hld.order[a].0, self.hld.order[b].0);
            self.ab = None;
            if ea < eb {
                Some((ea, eb))
            } else {
                Some((eb, ea))
            }
        } else if self.hld.order[a].0 < self.hld.order[b].0 {
            // lift up b
            let ret = (self.hld.order[self.hld.head[b]].0, self.hld.order[b].0);
            b = self.hld.par[self.hld.head[b]];
            self.ab = Some((a, b));
            Some(ret)
        } else {
            // lift up a
            let ret = (self.hld.order[self.hld.head[a]].0, self.hld.order[a].0);
            a = self.hld.par[self.hld.head[a]];
            self.ab = Some((a, b));
            Some(ret)
        }
    }
}
#[snippet("Hld")]
pub struct EdgeIterator<'a> {
    vit: VertexIterator<'a>,
}
#[snippet("Hld")]
impl<'a> EdgeIterator<'a> {
    pub fn new(a: usize, b: usize, hld: &'a Hld) -> Self {
        Self {
            vit: VertexIterator::new(a, b, hld),
        }
    }
}
#[snippet("Hld")]
impl<'a> Iterator for EdgeIterator<'a> {
    type Item = (usize, usize);
    fn next(&mut self) -> Option<Self::Item> {
        let (a, b) = self.vit.next()?;
        if a == b {
            return None;
        }
        Some((a - 1, b - 1))
    }
}

#[cfg(test)]
mod test {
    use super::Hld;
    use crate::union_find::UnionFind;
    use rand::{seq::SliceRandom, SeedableRng};
    use rand_chacha::ChaChaRng;
    use std::collections::{BTreeSet, VecDeque};
    fn initialize(n: usize, rng: &mut ChaChaRng) -> (Vec<Vec<usize>>, Vec<(usize, usize)>, Hld) {
        let mut es0 = vec![];
        for a in 0..n {
            for b in 0..n {
                if a == b {
                    continue;
                }
                es0.push((a, b));
            }
        }
        es0.shuffle(rng);
        let mut uf = UnionFind::new(n);
        let mut g = vec![vec![]; n];
        let mut es = vec![];
        let mut hld = Hld::new(n, 0);
        for (a, b) in es0 {
            if uf.same(a, b) {
                continue;
            }
            uf.unite(a, b);
            g[a].push(b);
            g[b].push(a);
            es.push((a, b));
            hld.unite(a, b);
        }
        (g, es, hld)
    }
    #[test]
    fn iter_vertex() {
        const T: usize = 10;
        const NMAX: usize = 100;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for n in 1..=NMAX {
            for _ in 0..T {
                let (g, _es, hld) = initialize(n, &mut rng);
                let mut order = vec![0; n];
                for v in 0..n {
                    for (i0, i1) in hld.iter_vertex(v, v) {
                        assert_eq!(i0, i1);
                        order[v] = i0;
                    }
                }
                for a in 0..n {
                    for b in 0..n {
                        let mut que = VecDeque::new();
                        que.push_back(a);
                        let mut vis = BTreeSet::new();
                        vis.insert(a);
                        let mut par = vec![a; n];
                        while let Some(v0) = que.pop_front() {
                            for &v1 in g[v0].iter() {
                                if !vis.insert(v1) {
                                    continue;
                                }
                                par[v1] = v0;
                                que.push_back(v1);
                            }
                        }
                        let expected = {
                            let mut v = b;
                            let mut expected = vec![order[b]];
                            while v != a {
                                v = par[v];
                                expected.push(order[v]);
                            }
                            expected.sort();
                            expected
                        };
                        let mut actual = vec![];
                        for (l, r) in hld.iter_vertex(a, b) {
                            for v in l..=r {
                                actual.push(v);
                            }
                        }
                        actual.sort();
                        assert_eq!(expected, actual);
                    }
                }
            }
        }
    }
    #[test]
    fn lca() {
        const T: usize = 100;
        const NMAX: usize = 100;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for n in 1..=NMAX {
            for _ in 0..T {
                let (g, _es, hld) = initialize(n, &mut rng);
                let mut depth = vec![n; n];
                let mut par = vec![0; n];
                depth[0] = 0;
                let mut que = VecDeque::new();
                que.push_back(0);
                while let Some(v0) = que.pop_front() {
                    let d0 = depth[v0];
                    let d1 = d0 + 1;
                    for &v1 in g[v0].iter() {
                        if depth[v1] > d1 {
                            depth[v1] = d1;
                            par[v1] = v0;
                            que.push_back(v1);
                        }
                    }
                }
                let lca_expected = |mut a: usize, mut b: usize| -> usize {
                    while a != b {
                        if depth[a] < depth[b] {
                            b = par[b];
                        } else {
                            a = par[a];
                        }
                    }
                    a
                };
                for a in 0..n {
                    for b in 0..n {
                        assert_eq!(lca_expected(a, b), hld.lca(a, b));
                    }
                }
            }
        }
    }
}
