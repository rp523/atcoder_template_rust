use cargo_snippet::snippet;

#[snippet("RootedTree")]
pub struct RootedTree {
    n: usize,
    root: usize,
    rise_tbl: Vec<Vec<usize>>,
    dist: Vec<usize>,
    depth: Vec<usize>,
    pub graph: Vec<Vec<(usize, usize)>>,
    edge_cnt: usize,
}
#[snippet("RootedTree")]
impl RootedTree {
    pub fn new(n: usize, root: usize) -> RootedTree {
        let mut doubling_bit_width = 0;
        while (1 << doubling_bit_width) < n {
            doubling_bit_width += 1;
        }
        RootedTree {
            n,
            root,
            rise_tbl: vec![vec![0; n]; doubling_bit_width],
            dist: vec![0; n],
            depth: vec![0; n],
            graph: vec![vec![]; n],
            edge_cnt: 0,
        }
    }
    pub fn unite(&mut self, a: usize, b: usize) {
        self.unite_with_distance(a, b, 1);
    }
    pub fn unite_with_distance(&mut self, a: usize, b: usize, delta: usize) {
        self.graph[a].push((b, delta));
        self.graph[b].push((a, delta));
        self.edge_cnt += 1;
        if self.edge_cnt >= self.n - 1 {
            self.analyze(self.root);
        }
    }
    pub fn step_back(&self, from: usize, step: usize) -> usize {
        let mut v = from;
        for (di, rise_tbl) in self.rise_tbl.iter().enumerate().rev() {
            if ((step >> di) & 1) != 0 {
                v = rise_tbl[v];
            }
        }
        v
    }
    fn dfs(
        v: usize,
        pre: usize,
        graph: &Vec<Vec<(usize, usize)>>,
        dist: &mut Vec<usize>,
        depth: &mut Vec<usize>,
        rise_tbl: &mut [usize],
    ) {
        for &(nv, delta) in graph[v].iter() {
            if nv == pre {
                continue;
            }
            depth[nv] = depth[v] + 1;
            dist[nv] = dist[v] + delta;
            rise_tbl[nv] = v;
            Self::dfs(nv, v, graph, dist, depth, rise_tbl);
        }
    }
    fn analyze(&mut self, root: usize) {
        self.dist[root] = 0;
        self.depth[root] = 0;
        self.rise_tbl[0][root] = root;
        Self::dfs(
            root,
            self.graph.len(),
            &self.graph,
            &mut self.dist,
            &mut self.depth,
            &mut self.rise_tbl[0],
        );
        // doubling
        for di in (0..self.rise_tbl.len()).skip(1) {
            for v in 0_usize..self.n {
                self.rise_tbl[di][v] = self.rise_tbl[di - 1][self.rise_tbl[di - 1][v]];
            }
        }
    }
    pub fn lca(&self, mut a: usize, mut b: usize) -> usize {
        if self.depth[a] > self.depth[b] {
            std::mem::swap(&mut a, &mut b);
        }
        assert!(self.depth[a] <= self.depth[b]);
        // bring up the deeper one to the same depth of the shallower one.
        for rise_tbl in self.rise_tbl.iter().rev() {
            let rise_b = rise_tbl[b];
            if self.depth[a] <= self.depth[rise_b] {
                b = rise_b;
            }
        }
        assert!(self.depth[a] == self.depth[b]);
        if a != b {
            // simultaneously rise to the next depth of LCA.
            for rise_tbl in self.rise_tbl.iter().rev() {
                if rise_tbl[a] != rise_tbl[b] {
                    a = rise_tbl[a];
                    b = rise_tbl[b];
                }
            }
            // 1-depth higher level is LCA.
            a = self.rise_tbl[0][a];
            b = self.rise_tbl[0][b];
        }
        assert!(a == b);
        a
    }
    pub fn distance(&self, a: usize, b: usize) -> usize {
        let lca_v = self.lca(a, b);
        self.dist[a] + self.dist[b] - 2 * self.dist[lca_v]
    }
}

#[cfg(test)]
pub mod test {
    use std::collections::VecDeque;

    #[test]
    pub fn random() {
        use super::RootedTree;
        use crate::union_find::UnionFind;
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaChaRng;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        const N: usize = 20;
        const T: usize = 100;
        const D: usize = 100;
        for n in 1..=N {
            for ti in 0..T {
                let mut uf = UnionFind::new(n);
                let mut es = vec![];
                while uf.group_num() > 1 {
                    let a = rng.random_range(0..n);
                    let b = (a + 1 + rng.random_range(0..n - 1)) % n;
                    assert!(a != b);
                    if !uf.unite(a, b) {
                        continue;
                    }
                    let d = rng.random_range(1..=D);
                    es.push((a, b, d));
                }
                fn calc_distance(
                    v: usize,
                    p: usize,
                    t: usize,
                    g: &[Vec<(usize, usize)>],
                ) -> Option<usize> {
                    if v == t {
                        return Some(0);
                    }
                    for &(nv, delta) in g[v].iter() {
                        if nv == p {
                            continue;
                        }
                        if let Some(nxt) = calc_distance(nv, v, t, g) {
                            return Some(nxt + delta);
                        }
                    }
                    None
                }
                for root in 0..n {
                    let mut g = vec![vec![]; n];
                    let mut t = RootedTree::new(n, root);
                    for &(a, b, d) in es.iter() {
                        g[a].push((b, d));
                        g[b].push((a, d));
                        t.unite_with_distance(a, b, d);
                    }
                    let mut back = vec![0; n];
                    let mut que = VecDeque::new();
                    let mut vis = vec![false; n];
                    que.push_back(root);
                    vis[root] = true;
                    back[root] = root;
                    while let Some(v0) = que.pop_front() {
                        for &(v1, _) in g[v0].iter() {
                            if vis[v1] {
                                continue;
                            }
                            vis[v1] = true;
                            que.push_back(v1);
                            back[v1] = v0;
                        }
                    }
                    for v0 in 0..n {
                        for v1 in 0..n {
                            let expected = calc_distance(v0, n, v1, &g).unwrap();
                            let actual = t.distance(v0, v1);
                            assert_eq!(expected, actual);
                        }
                        /*
                        for step in 0..=n {
                            let mut expected = v0;
                            for _ in 0..step {
                                expected = back[expected];
                            }
                            let actual = t.step_back(v0, step);
                            assert_eq!(expected, actual);
                        }
                         */
                    }
                }
            }
        }
    }
}
