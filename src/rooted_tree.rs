use crate::union_find::UnionFind;
use cargo_snippet::snippet;

#[snippet("RootedTree")]
#[snippet(include = "UnionFind")]
pub struct RootedTree {
    n: usize,
    doubling_bit_width: usize,
    root: usize,
    rise_tbl: Vec<Vec<Option<usize>>>,
    dist: Vec<Option<i64>>,
    step: Vec<Option<usize>>,
    pub graph: Vec<Vec<(i64, usize)>>,
    edge_cnt: usize,
    uf: UnionFind,
}
#[snippet("RootedTree")]
impl RootedTree {
    pub fn new(n: usize, root: usize) -> RootedTree {
        let mut doubling_bit_width = 1;
        while (1 << doubling_bit_width) < n {
            doubling_bit_width += 1;
        }
        RootedTree {
            n,
            doubling_bit_width,
            root,
            rise_tbl: vec![vec![None; n]; doubling_bit_width],
            dist: vec![None; n],
            step: vec![None; n],
            graph: vec![vec![]; n],
            edge_cnt: 0,
            uf: UnionFind::new(n),
        }
    }
    pub fn unite(&mut self, a: usize, b: usize) {
        self.unite_with_distance(a, b, 1);
    }
    pub fn unite_with_distance(&mut self, a: usize, b: usize, delta: i64) {
        self.graph[a].push((delta, b));
        self.graph[b].push((delta, a));
        self.edge_cnt += 1;
        self.uf.unite(a, b);
        if self.edge_cnt >= self.n - 1 {
            if self.uf.group_num() != 1 {
                panic!("nodes are NOT connected into one union.")
            }
            self.analyze(self.root);
        }
    }
    pub fn stepback(&self, from: usize, step: usize) -> usize {
        let mut v = from;
        for d in (0..self.doubling_bit_width - 1).rev() {
            if ((step >> d) & 1) != 0 {
                v = self.rise_tbl[d][v].unwrap();
            }
        }
        v
    }
    fn dfs(
        v: usize,
        pre: Option<usize>,
        graph: &Vec<Vec<(i64, usize)>>,
        dist: &mut Vec<Option<i64>>,
        step: &mut Vec<Option<usize>>,
        rise_tbl: &mut Vec<Vec<Option<usize>>>,
    ) {
        for (delta, nv) in graph[v].iter() {
            if let Some(pre) = pre {
                if *nv == pre {
                    continue;
                }
            }
            if dist[*nv].is_none() {
                dist[*nv] = Some(dist[v].unwrap() + *delta);
                step[*nv] = Some(step[v].unwrap() + 1);
                rise_tbl[0][*nv] = Some(v);
                Self::dfs(*nv, Some(v), graph, dist, step, rise_tbl);
            }
        }
    }
    fn analyze(&mut self, root: usize) {
        self.dist[root] = Some(0);
        self.step[root] = Some(0);
        self.rise_tbl[0][root] = Some(root);
        Self::dfs(
            root,
            None,
            &self.graph,
            &mut self.dist,
            &mut self.step,
            &mut self.rise_tbl,
        );
        // doubling
        for d in (0..self.doubling_bit_width).skip(1) {
            for v in 0_usize..self.n {
                self.rise_tbl[d][v] = self.rise_tbl[d - 1][self.rise_tbl[d - 1][v].unwrap()];
            }
        }
    }
    pub fn lca(&self, mut a: usize, mut b: usize) -> usize {
        if self.step[a] > self.step[b] {
            std::mem::swap(&mut a, &mut b);
        }
        assert!(self.step[a] <= self.step[b]);
        // bring up the deeper one to the same level of the shallower one.
        for d in (0..self.doubling_bit_width).rev() {
            let rise_v = self.rise_tbl[d][b].unwrap();
            if self.step[rise_v] >= self.step[a] {
                b = rise_v;
            }
        }
        assert!(self.step[a] == self.step[b]);
        if a != b {
            // simultaneously rise to the previous level of LCA.
            for d in (0..self.doubling_bit_width).rev() {
                if self.rise_tbl[d][a] != self.rise_tbl[d][b] {
                    a = self.rise_tbl[d][a].unwrap();
                    b = self.rise_tbl[d][b].unwrap();
                }
            }
            // 1-step higher level is LCA.
            a = self.rise_tbl[0][a].unwrap();
            b = self.rise_tbl[0][b].unwrap();
        }
        assert!(a == b);
        a
    }
    pub fn distance(&self, a: usize, b: usize) -> i64 {
        let lca_v = self.lca(a, b);
        self.dist[a].unwrap() + self.dist[b].unwrap() - 2 * self.dist[lca_v].unwrap()
    }
}
