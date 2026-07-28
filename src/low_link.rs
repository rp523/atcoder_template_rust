use cargo_snippet::snippet;

#[snippet("LowLink")]
#[snippet("LowLink")]
#[derive(Clone, Debug)]
pub struct LowLink {
    g: Vec<Vec<usize>>,
    built: bool,
    ord: Vec<usize>,
    low: Vec<usize>,
}
#[snippet("LowLink")]
impl LowLink {
    pub fn new(n: usize) -> Self {
        Self {
            g: vec![vec![]; n],
            built: false,
            ord: vec![n; n],
            low: vec![n; n],
        }
    }
    pub fn unite(&mut self, a: usize, b: usize) {
        self.g[a].push(b);
        self.g[b].push(a);
    }
    pub fn is_bridge(&mut self, a: usize, b: usize) -> bool {
        if !self.built {
            self.build();
            self.built = true;
        }
        let (vp, vc) = if self.ord[a] < self.ord[b] {
            (a, b)
        } else {
            (b, a)
        };
        self.ord[vp] < self.low[vc]
    }
    fn build(&mut self) {
        let n = self.g.len();
        for v in 0..n {
            if self.ord[v] < n {
                continue;
            }
            dfs(
                v,
                self.g.len(),
                &self.g,
                &mut self.ord,
                &mut self.low,
                &mut 0,
            );
        }
        fn dfs(
            v: usize,
            pv: usize,
            g: &[Vec<usize>],
            ord: &mut [usize],
            low: &mut [usize],
            nxt: &mut usize,
        ) -> usize {
            let n = g.len();
            ord[v] = *nxt;
            low[v] = *nxt;
            *nxt += 1;
            for &nv in &g[v] {
                if nv == pv {
                    continue;
                }
                low[v] = std::cmp::min(
                    low[v],
                    if ord[nv] == n {
                        dfs(nv, v, g, ord, low, nxt)
                    } else {
                        ord[nv]
                    },
                );
            }
            low[v]
        }
    }
}

#[test]
fn low_link() {
    use crate::union_find::UnionFind;
    use rand::{Rng, SeedableRng};
    use rand_chacha::*;
    let mut rng = ChaChaRng::from_seed([0; 32]);
    const TEST: usize = 10000;
    const NMIN: usize = 2;
    const NMAX: usize = 20;
    for _ in 0..TEST {
        let n = NMIN + (rng.random_range(0..NMAX - NMIN + 1));
        let m = 1 + (rng.random_range(0..(n * (n - 1)) / 2));
        let mut es = vec![];
        let mut uf0 = UnionFind::new(n);
        let mut ll = LowLink::new(n);
        for _ in 0..m {
            let a = rng.random_range(0..n - 1);
            let b = a + 1 + rng.random_range(0..n - a - 1);
            es.push((a, b));
            uf0.unite(a, b);
            ll.unite(a, b);
        }
        for &(cut_a, cut_b) in es.iter() {
            let mut uf = UnionFind::new(n);
            for &(a, b) in es.iter().filter(|&&(a, b)| (a, b) != (cut_a, cut_b)) {
                uf.unite(a, b);
            }
            let expected_split = uf0.group_num() != uf.group_num();
            let actual_split = ll.is_bridge(cut_a, cut_b);
            assert_eq!(expected_split, actual_split);
        }
    }
}
