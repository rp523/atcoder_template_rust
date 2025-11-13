use cargo_snippet::snippet;

#[snippet("Scc")]
pub struct Scc {
    n: usize,
    pub graph: Vec<Vec<usize>>,
    bwd_graph: Vec<Vec<usize>>,
}
#[snippet("Scc")]
impl Scc {
    pub fn new(n: usize) -> Scc {
        Scc {
            n,
            graph: vec![vec![]; n],
            bwd_graph: vec![vec![]; n],
        }
    }
    pub fn add(&mut self, from: usize, into: usize) {
        self.graph[from].push(into);
        self.bwd_graph[into].push(from);
    }
    pub fn decompose(&mut self) -> Vec<Vec<usize>> {
        let mut scc = Vec::<Vec<usize>>::new();
        let mut fwd_seen = vec![false; self.n];
        let mut order = Vec::<usize>::new();
        for i in 0..self.n {
            if !fwd_seen[i] {
                Scc::fwd_dfs(&self.graph, i, None, &mut fwd_seen, &mut order);
            }
        }
        order.reverse();
        let mut bwd_seen = vec![false; self.n];
        for i_ in &order {
            let i = *i_;
            if !bwd_seen[i] {
                let mut grp = Vec::<usize>::new();
                Scc::bwd_dfs(&self.bwd_graph, i, None, &mut bwd_seen, &mut grp);
                grp.reverse();
                scc.push(grp);
            }
        }
        scc
    }
    fn bwd_dfs(
        graph: &Vec<Vec<usize>>,
        v: usize,
        pre: Option<usize>,
        seen: &mut Vec<bool>,
        grp: &mut Vec<usize>,
    ) {
        seen[v] = true;
        for nv_ in &graph[v] {
            let nv = *nv_;
            if let Some(pre_v) = pre {
                if nv == pre_v {
                    continue;
                }
            }
            if !seen[nv] {
                Scc::bwd_dfs(graph, nv, Some(v), seen, grp);
            }
        }
        grp.push(v);
    }
    fn fwd_dfs(
        graph: &Vec<Vec<usize>>,
        v: usize,
        pre: Option<usize>,
        seen: &mut Vec<bool>,
        order: &mut Vec<usize>,
    ) {
        seen[v] = true;
        for nv_ in &graph[v] {
            let nv = *nv_;
            if let Some(pre_v) = pre {
                if nv == pre_v {
                    continue;
                }
            }
            if !seen[nv] {
                Scc::fwd_dfs(graph, nv, Some(v), seen, order);
            }
        }
        order.push(v);
    }
}
