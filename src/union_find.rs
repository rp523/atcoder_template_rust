use cargo_snippet::snippet;

#[snippet("UnionFind")]
#[derive(Debug, Clone)]
pub struct UnionFind {
    pub graph: Vec<Vec<usize>>,
    potential: Vec<i64>,
    parents: Vec<usize>,
    grp_sz: Vec<usize>,
    grp_num: usize,
}

#[snippet("UnionFind")]
impl UnionFind {
    pub fn new(sz: usize) -> Self {
        Self {
            graph: vec![vec![]; sz],
            potential: vec![0; sz],
            parents: (0..sz).collect::<Vec<usize>>(),
            grp_sz: vec![1; sz],
            grp_num: sz,
        }
    }
    pub fn root(&mut self, v: usize) -> usize {
        if v == self.parents[v] {
            v
        } else {
            let pv = self.parents[v];
            let rv = self.root(pv);
            self.potential[v] += self.potential[pv];
            self.parents[v] = rv;
            self.parents[v]
        }
    }
    pub fn get_delta(&mut self, v0: usize, v1: usize) -> Option<i64> {
        if !self.same(v0, v1) {
            return None;
        }
        Some(self.potential[v1] - self.potential[v0])
    }
    pub fn same(&mut self, a: usize, b: usize) -> bool {
        self.root(a) == self.root(b)
    }
    pub fn unite(&mut self, into: usize, from: usize) -> bool {
        self.unite_with_delta(into, from, 0)
    }
    pub fn unite_with_delta(&mut self, into: usize, from: usize, delta: i64) -> bool {
        self.graph[into].push(from);
        self.graph[from].push(into);
        let r_into = self.root(into);
        let r_from = self.root(from);
        if r_into == r_from {
            return false;
        }
        self.parents[r_from] = r_into;
        self.potential[r_from] = self.potential[into] - self.potential[from] + delta;
        self.grp_sz[r_into] += self.grp_sz[r_from];
        self.grp_sz[r_from] = 0;
        self.grp_num -= 1;
        true
    }
    pub fn group_num(&self) -> usize {
        self.grp_num
    }
    pub fn group_size(&mut self, a: usize) -> usize {
        let ra = self.root(a);
        self.grp_sz[ra]
    }
}
