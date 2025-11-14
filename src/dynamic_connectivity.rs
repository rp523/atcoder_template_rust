#[derive(Clone, Copy, PartialEq)]
enum SplayDir {
    None = 0,
    Left,
    Right,
}
mod euler_step {
    use super::SplayDir;
    #[derive(Clone)]
    pub struct EulerStep {
        // splay
        pub left: *mut EulerStep,
        pub right: *mut EulerStep,
        pub parent: *mut EulerStep,
        // euler tour
        pub from: usize,
        pub to: usize,
        pub size: usize,
        pub at_this_level: bool,
        pub at_this_level_subany: bool,
        pub useless_connected: bool,
        pub useless_connected_subany: bool,
        // state
        value: i64,
        value_sum: i64,
    }
    impl EulerStep {
        pub fn new(from: usize, to: usize) -> Self {
            Self {
                // splay
                left: std::ptr::null_mut(),
                right: std::ptr::null_mut(),
                parent: std::ptr::null_mut(),
                // euler tour
                from,
                to,
                size: if from == to { 1 } else { 0 },
                at_this_level: from < to,
                at_this_level_subany: from < to,
                useless_connected: false,
                useless_connected_subany: false,
                value: 0,
                value_sum: 0,
            }
        }
        fn root(&mut self) -> *mut EulerStep {
            let mut t = self as *mut Self;
            unsafe {
                while !(*t).parent.is_null() {
                    t = (*t).parent;
                }
            }
            t
        }
        pub fn same(s: *mut Self, t: *mut Self) -> bool {
            if s.is_null() {
                debug_assert!(!t.is_null());
                return false;
            }
            if t.is_null() {
                debug_assert!(!s.is_null());
                return false;
            }
            unsafe {
                (*s).splay();
                (*t).splay();
                (*s).root() == (*t).root()
            }
        }
        pub fn update(&mut self) {
            self.size = if self.from == self.to { 1 } else { 0 };
            self.at_this_level_subany = self.at_this_level;
            self.useless_connected_subany = self.useless_connected;
            self.value_sum = self.value;
            let left = self.left;
            let right = self.right;
            unsafe {
                if !left.is_null() {
                    self.size += (*left).size;
                    self.at_this_level_subany =
                        self.at_this_level_subany || (*left).at_this_level_subany;
                    self.useless_connected_subany =
                        self.useless_connected_subany || (*left).useless_connected_subany;
                    self.value_sum += (*left).value_sum;
                }
                if !right.is_null() {
                    self.size += (*right).size;
                    self.at_this_level_subany =
                        self.at_this_level_subany || (*right).at_this_level_subany;
                    self.useless_connected_subany =
                        self.useless_connected_subany || (*right).useless_connected_subany;
                    self.value_sum += (*right).value_sum;
                }
            }
        }
        pub fn splay(&mut self) {
            while self.for_parent() != SplayDir::None {
                unsafe {
                    let p = self.parent;
                    let p_for_pp = (*p).for_parent();
                    if p_for_pp == SplayDir::None {
                        // zig
                        self.rotate();
                    } else if p_for_pp == self.for_parent() {
                        // zig zig
                        (*p).rotate();
                        self.rotate();
                    } else {
                        // zig zag
                        self.rotate();
                        self.rotate();
                    }
                }
            }
        }
        fn for_parent(&mut self) -> SplayDir {
            if self.parent.is_null() {
                SplayDir::None
            } else {
                unsafe {
                    let me = self as *mut Self;
                    if (*self.parent).left == me {
                        SplayDir::Left
                    } else {
                        debug_assert!((*self.parent).right == me);
                        SplayDir::Right
                    }
                }
            }
        }
        fn rotate(&mut self) {
            let p = self.parent;
            debug_assert!(!p.is_null());
            let me = self as *mut Self;
            unsafe {
                debug_assert!((*me).for_parent() != SplayDir::None);
                let pp = (*p).parent;
                let c;
                if (*me).for_parent() == SplayDir::Left {
                    c = (*me).right;
                    (*me).right = p;
                    (*p).left = c;
                } else {
                    c = (*me).left;
                    (*me).left = p;
                    (*p).right = c;
                }
                if !pp.is_null() {
                    if (*pp).left == p {
                        (*pp).left = me;
                    } else {
                        (*pp).right = me;
                    }
                }
                (*me).parent = pp;
                (*p).parent = me;
                if !c.is_null() {
                    (*c).parent = p;
                }
                (*p).update();
            }
            self.update();
        }
        pub fn merge(mut s: *mut Self, mut t: *mut Self) -> *mut Self {
            if s.is_null() {
                debug_assert!(!t.is_null());
                return t;
            }
            if t.is_null() {
                debug_assert!(!s.is_null());
                return s;
            }
            unsafe {
                s = (*s).root();
                t = (*t).root();
                while !(*s).right.is_null() {
                    s = (*s).right;
                }
                (*s).splay();
                (*s).right = t;
                (*t).parent = s;
                (*s).update();
            }
            s
        }
        pub fn split(s: *mut Self) -> (*mut Self, *mut Self) // (..s, s..)
        {
            unsafe {
                (*s).splay();
                let t = (*s).left;
                if !t.is_null() {
                    (*t).parent = std::ptr::null_mut();
                }
                (*s).left = std::ptr::null_mut();
                (*s).update();
                (t, s)
            }
        }
        pub fn set_value(&mut self, value: i64) {
            self.value = value;
        }
        pub fn get_value(&self) -> i64 {
            self.value
        }
        pub fn get_sum(&self) -> i64 {
            self.value_sum
        }
    }
}
mod euler_tree {
    use super::euler_step::EulerStep;
    use std::collections::HashMap;
    pub struct EulerTour {
        tour: Vec<HashMap<usize, Box<EulerStep>>>,
    }
    impl EulerTour {
        pub fn new(n: usize) -> Self {
            Self {
                tour: (0..n)
                    .map(|i| {
                        let mut mp = HashMap::new();
                        mp.insert(i, Box::new(EulerStep::new(i, i)));
                        mp
                    })
                    .collect::<Vec<_>>(),
            }
        }
        pub fn get_node(&mut self, from: usize, to: usize) -> *mut EulerStep {
            self.tour[from]
                .entry(to)
                .or_insert_with(|| Box::new(EulerStep::new(from, to)));
            &mut **self.tour[from].get_mut(&to).unwrap()
        }
        #[allow(unused_assignments)]
        fn re_tour(s: *mut EulerStep) {
            let (s0, s1) = EulerStep::split(s);
            EulerStep::merge(s1, s0);
        }
        pub fn same(&mut self, a: usize, b: usize) -> bool {
            let a = self.get_node(a, a);
            let b = self.get_node(b, b);
            EulerStep::same(a, b)
        }
        #[allow(unused_assignments)]
        pub fn unite(&mut self, a: usize, b: usize) -> bool {
            if self.same(a, b) {
                return false;
            }
            let aa = self.get_node(a, a);
            Self::re_tour(aa);
            let bb = self.get_node(b, b);
            Self::re_tour(bb);

            let ab = self.get_node(a, b);
            let ba = self.get_node(b, a);
            let aa_ab = EulerStep::merge(aa, ab);
            let bb_ba = EulerStep::merge(bb, ba);
            let _ = EulerStep::merge(aa_ab, bb_ba);
            true
        }
        fn remove_split(&mut self, from: usize, to: usize) -> (*mut EulerStep, *mut EulerStep) {
            let c = self.get_node(from, to);
            unsafe {
                (*c).splay();
                let left = (*c).left;
                let right = (*c).right;
                if !left.is_null() {
                    (*left).parent = std::ptr::null_mut();
                }
                if !right.is_null() {
                    (*right).parent = std::ptr::null_mut();
                }
                assert!(self.tour[from].remove(&to).is_some());
                (left, right)
            }
        }
        pub fn cut(&mut self, a: usize, b: usize) -> bool {
            if !self.tour[a].contains_key(&b) {
                return false;
            }
            let (xxa, bxx) = self.remove_split(a, b);
            if EulerStep::same(xxa, self.get_node(b, a)) {
                let (xxb, _axxa) = self.remove_split(b, a);
                let _ = EulerStep::merge(bxx, xxb);
            } else {
                let (_bxxb, axx) = self.remove_split(b, a);
                let _ = EulerStep::merge(axx, xxa);
            }
            true
        }
        pub fn get_size(&mut self, a: usize) -> usize {
            let node = self.tour[a].get_mut(&a).unwrap();
            node.splay();
            node.size
        }
        pub fn extract_level_match(t: *mut EulerStep) -> Option<(usize, usize)> {
            unsafe {
                if t.is_null() || !(*t).at_this_level_subany {
                    return None;
                }
                if (*t).at_this_level {
                    (*t).splay();
                    (*t).at_this_level = false;
                    (*t).update();
                    return Some(((*t).from, (*t).to));
                }
                let left = (*t).left;
                if let Some(ret) = Self::extract_level_match(left) {
                    return Some(ret);
                }
                let right = (*t).right;
                if let Some(ret) = Self::extract_level_match(right) {
                    return Some(ret);
                }
                None
            }
        }
        pub fn extract_useless_connected(t: *mut EulerStep) -> Option<usize> {
            unsafe {
                if t.is_null() || !(*t).useless_connected_subany {
                    return None;
                }
                if (*t).useless_connected {
                    (*t).splay();
                    return Some((*t).from);
                }
                let left = (*t).left;
                if let Some(ret) = Self::extract_useless_connected(left) {
                    return Some(ret);
                }
                let right = (*t).right;
                if let Some(ret) = Self::extract_useless_connected(right) {
                    return Some(ret);
                }
                None
            }
        }
        pub fn update_useless_connected(&mut self, a: usize, b: bool) {
            let node = self.tour[a].get_mut(&a).unwrap();
            node.splay();
            node.useless_connected = b;
            node.update();
        }
        pub fn set_value(&mut self, a: usize, value: i64) {
            let node = self.tour[a].get_mut(&a).unwrap();
            node.splay();
            node.set_value(value);
            node.update();
        }
        pub fn get_value(&self, a: usize) -> i64 {
            self.tour[a][&a].get_value()
        }
        pub fn get_sum(&mut self, a: usize) -> i64 {
            let node = self.tour[a].get_mut(&a).unwrap();
            node.splay();
            node.get_sum()
        }
    }
}
use self::euler_tree::EulerTour;
use std::collections::HashSet;
pub struct DynamicConnectivity {
    n: usize,
    trees: Vec<EulerTour>,
    useless_edges: Vec<Vec<HashSet<usize>>>,
    grp_num: usize,
}
impl DynamicConnectivity {
    pub fn new(n: usize) -> Self {
        Self {
            n,
            trees: vec![EulerTour::new(n)],
            useless_edges: vec![vec![HashSet::new(); n]],
            grp_num: n,
        }
    }
    pub fn unite(&mut self, a: usize, b: usize) -> bool {
        if a == b {
            return false;
        }
        if self.trees[0].unite(a, b) {
            self.grp_num -= 1;
            return true;
        }
        assert!(self.useless_edges[0][a].insert(b));
        assert!(self.useless_edges[0][b].insert(a));
        if self.useless_edges[0][a].len() == 1 {
            self.trees[0].update_useless_connected(a, true);
        }
        if self.useless_edges[0][b].len() == 1 {
            self.trees[0].update_useless_connected(b, true);
        }
        false
    }
    pub fn same(&mut self, a: usize, b: usize) -> bool {
        self.trees[0].same(a, b)
    }
    pub fn cut(&mut self, a: usize, b: usize) -> bool {
        if a == b {
            return false;
        }
        self.trees
            .iter_mut()
            .zip(self.useless_edges.iter_mut())
            .for_each(|(tree, edges)| {
                for (a, b) in [(a, b), (b, a)].iter().copied() {
                    if edges[a].remove(&b) && edges[a].is_empty() {
                        tree.update_useless_connected(a, false);
                    }
                }
            });
        let org_level_len = self.trees.len();
        for level in (0..org_level_len).rev() {
            if self.trees[level].cut(a, b) {
                // tree-connectivity changed.
                if level == org_level_len - 1 {
                    self.trees.push(EulerTour::new(self.n));
                    self.useless_edges.push(vec![HashSet::new(); self.n]);
                }
                // try reconnect
                self.trees.iter_mut().take(level).for_each(|tree| {
                    tree.cut(a, b);
                });
                let reconstruct = self.reconstruct_connectivity(a, b, level);
                if !reconstruct {
                    self.grp_num += 1;
                }
                return !reconstruct;
            }
        }
        false
    }
    fn reconstruct_connectivity(&mut self, mut a: usize, mut b: usize, level: usize) -> bool {
        for i in (0..=level).rev() {
            if self.trees[i].get_size(a) > self.trees[i].get_size(b) {
                std::mem::swap(&mut a, &mut b);
            }
            // edge update
            unsafe {
                let node_a = self.trees[i].get_node(a, a);
                (*node_a).splay();
                while let Some((lup_a, lup_b)) = EulerTour::extract_level_match(node_a) {
                    self.trees[i + 1].unite(lup_a, lup_b);
                    (*node_a).splay();
                }
                // try_reconnect in euler tour
                while let Some(x) = EulerTour::extract_useless_connected(node_a) {
                    while let Some(&y) = self.useless_edges[i][x].iter().next() {
                        for (x, y) in [(x, y), (y, x)].iter().copied() {
                            assert!(self.useless_edges[i][x].remove(&y));
                            if self.useless_edges[i][x].is_empty() {
                                self.trees[i].update_useless_connected(x, false);
                            }
                        }
                        if self.trees[i].same(x, y) {
                            for (x, y) in [(x, y), (y, x)].iter().copied() {
                                self.useless_edges[i + 1][x].insert(y);
                                if self.useless_edges[i + 1][x].len() == 1 {
                                    self.trees[i + 1].update_useless_connected(x, true);
                                }
                            }
                        } else {
                            for j in 0..=i {
                                self.trees[j].unite(x, y);
                            }
                            return true;
                        }
                    }
                    (*node_a).splay();
                }
            }
        }
        false
    }
    pub fn set_value(&mut self, x: usize, value: i64) {
        self.trees[0].set_value(x, value);
    }
    pub fn get_value(&self, x: usize) -> i64 {
        self.trees[0].get_value(x)
    }
    pub fn group_size(&mut self, x: usize) -> usize {
        self.trees[0].get_size(x)
    }
    pub fn group_num(&self) -> usize {
        self.grp_num
    }
    pub fn get_sum(&mut self, x: usize) -> i64 {
        self.trees[0].get_sum(x)
    }
}
#[cfg(test)]
mod tests {
    use super::DynamicConnectivity;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    use std::collections::BTreeSet;
    use crate::union_find::UnionFind;
    const N: usize = 10;
    fn trial(ques: Vec<(usize, usize, usize)>) {
        let mut dc = DynamicConnectivity::new(N);
        let mut g = vec![BTreeSet::new(); N];
        let mut log_n = 1usize;
        while (1usize << log_n) < N {
            log_n += 1;
        }
        for (t, a, b) in ques {
            match t {
                0 => {
                    dc.unite(a, b);
                    g[a].insert(b);
                    g[b].insert(a);
                }
                1 => {
                    dc.cut(a, b);
                    g[a].remove(&b);
                    g[b].remove(&a);
                }
                _ => unreachable!(),
            }
            let mut uf = UnionFind::new(N);
            for a in 0..N {
                for b in g[a].iter().copied() {
                    uf.unite(a, b);
                }
            }
            assert_eq!(uf.group_num(), dc.group_num());
            for j in 0..N {
                for i in 0..N {
                    assert_eq!(dc.same(i, j), uf.same(i, j));
                }
                assert_eq!(uf.group_size(j), dc.group_size(j));
            }
            assert!(dc.trees.len() <= log_n);
        }
    }
    #[test]
    fn random_operation() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for _ in 0..100 {
            let ques = {
                let mut es = vec![BTreeSet::new(); N];
                let mut ques = vec![];
                while ques.len() < N * N {
                    let t = rng.random_range(0..2);
                    let a = rng.random_range(0..N);
                    let b = (a + 1 + rng.random_range(0..N - 1)) % N;
                    match t {
                        0 => {
                            // unite
                            if es[a].contains(&b) {
                                continue;
                            }
                            es[a].insert(b);
                            es[b].insert(a);
                            ques.push((t, a, b));
                        }
                        1 => {
                            // cut
                            if !es[a].contains(&b) {
                                continue;
                            }
                            es[a].remove(&b);
                            es[b].remove(&a);
                            ques.push((t, a, b));
                        }
                        _ => unreachable!(),
                    }
                }
                ques
            };
            trial(ques);
        }
    }
}
