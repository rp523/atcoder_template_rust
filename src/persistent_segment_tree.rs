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
        fn set_impl<T: Clone>(
            now: usize,
            node_size: usize,
            i: usize,
            new_val: &T,
            nodes: &mut Vec<PersistentNode<T>>,
            pair_op: fn(T, T) -> T,
        ) -> usize {
            if node_size == 1 {
                nodes.push(PersistentNode {
                    l: 0,
                    r: 0,
                    val: new_val.clone(),
                });
                nodes.len() - 1
            } else {
                let half = node_size / 2;
                let (l, r) = if i < half {
                    (
                        set_impl(nodes[now].l, half, i, new_val, nodes, pair_op),
                        nodes[now].r,
                    )
                } else {
                    (
                        nodes[now].l,
                        set_impl(nodes[now].r, half, i - half, new_val, nodes, pair_op),
                    )
                };
                nodes.push(PersistentNode {
                    l,
                    r,
                    val: (pair_op)(nodes[l].val.clone(), nodes[r].val.clone()),
                });
                nodes.len() - 1
            }
        }
        let ver_toot_new = set_impl(
            self.ver_roots[ver],
            self.n2,
            i,
            &new_val,
            &mut self.nodes,
            self.pair_op,
        );
        self.ver_roots.push(ver_toot_new);
        self.ver_roots.len() - 1
    }
    pub fn query(&self, ver: usize, l: usize, r: usize) -> T {
        fn query_impl<T: Clone>(
            now: usize,
            node_size: usize,
            l: usize,
            r: usize,
            nodes: &Vec<PersistentNode<T>>,
            pair_op: fn(T, T) -> T,
        ) -> T {
            debug_assert!(r - l <= node_size);
            if r - l == node_size {
                nodes[now].val.clone()
            } else {
                let half = node_size / 2;
                debug_assert!(half > 0);
                debug_assert!(nodes[now].l > 0);
                if r == 0 || r <= half {
                    // only left half
                    query_impl(nodes[now].l, half, l, r, nodes, pair_op)
                } else if half <= l {
                    // only right half
                    query_impl(nodes[now].r, half, l - half, r - half, nodes, pair_op)
                } else {
                    // split
                    (pair_op)(
                        query_impl(nodes[now].l, half, l, half, nodes, pair_op),
                        query_impl(nodes[now].r, half, 0, r - half, nodes, pair_op),
                    )
                }
            }
        }
        query_impl(
            self.ver_roots[ver],
            self.n2,
            l,
            r + 1,
            &self.nodes,
            self.pair_op,
        )
    }
    fn get_leaf(&self, ver: usize, i: usize) -> usize {
        fn calc_node_impl<T: Clone>(
            now: usize,
            node_size: usize,
            i: usize,
            nodes: &[PersistentNode<T>],
        ) -> usize {
            debug_assert!(now < nodes.len());
            if node_size == 1 {
                return now;
            }
            if i < node_size / 2 {
                calc_node_impl(nodes[now].l, node_size / 2, i, nodes)
            } else {
                calc_node_impl(nodes[now].r, node_size / 2, i - node_size / 2, nodes)
            }
        }
        calc_node_impl(self.ver_roots[ver], self.n2, i, &self.nodes)
    }
}
#[snippet("PersistentSegmentTree")]
impl<T: Clone + std::fmt::Debug> std::fmt::Debug for PersistentSegmentTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "[")?;
        for ver in 0..self.ver_roots.len() {
            write!(f, "[")?;
            for i in 0..self.n {
                write!(f, "{:?}", self.nodes[self.get_leaf(ver, i)].val)?;
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
                write!(f, "{}", self.nodes[self.get_leaf(ver, i)].val)?;
                if i < self.n - 1 {
                    write!(f, ", ")?
                }
            }
            writeln!(f, "]")?;
        }
        write!(f, "]")
    }
}
