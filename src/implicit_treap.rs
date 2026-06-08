use cargo_snippet::snippet;

#[snippet("ImplicitTreap")]
#[derive(Clone, Debug)]
struct TreapNode<T: Clone + std::fmt::Debug> {
    // status
    value: T,
    sub_sz: usize,
    // connection
    left: Option<usize>,
    right: Option<usize>,
    // static priosrity
    priority: u32,
}

#[snippet("ImplicitTreap")]
#[derive(Clone, Debug)]
pub struct ImplicitTreap<T: Clone + std::fmt::Debug, M: Clone + std::fmt::Debug> {
    root: Option<usize>,
    nodes: Vec<TreapNode<T>>,
    empties: Vec<usize>,
    rng: u32,
    cum: Vec<T>,
    lazy: Vec<Option<M>>,
    pair_op: fn(T, T) -> T,
    update_op: fn(T, M) -> T,
    update_concat: fn(M, M) -> M,
}

#[snippet("ImplicitTreap")]
impl<T, M> ImplicitTreap<T, M>
where
    T: Clone + std::fmt::Debug,
    M: Clone + std::fmt::Debug,
{
    pub fn new(
        pair_op: fn(T, T) -> T,
        update_op: fn(T, M) -> T,
        update_concat: fn(M, M) -> M,
    ) -> Self {
        Self {
            root: None,
            nodes: vec![],
            empties: vec![],
            rng: 0x11001100,
            cum: vec![],
            lazy: vec![],
            pair_op,
            update_op,
            update_concat,
        }
    }
    fn random_trans(x: &mut u32) {
        // xor shift
        *x ^= *x << 13;
        *x ^= *x >> 17;
        *x ^= *x << 5;
    }
    pub fn from_vec(
        pair_op: fn(T, T) -> T,
        update_op: fn(T, M) -> T,
        update_concat: fn(M, M) -> M,
        a: Vec<T>,
    ) -> Self {
        let mut rng = 11001100;
        let mut nodes = a
            .iter()
            .cloned()
            .map(|value| TreapNode {
                value: value.clone(),
                sub_sz: 1,
                left: None,
                right: None,
                priority: {
                    Self::random_trans(&mut rng);
                    rng
                },
            })
            .collect::<Vec<_>>();
        let mut cum = a.clone();
        let n = a.len();
        let mut stack = vec![0];
        for i in 1..n {
            let mut l = None;
            while let Some(&j) = stack.iter().next_back() {
                if nodes[j].priority > nodes[i].priority {
                    stack.push(i);
                    nodes[j].right = Some(i);
                    break;
                } else {
                    l = stack.pop();
                }
            }
            if let Some(l) = l {
                nodes[i].left = Some(l);
            }
            if stack.is_empty() {
                stack.push(i);
            }
        }
        Self::dfs(stack[0], pair_op, &mut nodes, &mut cum);
        let root = Some(stack[0]);
        let ret = Self {
            root,
            nodes,
            empties: vec![],
            rng,
            cum: a.clone(),
            lazy: vec![None; n],
            pair_op,
            update_op,
            update_concat,
        };
        ret
    }
    fn dfs(node: usize, pair_op: fn(T, T) -> T, nodes: &mut [TreapNode<T>], cum: &mut [T]) {
        if let Some(left) = nodes[node].left {
            Self::dfs(left, pair_op, nodes, cum);
        }
        if let Some(right) = nodes[node].right {
            Self::dfs(right, pair_op, nodes, cum);
        }
        nodes[node].sub_sz = Self::update_sz(nodes, node);
        cum[node] = Self::update_cum(nodes, cum, node, pair_op);
    }
    #[inline(always)]
    fn get_key(node: usize, nodes: &[TreapNode<T>]) -> usize {
        if let Some(left) = nodes[node].left {
            nodes[left].sub_sz
        } else {
            0
        }
    }
    fn update_sz(nodes: &mut [TreapNode<T>], node: usize) -> usize {
        if let Some(left) = nodes[node].left {
            if let Some(right) = nodes[node].right {
                nodes[left].sub_sz + 1 + nodes[right].sub_sz
            } else {
                nodes[left].sub_sz + 1
            }
        } else if let Some(right) = nodes[node].right {
            1 + nodes[right].sub_sz
        } else {
            1
        }
    }
    fn update_cum(
        nodes: &mut [TreapNode<T>],
        cum: &mut [T],
        node: usize,
        pair_op: fn(T, T) -> T,
    ) -> T {
        if let Some(left) = nodes[node].left {
            if let Some(right) = nodes[node].right {
                (pair_op)(
                    (pair_op)(cum[left].clone(), nodes[node].value.clone()),
                    cum[right].clone(),
                )
            } else {
                (pair_op)(cum[left].clone(), nodes[node].value.clone())
            }
        } else if let Some(right) = nodes[node].right {
            (pair_op)(nodes[node].value.clone(), cum[right].clone())
        } else {
            nodes[node].value.clone()
        }
    }
    // calulate correct value of sub_size and value.
    fn update(&mut self, node: usize) -> Option<usize> {
        self.nodes[node].sub_sz = Self::update_sz(&mut self.nodes, node);
        self.cum[node] = Self::update_cum(&mut self.nodes, &mut self.cum, node, self.pair_op);
        Some(node)
    }
    // split and return roots of left/right trees
    fn split(&mut self, node: Option<usize>, key: usize) -> (Option<usize>, Option<usize>) {
        let Some(node) = node else {
            return (None, None);
        };
        self.push_down(node);
        if key <= Self::get_key(node, &self.nodes) {
            let (nl, nr) = self.split(self.nodes[node].left, key);
            self.nodes[node].left = nr;
            (nl, self.update(node))
        } else {
            let (nl, nr) = self.split(
                self.nodes[node].right,
                key - Self::get_key(node, &self.nodes) - 1,
            );
            self.nodes[node].right = nl;
            (self.update(node), nr)
        }
    }
    fn merge(&mut self, l: Option<usize>, r: Option<usize>) -> Option<usize> {
        if let Some(l) = l {
            if let Some(r) = r {
                if self.nodes[l].priority > self.nodes[r].priority {
                    self.push_down(l);
                    self.nodes[l].right = self.merge(self.nodes[l].right, Some(r));
                    self.update(l)
                } else {
                    self.push_down(r);
                    self.nodes[r].left = self.merge(Some(l), self.nodes[r].left);
                    self.update(r)
                }
            } else {
                Some(l)
            }
        } else if let Some(r) = r {
            Some(r)
        } else {
            None
        }
    }
    pub fn len(&self) -> usize {
        self.nodes.len() - self.empties.len()
    }
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }
    pub fn insert_at(&mut self, i: usize, value: T) {
        let new_info = TreapNode {
            value: value.clone(),
            sub_sz: 1,
            left: None,
            right: None,
            priority: {
                Self::random_trans(&mut self.rng);
                self.rng
            },
        };
        let v = if let Some(v) = self.empties.pop() {
            self.nodes[v] = new_info;
            self.cum[v] = value.clone();
            self.lazy[v] = None;
            v
        } else {
            self.nodes.push(new_info);
            self.cum.push(value.clone());
            self.lazy.push(None);
            self.nodes.len() - 1
        };
        let (left, right) = self.split(self.root, i);
        let center_and_right = self.merge(Some(v), right);
        self.root = self.merge(left, center_and_right);
    }
    pub fn remove_at(&mut self, i: usize) -> Option<T> {
        let (left, center_and_right) = self.split(self.root, i);
        let (center, right) = self.split(center_and_right, 1);
        let center = center.unwrap();
        self.empties.push(center);
        self.root = self.merge(left, right);
        Some(self.nodes[center].value.clone())
    }
    pub fn push(&mut self, value: T) {
        self.insert_at(self.len(), value);
    }
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        self.remove_at(self.len() - 1)
    }
    pub fn get(&mut self, i: usize) -> T {
        debug_assert!(i < self.len());
        let (l, cr) = self.split(self.root, i);
        let (c, r) = self.split(cr, 1);
        let ret = self.cum[c.unwrap()].clone();
        let cr = self.merge(c, r);
        self.root = self.merge(l, cr);
        ret
    }
    pub fn set(&mut self, i: usize, value: T) {
        debug_assert!(i < self.len());
        let (l, cr) = self.split(self.root, i);
        let (c, r) = self.split(cr, 1);
        self.nodes[c.unwrap()].value = value.clone();
        self.cum[c.unwrap()] = value;
        let cr = self.merge(c, r);
        self.root = self.merge(l, cr);
    }
    pub fn query(&mut self, li: usize, ri: usize) -> T {
        debug_assert!(li <= ri);
        let (lc, r) = self.split(self.root, ri + 1);
        let (l, c) = self.split(lc, li);
        let ret = self.cum[c.unwrap()].clone();
        let cr = self.merge(c, r);
        self.root = self.merge(l, cr);
        ret
    }
    pub fn reserve(&mut self, li: usize, ri: usize, m: M) {
        debug_assert!(li <= ri);
        let (lc, r) = self.split(self.root, ri + 1);
        let (l, c) = self.split(lc, li);
        let c = c.unwrap();
        self.lazy[c] = Some(if let Some(lazy_old) = self.lazy[c].clone() {
            (self.update_concat)(lazy_old, m)
        } else {
            m
        });
        let cr = self.merge(Some(c), r);
        self.root = self.merge(l, cr);
    }
    fn push_down(&mut self, node: usize) {
        if let Some(lazy) = self.lazy[node].clone() {
            self.lazy[node] = None;
            self.nodes[node].value = (self.update_op)(self.nodes[node].value.clone(), lazy.clone());
            self.cum[node] = (self.update_op)(self.cum[node].clone(), lazy.clone());
            if let Some(left) = self.nodes[node].left {
                self.lazy[left] = Some(if let Some(lazy_old) = self.lazy[left].clone() {
                    (self.update_concat)(lazy_old, lazy.clone())
                } else {
                    lazy.clone()
                });
            }
            if let Some(right) = self.nodes[node].right {
                self.lazy[right] = Some(if let Some(lazy_old) = self.lazy[right].clone() {
                    (self.update_concat)(lazy_old, lazy.clone())
                } else {
                    lazy.clone()
                });
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::ImplicitTreap;
    use rand::Rng;
    const N: usize = 16;
    const V: usize = 16;
    const T: usize = 512;
    #[test]
    fn random() {
        use crate::modint::{ModIntTrait, StaticModInt};
        use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
        type Mint = StaticModInt<998244353>;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for _case in 0..T {
            let mut expected = vec![];
            for _ in 0..N {
                let v = rng.random_range(0..V);
                expected.push((Mint::new(v), Mint::one()));
            }
            let mut actual = ImplicitTreap::<(Mint, Mint), (Mint, Mint)>::from_vec(
                |x, y| (x.0 + y.0, x.1 + y.1),
                |x, y| (x.0 * y.0 + x.1 * y.1, x.1),
                |x, y| (x.0 * y.0, x.1 * y.0 + y.1),
                expected.clone(),
            );
            for _op in 0..T {
                match rng.random_range(0..=5) {
                    0 => {
                        // push
                        let v = rng.random_range(0..V);
                        expected.push((Mint::new(v), Mint::one()));
                        actual.push((Mint::new(v), Mint::one()));
                    }
                    1 => {
                        // pop
                        assert_eq!(expected.pop(), actual.pop());
                    }
                    2 => {
                        // set
                        if !expected.is_empty() {
                            let at = rng.random_range(0..expected.len());
                            let v = rng.random_range(0..V);
                            expected[at] = (Mint::new(v), Mint::one());
                            actual.set(at, (Mint::new(v), Mint::one()));
                        }
                    }
                    3 => {
                        // remove_at
                        if !expected.is_empty() {
                            let at = rng.random_range(0..expected.len());
                            expected.remove(at);
                            actual.remove_at(at);
                        }
                    }
                    4 => {
                        // insert_at
                        let at = rng.random_range(0..=expected.len());
                        let v = rng.random_range(0..V);
                        expected = expected
                            .iter()
                            .copied()
                            .take(at)
                            .chain(vec![(Mint::new(v), Mint::one())])
                            .chain(expected.iter().copied().skip(at))
                            .collect::<Vec<_>>();
                        actual.insert_at(at, (Mint::new(v), Mint::one()));
                    }
                    5 => {
                        // linear
                        if !expected.is_empty() {
                            let l = rng.random_range(0..expected.len());
                            let r = rng.random_range(0..expected.len());
                            let (l, r) = if l < r { (l, r) } else { (r, l) };
                            let a = Mint::one(); //Mint::new(rng.random_range(0..V));
                            let b = Mint::new(rng.random_range(0..V));
                            for i in l..=r {
                                expected[i].0 = a * expected[i].0 + b;
                            }
                            actual.reserve(l, r, (a, b));
                        }
                    }
                    _ => unreachable!(),
                }
                // check
                assert_eq!(expected.len(), actual.len());
                assert_eq!(expected.is_empty(), actual.is_empty());
                for i in 0..expected.len() {
                    assert_eq!(expected[i], actual.get(i));
                    for j in i..expected.len() {
                        assert_eq!(
                            (i..=j)
                                .map(|k| expected[k])
                                .fold((Mint::zero(), Mint::zero()), |x, y| (x.0 + y.0, x.1 + y.1)),
                            actual.query(i, j)
                        );
                    }
                }
            }
        }
    }
}
