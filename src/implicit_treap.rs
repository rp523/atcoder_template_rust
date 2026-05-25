use crate::xor_shift::XorShift64;
use cargo_snippet::snippet;

#[snippet("ImplicitTreap")]
#[snippet(include = "XorShift64")]
#[derive(Clone, Debug)]
struct TreapNode<T: Clone + std::fmt::Debug, M: Clone + std::fmt::Debug> {
    // status
    value: T,
    cum: T,
    sub_sz: usize,
    lazy: Option<M>,
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
    nodes: Vec<TreapNode<T, M>>,
    empties: Vec<usize>,
    rng: XorShift64,
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
            rng: XorShift64::new(),
            pair_op,
            update_op,
            update_concat,
        }
    }
    fn count(&self, node: Option<usize>) -> usize {
        if let Some(node) = node {
            self.nodes[node].sub_sz
        } else {
            0
        }
    }
    // calulate correct value of sub_size and value.
    fn update(&mut self, node: usize) -> Option<usize> {
        (self.nodes[node].sub_sz, self.nodes[node].cum) = if let Some(left) = self.nodes[node].left
        {
            if let Some(right) = self.nodes[node].right {
                (
                    self.nodes[left].sub_sz + 1 + self.nodes[right].sub_sz,
                    (self.pair_op)(
                        (self.pair_op)(
                            self.nodes[left].cum.clone(),
                            self.nodes[node].value.clone(),
                        ),
                        self.nodes[right].cum.clone(),
                    ),
                )
            } else {
                (
                    self.nodes[left].sub_sz + 1,
                    (self.pair_op)(self.nodes[left].cum.clone(), self.nodes[node].value.clone()),
                )
            }
        } else if let Some(right) = self.nodes[node].right {
            (
                1 + self.nodes[right].sub_sz,
                (self.pair_op)(
                    self.nodes[node].value.clone(),
                    self.nodes[right].cum.clone(),
                ),
            )
        } else {
            (1, self.nodes[node].value.clone())
        };
        Some(node)
    }
    // split and return roots of left/right trees
    fn split(&mut self, node: Option<usize>, at: usize) -> (Option<usize>, Option<usize>) {
        let Some(node) = node else {
            return (None, None);
        };
        self.push_down(node);
        if at <= self.count(self.nodes[node].left) {
            let (nl, nr) = self.split(self.nodes[node].left, at);
            self.nodes[node].left = nr;
            (nl, self.update(node))
        } else {
            let (nl, nr) = self.split(
                self.nodes[node].right,
                at - 1 - self.count(self.nodes[node].left),
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
        self.count(self.root)
    }
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }
    pub fn insert_at(&mut self, i: usize, value: T) {
        let new_info = TreapNode {
            value: value.clone(),
            cum: value,
            sub_sz: 1,
            lazy: None,
            left: None,
            right: None,
            priority: (self.rng.next_usize() & 0x00000000ffffffff) as u32,
        };
        let v = if let Some(v) = self.empties.pop() {
            self.nodes[v] = new_info;
            v
        } else {
            self.nodes.push(new_info);
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
        let ret = self.nodes[c.unwrap()].cum.clone();
        let cr = self.merge(c, r);
        self.root = self.merge(l, cr);
        ret
    }
    pub fn set(&mut self, i: usize, value: T) {
        debug_assert!(i < self.len());
        let (l, cr) = self.split(self.root, i);
        let (c, r) = self.split(cr, 1);
        self.nodes[c.unwrap()].value = value.clone();
        self.nodes[c.unwrap()].cum = value;
        let cr = self.merge(c, r);
        self.root = self.merge(l, cr);
    }
    pub fn query(&mut self, li: usize, ri: usize) -> T {
        debug_assert!(li <= ri);
        let (lc, r) = self.split(self.root, ri + 1);
        let (l, c) = self.split(lc, li);
        let ret = self.nodes[c.unwrap()].cum.clone();
        let cr = self.merge(c, r);
        self.root = self.merge(l, cr);
        ret
    }
    pub fn reserve(&mut self, li: usize, ri: usize, m: M) {
        debug_assert!(li <= ri);
        let (lc, r) = self.split(self.root, ri + 1);
        let (l, c) = self.split(lc, li);
        self.nodes[c.unwrap()].lazy = Some(
            if let Some(lazy_old) = self.nodes[c.unwrap()].lazy.clone() {
                (self.update_concat)(lazy_old, m)
            } else {
                m
            },
        );
        let cr = self.merge(c, r);
        self.root = self.merge(l, cr);
    }
    fn push_down(&mut self, node: usize) {
        if let Some(lazy) = self.nodes[node].lazy.clone() {
            self.nodes[node].lazy = None;
            self.nodes[node].value = (self.update_op)(self.nodes[node].value.clone(), lazy.clone());
            self.nodes[node].cum = (self.update_op)(self.nodes[node].cum.clone(), lazy.clone());
            if let Some(left) = self.nodes[node].left {
                self.nodes[left].lazy =
                    Some(if let Some(lazy_old) = self.nodes[left].lazy.clone() {
                        (self.update_concat)(lazy_old, lazy.clone())
                    } else {
                        lazy.clone()
                    });
            }
            if let Some(right) = self.nodes[node].right {
                self.nodes[right].lazy =
                    Some(if let Some(lazy_old) = self.nodes[right].lazy.clone() {
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
        use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for _case in 0..T {
            let mut expected = vec![];
            let mut actual = ImplicitTreap::<(usize, usize), usize>::new(
                |x, y| (x.0 + y.0, x.1 + y.1),
                |x, y| (x.0 + x.1 * y, x.1),
                |x, y| x + y,
            );
            for _ in 0..N {
                let v = rng.random_range(0..V);
                expected.push((v, 1));
                actual.push((v, 1));
            }
            for _op in 0..T {
                match rng.random_range(0..=5) {
                    0 => {
                        // push
                        let v = rng.random_range(0..V);
                        expected.push((v, 1));
                        actual.push((v, 1));
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
                            expected[at] = (v, 1);
                            actual.set(at, (v, 1));
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
                            .chain(vec![(v, 1)])
                            .chain(expected.iter().copied().skip(at))
                            .collect::<Vec<_>>();
                        actual.insert_at(at, (v, 1));
                    }
                    5 => {
                        if !expected.is_empty() {
                            let l = rng.random_range(0..expected.len());
                            let r = rng.random_range(0..expected.len());
                            let (l, r) = if l < r { (l, r) } else { (r, l) };
                            let v = rng.random_range(0..V);
                            for i in l..=r {
                                expected[i].0 += v;
                            }
                            actual.reserve(l, r, v);
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
                                .fold((0, 0), |x, y| (x.0 + y.0, x.1 + y.1)),
                            actual.query(i, j)
                        );
                    }
                }
            }
        }
    }
}
