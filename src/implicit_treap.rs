use crate::xor_shift::XorShift64;

#[derive(Clone, Debug)]
struct TreapNode<T: Clone + std::fmt::Debug> {
    // status
    value: T,
    cum: T,
    sub_sz: usize,
    // connection
    left: Option<usize>,
    right: Option<usize>,
    // static priosrity
    priority: u32,
}

#[derive(Clone, Debug)]
struct ImplicitTreap<T: Clone + std::fmt::Debug> {
    rng: XorShift64,
    nodes: Vec<TreapNode<T>>,
    empties: Vec<usize>,
    op: fn(T, T) -> T,
    root: Option<usize>,
}

impl<T> ImplicitTreap<T>
where
    T: Clone + std::fmt::Debug,
{
    fn new(op: fn(T, T) -> T) -> Self {
        Self {
            rng: XorShift64::new(),
            nodes: vec![],
            empties: vec![],
            op,
            root: None,
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
                    (self.op)(
                        (self.op)(
                            self.nodes[left].value.clone(),
                            self.nodes[node].value.clone(),
                        ),
                        self.nodes[right].value.clone(),
                    ),
                )
            } else {
                (
                    self.nodes[left].sub_sz + 1,
                    (self.op)(
                        self.nodes[left].value.clone(),
                        self.nodes[node].value.clone(),
                    ),
                )
            }
        } else if let Some(right) = self.nodes[node].right {
            (
                1 + self.nodes[right].sub_sz,
                (self.op)(
                    self.nodes[node].value.clone(),
                    self.nodes[right].value.clone(),
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
                    self.nodes[l].right = self.merge(self.nodes[l].right, Some(r));
                    self.update(l)
                } else {
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
    fn len(&self) -> usize {
        self.count(self.root)
    }
    fn is_empty(&self) -> bool {
        self.root.is_none()
    }
    fn insert_at(&mut self, i: usize, value: T) {
        let new_info = TreapNode {
            value: value.clone(),
            cum: value,
            sub_sz: 1,
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
    fn remove_at(&mut self, i: usize) -> Option<T> {
        let (left, center_and_right) = self.split(self.root, i);
        let (center, right) = self.split(center_and_right, 1);
        let center = center.unwrap();
        self.empties.push(center);
        self.root = self.merge(left, right);
        Some(self.nodes[center].value.clone())
    }
    fn push(&mut self, value: T) {
        self.insert_at(self.len(), value);
    }
    fn pop(&mut self) -> Option<T> {
        self.remove_at(self.len() - 1)
    }
    fn get_impl(&self, node: usize, i: usize) -> T {
        match i.cmp(&self.count(self.nodes[node].left)) {
            std::cmp::Ordering::Equal => self.nodes[node].value.clone(),
            std::cmp::Ordering::Less => self.get_impl(self.nodes[node].left.unwrap(), i),
            std::cmp::Ordering::Greater => self.get_impl(
                self.nodes[node].right.unwrap(),
                i - (1 + self.count(self.nodes[node].left)),
            ),
        }
    }
    fn get(&self, i: usize) -> T {
        self.get_impl(self.root.unwrap(), i)
    }
}

pub mod test {
    use rand::Rng;

    use super::ImplicitTreap;
    const N: usize = 128;
    const V: usize = 128;
    const T: usize = 128;
    pub fn get() {
        use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for _ in 0..T {
            let mut expected = vec![];
            let mut actual = ImplicitTreap::new(|x, y| x + y);
            for _ in 0..N {
                let v = rng.random_range(0..V);
                if rng.random_range(0..2) == 0 {
                    let at = rng.random_range(0..=expected.len());
                    actual.insert_at(at, v);
                    expected = expected
                        .iter()
                        .copied()
                        .take(at)
                        .chain(vec![v])
                        .chain(expected.iter().copied().skip(at))
                        .collect::<Vec<_>>();
                } else {
                    expected.push(v);
                    actual.push(v);
                }
                assert_eq!(expected.len(), actual.len());
                for i in 0..actual.len() {
                    let e = expected[i];
                    let a = actual.get(i);
                    assert_eq!(e, a);
                }
            }
            for _ in 0..N {
                if rng.random_range(0..2) == 0 {
                    let at = rng.random_range(0..expected.len());
                    expected.remove(at);
                    actual.remove_at(at);
                } else {
                    assert_eq!(expected.pop(), actual.pop());
                }
                assert_eq!(expected.is_empty(), actual.is_empty());
                if !expected.is_empty() {
                    for i in 0..actual.len() {
                        let e = expected[i];
                        let a = actual.get(i);
                        assert_eq!(e, a);
                    }
                }
            }
        }
    }
}
