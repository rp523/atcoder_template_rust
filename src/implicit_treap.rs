use crate::xor_shift::XorShift64;

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
    fn update(&self, node: usize) -> (usize, T) {
        let me = &self.nodes[node];
        if let Some(left) = me.left {
            if let Some(right) = me.right {
                (
                    self.nodes[left].sub_sz + 1 + self.nodes[right].sub_sz,
                    (self.op)(
                        (self.op)(self.nodes[left].value.clone(), me.value.clone()),
                        self.nodes[right].value.clone(),
                    ),
                )
            } else {
                (
                    self.nodes[left].sub_sz + 1,
                    (self.op)(self.nodes[left].value.clone(), me.value.clone()),
                )
            }
        } else if let Some(right) = me.right {
            (
                1 + self.nodes[right].sub_sz,
                (self.op)(me.value.clone(), self.nodes[right].value.clone()),
            )
        } else {
            (1, me.value.clone())
        }
    }
    // split and return roots of left/right trees
    fn split(&mut self, node: Option<usize>, at: usize) -> (Option<usize>, Option<usize>) {
        let Some(node) = node else {
            return (None, None);
        };
        if at <= self.count(self.nodes[node].left) {
            let (nl, nr) = self.split(self.nodes[node].left, at);
            self.nodes[node].left = nr;
            (self.nodes[node].sub_sz, self.nodes[node].value) = self.update(node);
            (nl, Some(node))
        } else {
            let (nl, nr) = self.split(
                self.nodes[node].right,
                at - 1 - self.count(self.nodes[node].left),
            );
            self.nodes[node].right = nl;
            (self.nodes[node].sub_sz, self.nodes[node].value) = self.update(node);
            (Some(node), nr)
        }
    }
    fn merge(&mut self, l: Option<usize>, r: Option<usize>) -> Option<usize> {
        if let Some(l) = l {
            if let Some(r) = r {
                if self.nodes[l].priority > self.nodes[r].priority {
                    self.nodes[l].right = self.merge(self.nodes[l].right, Some(r));
                    (self.nodes[l].sub_sz, self.nodes[l].value) = self.update(l);
                    Some(l)
                } else {
                    self.nodes[r].left = self.merge(Some(l), self.nodes[r].left);
                    (self.nodes[r].sub_sz, self.nodes[r].value) = self.update(r);
                    Some(r)
                }
            } else {
                //(self.nodes[l].sub_sz, self.nodes[l].value) = self.update(l);
                Some(l)
            }
        } else {
            let r = r.unwrap();
            //(self.nodes[r].sub_sz, self.nodes[r].value) = self.update(r);
            Some(r)
        }
    }
    fn len(&self) -> usize {
        self.count(self.root)
    }
    fn insert_at(&mut self, i: usize, value: T) {
        let v = if let Some(v) = self.empties.pop() {
            v
        } else {
            let v = self.nodes.len();
            self.nodes.push(TreapNode {
                value,
                sub_sz: 1,
                left: None,
                right: None,
                priority: self.rng.next_usize() as u32,
            });
            v
        };
        let (left, right) = self.split(self.root, i);
        let center_and_right = self.merge(Some(v), right);
        self.root = self.merge(left, center_and_right);
    }
    fn remove_at(&mut self, i: usize) {
        let (left, center_and_right) = self.split(self.root, i);
        let (center, right) = self.split(center_and_right, 1);
        self.empties.push(center.unwrap());
        self.root = self.merge(left, right);
    }
    fn push(&mut self, value: T) {
        self.insert_at(self.len(), value);
    }
    fn get_impl(&self, node: usize, i: usize) -> T {
        dbg!(i + 1);
        dbg!(node);
        dbg!(&self.nodes[node]);
        dbg!(&self.count(Some(node)));
        match (i + 1).cmp(&self.count(Some(node))) {
            std::cmp::Ordering::Equal => self.nodes[node].value.clone(),
            std::cmp::Ordering::Less => self.get_impl(self.nodes[node].left.unwrap(), i),
            std::cmp::Ordering::Greater => self.get_impl(
                self.nodes[node].right.unwrap(),
                i - 1 - self.count(self.nodes[node].left),
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
    const N: usize = 32;
    const V: usize = 32;
    pub fn get() {
        let mut expected = vec![];
        let mut actual = ImplicitTreap::new(|x, y| x + y);
        use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for t in 0..N {
            let v = rng.random_range(0..V);
            expected.push(v);
            actual.push(v);
            dbg!(expected.len(), actual.len());
            dbg!(&actual);
            assert_eq!(expected.len(), actual.len());
            for i in 0..actual.len() {
                let e = expected[i];
                let a = actual.get(i);
                dbg!(t, i, e, a);
                dbg!(&actual);
                assert_eq!(e, a);
            }
        }
    }
}
