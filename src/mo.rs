use cargo_snippet::snippet;

#[snippet("Mo")]
pub struct Mo {
    ls: Vec<usize>,
    rs: Vec<usize>,
}
#[snippet("Mo")]
pub struct MoIterator {
    index_iter: std::vec::IntoIter<usize>,
    ls: Vec<usize>,
    rs: Vec<usize>,
}
#[snippet("Mo")]
impl Mo {
    pub fn new() -> Self {
        Self {
            ls: vec![],
            rs: vec![],
        }
    }
    pub fn add_range_queue(&mut self, l: usize, r: usize) {
        self.ls.push(l);
        self.rs.push(r);
    }
    pub fn into_iter(self) -> MoIterator {
        let n = self.rs.iter().max().unwrap() + 1;
        let q = self.rs.len();
        let d = n / ((q as f64).sqrt() as usize + 1) + 1;
        let mut indexes = (0..q).collect::<Vec<_>>();
        indexes.sort_by_cached_key(|&i| {
            let div = self.ls[i] / d;
            if div % 2 == 0 {
                (div, self.rs[i])
            } else {
                (div, n - self.rs[i])
            }
        });
        MoIterator {
            index_iter: indexes.into_iter(),
            ls: self.ls,
            rs: self.rs,
        }
    }
    pub fn add_chain(
        l0: usize,
        r0: usize,
        l1: usize,
        r1: usize,
    ) -> std::iter::Chain<std::iter::Rev<std::ops::Range<usize>>, std::ops::RangeInclusive<usize>>
    {
        (l1..l0).rev().chain(r0 + 1..=r1)
    }
    pub fn remove_chain(
        l0: usize,
        r0: usize,
        l1: usize,
        r1: usize,
    ) -> std::iter::Chain<std::ops::Range<usize>, std::iter::Rev<std::ops::RangeInclusive<usize>>>
    {
        (l0..l1).chain(((r1 + 1)..=r0).rev())
    }
}
#[snippet("Mo")]
impl Iterator for MoIterator {
    type Item = (usize, (usize, usize));
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i) = self.index_iter.next() {
            Some((i, (self.ls[i], self.rs[i])))
        } else {
            None
        }
    }
}
