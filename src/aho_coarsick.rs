use cargo_snippet::snippet;

#[snippet("AhoCoarsick")]
#[derive(Clone, Debug)]
pub struct AhoCoarsick<T> {
    trie: Vec<std::collections::HashMap<T, usize>>,
    hit_keyword_num: Vec<usize>,
    failure: Vec<usize>,
}
#[snippet("AhoCoarsick")]
impl<T: Eq + std::hash::Hash + Copy> AhoCoarsick<T> {
    pub fn new(keywords: Vec<Vec<T>>) -> Self {
        let (trie, mut hit_keyword_num) = {
            let mut trie = vec![std::collections::HashMap::new()];
            let mut hit_keyword_num = vec![0];
            for keyword in keywords.into_iter() {
                let mut v = 0;
                for val in keyword {
                    let nv = if let Some(&nv) = trie[v].get(&val) {
                        nv
                    } else {
                        let nv = trie.len();
                        trie.push(std::collections::HashMap::new());
                        hit_keyword_num.push(0);
                        trie[v].insert(val, nv);
                        nv
                    };
                    v = nv;
                }
                hit_keyword_num[v] += 1;
            }
            (trie, hit_keyword_num)
        };
        let failure = {
            let mut failure = vec![0; trie.len()];
            let mut que = std::collections::VecDeque::new();
            for (_c, &nv) in trie[0].iter() {
                que.push_back(nv);
            }
            while let Some(v) = que.pop_front() {
                for (&c, &nv) in trie[v].iter() {
                    failure[nv] = Self::next_impl(&trie, &failure, failure[v], c);
                    hit_keyword_num[nv] += hit_keyword_num[failure[nv]];
                    que.push_back(nv);
                }
            }
            failure
        };
        Self {
            trie,
            hit_keyword_num,
            failure,
        }
    }
    pub fn next(&self, from: usize, c: T) -> usize {
        Self::next_impl(&self.trie, &self.failure, from, c)
    }
    fn next_impl(
        trie: &[std::collections::HashMap<T, usize>],
        failure: &[usize],
        from: usize,
        c: T,
    ) -> usize {
        let mut now = from;
        loop {
            if let Some(&to) = trie[now].get(&c) {
                // trie has next node.
                return to;
            } else if now != failure[now] {
                // proceed failure
                // retry from failure-link.
                now = failure[now];
            } else {
                // proceed failure at root.
                debug_assert!(now == 0);
                return 0;
            }
        }
    }
    // count num of keyword, that end at this node.
    pub fn hit_keyword_num(&self, node: usize) -> usize {
        self.hit_keyword_num[node]
    }
    pub fn len(&self) -> usize {
        self.trie.len()
    }
}

#[cfg(test)]
pub mod test {
    use super::AhoCoarsick;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    #[test]
    pub fn random() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        const NMAX: usize = 50;
        const C: usize = 10;
        const K: usize = NMAX;
        const T: usize = 1000;
        for n in 1..=NMAX {
            for _ in 0..T {
                let s = (0..n).map(|_| rng.random_range(0..C)).collect::<Vec<_>>();
                let keywords = (0..K)
                    .map(|_| {
                        let keyword_len = 1 + rng.random_range(0..n);
                        (0..keyword_len)
                            .map(|_| rng.random_range(0..C))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                let ac = AhoCoarsick::new(keywords.clone());
                let mut v = 0;
                for (i, &c) in s.iter().enumerate() {
                    let expected_hit_num = keywords
                        .iter()
                        .filter(|keyword| {
                            if i < keyword.len() - 1 {
                                false
                            } else {
                                &&s[i - (keyword.len() - 1)..=i] == keyword
                            }
                        })
                        .count();
                    v = ac.next(v, c);
                    let actual_hit_num = ac.hit_keyword_num(v);
                    assert_eq!(expected_hit_num, actual_hit_num);
                }
            }
        }
    }
}
