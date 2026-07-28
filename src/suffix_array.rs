use cargo_snippet::snippet;

#[snippet("SuffixArray")]
fn construct_suffix_array(s: &[usize]) -> Vec<usize> {
    fn compare(pos_to_ord: &[i64], i: usize, j: usize, k: usize, n: usize) -> std::cmp::Ordering {
        let ri0 = pos_to_ord[i];
        let rj0 = pos_to_ord[j];
        let ri1 = if i + k <= n { pos_to_ord[i + k] } else { -1 };
        let rj1 = if j + k <= n { pos_to_ord[j + k] } else { -1 };
        (ri0, ri1).cmp(&(rj0, rj1))
    }
    let n = s.len();
    let mut ord_to_pos = vec![0usize; n + 1];
    let mut pos_to_ord = vec![0i64; n + 1];
    let mut pos_to_ord_nxt = vec![0i64; n + 1];
    for i in 0..=n {
        ord_to_pos[i] = i;
        pos_to_ord[i] = if i < n { s[i] as i64 } else { -1 };
    }
    let mut k = 1;
    while k <= n {
        ord_to_pos.sort_by(|&i, &j| compare(&pos_to_ord, i, j, k, n));
        pos_to_ord_nxt[ord_to_pos[0]] = 0;
        for ord in 1..=n {
            pos_to_ord_nxt[ord_to_pos[ord]] = pos_to_ord_nxt[ord_to_pos[ord - 1]]
                + if compare(&pos_to_ord, ord_to_pos[ord - 1], ord_to_pos[ord], k, n)
                    == std::cmp::Ordering::Less
                {
                    1
                } else {
                    0
                };
        }
        //
        k *= 2;
        std::mem::swap(&mut pos_to_ord, &mut pos_to_ord_nxt);
    }
    ord_to_pos
}
#[snippet("SuffixArray")]
fn construct_longest_common_prefix(s: &[usize], ord_to_pos: &[usize]) -> Vec<usize> {
    let n = s.len();
    debug_assert_eq!(ord_to_pos.len(), n + 1);
    let pos_to_ord = {
        let mut pos_to_ord = vec![0; ord_to_pos.len()];
        for (ord, &pos) in ord_to_pos.iter().enumerate() {
            pos_to_ord[pos] = ord;
        }
        pos_to_ord
    };
    let mut lcp_now = 0usize;
    let mut lcp = vec![0; n];
    for pos in 0..n {
        let pre_ord = pos_to_ord[pos] - 1;
        let pre_ord_pos = ord_to_pos[pre_ord];
        lcp_now = lcp_now.saturating_sub(1);
        while pre_ord_pos + lcp_now < n && pos + lcp_now < n {
            if s[pre_ord_pos + lcp_now] == s[pos + lcp_now] {
                lcp_now += 1;
            } else {
                break;
            }
        }
        lcp[pre_ord] = lcp_now;
    }
    lcp
}
#[snippet("SuffixArray")]
pub trait ToSuffixArray {
    fn suffix_array(&self) -> (Vec<usize>, Vec<usize>);
}
#[snippet("SuffixArray")]
impl ToSuffixArray for Vec<usize> {
    fn suffix_array(&self) -> (Vec<usize>, Vec<usize>) {
        let ord_to_pos = construct_suffix_array(self);
        let lcp = construct_longest_common_prefix(self, &ord_to_pos);
        (ord_to_pos, lcp)
    }
}

#[cfg(test)]
mod test {
    const T: usize = 100;
    const N: usize = 100;
    const C: usize = 26;
    use super::ToSuffixArray;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    #[test]
    fn suffix_array() {
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for n in 1..=N {
            for _ in 0..T {
                let a = (0..n).map(|_| rng.random_range(0..C)).collect::<Vec<_>>();
                let sa_expected = {
                    let mut sa_expected = (0..=n).collect::<Vec<_>>();
                    sa_expected.sort_by(|&i, &j| a[i..].cmp(&a[j..]));
                    sa_expected
                };
                let lcp_expected = (0..n)
                    .map(|i| {
                        (0..)
                            .take_while(|&d| {
                                (sa_expected[i] + d < n)
                                    && (sa_expected[i + 1] + d < n)
                                    && a[sa_expected[i] + d] == a[sa_expected[i + 1] + d]
                            })
                            .count()
                    })
                    .collect::<Vec<_>>();
                let (sa_actual, lcp_actual) = a.suffix_array();
                assert_eq!(sa_expected, sa_actual);
                assert_eq!(lcp_expected, lcp_actual);
            }
        }
    }
}
