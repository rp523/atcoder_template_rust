use cargo_snippet::snippet;

#[snippet("cartesian_tree")]
pub fn cartesian_tree<T>(a: &[T], op: fn(T, T) -> T) -> (usize, Vec<Vec<Option<usize>>>)
where
    T: Clone + Copy + PartialEq + PartialOrd,
{
    let n = a.len();
    let mut stack = vec![0];
    let mut ret = vec![vec![None; 2]; n];
    for i in 1..n {
        let mut l = None;
        while let Some(&j) = stack.last() {
            if op(a[j], a[i]) == a[j] {
                ret[j][1] = Some(i);
                break;
            } else {
                l = stack.pop();
            }
        }
        if let Some(l) = l {
            ret[i][0] = Some(l);
        }
        stack.push(i);
    }
    (stack[0], ret)
}

#[cfg(test)]
pub mod test {
    use super::cartesian_tree;
    #[test]
    pub fn random() {
        use rand::{Rng, SeedableRng};
        let mut rng = rand_chacha::ChaChaRng::from_seed([0; 32]);
        const T: usize = 1000;
        const N: usize = 100;
        const V: usize = 100;
        for n in 1..=N {
            for _ in 0..T {
                for op in [std::cmp::min::<usize>, std::cmp::max::<usize>] {
                    let a = (0..n).map(|_| rng.random_range(0..V)).collect::<Vec<_>>();
                    let mut expected = vec![vec![None; 2]; n];
                    let expected_root = build(&a, 0, n - 1, &mut expected, op);
                    let (actual_root, actual) = cartesian_tree(&a, op);
                    assert_eq!(expected_root, actual_root);
                    assert_eq!(expected, actual);
                    fn build(
                        a: &[usize],
                        i0: usize,
                        i1: usize,
                        expected: &mut Vec<Vec<Option<usize>>>,
                        op: fn(usize, usize) -> usize,
                    ) -> usize {
                        if i0 == i1 {
                            return i0;
                        }
                        let mut minv = None;
                        for i in i0..=i1 {
                            if let Some((val, _)) = minv {
                                if op(val, a[i]) != val && op(val, a[i]) == a[i] {
                                    minv = Some((a[i], i));
                                }
                            } else {
                                minv = Some((a[i], i));
                            }
                        }
                        let (_, i) = minv.unwrap();
                        if i0 < i {
                            expected[i][0] = Some(build(a, i0, i - 1, expected, op));
                        }
                        if i < i1 {
                            expected[i][1] = Some(build(a, i + 1, i1, expected, op));
                        }
                        i
                    }
                }
            }
        }
    }
}
