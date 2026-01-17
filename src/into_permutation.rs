use cargo_snippet::snippet;

#[snippet("IntoPermutation")]
pub fn next_permutation<T: Ord>(arr: &mut [T]) -> bool {
    let last_ascending = match arr.windows(2).rposition(|w| w[0] < w[1]) {
        Some(i) => i,
        None => {
            return false;
        }
    };
    let swap_target = arr.iter().rposition(|x| x > &arr[last_ascending]).unwrap();
    arr.swap(last_ascending, swap_target);
    arr[last_ascending + 1..].reverse();
    true
}
#[snippet("IntoPermutation")]
pub struct PermutationIterator<T> {
    v: Vec<T>,
    is_first: bool,
}
#[snippet("IntoPermutation")]
impl<T: Copy + Ord + Clone> PermutationIterator<T> {
    pub fn new(mut v: Vec<T>) -> PermutationIterator<T> {
        v.sort();
        PermutationIterator { v, is_first: true }
    }
}
#[snippet("IntoPermutation")]
impl<T: Copy + Ord + Clone> Iterator for PermutationIterator<T> {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_first {
            self.is_first = false;
            Some(self.v.clone())
        } else if next_permutation(&mut self.v) {
            Some(self.v.clone())
        } else {
            None
        }
    }
}

#[snippet("IntoPermutation")]
pub trait IntoPermutations<T: Copy + Ord + Clone> {
    fn into_permutations(self) -> PermutationIterator<T>;
}
#[snippet("IntoPermutation")]
// implement for ones that has IntoIterator.
impl<T: Copy + Ord + Clone, I: IntoIterator<Item = T>> IntoPermutations<T> for I {
    fn into_permutations(self) -> PermutationIterator<T> {
        PermutationIterator::new(self.into_iter().collect())
    }
}
