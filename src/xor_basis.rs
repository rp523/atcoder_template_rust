use cargo_snippet::snippet;

// construct XOR basis.
// Some XOR combination of these can make every element of the array.
// When msb of a[i] is b-th, b-th bit of all the other element is zero.
#[snippet("xor_basis")]
#[allow(dead_code)]
fn xor_basis(a: &[usize]) -> Vec<usize> {
    let mut basis: Vec<usize> = vec![];
    for mut a in a.iter().copied() {
        for &base in basis.iter() {
            if a > (a ^ base) {
                a ^= base;
            }
        }
        for base in basis.iter_mut() {
            if *base > (a ^ *base) {
                *base ^= a;
            }
        }
        if a > 0 {
            basis.push(a);
        }
    }
    basis.sort();
    basis
}
