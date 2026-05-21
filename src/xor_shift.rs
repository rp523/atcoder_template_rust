use cargo_snippet::snippet;

#[snippet("XorShift64")]
#[derive(Clone, Debug)]
pub struct XorShift64(usize);
#[snippet("XorShift64")]
impl XorShift64 {
    pub fn new() -> Self {
        Self(88172645463325252_usize)
    }
    fn next(&mut self) {
        self.0 ^= self.0 << 7;
        self.0 ^= self.0 >> 9;
    }
    pub fn next_usize(&mut self) -> usize {
        self.next();
        self.0
    }
    pub fn next_f64(&mut self) -> f64 {
        self.next();
        self.0 as f64 * 5.421_010_862_427_522e-20
    }
}
#[snippet("XorShift64")]
pub trait Shuffle {
    fn shuffle(&mut self, rand: &mut XorShift64);
}
#[snippet("XorShift64")]
impl<T> Shuffle for Vec<T> {
    fn shuffle(&mut self, rand: &mut XorShift64) {
        let n = self.len();
        for i in (1..n).rev() {
            let j = rand.next_usize() % (i + 1);
            self.swap(i, j);
        }
    }
}
