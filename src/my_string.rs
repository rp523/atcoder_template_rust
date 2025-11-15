use cargo_snippet::snippet;

#[snippet("MyStr")]
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct MyStr {
    vc: Vec<char>,
}
#[snippet("MyStr")]
impl MyStr {
    pub fn new() -> Self {
        Self { vc: vec![] }
    }
    pub fn from(s: &str) -> Self {
        Self {
            vc: s.to_string().chars().collect::<Vec<char>>(),
        }
    }
    pub fn len(&self) -> usize {
        self.vc.len()
    }
    pub fn clear(&mut self) {
        self.vc.clear()
    }
    pub fn is_empty(&self) -> bool {
        self.vc.is_empty()
    }
    pub fn first(&self) -> Option<&char> {
        self.vc.first()
    }
    pub fn last(&self) -> Option<&char> {
        self.vc.last()
    }
    pub fn push(&mut self, c: char) {
        self.vc.push(c);
    }
    pub fn push_str(&mut self, s: &str) {
        for c in s.to_string().chars().collect::<Vec<char>>().into_iter() {
            self.push(c);
        }
    }
    pub fn pop(&mut self) -> Option<char> {
        self.vc.pop()
    }
    pub fn into_iter(self) -> std::vec::IntoIter<char> {
        self.vc.into_iter()
    }
    pub fn iter(&self) -> std::slice::Iter<'_, char> {
        self.vc.iter()
    }
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, char> {
        self.vc.iter_mut()
    }
    pub fn swap(&mut self, a: usize, b: usize) {
        self.vc.swap(a, b);
    }
    pub fn reverse(&mut self) {
        self.vc.reverse();
    }
    pub fn find(&self, p: &Self) -> Option<usize> {
        let s: String = self.vc.iter().collect::<String>();
        let p: String = p.vc.iter().collect::<String>();
        s.find(&p)
    }
    pub fn rfind(&self, p: &Self) -> Option<usize> {
        let s: String = self.vc.iter().collect::<String>();
        let p: String = p.vc.iter().collect::<String>();
        s.rfind(&p)
    }
    pub fn into_usize(self, base: char, offset: usize) -> Vec<usize> {
        self.vc
            .into_iter()
            .map(|c| (c as u8 - base as u8) as usize + offset)
            .collect::<Vec<usize>>()
    }
    pub fn sort(&mut self) {
        self.vc.sort();
    }
    pub fn remove(&mut self, index: usize) -> char {
        self.vc.remove(index)
    }
}
#[snippet("MyStr")]
impl std::str::FromStr for MyStr {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self {
            vc: s.to_string().chars().collect::<Vec<char>>(),
        })
    }
}
#[snippet("MyStr")]
impl<Idx: std::slice::SliceIndex<[char]>> std::ops::Index<Idx> for MyStr {
    type Output = Idx::Output;
    fn index(&self, i: Idx) -> &Self::Output {
        &self.vc[i]
    }
}
#[snippet("MyStr")]
impl<Idx: std::slice::SliceIndex<[char]>> std::ops::IndexMut<Idx> for MyStr {
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        &mut self.vc[index]
    }
}
#[snippet("MyStr")]
impl std::ops::Add<MyStr> for MyStr {
    type Output = MyStr;
    fn add(self, rhs: Self) -> Self::Output {
        let mut ret = self;
        for c in rhs.into_iter() {
            ret.vc.push(c);
        }
        ret
    }
}
#[snippet("MyStr")]
impl std::ops::AddAssign<MyStr> for MyStr {
    fn add_assign(&mut self, rhs: Self) {
        for c in rhs.into_iter() {
            self.vc.push(c);
        }
    }
}
#[snippet("MyStr")]
impl std::ops::Add<char> for MyStr {
    type Output = MyStr;
    fn add(self, rhs: char) -> Self::Output {
        let mut ret = self;
        ret.vc.push(rhs);
        ret
    }
}
#[snippet("MyStr")]
impl std::ops::AddAssign<char> for MyStr {
    fn add_assign(&mut self, rhs: char) {
        self.vc.push(rhs);
    }
}
#[snippet("MyStr")]
impl std::fmt::Display for MyStr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.vc.iter().collect::<String>())
    }
}
#[snippet("MyStr")]
impl std::fmt::Debug for MyStr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.vc.iter().collect::<String>())
    }
}
