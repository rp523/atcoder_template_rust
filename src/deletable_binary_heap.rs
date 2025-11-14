use cargo_snippet::snippet;

#[snippet("DeletableBinaryHeap")]
#[derive(Clone)]
pub struct DeletableBinaryHeap<T> {
    que: std::collections::BinaryHeap<T>,
    del_rsv: std::collections::BinaryHeap<T>,
}
#[snippet("DeletableBinaryHeap")]
impl<T: Clone + PartialOrd + Ord> DeletableBinaryHeap<T> {
    pub fn new() -> Self {
        Self {
            que: std::collections::BinaryHeap::<T>::new(),
            del_rsv: std::collections::BinaryHeap::<T>::new(),
        }
    }
    pub fn pop(&mut self) -> Option<T> {
        let ret = self.que.pop();
        self.lazy_eval();
        ret
    }
    pub fn push(&mut self, v: T) {
        self.que.push(v)
    }
    pub fn peek(&self) -> Option<&T> {
        self.que.peek()
    }
    pub fn remove(&mut self, del_v: &T) {
        self.del_rsv.push(del_v.clone());
        debug_assert!(self.que.iter().any(|v| v == del_v));
        self.lazy_eval();
    }
    pub fn is_empty(&self) -> bool {
        self.que.is_empty()
    }
    pub fn len(&self) -> usize {
        self.que.len() - self.del_rsv.len()
    }
    fn lazy_eval(&mut self) {
        while let Some(del_v) = self.del_rsv.peek() {
            if let Some(v) = self.que.peek() {
                if del_v == v {
                    self.que.pop();
                    self.del_rsv.pop();
                } else {
                    break;
                }
            } else {
                unreachable!()
            }
        }
    }
}