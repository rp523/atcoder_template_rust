#![allow(unused_macros, unused_imports, dead_code)]

mod procon_reader {
    use std::fmt::Debug;
    use std::io::Read;
    use std::str::FromStr;
    pub fn read<T: FromStr>() -> T
    where
        <T as FromStr>::Err: Debug,
    {
        let stdin = std::io::stdin();
        let mut stdin_lock = stdin.lock();
        let mut u8b: [u8; 1] = [0];
        loop {
            let mut buf: Vec<u8> = Vec::with_capacity(16);
            loop {
                let res = stdin_lock.read(&mut u8b);
                if res.unwrap_or(0) == 0 || u8b[0] <= b' ' {
                    break;
                } else {
                    buf.push(u8b[0]);
                }
            }
            if !buf.is_empty() {
                let ret = String::from_utf8(buf).unwrap();
                return ret.parse().unwrap();
            }
        }
    }
    pub fn read_vec<T: std::str::FromStr>(n: usize) -> Vec<T>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..n).map(|_| read::<T>()).collect::<Vec<T>>()
    }
    pub fn read_vec_sub1(n: usize) -> Vec<usize> {
        (0..n).map(|_| read::<usize>() - 1).collect::<Vec<usize>>()
    }
    pub fn read_mat<T: std::str::FromStr>(h: usize, w: usize) -> Vec<Vec<T>>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..h).map(|_| read_vec::<T>(w)).collect::<Vec<Vec<T>>>()
    }
}
use procon_reader::*;
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////

mod online_dynamic_connectivity {
    #[derive(Clone, Copy, PartialEq)]
    enum SplayDir {
        None = 0,
        Left,
        Right,
    }
    mod euler_move {
        use super::SplayDir;
        #[derive(Clone)]
        pub struct EulerMove {
            // splay
            pub left: *mut EulerMove,
            pub right: *mut EulerMove,
            pub parent: *mut EulerMove,
            // euler tour
            pub from: usize,
            pub to: usize,
            pub size: usize,
            pub at_this_level: bool,
            pub at_this_level_subany: bool,
            pub useless_connected: bool,
            pub useless_connected_subany: bool,
        }
        impl EulerMove {
            pub fn new(from: usize, to: usize) -> Self {
                Self {
                    // splay
                    left: std::ptr::null_mut(),
                    right: std::ptr::null_mut(),
                    parent: std::ptr::null_mut(),
                    // euler tour
                    from,
                    to,
                    size: if from == to { 1 } else { 0 },
                    at_this_level: from < to,
                    at_this_level_subany: from < to,
                    useless_connected: false,
                    useless_connected_subany: false,
                }
            }
            fn root(&mut self) -> *mut EulerMove {
                let mut t = self as *mut Self;
                unsafe {
                    while !(*t).parent.is_null() {
                        t = (*t).parent;
                    }
                }
                t
            }
            pub fn same(s: *mut Self, t: *mut Self) -> bool {
                if s.is_null() {
                    debug_assert!(!t.is_null());
                    return false;
                }
                if t.is_null() {
                    debug_assert!(!s.is_null());
                    return false;
                }
                unsafe {
                    (*s).splay();
                    (*t).splay();
                    (*s).root() == (*t).root()
                }
            }
            pub fn update(&mut self) {
                self.size = if self.from == self.to { 1 } else { 0 };
                self.at_this_level_subany = self.at_this_level;
                self.useless_connected_subany = self.useless_connected;
                let left = self.left;
                let right = self.right;
                unsafe {
                    if !left.is_null() {
                        self.size += (*left).size;
                        self.at_this_level_subany =
                            self.at_this_level_subany || (*left).at_this_level_subany;
                        self.useless_connected_subany =
                            self.useless_connected_subany || (*left).useless_connected_subany;
                    }
                    if !right.is_null() {
                        self.size += (*right).size;
                        self.at_this_level_subany =
                            self.at_this_level_subany || (*right).at_this_level_subany;
                        self.useless_connected_subany =
                            self.useless_connected_subany || (*right).useless_connected_subany;
                    }
                }
            }
            pub fn splay(&mut self) {
                while self.for_parent() != SplayDir::None {
                    unsafe {
                        let p = self.parent;
                        let p_for_pp = (*p).for_parent();
                        if p_for_pp == SplayDir::None {
                            // zig
                            self.rotate();
                        } else if p_for_pp == self.for_parent() {
                            // zig zig
                            (*p).rotate();
                            self.rotate();
                        } else {
                            // zig zag
                            self.rotate();
                            self.rotate();
                        }
                    }
                }
            }
            fn for_parent(&mut self) -> SplayDir {
                if self.parent.is_null() {
                    SplayDir::None
                } else {
                    unsafe {
                        let me = self as *mut Self;
                        if (*self.parent).left == me {
                            SplayDir::Left
                        } else {
                            debug_assert!((*self.parent).right == me);
                            SplayDir::Right
                        }
                    }
                }
            }
            fn rotate(&mut self) {
                let p = self.parent;
                debug_assert!(!p.is_null());
                let me = self as *mut Self;
                unsafe {
                    debug_assert!((*me).for_parent() != SplayDir::None);
                    let pp = (*p).parent;
                    let c;
                    if (*me).for_parent() == SplayDir::Left {
                        c = (*me).right;
                        (*me).right = p;
                        (*p).left = c;
                    } else {
                        c = (*me).left;
                        (*me).left = p;
                        (*p).right = c;
                    }
                    if !pp.is_null() {
                        if (*pp).left == p {
                            (*pp).left = me;
                        } else {
                            (*pp).right = me;
                        }
                    }
                    (*me).parent = pp;
                    (*p).parent = me;
                    if !c.is_null() {
                        (*c).parent = p;
                    }
                    (*p).update();
                }
                self.update();
            }
            pub fn merge(mut s: *mut Self, t: *mut Self) -> *mut Self {
                if s.is_null() {
                    debug_assert!(!t.is_null());
                    return t;
                }
                if t.is_null() {
                    debug_assert!(!s.is_null());
                    return s;
                }
                unsafe {
                    while !(*s).parent.is_null() {
                        s = (*s).parent;
                    }
                    while !(*s).right.is_null() {
                        s = (*s).right;
                    }
                    (*s).splay();
                    (*s).right = t;
                    (*t).parent = s;
                    (*s).update();
                }
                s
            }
            pub fn split(s: *mut Self) -> (*mut Self, *mut Self) // (..s, s..)
            {
                unsafe {
                    (*s).splay();
                    let t = (*s).left;
                    if !t.is_null() {
                        (*t).parent = std::ptr::null_mut();
                    }
                    (*s).left = std::ptr::null_mut();
                    (*s).update();
                    (t, s)
                }
            }
        }
    }
    mod euler_tree {
        use super::euler_move::EulerMove;
        use std::collections::HashMap;
        pub struct EulerTour {
            tour: Vec<HashMap<usize, Box<EulerMove>>>,
        }
        impl EulerTour {
            pub fn new(n: usize) -> Self {
                Self {
                    tour: (0..n)
                        .map(|i| {
                            let mut mp = HashMap::new();
                            mp.insert(i, Box::new(EulerMove::new(i, i)));
                            mp
                        }
                    ).collect::<Vec<_>>(),
                }
            }
            pub fn get_node(&mut self, from: usize, to: usize) -> *mut EulerMove {
                self.tour[from]
                    .entry(to)
                    .or_insert_with(|| Box::new(EulerMove::new(from, to)));
                &mut **self.tour[from].get_mut(&to).unwrap()
            }
            #[allow(unused_assignments)]
            fn re_tour(s: *mut EulerMove) -> *mut EulerMove {
                let (s0, s1) = EulerMove::split(s);
                EulerMove::merge(s1, s0)
            }
            pub fn same(&mut self, a: usize, b: usize) -> bool {
                let a = self.get_node(a, a);
                let b = self.get_node(b, b);
                EulerMove::same(a, b)
            }
            #[allow(unused_assignments)]
            pub fn unite(&mut self, a: usize, b: usize) -> bool {
                if self.same(a, b) {
                    return false;
                }
                let aa = self.get_node(a, a);
                let aa_root = Self::re_tour(aa);
                let bb = self.get_node(b, b);
                let bb_root = Self::re_tour(bb);

                let ab = self.get_node(a, b);
                let ba = self.get_node(b, a);
                let aa_ab = EulerMove::merge(aa_root, ab);
                let bb_ba = EulerMove::merge(bb_root, ba);
                let _ = EulerMove::merge(aa_ab, bb_ba);
                true
            }
            fn remove_split(&mut self, from: usize, to: usize) -> (*mut EulerMove, *mut EulerMove) {
                let c = self.get_node(from, to);
                unsafe {
                    (*c).splay();
                    let left = (*c).left;
                    let right = (*c).right;
                    if !left.is_null() {
                        (*left).parent = std::ptr::null_mut();
                    }
                    if !right.is_null() {
                        (*right).parent = std::ptr::null_mut();
                    }
                    assert!(self.tour[from].remove(&to).is_some());
                    (left, right)
                }
            }
            pub fn cut(&mut self, a: usize, b: usize) -> bool {
                if !self.tour[a].contains_key(&b) {
                    return false;
                }
                let (xxa, bxx) = self.remove_split(a, b);
                if EulerMove::same(xxa, self.get_node(b, a)) {
                    let (xxb, _axxa) = self.remove_split(b, a);
                    let _ = EulerMove::merge(bxx, xxb);
                } else {
                    let (_bxxb, axx) = self.remove_split(b, a);
                    let _ = EulerMove::merge(axx, xxa);
                }
                true
            }
            pub fn get_size(&mut self, a: usize) -> usize {
                let a = self.get_node(a, a);
                unsafe {
                    (*a).splay();
                    (*a).size
                }
            }
            pub fn extract_level_match(t: *mut EulerMove) -> Option<(usize, usize)> {
                unsafe {
                    if t.is_null() || !(*t).at_this_level_subany {
                        return None;
                    }
                    if (*t).at_this_level {
                        (*t).splay();
                        (*t).at_this_level = false;
                        (*t).update();
                        return Some(((*t).from, (*t).to));
                    }
                    let left = (*t).left;
                    if let Some(ret) = Self::extract_level_match(left) {
                        return Some(ret);
                    }
                    let right = (*t).right;
                    if let Some(ret) = Self::extract_level_match(right) {
                        return Some(ret);
                    }
                    None
                }
            }
            pub fn extract_useless_connected(t: *mut EulerMove) -> Option<usize> {
                unsafe {
                    if t.is_null() || !(*t).useless_connected_subany {
                        return None;
                    }
                    if (*t).useless_connected {
                        (*t).splay();
                        return Some((*t).from);
                    }
                    let left = (*t).left;
                    if let Some(ret) = Self::extract_useless_connected(left) {
                        return Some(ret);
                    }
                    let right = (*t).right;
                    if let Some(ret) = Self::extract_useless_connected(right) {
                        return Some(ret);
                    }
                    None
                }
            }
            pub fn update_useless_connected(&mut self, x: usize, b: bool) {
                let x = self.get_node(x, x);
                unsafe {
                    (*x).splay();
                    (*x).useless_connected = b;
                    (*x).update();
                }
            }
        }
    }
    pub mod dynamic_connectivity {
        use super::{euler_move::EulerMove, euler_tree::EulerTour};
        use std::collections::HashSet;
        pub struct DynamicConnectivity {
            n: usize,
            pub trees: Vec<EulerTour>,
            useless_edges: Vec<Vec<HashSet<usize>>>,
        }
        impl DynamicConnectivity {
            pub fn new(n: usize) -> Self {
                Self {
                    n,
                    trees: vec![EulerTour::new(n)],
                    useless_edges: vec![vec![HashSet::new(); n]],
                }
            }
            pub fn unite(&mut self, a: usize, b: usize) -> bool {
                if a == b {
                    return false;
                }
                if self.trees[0].unite(a, b) {
                    return true;
                }
                assert!(self.useless_edges[0][a].insert(b));
                assert!(self.useless_edges[0][b].insert(a));
                if self.useless_edges[0][a].len() == 1 {
                    self.trees[0].update_useless_connected(a, true);
                }
                if self.useless_edges[0][b].len() == 1 {
                    self.trees[0].update_useless_connected(b, true);
                }
                false
            }
            pub fn same(&mut self, a: usize, b: usize) -> bool {
                self.trees[0].same(a, b)
            }
            pub fn cut(&mut self, mut a: usize, mut b: usize) -> bool {
                if a == b {
                    return false;
                }
                self.trees
                    .iter_mut()
                    .zip(self.useless_edges.iter_mut())
                    .for_each(|(tree, edges)| {
                        for (a, b) in [(a, b), (b, a)].iter().copied() {
                            if edges[a].remove(&b) && edges[a].is_empty() {
                                tree.update_useless_connected(a, false);
                            }
                        }
                    });
                let org_level_len = self.trees.len();
                for level in (0..org_level_len).rev() {
                    if self.trees[level].cut(a, b) {
                        // tree-connectivity changed.
                        if level == org_level_len - 1 {
                            self.trees.push(EulerTour::new(self.n));
                            self.useless_edges.push(vec![HashSet::new(); self.n]);
                        }
                        // try reconnect
                        self.trees.iter_mut().take(level).for_each(|tree| {
                            tree.cut(a, b);
                        });
                        for i in (0..=level).rev() {
                            if self.trees[i].get_size(a) > self.trees[i].get_size(b) {
                                std::mem::swap(&mut a, &mut b);
                            }
                            // edge update
                            unsafe {
                                let node_a = self.trees[i].get_node(a, a);
                                (*node_a).splay();
                                while let Some((lup_a, lup_b)) =
                                    EulerTour::extract_level_match(node_a)
                                {
                                    self.trees[i + 1].unite(lup_a, lup_b);
                                    (*node_a).splay();
                                }
                                // try_reconnect in euler tour
                                while let Some(x) = EulerTour::extract_useless_connected(node_a) {
                                    while let Some(&y) = self.useless_edges[i][x].iter().next() {
                                        for (x, y) in vec![(x, y), (y, x)].iter().copied() {
                                            assert!(self.useless_edges[i][x].remove(&y));
                                            if self.useless_edges[i][x].is_empty() {
                                                self.trees[i].update_useless_connected(x, false);
                                            }
                                        }
                                        if self.trees[i].same(x, y) {
                                            for (x, y) in vec![(x, y), (y, x)].iter().copied() {
                                                self.useless_edges[i + 1][x].insert(y);
                                                if self.useless_edges[i + 1][x].len() == 1 {
                                                    self.trees[i + 1]
                                                        .update_useless_connected(x, true);
                                                }
                                            }
                                        } else {
                                            for j in 0..=i {
                                                self.trees[j].unite(x, y);
                                            }
                                            return false;
                                        }
                                    }
                                    (*node_a).splay();
                                }
                            }
                        }
                        return true;
                    }
                }
                false
            }
        }
    }
}
use online_dynamic_connectivity::dynamic_connectivity::DynamicConnectivity;

#[cfg(test)]
fn check() {
    fn trial(n: usize, ques: Vec<(usize, usize, usize)>) {
        println!("{:?}", ques);
        let mut dc = DynamicConnectivity::new(n);
        let mut es = BTreeSet::new();
        let mut log_n = 1usize;
        while 2usize.pow(log_n as u32) < n {
            log_n += 1;
        }
        for (t, a, b) in ques {
            debug!(t, a, b);
            let mut uf0 = UnionFind::new(n);
            for &(a, b) in es.iter() {
                uf0.unite(a, b);
            }
            match t {
                1 => {
                    assert!(dc.unite(a, b) != uf0.same(a, b));
                    assert!(es.insert((a, b)));
                }
                2 => {
                    let dc_ret = dc.cut(a, b);
                    assert!(es.remove(&(a, b)));
                    {
                        let mut uf = UnionFind::new(n);
                        for &(a, b) in es.iter() {
                            uf.unite(a, b);
                        }
                        assert!(dc_ret != uf.same(a, b));
                    }
                }
                _ => unreachable!(),
            }
            let mut uf = UnionFind::new(n);
            for &(a, b) in es.iter() {
                uf.unite(a, b);
            }
            for j in 0..n {
                for i in 0..j {
                    assert!(dc.same(i, j) == uf.same(i, j));
                }
            }
            assert!(dc.trees.len() <= log_n);
        }
    }
    let n = 10;
    let mut rand = XorShift64::new();
    for _ in 0..1000 {
        let ques = {
            let mut es = BTreeSet::new();
            let mut ques = vec![];
            while ques.len() < n * n {
                let t = rand.next_usize() % 2 + 1;
                let a = rand.next_usize() % n;
                let b = (a + 1 + rand.next_usize() % (n - 1)) % n;
                let (a, b) = (min(a, b), max(a, b));
                match t {
                    1 => {
                        if es.contains(&(a, b)) {
                            continue;
                        }
                        es.insert((a, b));
                        ques.push((t, a, b));
                    }
                    2 => {
                        if !es.contains(&(a, b)) {
                            continue;
                        }
                        es.remove(&(a, b));
                        ques.push((t, a, b));
                    }
                    _ => unreachable!(),
                }
            }
            ques
        };
        trial(n, ques);
    }
}
fn main() {
    let n = read::<usize>();
    let k = read::<usize>();
    let mut uf = DynamicConnectivity::new(n);
    for _ in 0..k {
        let t = read::<usize>();
        let a = read::<usize>();
        let b = read::<usize>();
        match t {
            1 => {
                uf.unite(a, b);
            }
            2 => {
                uf.cut(a, b);
            }
            3 => {
                if uf.same(a, b) {
                    println!("YES");
                } else {
                    println!("NO");
                }
            }
            _ => unreachable!()
        }
    }
}
