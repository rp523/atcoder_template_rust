// ランダム入力生成器。使い方: gen <seed>  → 標準出力に入力を1つ書く
// 問題ごとに `generate` だけ書き換える。Rng のヘルパーはそのまま使い回せる。
#![allow(dead_code)]
use std::collections::HashSet;
use std::fmt::Write;

// ===================== 問題ごとにここを書き換える =====================
fn generate(rng: &mut Rng, out: &mut String) {
    let t = rng.range(1, 3);
    println!("{}", t);
}
// =====================================================================

fn main() {
    let seed: u64 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let mut rng = Rng::new(seed);
    let mut out = String::new();
    generate(&mut rng, &mut out);
    print!("{out}");
}

/// 依存なしの乱数 (splitmix64)。seed が同じなら同じ入力が出るので、反例を再現できる。
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        let mut r = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) ^ 0xDEADBEEF);
        r.next();
        r
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    /// [lo, hi] の一様乱数(両端含む)
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
    fn urange(&mut self, lo: usize, hi: usize) -> usize {
        self.range(lo as i64, hi as i64) as usize
    }
    /// 確率 p で true
    fn chance(&mut self, p: f64) -> bool {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64 <= p
    }
    fn vec(&mut self, n: usize, lo: i64, hi: i64) -> Vec<i64> {
        (0..n).map(|_| self.range(lo, hi)).collect()
    }
    fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            let j = self.urange(0, i);
            v.swap(i, j);
        }
    }
    /// 0..n の順列
    fn perm(&mut self, n: usize) -> Vec<usize> {
        let mut v: Vec<usize> = (0..n).collect();
        self.shuffle(&mut v);
        v
    }
    /// 長さ n、文字種 alphabet の文字列 (例: rng.string(5, "ab"))
    fn string(&mut self, n: usize, alphabet: &str) -> String {
        let cs: Vec<char> = alphabet.chars().collect();
        (0..n).map(|_| cs[self.urange(0, cs.len() - 1)]).collect()
    }
    /// n 頂点のランダムな木の辺 (0-indexed, 頂点番号もシャッフル済み)
    fn tree(&mut self, n: usize) -> Vec<(usize, usize)> {
        let p = self.perm(n);
        let mut es: Vec<(usize, usize)> =
            (1..n).map(|i| (p[self.urange(0, i - 1)], p[i])).collect();
        self.shuffle(&mut es);
        es
    }
    /// n 頂点 m 辺のランダムグラフ (0-indexed)。
    /// connected: 頂点0から全頂点へ到達可能にする(有向なら0→各頂点の向きの全域木を含める)
    /// simple: 自己ループ・多重辺なし
    fn graph(&mut self, n: usize, m: usize, directed: bool, connected: bool, simple: bool) -> Vec<(usize, usize)> {
        let mut es = vec![];
        let mut seen = HashSet::new();
        let key = |a: usize, b: usize| if directed || a < b { (a, b) } else { (b, a) };
        if connected {
            let mut order = self.perm(n);
            let z = order.iter().position(|&v| v == 0).unwrap();
            order.swap(0, z); // 根を頂点0にする
            for i in 1..n {
                let (a, b) = (order[self.urange(0, i - 1)], order[i]);
                seen.insert(key(a, b));
                es.push((a, b));
            }
        }
        let mut guard = 0;
        while es.len() < m && guard < 100 * (m + 1) {
            guard += 1;
            let (a, b) = (self.urange(0, n - 1), self.urange(0, n - 1));
            if simple && (a == b || seen.contains(&key(a, b))) {
                continue;
            }
            seen.insert(key(a, b));
            es.push((a, b));
        }
        self.shuffle(&mut es);
        es
    }
}
