use cargo_snippet::snippet;

#[snippet("SparseTable")]
#[derive(Clone, Debug)]
pub struct SparseTable<T> {
    left: Vec<Vec<T>>,
    len_to_di: Vec<usize>,
    op: fn(T, T) -> T,
}
#[snippet("SparseTable")]
impl<T> SparseTable<T>
where
    T: Clone + std::fmt::Debug,
{
    pub fn new(op: fn(T, T) -> T, a: Vec<T>) -> Self {
        let n = a.len();
        let mut dmax = 0;
        let len_to_di = {
            let mut len_to_di = vec![0; n + 1];
            for (ln, len_to_di) in len_to_di.iter_mut().enumerate().take(n + 1).skip(1) {
                if ln > 2 * (1 << dmax) {
                    dmax += 1;
                }
                *len_to_di = dmax;
            }
            len_to_di
        };
        let mut left = vec![a.clone(); dmax + 1];
        for di in 0..dmax {
            for i in 0..n {
                let ri = std::cmp::min(i + (1 << di), n - 1);
                left[di + 1][i] = op(left[di][i].clone(), left[di][ri].clone());
            }
        }
        Self {
            left,
            len_to_di,
            op,
        }
    }
    pub fn query(&self, l: usize, r: usize) -> T {
        let di = self.len_to_di[r - l + 1];
        (self.op)(
            self.left[di][l].clone(),
            self.left[di][r - ((1 << di) - 1)].clone(),
        )
    }
    pub fn get(&self, i: usize) -> T {
        self.left[0][i].clone()
    }
}

#[snippet("SparseTable2D")]
#[derive(Clone, Debug)]
pub struct SparseTable2D<T> {
    left_lower: Vec<Vec<Vec<Vec<T>>>>,
    len_to_di: Vec<usize>,
    op: fn(T, T) -> T,
}
#[snippet("SparseTable2D")]
impl<T> SparseTable2D<T>
where
    T: Clone + std::fmt::Debug,
{
    pub fn new(op: fn(T, T) -> T, a: Vec<Vec<T>>) -> Self {
        let h = a.len();
        let w = a[0].len();
        let mut dmax = 0;
        let len_to_di = {
            let mut len_to_di = vec![0; std::cmp::max(h, w) + 1];
            for (ln, len_to_di) in len_to_di
                .iter_mut()
                .enumerate()
                .take(std::cmp::max(h, w) + 1)
            {
                if ln > 2 * (1 << dmax) {
                    dmax += 1;
                }
                *len_to_di = dmax;
            }
            len_to_di
        };
        let mut left_lower = vec![vec![a.clone(); len_to_di[w] + 1]; len_to_di[h] + 1];
        for di_y in 0..=len_to_di[h] {
            let pdi_y = di_y.saturating_sub(1);
            for di_x in 0..=len_to_di[w] {
                let pdi_x = di_x.saturating_sub(1);
                if (di_y, di_x) == (0, 0) {
                    continue;
                }
                for y0 in 0..h {
                    let y1 = if di_y == 0 {
                        y0
                    } else {
                        std::cmp::min(y0 + (1 << (di_y - 1)), h - 1)
                    };
                    for x0 in 0..w {
                        let x1 = if di_x == 0 {
                            x0
                        } else {
                            std::cmp::min(x0 + (1 << (di_x - 1)), w - 1)
                        };
                        left_lower[di_y][di_x][y0][x0] = op(
                            op(
                                left_lower[pdi_y][pdi_x][y0][x0].clone(),
                                left_lower[pdi_y][pdi_x][y0][x1].clone(),
                            ),
                            op(
                                left_lower[pdi_y][pdi_x][y1][x0].clone(),
                                left_lower[pdi_y][pdi_x][y1][x1].clone(),
                            ),
                        );
                    }
                }
            }
        }
        Self {
            left_lower,
            len_to_di,
            op,
        }
    }
    pub fn query(&self, y0: usize, y1: usize, x0: usize, x1: usize) -> T {
        let di_y = self.len_to_di[y1 - y0 + 1];
        let di_x = self.len_to_di[x1 - x0 + 1];
        (self.op)(
            (self.op)(
                self.left_lower[di_y][di_x][y0][x0].clone(),
                self.left_lower[di_y][di_x][y0][x1 - ((1 << di_x) - 1)].clone(),
            ),
            (self.op)(
                self.left_lower[di_y][di_x][y1 - ((1 << di_y) - 1)][x0].clone(),
                self.left_lower[di_y][di_x][y1 - ((1 << di_y) - 1)][x1 - ((1 << di_x) - 1)].clone(),
            ),
        )
    }
    pub fn get(&self, y: usize, x: usize) -> T {
        self.left_lower[0][0][y][x].clone()
    }
}

#[cfg(test)]
mod test {
    use super::{SparseTable, SparseTable2D};
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    use std::cmp::{max, min};
    #[test]
    fn sparse_table() {
        const NMAX: usize = 400;
        const V: i64 = 1000;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for op in [min, max] {
            for n in 1..=NMAX {
                let a = (0..n).map(|_| rng.random_range(-V..=V)).collect::<Vec<_>>();
                let table = SparseTable::new(op, a.clone());
                for l in 0..n {
                    assert_eq!(a[l], table.get(l));
                    for r in l..n {
                        let expected = (l + 1..=r).fold(a[l], |cum, i| op(cum, a[i]));
                        let actual = table.query(l, r);
                        assert_eq!(expected, actual);
                    }
                }
            }
        }
    }
    #[test]
    fn sparse_table2d() {
        const NMAX: usize = 20;
        const V: i64 = 1000;
        let mut rng = ChaChaRng::from_seed([0; 32]);
        for op in [min, max] {
            for h in 1..=NMAX {
                for w in 1..=NMAX {
                    let a = (0..h)
                        .map(|_| (0..w).map(|_| rng.random_range(-V..=V)).collect::<Vec<_>>())
                        .collect::<Vec<_>>();
                    let table = SparseTable2D::new(op, a.clone());
                    for y0 in 0..h {
                        for x0 in 0..w {
                            assert_eq!(a[y0][x0], table.get(y0, x0));
                            for y1 in y0..h {
                                for x1 in x0..w {
                                    let expected = (y0 + 1..=y1).fold(
                                        (x0 + 1..=x1).fold(a[y0][x0], |cum, x| op(cum, a[y0][x])),
                                        |cum, y| {
                                            op(
                                                cum,
                                                (x0 + 1..=x1)
                                                    .fold(a[y][x0], |cum, x| op(cum, a[y][x])),
                                            )
                                        },
                                    );
                                    let actual = table.query(y0, y1, x0, x1);
                                    assert_eq!(expected, actual);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
