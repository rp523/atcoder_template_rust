use cargo_snippet::snippet;

#[snippet("floor_sum")]
// sum_0^{n-1} (a * i + b) / m
pub fn floor_sum(n: usize, m: i64, mut a: i64, mut b: i64) -> i64 {
    debug_assert!(m > 0);
    let mut ret = 0;
    if a >= m {
        let d = a / m;
        let n = n as i64;
        ret += d * ((n * (n - 1)) / 2);
        a %= m;
    } else if a < 0 {
        let d = (-a + m - 1) / m;
        let n = n as i64;
        ret -= d * ((n * (n - 1)) / 2);
        a = (a + m * d) % m;
    }
    if b >= m {
        let d = b / m;
        let n = n as i64;
        ret += d * n;
        b %= m;
    } else if b < 0 {
        let d = (-b + m - 1) / m;
        let n = n as i64;
        ret -= d * n;
        b = (b + m * d) % m;
    }
    let last = a * n as i64 + b;
    if last >= m {
        let y = last / m;
        let z = last % m;
        ret += floor_sum(y as usize, a, m, z)
    }
    ret
}

#[test]
fn floor_sum_test() {
    for n in 0..50 {
        for m in 1..50 {
            for a in -50..50 {
                for b in -50..50 {
                    let expected = (0..n)
                        .map(|i| {
                            let num = a * i as i64 + b;
                            if num >= 0 {
                                num / m
                            } else {
                                -(-num + m - 1) / m
                            }
                        })
                        .sum::<i64>();
                    let actual = floor_sum(n, m, a, b);
                    assert_eq!(expected, actual);
                }
            }
        }
    }
}
