#!/usr/bin/env python3
"""
ランダムテスト(ストレステスト)ランナー。Windows / Mac / Linux 共通。

  src/bin/main.rs   … 提出コード(テストしたい解)
  src/bin/naive.rs  … 愚直解(遅くていいので確実に正しいもの)
  src/bin/gen.rs    … 入力生成器 (gen <seed> で入力を1つ出力)
  src/bin/checker.rs… (任意) 答えが複数ありうる問題用。
                      checker <入力> <mainの出力> <naiveの出力> を実行し、終了コード0なら正解扱い

使い方:
  python stress.py                 # seed 0 から 1000 ケース
  python stress.py -n 5000 -s 100  # seed 100 から 5000 ケース
  python stress.py --seed-only 42  # seed 42 だけ再実行(修正後の確認用)

反例が見つかると fail/ に input.txt / main.txt / naive.txt を保存して止まる。
"""
import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXE = ".exe" if os.name == "nt" else ""
BIN = ROOT / "target" / "release"


def build():
    print("building...", flush=True)
    r = subprocess.run(["cargo", "build", "--release", "--bins", "-q"], cwd=ROOT)
    if r.returncode != 0:
        sys.exit("build failed")


def run(name, args=(), stdin="", timeout=5.0):
    """(stdout, エラー文字列 or None) を返す"""
    try:
        r = subprocess.run(
            [str(BIN / (name + EXE)), *map(str, args)],
            input=stdin, capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return "", f"TLE (>{timeout}s)"
    if r.returncode != 0:
        return r.stdout, f"RE (exit {r.returncode})\n{r.stderr[-2000:]}"
    return r.stdout, None


def save_fail(inp, out_main, out_naive, why):
    d = ROOT / "fail"
    d.mkdir(exist_ok=True)
    (d / "input.txt").write_text(inp)
    (d / "main.txt").write_text(out_main)
    (d / "naive.txt").write_text(out_naive)
    print(f"\n==== {why} ====")
    if len(inp) <= 2000:
        print("[input]\n" + inp.rstrip())
        print("[main]\n" + out_main.rstrip())
        print("[naive]\n" + out_naive.rstrip())
    print(f"\n保存先: {d}")


def check_one(seed, use_checker, timeout):
    inp, err = run("gen", [seed], timeout=timeout)
    if err:
        print(f"gen が失敗 (seed={seed}): {err}")
        return False
    out_n, err = run("naive", stdin=inp, timeout=timeout * 10)
    if err:
        save_fail(inp, "", out_n, f"naive が失敗 seed={seed}: {err}")
        return False
    out_m, err = run("main", stdin=inp, timeout=timeout)
    if err:
        save_fail(inp, out_m, out_n, f"main が {err} seed={seed}")
        return False

    if use_checker:
        d = ROOT / "fail"
        d.mkdir(exist_ok=True)
        files = [d / "_in.txt", d / "_main.txt", d / "_naive.txt"]
        for f, s in zip(files, (inp, out_m, out_n)):
            f.write_text(s)
        _, err = run("checker", files, timeout=timeout)
        ok = err is None
    else:
        ok = out_m.split() == out_n.split()  # 空白・改行の違いは無視

    if not ok:
        save_fail(inp, out_m, out_n, f"WA seed={seed}")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=1000, help="ケース数")
    ap.add_argument("-s", "--start", type=int, default=0, help="開始seed")
    ap.add_argument("--seed-only", type=int, help="このseedだけ実行")
    ap.add_argument("-t", "--timeout", type=float, default=5.0, help="main の制限秒")
    ap.add_argument("--no-build", action="store_true")
    a = ap.parse_args()

    if not a.no_build:
        build()
    use_checker = (ROOT / "src" / "bin" / "checker.rs").exists()
    seeds = [a.seed_only] if a.seed_only is not None else range(a.start, a.start + a.n)

    t0 = time.time()
    for i, seed in enumerate(seeds, 1):
        if not check_one(seed, use_checker, a.timeout):
            sys.exit(1)
        if i % 100 == 0:
            print(f"\r{i} ケース OK ({time.time() - t0:.1f}s)", end="", flush=True)
    print(f"\n全 {len(seeds)} ケース一致しました")


if __name__ == "__main__":
    main()
