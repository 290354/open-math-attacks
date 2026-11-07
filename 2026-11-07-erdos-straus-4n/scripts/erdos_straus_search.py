#!/usr/bin/env python3
"""Erdos-Straus 猜想计算核查脚本（可复现）。

对 2 <= n <= N 逐一验证：4/n = 1/x + 1/y + 1/z 存在正整数解。
- 偶数 / n≡3 (mod 4) / 3|n 三类直接用 Lean 已形式化的显式 witness；
- 其余（n ≡ 1 (mod 4) 且不被 3 整除的"难类"）做精确有理数搜索：
  固定 x (n/4 < x <= 3n/4)，把 1/y + 1/z = (4x-n)/(nx) 化为最简分数 a/b，
  在 b/a < y <= 2b/a 内枚举 y，检查 (a*y - b) | (b*y)。

所有解都回代整式方程 4xyz = n(xy + xz + yz) 做精确校验。

运行：
    python3 scripts/erdos_straus_search.py [N]     # 默认 N = 10000
"""
import sys
import time
from math import gcd


def witness(n: int):
    """显式类：直接给出 witness（与 lean/Attack/Basic.lean 中一致）。"""
    if n % 2 == 0:
        m = n // 2
        return (m, 2 * m, 2 * m)
    if n % 4 == 3:
        x = (n + 1) // 4
        y = n * (n + 1) // 2
        return (x, y, y)
    if n % 3 == 0:
        k = n // 3
        return (k, 6 * k, 6 * k)
    return None


def check(n: int, x: int, y: int, z: int) -> bool:
    """整式方程精确校验：4xyz == n(xy + xz + yz)。"""
    return 4 * x * y * z == n * (y * z + x * z + x * y)


def search(n: int):
    """难类精确搜索：返回一组解 (x, y, z)，找不到返回 None。"""
    hi = (3 * n) // 4
    for x in range(n // 4 + 1, hi + 1):
        p = 4 * x - n          # > 0 因为 x > n/4
        q = n * x
        g = gcd(p, q)
        a, b = p // g, q // g  # 1/y + 1/z = a/b（最简）
        lo = max(x, b // a + 1)  # y > b/a 且 y >= x
        hiy = (2 * b) // a       # a/b <= 2/y => y <= 2b/a
        for y in range(lo, hiy + 1):
            d = a * y - b
            if d > 0 and (b * y) % d == 0:
                z = b * y // d
                if z >= y and check(n, x, y, z):
                    return (x, y, z)
    return None


def main() -> int:
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    t0 = time.time()
    hard_total = hard_ok = 0
    first_certs = {}
    for n in range(2, N + 1):
        sol = witness(n)
        via = "explicit-class"
        if sol is None:
            hard_total += 1
            sol = search(n)
            via = "search"
            if sol is not None and n not in first_certs and hard_ok < 5:
                first_certs[n] = sol
        if sol is None or not check(n, *sol):
            print(f"FAIL: n={n} 未找到解或校验失败（sol={sol}）")
            return 1
        if via == "search":
            hard_ok += 1
    dt = time.time() - t0
    print(f"OK: 2 <= n <= {N} 全部通过（含 {hard_total} 个难类 n，全部找到并校验）")
    print(f"难类样例证书（n: (x,y,z)）: {first_certs}")
    print(f"耗时 {dt:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
