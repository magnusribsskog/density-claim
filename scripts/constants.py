#!/usr/bin/env python3
"""Witnesses for the numerical constants of §4 of the note.

These check numbers. They do not prove Theorem A, Lemma 1 or Lemma 4, whose
proofs are on the page and are meant to be read. Integer and rational
arithmetic wherever the claim is exact; 60-digit decimals where it is real.
Python 3.8+, standard library only:  python3 scripts/constants.py
"""
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 60
ok = True

def check(label, cond, shown):
    global ok
    ok &= bool(cond)
    print(f"{'PASS' if cond else 'FAIL'}  {label}: {shown}")

# a_0 = 1, a_1 = 15, a_{n+1} = 14 a_n + 14 a_{n-1}   (exact integers)
N = 10_000
a = [1, 15]
while len(a) <= N:
    a.append(14 * a[-1] + 14 * a[-2])

# The recurrence is the series of A(z) = (1+z)/(1-14z-14z^2):
# (1 - 14z - 14z^2) * sum a_n z^n = 1 + z, coefficient by coefficient.
coef = [a[0], a[1] - 14 * a[0]] + [a[n] - 14 * a[n-1] - 14 * a[n-2] for n in range(2, 50)]
check("series of A(z) has the recurrence's coefficients", coef == [1, 1] + [0] * 48, "1, 1, 0, 0, ... (exact)")

z = Fraction(1, 15)
A = (1 + z) / (1 - 14 * z - 14 * z * z)
check("A(1/15) = 240", A == 240, f"{A} (exact rational)")

lam = 7 + Decimal(63).sqrt()
check("lambda = 7 + sqrt 63 solves x^2 = 14x + 14", abs(lam * lam - 14 * lam - 14) < Decimal(10) ** -50,
      f"residual {lam*lam - 14*lam - 14:.1e}")
check("lambda = 14.937253933...", str(lam).startswith("14.937253933"), f"{str(lam)[:22]}...")
check("lambda / 15 ~ 0.9958169", str(lam / 15).startswith("0.9958169"), f"{str(lam / 15)[:14]}...")

log15 = lambda d: d.ln() / Decimal(15).ln()
k = 1 / (1 - log15(lam))
check("1/(1 - log_15 lambda) ~ 646.028", round(k, 3) == Decimal("646.028"), f"{k:.6f}")

# Leading coefficient C in a_n ~ C lambda^n, from the closed form of the recurrence.
mu = 7 - Decimal(63).sqrt()
C = (15 - mu) / (lam - mu)
check("closed form C lambda^n + D mu^n reproduces a_n", all(
      abs(C * lam ** n + (1 - C) * mu ** n - a[n]) < Decimal("0.5") for n in range(40)), "n = 0..39")
check("leading coefficient ~ 1.00395", str(C).startswith("1.00395"), f"{str(C)[:12]}...")

check("a_1939 >= 15^1936", a[1939] >= 15 ** 1936, "exact integer comparison")
check("1939 > 3 x 646.03", 1939 > 3 * 646.03, f"3 x 646.03 = {3 * 646.03:.2f}")
last = max(n for n in range(3, N + 1) if a[n] >= 15 ** (n - 3))
print(f"INFO  largest n <= {N} with a_n >= 15^(n-3): {last}   (not claimed in the note; reported)")

# §4: ln(15^n / a_n) ~ 41.91 nats at n = 10 000, the density of a_n among all
# 15^n strings; and, relative to 15^(n-3), 33.79 nats.
nats = N * Decimal(15).ln() - Decimal(a[N]).ln()
check("ln(15^n / a_n) at n = 10000 ~ 41.91 nats", round(nats, 2) == Decimal("41.91"), f"{nats:.4f} nats = 10^{nats / Decimal(10).ln():.2f}")
alt = (N - 3) * Decimal(15).ln() - Decimal(a[N]).ln()
print(f"INFO  against 15^(n-3) instead: {alt:.4f} nats   (the note states both since 29 October 2026)")

l6, f6 = lam ** -6, Decimal(15) ** -6
check("lambda^-6 ~ 9.0028e-8", f"{l6:.4e}" == "9.0028e-8", f"{l6:.6e}")
check("15^-6 ~ 8.7791e-8", f"{f6:.4e}" == "8.7791e-8", f"{f6:.6e}")

print("\nALL PASS" if ok else "\nSOME CHECKS FAILED")
raise SystemExit(0 if ok else 1)
