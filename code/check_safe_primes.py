#!/usr/bin/env python3
"""Numerical cross-check of the safe-prime results, independent of the Lean proofs.

For every safe prime p = 2q + 1 <= LIMIT:
  * the least positive primitive root g is prime (Ramesh-Makeshwari);
  * (for p < 5000) every quadratic nonresidue x with 1 < x < p - 1 is a primitive root;
  * if q % 4 == 1, then 2 is a primitive root.
Primitive-root status uses the prime-divisor test (p - 1 = 2q). It is cross-checked against a
brute-force order computation for p < 5000. Control: for primes that are not safe, the least
primitive root can be composite."""
import sys
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return s
S = sieve(max(LIMIT, 100000))  # the control search below looks at p < 100000
def order(a, p):
    x, k = a % p, 1
    while x != 1:
        x = x * a % p; k += 1
    return k
def is_pr_safe(a, p, q):
    return a % p != 0 and pow(a, q, p) != 1 and pow(a, 2, p) != 1
safe = brute = nonres_checked = two_cases = 0
for q in range(2, (LIMIT - 1) // 2 + 1):
    p = 2 * q + 1
    if not (S[q] and S[p]): continue
    safe += 1
    g = next(a for a in range(1, p) if is_pr_safe(a, p, q))
    assert S[g], ("least primitive root not prime", p, g)
    if p < 5000:
        assert order(g, p) == p - 1 and all(order(a, p) != p - 1 for a in range(1, g)), p; brute += 1
        for x in range(2, p - 1):
            if pow(x, q, p) == p - 1:
                assert is_pr_safe(x, p, q) and order(x, p) == p - 1, (p, x); nonres_checked += 1
    if q % 4 == 1:
        assert is_pr_safe(2, p, q), ("2 not a primitive root", p); two_cases += 1
print(f"safe primes p <= {LIMIT}: {safe}; least primitive root is prime for all")
print(f"brute-force check on {brute} safe primes < 5000 ({nonres_checked} nonresidues x with 1 < x < p-1, all primitive roots)")
print(f"q % 4 == 1: {two_cases} safe primes, 2 is a primitive root for all")
def least_pr(p):
    fs = [f for f in range(2, p) if (p - 1) % f == 0 and S[f]]
    return next(a for a in range(2, p) if all(pow(a, (p - 1) // f, p) != 1 for f in fs))
c = next(p for p in range(3, 100000) if S[p] and not S[(p - 1) // 2] and not S[least_pr(p)])
print(f"control (not a safe prime): p={c}, least primitive root {least_pr(c)} is composite")
