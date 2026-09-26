#!/usr/bin/env python3
"""Numerical cross-check of the Chebyshev family and its converse, independent of the Lean proof.

For every prime p <= LIMIT with q = 4p+1 prime, compute whether 10 is a primitive root mod q.
Check that this happens exactly when p % 5 == 2. (p = 2 never occurs, since q = 9 is not prime.) Uses the prime-divisor test for all q, and a brute-force order
computation for q < 20000. Also runs a control: when p is not prime, the conclusion can fail."""
import sys
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return s
S = sieve(4 * LIMIT + 1)
def order(a, q):
    x, k = a % q, 1
    while x != 1:
        x = x * a % q; k += 1
    return k
def is_prim_root(a, q):
    n = q - 1
    fs = {f for f in range(2, n + 1) if n % f == 0 and S[f]} if n < 100 else \
         {f for f in (2, n // 4) if S[f] and n % f == 0}   # q - 1 = 4p: prime divisors 2 and p
    return all(pow(a, n // f, q) != 1 for f in fs)
pairs = members = brute = 0
for p in range(2, LIMIT + 1):
    if S[p] and S[4 * p + 1]:
        q = 4 * p + 1; pairs += 1
        pr = is_prim_root(10, q)
        if q < 20000:
            assert pr == (order(10, q) == q - 1), (p, q); brute += 1
        assert pr == (p % 5 == 2), ("iff fails", p, q)
        members += pr
print(f"prime pairs (p, 4p+1) with p <= {LIMIT}: {pairs}; brute-force order check on {brute}")
print(f"10 is a primitive root mod 4p+1 exactly when p % 5 == 2: holds for all {pairs} pairs ({members} with p % 5 == 2)")
fails_prime = next(p for p in range(3, 2000) if not S[p] and p % 5 == 2 and S[4*p+1] and order(10, 4*p+1) != 4*p)
print(f"control (p not prime): p={fails_prime}, q={4*fails_prime+1}: 10 has order {order(10,4*fails_prime+1)}, not {4*fails_prime}")
