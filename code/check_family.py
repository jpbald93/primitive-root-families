#!/usr/bin/env python3
"""Numerical cross-check of the Chebyshev family (independent of the Lean proof).
For every prime p <= LIMIT with p % 5 == 2 and q = 4p+1 prime, check that
10 has multiplicative order q-1 modulo q, by brute-force order computation for small q
and the prime-divisor test for all q.
Also runs negative controls showing that each hypothesis is needed."""
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
def is_prim_root(a, q):  # prime-divisor test; q - 1 = 4p has prime factors 2, p
    n = q - 1; fs = {f for f in range(2, int(n ** 0.5) + 1) if n % f == 0 and S[f]}
    fs |= {n // f for f in range(1, int(n ** 0.5) + 1) if n % f == 0 and S[n // f]}
    return all(pow(a, n // f, q) != 1 for f in fs)
count = brute = 0
for p in range(2, LIMIT + 1):
    if S[p] and p % 5 == 2 and S[4 * p + 1]:
        q = 4 * p + 1; count += 1
        assert is_prim_root(10, q), (p, q)
        if q < 20000:
            assert order(10, q) == q - 1, (p, q); brute += 1
print(f"family members with p <= {LIMIT}: {count} (brute-force order check on {brute}); 10 is a primitive root for all")
# negative controls: drop one hypothesis at a time and show a failure exists
fails_mod5 = next(p for p in range(3, LIMIT) if S[p] and p % 5 != 2 and S[4*p+1] and not is_prim_root(10, 4*p+1))
print(f"control (p % 5 != 2): p={fails_mod5}, q={4*fails_mod5+1}: 10 is NOT a primitive root")
fails_prime = next(p for p in range(3, 2000) if not S[p] and p % 5 == 2 and S[4*p+1] and order(10, 4*p+1) != 4*p)
print(f"control (p not prime): p={fails_prime}, q={4*fails_prime+1}: 10 has order {order(10,4*fails_prime+1)}, not {4*fails_prime}")
