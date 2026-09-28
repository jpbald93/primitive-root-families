#!/usr/bin/env python3
"""Numerical cross-check of General.lean, independent of the Lean proofs (uses sympy).

For every prime p <= LIMIT of the form p = 2^k * l + 1 with l an odd prime and k >= 1:
  * (criterion) for every a in a fixed sample of small bases with p not dividing a,
    a is a primitive root mod p  <=>  (a | p) = -1 and a^(2^k) != 1 (mod p);
    primitive-root status comes from sympy.is_primitive_root, the Legendre symbol from
    sympy.legendre_symbol.
  * p = 4l + 1:  2 is a primitive root.
  * p = 8l + 1:  3 is a primitive root, except exactly for l = 5 (p = 41).
  * p = 16l + 1: 3 is a primitive root.
Brute-force order computation cross-checks sympy for p < 3000."""
import sys
from sympy import isprime, is_primitive_root, legendre_symbol, n_order
from sympy import sieve as sp_sieve

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
BASES = [2, 3, 5, 6, 7, 10, 11, 12, -1, -2, -3]

def order(a, p):
    x, k = a % p, 1
    while x != 1:
        x = x * a % p; k += 1
    return k

crit_primes = crit_cases = crit_mismatch = brute = 0
fam = {4: [0, 0, []], 8: [0, 0, []], 16: [0, 0, []]}  # cases, mismatches, exceptions
for p in sp_sieve.primerange(3, LIMIT + 1):
    m, k = p - 1, 0
    while m % 2 == 0:
        m //= 2; k += 1
    l = m
    if l == 1 or not isprime(l):
        continue
    crit_primes += 1
    for a in BASES:
        if a % p == 0:
            continue
        pr = is_primitive_root(a % p, p)
        if p < 3000:
            assert pr == (order(a, p) == p - 1), (p, a); brute += 1
        rhs = legendre_symbol(a % p, p) == -1 and pow(a, 2 ** k, p) != 1
        crit_cases += 1
        if pr != rhs:
            crit_mismatch += 1
    for c, a in ((4, 2), (8, 3), (16, 3)):
        if p == c * l + 1:
            pr = is_primitive_root(a, p)
            fam[c][0] += 1
            if not pr:
                fam[c][2].append((p, l, n_order(a, p)))
                if not (c == 8 and l == 5):
                    fam[c][1] += 1
# The families with l = 2 are outside the criterion (l odd); handle them directly.
for c, a in ((4, 2), (8, 3), (16, 3)):
    p = 2 * c + 1
    if isprime(p) and p <= LIMIT:
        fam[c][0] += 1
        if not is_primitive_root(a, p):
            fam[c][1] += 1; fam[c][2].append((p, 2, n_order(a, p)))

print(f"criterion: {crit_primes} primes p = 2^k l + 1 <= {LIMIT} (l odd prime), "
      f"{crit_cases} (p, a) cases, {crit_mismatch} mismatches "
      f"(brute-force order check on {brute} cases with p < 3000)")
print(f"p = 4l + 1:  {fam[4][0]} primes, 2 is a primitive root for all; {fam[4][1]} mismatches")
print(f"p = 8l + 1:  {fam[8][0]} primes, {fam[8][1]} mismatches; "
      f"exceptions (p, l, order of 3): {fam[8][2]}")
print(f"p = 16l + 1: {fam[16][0]} primes, 3 is a primitive root for all; {fam[16][1]} mismatches")
assert crit_mismatch == 0 and fam[4][1] == fam[8][1] == fam[16][1] == 0
assert fam[4][2] == [] and fam[16][2] == [] and fam[8][2] == [(41, 5, 8)]
print("control: the only failure of 3 in the 8l + 1 family is p = 41 (l = 5), where 3 has order 8")
