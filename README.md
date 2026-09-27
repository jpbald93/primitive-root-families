# Primitive-root families, formalised in Lean 4

Machine-checked proofs, in Lean 4 with Mathlib, of classical elementary results about when a fixed integer is a primitive root modulo a prime.

**Status:** work in progress. Part 1 (Chebyshev's base-10 family) and Part 2 (safe primes) are complete.

## Part 1: Chebyshev's base-10 family
**Theorem (Chebyshev).** If `p` and `q = 4p + 1` are both prime and `p ≡ 2 (mod 5)`, then `10` is a primitive root modulo `q`.

- **Source:** the statement is quoted in P. Moree, "Artin's primitive root conjecture: a survey", *Integers* 12 (2012), no. 6, 1305–1416, [doi:10.1515/integers-2012-0043](https://doi.org/10.1515/integers-2012-0043), §1 (arXiv:[math/0412262](https://arxiv.org/abs/math/0412262)); the same paper is listed on the journal's site as *Integers* 12A, A13. The result itself is classical.
- **Converse:** the same proof gives the converse. For primes `p` and `q = 4p + 1`, `10` is a primitive root modulo `q` **exactly when** `p ≡ 2 (mod 5)`. It is an elementary consequence of the argument. We did not find it stated in the literature, and we do not claim it as a new result. It is most likely folklore: the underlying criterion is a standard exercise (D. M. Burton, *Elementary Number Theory*, Problem 9.2.11).

Lean statements are in [`PrimitiveRootFamilies/Chebyshev.lean`](PrimitiveRootFamilies/Chebyshev.lean), namespace `PrimitiveRootFamilies`:

| Lean name | Statement |
|---|---|
| `isPrimitiveRoot_ten_of_mod_five_eq_two` | Chebyshev's theorem, as stated above (old name `ten_isPrimitiveRoot` kept as a deprecated alias) |
| `isPrimitiveRoot_ten_iff_mod_five_eq_two` | `IsPrimitiveRoot (10 : ZMod q) (q - 1) ↔ p % 5 = 2`, for primes `p` and `q = 4p + 1` |
| `isPrimitiveRoot_iff_of_eq_four_mul_add_one` | for primes `p` and `q = 4p + 1`, a nonzero `a` is a primitive root modulo `q` iff `a ^ (2p) ≠ 1` and `a ^ 4 ≠ 1` |
| `legendreSym_ten_of_eq_four_mul_add_one` | for primes `p` and `q = 4p + 1`, `(10 \| q) = -(q \| 5)` |

```lean
theorem isPrimitiveRoot_ten_of_mod_five_eq_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q = 4 * p + 1) (hp5 : p % 5 = 2) : IsPrimitiveRoot (10 : ZMod q) (q - 1)
```
`IsPrimitiveRoot (10 : ZMod q) (q - 1)` is Mathlib's definition: 10 has multiplicative order exactly `q − 1` modulo `q`. This is the standard meaning of "primitive root modulo q".

**Proof outline** (the file header gives the details):
- The criterion: since `q − 1 = 4p`, the prime-divisor test for the order reduces "primitive root" to `a^(2p) ≠ 1` and `a^4 ≠ 1`.
- The Legendre symbol: by Euler's criterion, `10^(2p) = (10 | q)`. By reciprocity and `q ≡ 5 (mod 8)`, `(10 | q) = −(q | 5)`, and this is `−1` exactly when `p ≡ 2 (mod 5)`.
- The fourth power: `10^4 ≠ 1`, because `q ∤ 9999 = 3² · 11 · 101`.

Both examples are checked in Lean: `p = 7`, `q = 29` (10 is a primitive root), and `p = 3`, `q = 13` (it is not).

## Part 2: safe primes
A *safe prime* is a prime `p = 2q + 1` with `q` also prime.

**Theorem (Ramesh–Makeshwari).** The least positive primitive root modulo a safe prime is prime.

- **Source:** V. P. Ramesh and M. Makeshwari, "Least primitive root of any safe prime is prime", *Amer. Math. Monthly* 129 (2022), no. 10, 971, [doi:10.1080/00029890.2022.2115816](https://doi.org/10.1080/00029890.2022.2115816).
- **Lean statements:** in [`PrimitiveRootFamilies/SafePrime.lean`](PrimitiveRootFamilies/SafePrime.lean), all with hypotheses `[Fact p.Prime] (hq : q.Prime) (hpq : p = 2 * q + 1)`, except `exists_isLeast_isPrimitiveRoot`, which needs only `[Fact p.Prime]`:

| Lean name | Statement |
|---|---|
| `exists_isLeast_isPrimitiveRoot_and_prime` | unconditional form: the least positive primitive root exists and is prime |
| `exists_isLeast_isPrimitiveRoot` | for every prime `p` (not only safe primes), a least positive primitive root exists |
| `prime_of_isLeast_isPrimitiveRoot` | if `g` is the least element of `{a : ℕ \| 0 < a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)}`, then `g` is prime |
| `isPrimitiveRoot_iff_of_eq_two_mul_add_one` | a nonzero `a` is a primitive root modulo `p` iff `a ^ q ≠ 1` and `a ^ 2 ≠ 1` |
| `isPrimitiveRoot_of_legendreSym_eq_neg_one` | every quadratic nonresidue `x` with `1 < x < p - 1` is a primitive root |
| `isPrimitiveRoot_two_of_mod_four_eq_one` | if moreover `q ≡ 1 (mod 4)`, then `2` is a primitive root (a classical corollary) |

"Least" is stated with Mathlib's `IsLeast`, so the theorem really is about the least positive primitive root. The proof also shows that this least root is below `p`, so it is not assumed. Existence of the least root is proved too (`exists_isLeast_isPrimitiveRoot`), so the theorem is not vacuous.

**Proof outline** (the file header gives the details):
- Since `p − 1 = 2q`, a primitive root is exactly a nonzero residue with `a^q ≠ 1` and `a^2 ≠ 1`. By Euler's criterion `a^q = (a | p)`, so every nonresidue other than `−1` is a primitive root.
- If the least primitive root `g` were composite, `g = mn`, then `(m | p)(n | p) = (g | p) = −1`. So one of the factors is a smaller nonresidue, and hence a smaller primitive root.
- This Legendre-symbol argument differs in form from the published note, which works with multiplicative orders and the quotient `a / m`.

**Checked in Lean:** `2` is a primitive root modulo the safe prime `11 = 2 · 5 + 1`.

## Verification
- `bash gate.sh` does the following, in order:
  - a heuristic source filter: the project's `.lean` files contain no `sorry`, `admit`, `native_decide`, `axiom` keyword, `#eval`, `run_cmd`, `initialize`, `IO` or `set_option`, and no syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, …) that could redefine `#print axioms`;
  - it builds the library;
  - the gate writes its own `#print axioms` check for each named theorem, rather than trusting a report printed by a file in the repo;
  - each of the ten named theorems (four in Part 1, six in Part 2), together with everything it depends on, uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Trust boundary:** the gate assumes the pinned Lean toolchain, Mathlib version and lake configuration are unmodified. It is not a sandbox or an integrity check for those, and it checks the named theorems only, not every declaration in the files.
- Output: `PASS (10 theorems, standard axioms only)`.
- The gate has been negative-tested. It fails, as it should, when any of these is added:
  - a `sorry`;
  - an axiom, including one whose keyword sits on a line of its own;
  - fake axiom reports printed with `#eval`, or produced by a `macro_rules` that redefines `#print axioms`;
  - an extra axiom hidden on a wrapped output line.
- `python3 code/check_family.py 200000` is an independent numerical cross-check. For all 1916 prime pairs `(p, 4p + 1)` with `p ≤ 200000`, it confirms that 10 is a primitive root modulo `4p + 1` exactly when `p ≡ 2 (mod 5)`: 628 pairs meet the congruence. As a control, it exhibits a failure when `p` is not prime (`p = 22`).

- `python3 code/check_safe_primes.py 1000000` is an independent numerical cross-check of Part 2:
  - for all 4324 safe primes `p ≤ 1000000`, the least primitive root is prime;
  - for the 2133 of them with `q ≡ 1 (mod 4)`, `2` is a primitive root;
  - for the 72 safe primes below 5000, brute-force order computations confirm that each of the 73514 nonresidues `x` with `1 < x < p − 1` is a primitive root.
  - As a control, the least primitive root of `p = 41`, which is not a safe prime, is `6`, a composite number.

## Build
```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh   # if Lean is not installed
lake exe cache get      # prebuilt Mathlib, pinned by lake-manifest.json
bash gate.sh
```
Toolchain: `leanprover/lean4:v4.33.1`. Mathlib is pinned in `lake-manifest.json`.

## AI assistance
This formalisation was prepared with the large-language-model assistants GPT-6 Astra and Claude Opus 5.5 (Anthropic), accessed through the Genspark platform. Every proof is checked by the Lean kernel.

## License
Apache 2.0.
