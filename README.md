# Primitive-root families, formalised in Lean 4

Machine-checked proofs, in Lean 4 with Mathlib, of classical elementary results about when a fixed integer is a primitive root modulo a prime.

**Status:** work in progress. Part 1 (Chebyshev's base-10 family) is complete. Part 2, the safe-prime results, is planned.

## Part 1: Chebyshev's base-10 family
**Theorem (Chebyshev).** If `p` and `q = 4p + 1` are both prime and `p ≡ 2 (mod 5)`, then `10` is a primitive root modulo `q`.

- **Source:** the statement is quoted in P. Moree, "Artin's primitive root conjecture: a survey", *Integers* 12 (2012), no. 6, 1305–1416, [doi:10.1515/integers-2012-0043](https://doi.org/10.1515/integers-2012-0043), §1 (arXiv:[math/0412262](https://arxiv.org/abs/math/0412262)); the same paper is listed on the journal's site as *Integers* 12A, A13. The result itself is classical.
- **Converse:** the same proof gives the converse. For primes `p` and `q = 4p + 1`, `10` is a primitive root modulo `q` **exactly when** `p ≡ 2 (mod 5)`. It is an elementary consequence of the argument. We did not find it stated in the literature, and we do not claim it as a new result. It is most likely folklore: the underlying criterion is a standard exercise (Burton, *Elementary Number Theory*, Problem 9.2.11).

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

## Verification
- `bash gate.sh` builds the library and then checks that:
  - the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword, `#eval`, `run_cmd`, `initialize`, `IO` or `set_option`, and no syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, …) that could redefine `#print axioms`;
  - the gate writes its own `#print axioms` check for each named theorem, rather than trusting a report printed by a file in the repo;
  - every theorem depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Output: `PASS (4 theorems, standard axioms only)`.
- The gate has been negative-tested. It fails, as it should, when any of these is added:
  - a `sorry`;
  - an axiom, including one whose keyword sits on a line of its own;
  - fake axiom reports printed with `#eval`, or produced by a `macro_rules` that redefines `#print axioms`;
  - an extra axiom hidden on a wrapped output line.
- `python3 code/check_family.py 200000` is an independent numerical cross-check. For all 1916 prime pairs `(p, 4p + 1)` with `p ≤ 200000`, it confirms that 10 is a primitive root modulo `4p + 1` exactly when `p ≡ 2 (mod 5)`: 628 pairs meet the congruence. As a control, it exhibits a failure when `p` is not prime (`p = 22`).

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
