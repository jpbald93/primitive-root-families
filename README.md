# Primitive-root families, formalised in Lean 4

Machine-checked proofs, in Lean 4 with Mathlib, of classical elementary results about when a fixed integer is a primitive root modulo a prime.

**Status:** work in progress. Part 1 (Chebyshev's base-10 family) is complete. Part 2, the safe-prime results, is planned.

## Part 1: Chebyshev's base-10 family
**Theorem (Chebyshev).** If `p` and `q = 4p + 1` are both prime and `p ≡ 2 (mod 5)`, then `10` is a primitive root modulo `q`.

- **Source:** the statement is quoted in P. Moree, "Artin's primitive root conjecture: a survey", *Integers* 12 (2012), no. 6, 1305–1416, [doi:10.1515/integers-2012-0043](https://doi.org/10.1515/integers-2012-0043), §1 (arXiv:[math/0412262](https://arxiv.org/abs/math/0412262)). The result itself is classical.
- **Lean statement:** `PrimitiveRootFamilies.ten_isPrimitiveRoot` in [`PrimitiveRootFamilies/Chebyshev.lean`](PrimitiveRootFamilies/Chebyshev.lean):
  ```lean
  theorem ten_isPrimitiveRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q = 4 * p + 1)
      (hp5 : p % 5 = 2) : IsPrimitiveRoot (10 : ZMod q) (q - 1)
  ```
  `IsPrimitiveRoot (10 : ZMod q) (q - 1)` is Mathlib's definition: 10 has multiplicative order exactly `q − 1` modulo `q`. This is the standard meaning of "primitive root modulo q".
- **Proof outline:** the file's header gives the full outline.
  - Euler's criterion and quadratic reciprocity give `(10 | q) = (2 | q)(5 | q) = (−1)(1) = −1`, so `10^(2p) = −1`.
  - `10^4 ≠ 1`, because `q ∤ 9999 = 3² · 11 · 101`.
  - The prime-divisor test for the order finishes the proof.
- **Smallest instance, checked in Lean:** `p = 7`, `q = 29`.

## Verification
- `bash gate.sh` builds the library and then checks that:
  - the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword, `#eval`, `run_cmd`, `initialize`, `IO` or `debug.` option;
  - the gate generates its own `#print axioms` report for each named theorem, so no file in the repo can fake the report;
  - every theorem depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Output: `PASS (4 theorems, standard axioms only)`.
- The gate has been negative-tested. It fails, as it should, when any of these is added:
  - a `sorry`;
  - an axiom, including one whose keyword sits on a line of its own;
  - fake axiom reports printed with `#eval`;
  - an extra axiom hidden on a wrapped output line.
- Changing the hypothesis to the false `p % 5 = 3` breaks the proof.
- `python3 code/check_family.py 200000` is an independent numerical cross-check. It confirms that 10 is a primitive root for all 628 family members with `p ≤ 200000`. As controls, it exhibits failures when the congruence `p ≡ 2 (mod 5)` is dropped (`p = 3`) and when `p` is not prime (`p = 22`).

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
