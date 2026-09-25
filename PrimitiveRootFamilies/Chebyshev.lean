/-
Copyright (c) 2026 Josh Bald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Bald
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Chebyshev's base-10 primitive-root family

**Theorem (Chebyshev).** Let `p` and `q = 4p + 1` both be prime, with `p ≡ 2 (mod 5)`.
Then `10` is a primitive root modulo `q`.

The statement is quoted in P. Moree, *Artin's primitive root conjecture — a survey*,
Integers 12 (2012), no. 6, 1305–1416, doi:10.1515/integers-2012-0043 (arXiv:math/0412262), §1: "if `q = 4p+1` is a prime with `p` a
prime satisfying `p ≡ 2 (mod 5)`, then `10` is a primitive root modulo `q`."

## Proof outline
The unit group of `ZMod q` has order `q - 1 = 4p`, whose prime divisors are `2` and `p`.
By the prime-divisor test (`orderOf_eq_of_pow_and_pow_div_prime`) it suffices that
* `10 ^ (2p) ≠ 1`. By Euler's criterion, `10 ^ (2p) = 10 ^ (q / 2)` is the Legendre symbol
  `(10 | q) = (2 | q) (5 | q)`. Here `q ≡ 5 (mod 8)`, so `(2 | q) = -1`. By reciprocity
  `(5 | q) = (q | 5) = (4 | 5) = 1`, since `q ≡ 4 (mod 5)`. So `10 ^ (2p) = -1 ≠ 1`.
* `10 ^ 4 ≠ 1`. Otherwise `q ∣ 9999 = 3² · 11 · 101`, which forces `q ∈ {3, 11, 101}`.
  But `3` and `11` are not of the form `4p + 1`, and `101 = 4 · 25 + 1` with `25` not prime.
-/

namespace PrimitiveRootFamilies

/-- The residue facts about `p` and `q` used in the proof. -/
lemma chebyshev_residues {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q = 4 * p + 1)
    (hp5 : p % 5 = 2) : p % 2 = 1 ∧ q % 8 = 5 ∧ q % 5 = 4 ∧ 29 ≤ q := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · subst hqp; exact absurd hq (by norm_num)
  · have h7 : 7 ≤ p := by
      rcases Nat.lt_or_ge p 7 with h | h
      · interval_cases p <;> simp_all
      · exact h
    refine ⟨hodd, ?_, ?_, ?_⟩ <;> omega

/-- `q ∤ 10⁴ - 1 = 9999` under the hypotheses of the theorem. -/
lemma not_dvd_9999 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q = 4 * p + 1) :
    ¬ q ∣ 9999 := by
  intro h
  have h3 : (3 : ℕ).Prime := by norm_num
  have h11 : (11 : ℕ).Prime := by norm_num
  have h101 : (101 : ℕ).Prime := by norm_num
  have e : (9999 : ℕ) = 3 * (3 * (11 * 101)) := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rw [Nat.prime_dvd_prime_iff_eq hq h3] at h; omega
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rw [Nat.prime_dvd_prime_iff_eq hq h3] at h; omega
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rw [Nat.prime_dvd_prime_iff_eq hq h11] at h; omega
  · rw [Nat.prime_dvd_prime_iff_eq hq h101] at h
    have : p = 25 := by omega
    subst this; exact absurd hp (by norm_num)

/-- Local only: Mathlib deliberately provides no global `Fact (Nat.Prime 5)` instance. -/
local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `(4 | 5) = 1`, stated as `(2² | 5) = 1`. -/
lemma legendreSym_five_four_eq_one : legendreSym 5 ((2 : ℤ) ^ 2) = 1 :=
  legendreSym.sq_one' 5 (a := 2) (by decide)

/-- **Chebyshev.** If `p` and `q = 4p + 1` are prime and `p ≡ 2 (mod 5)`, then `10` is a
primitive root modulo `q`. -/
theorem ten_isPrimitiveRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q = 4 * p + 1)
    (hp5 : p % 5 = 2) : IsPrimitiveRoot (10 : ZMod q) (q - 1) := by
  have := Fact.mk hq
  obtain ⟨hpodd, hq8, hq5, hq29⟩ := chebyshev_residues hp hq hqp hp5
  have hq2 : q ≠ 2 := by omega
  have : Fact (2 < q) := ⟨by omega⟩
  -- (2 | q) = -1 since q ≡ 5 (mod 8)
  have h2 : legendreSym q 2 = -1 := by
    rw [legendreSym.at_two hq2, ZMod.χ₈_nat_eq_if_mod_eight]
    simp [hq8, show q % 2 = 1 by omega]
  -- (5 | q) = (q | 5) = (4 | 5) = 1
  have h5 : legendreSym q 5 = 1 := by
    have hr := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := q) (by norm_num) hq2
    have hr' : legendreSym q (5 : ℕ) = legendreSym 5 (q : ℕ) := hr
    have hmod : ((q : ℤ) % 5) = 4 := by omega
    rw [show ((5 : ℕ) : ℤ) = 5 by norm_num] at hr'
    rw [hr', legendreSym.mod 5 (q : ℤ), show ((5 : ℕ) : ℤ) = 5 by norm_num, hmod,
      show (4 : ℤ) = 2 ^ 2 by norm_num]
    exact legendreSym_five_four_eq_one
  have h10 : legendreSym q 10 = -1 := by
    rw [show (10 : ℤ) = 2 * 5 by norm_num, legendreSym.mul, h2, h5]; norm_num
  -- Euler's criterion: 10 ^ (q / 2) = (10 | q) = -1
  have hhalf : (10 : ZMod q) ^ (2 * p) = -1 := by
    have e := legendreSym.eq_pow q (10 : ℤ)
    rw [h10, show q / 2 = 2 * p by omega] at e
    simpa using e.symm
  have hne0 : (10 : ZMod q) ≠ 0 := by
    intro h0
    have : ((10 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this; omega
  have hfour : (10 : ZMod q) ^ 4 ≠ 1 := by
    intro h4
    have : ((9999 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_ofNat]; linear_combination h4
    rw [ZMod.natCast_eq_zero_iff] at this
    exact not_dvd_9999 hp hq hqp this
  rw [IsPrimitiveRoot.iff_orderOf, show q - 1 = 4 * p by omega]
  apply orderOf_eq_of_pow_and_pow_div_prime (by have := hp.pos; omega)
  · rw [← show q - 1 = 4 * p by omega]; exact ZMod.pow_card_sub_one_eq_one hne0
  · intro r hr hdvd
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
    · -- r ∣ 4, so r = 2
      have hr2 : r = 2 := by
        have : r ∣ 2 * 2 := by simpa using h
        rcases (Nat.Prime.dvd_mul hr).mp this with h' | h' <;>
          exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h'
      subst hr2
      rw [show 4 * p / 2 = 2 * p by omega, hhalf]
      exact ZMod.neg_one_ne_one
    · -- r ∣ p, so r = p
      rw [(Nat.prime_dvd_prime_iff_eq hr hp).mp h, Nat.mul_div_cancel _ hp.pos]
      exact hfour

/-- The smallest instance: `p = 7`, `q = 29`. -/
example : IsPrimitiveRoot (10 : ZMod 29) 28 :=
  ten_isPrimitiveRoot (p := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end PrimitiveRootFamilies
