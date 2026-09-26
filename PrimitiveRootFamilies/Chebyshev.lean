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
Integers 12 (2012), no. 6, 1305–1416 (= Integers 12A, A13), doi:10.1515/integers-2012-0043 (arXiv:math/0412262), §1:
"if `q = 4p+1` is a prime with `p` a prime satisfying `p ≡ 2 (mod 5)`, then `10` is a
primitive root modulo `q`."

The same computation also gives the converse: when `p` and `q = 4p + 1` are prime, `10` is a
primitive root modulo `q` *only* if `p ≡ 2 (mod 5)`. This is an elementary consequence of the
proof below. We did not find it stated in the literature, and we do not claim it as a new
result. The criterion below is a standard exercise; compare D. M. Burton, *Elementary Number
Theory*, Problem 9.2.11 (every quadratic nonresidue of `q = 4p + 1` is a primitive root or has
order 4).

## Main results
* `isPrimitiveRoot_iff_of_eq_four_mul_add_one`: for primes `p` and `q = 4p + 1`, a nonzero
  residue `a` is a primitive root modulo `q` iff `a ^ (2p) ≠ 1` and `a ^ 4 ≠ 1`.
* `legendreSym_ten_of_eq_four_mul_add_one`: for primes `p` and `q = 4p + 1`,
  `(10 | q) = -(q | 5)`.
* `isPrimitiveRoot_ten_of_mod_five_eq_two`: Chebyshev's theorem.
* `isPrimitiveRoot_ten_iff_mod_five_eq_two`: Chebyshev's theorem together with its converse.

## Proof outline
The unit group of `ZMod q` has order `q - 1 = 4p`, whose prime divisors are `2` and `p`. By the
prime-divisor test (`orderOf_eq_of_pow_and_pow_div_prime`), `a ≠ 0` is a primitive root iff
`a ^ (2p) ≠ 1` and `a ^ 4 ≠ 1`.
* Since `p` is odd, `q ≡ 5 (mod 8)`, so `(2 | q) = -1`; by reciprocity `(5 | q) = (q | 5)`.
  So `(10 | q) = -(q | 5)`, and by Euler's criterion `10 ^ (2p) = (10 | q)`.
  Hence `10 ^ (2p) ≠ 1` iff `(q | 5) = 1` iff `q ≡ 1, 4 (mod 5)`. Here `q ≡ 1 (mod 5)` forces
  `p = 5` and `q = 21`, which is not prime; and `q ≡ 4 (mod 5)` iff `p ≡ 2 (mod 5)`.
* `10 ^ 4 ≠ 1` always holds here: otherwise `q ∣ 9999 = 3² · 11 · 101`, so `q ∈ {3, 11, 101}`.
  But `3` and `11` are not of the form `4p + 1`, and `101 = 4 · 25 + 1` with `25` not prime.
-/

namespace PrimitiveRootFamilies

/-- Local only: Mathlib deliberately provides no global `Fact (Nat.Prime 5)` instance. -/
local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- If `p` and `4p + 1` are both prime, then `p` is odd. -/
private lemma odd_of_eq_four_mul_add_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q = 4 * p + 1) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with rfl | h
  · subst hqp; exact absurd hq (by norm_num)
  · exact h

/-- `q ∤ 10⁴ - 1 = 9999` when `p` and `q = 4p + 1` are prime. -/
private lemma not_dvd_9999 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q = 4 * p + 1) :
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

private lemma ten_ne_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q = 4 * p + 1) :
    (10 : ZMod q) ≠ 0 := by
  intro h0
  have h : ((10 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by norm_num) h
  have := hp.two_le
  have := odd_of_eq_four_mul_add_one hp hq hqp
  omega

private lemma ten_pow_four_ne_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q = 4 * p + 1) : (10 : ZMod q) ^ 4 ≠ 1 := by
  intro h4
  have h : ((9999 : ℕ) : ZMod q) = 0 := by
    rw [Nat.cast_ofNat]; linear_combination h4
  rw [ZMod.natCast_eq_zero_iff] at h
  exact not_dvd_9999 hp hq hqp h

/-- `(4 | 5) = 1`, stated as `(2² | 5) = 1`. -/
private lemma legendreSym_five_four : legendreSym 5 ((2 : ℤ) ^ 2) = 1 :=
  legendreSym.sq_one' 5 (a := 2) (by decide)

/-- `(n | 5) = -1` when `n ≡ 2` or `3 (mod 5)`. -/
private lemma legendreSym_five_of_mod {n : ℕ} (hn : n % 5 = 2 ∨ n % 5 = 3) :
    legendreSym 5 n = -1 := by
  rw [legendreSym.mod 5 (n : ℤ), show ((5 : ℕ) : ℤ) = 5 by norm_num]
  rcases hn with h | h
  · rw [show (n : ℤ) % 5 = 2 by omega, legendreSym.at_two (by norm_num),
      ZMod.χ₈_nat_eq_if_mod_eight]
    norm_num
  · rw [show (n : ℤ) % 5 = 3 by omega]
    have hr := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := 3)
      (by norm_num) (by norm_num)
    have hr' : legendreSym 3 (5 : ℕ) = legendreSym 5 (3 : ℕ) := hr
    rw [show ((5 : ℕ) : ℤ) = 5 by norm_num, show ((3 : ℕ) : ℤ) = 3 by norm_num] at hr'
    rw [← hr', legendreSym.mod 3 5, show ((3 : ℕ) : ℤ) = 3 by norm_num,
      show (5 : ℤ) % 3 = 2 by norm_num, legendreSym.at_two (by norm_num),
      ZMod.χ₈_nat_eq_if_mod_eight]
    norm_num

/-- For primes `p` and `q = 4p + 1`, a nonzero residue `a` is a primitive root modulo `q` if and
only if `a ^ (2p) ≠ 1` and `a ^ 4 ≠ 1`. -/
theorem isPrimitiveRoot_iff_of_eq_four_mul_add_one {p q : ℕ} (hp : p.Prime) [Fact q.Prime]
    (hqp : q = 4 * p + 1) {a : ZMod q} (ha : a ≠ 0) :
    IsPrimitiveRoot a (q - 1) ↔ a ^ (2 * p) ≠ 1 ∧ a ^ 4 ≠ 1 := by
  have hq1 : q - 1 = 4 * p := by omega
  have h2 := hp.two_le
  constructor
  · intro h
    exact ⟨h.pow_ne_one_of_pos_of_lt (by omega) (by omega),
      h.pow_ne_one_of_pos_of_lt (by omega) (by omega)⟩
  · rintro ⟨h2p, h4⟩
    rw [IsPrimitiveRoot.iff_orderOf, hq1]
    apply orderOf_eq_of_pow_and_pow_div_prime (by omega)
    · rw [← hq1]; exact ZMod.pow_card_sub_one_eq_one ha
    · intro r hr hdvd
      rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
      · have hr2 : r = 2 := by
          have : r ∣ 2 * 2 := by simpa using h
          rcases (Nat.Prime.dvd_mul hr).mp this with h' | h' <;>
            exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h'
        subst hr2
        rwa [show 4 * p / 2 = 2 * p by omega]
      · rw [(Nat.prime_dvd_prime_iff_eq hr hp).mp h, Nat.mul_div_cancel _ hp.pos]
        exact h4

/-- For primes `p` and `q = 4p + 1`, `(10 | q) = -(q | 5)`. -/
theorem legendreSym_ten_of_eq_four_mul_add_one {p q : ℕ} (hp : p.Prime) [Fact q.Prime]
    [Fact (Nat.Prime 5)] (hqp : q = 4 * p + 1) : legendreSym q 10 = -legendreSym 5 q := by
  have hq : q.Prime := Fact.out
  have hodd := odd_of_eq_four_mul_add_one hp hq hqp
  have hq2 : q ≠ 2 := by omega
  have h2 : legendreSym q 2 = -1 := by
    rw [legendreSym.at_two hq2, ZMod.χ₈_nat_eq_if_mod_eight]
    simp [show q % 8 = 5 by omega, show q % 2 = 1 by omega]
  have h5 : legendreSym q 5 = legendreSym 5 q := by
    have hr := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := q)
      (by norm_num) hq2
    have hr' : legendreSym q (5 : ℕ) = legendreSym 5 (q : ℕ) := hr
    rw [show ((5 : ℕ) : ℤ) = 5 by norm_num] at hr'
    exact hr'
  rw [show (10 : ℤ) = 2 * 5 by norm_num, legendreSym.mul, h2, h5, neg_one_mul]

/-- **Chebyshev's theorem with its converse.** If `p` and `q = 4p + 1` are prime, then `10` is
a primitive root modulo `q` if and only if `p ≡ 2 (mod 5)`. -/
theorem isPrimitiveRoot_ten_iff_mod_five_eq_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q = 4 * p + 1) : IsPrimitiveRoot (10 : ZMod q) (q - 1) ↔ p % 5 = 2 := by
  have := Fact.mk hq
  have hodd := odd_of_eq_four_mul_add_one hp hq hqp
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hne0 := ten_ne_zero hp hq hqp
  have hL := legendreSym_ten_of_eq_four_mul_add_one hp hqp
  -- Euler's criterion: `10 ^ (q / 2) = (10 | q)`, and `q / 2 = 2p`.
  have heuler : ((legendreSym q 10 : ℤ) : ZMod q) = (10 : ZMod q) ^ (2 * p) := by
    have e := legendreSym.eq_pow q (10 : ℤ)
    rw [show q / 2 = 2 * p by omega] at e
    simpa using e
  constructor
  · intro h
    have h2p : (10 : ZMod q) ^ (2 * p) ≠ 1 := h.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    have hL10 : legendreSym q 10 = -1 := by
      rcases legendreSym.eq_one_or_neg_one q (a := 10) (by exact_mod_cast hne0) with h1 | h1
      · exfalso; apply h2p; rw [← heuler, h1]; simp
      · exact h1
    have h5 : legendreSym 5 q = 1 := by rw [hL] at hL10; linarith
    have hq5 : q % 5 = 4 := by
      rcases (by omega : q % 5 = 0 ∨ q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4)
        with h0 | h0 | h0 | h0 | h0
      · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp (Nat.dvd_of_mod_eq_zero h0)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (by omega : 5 ∣ p)
        subst this; subst hqp; exact absurd hq (by norm_num)
      · rw [legendreSym_five_of_mod (Or.inl h0)] at h5; norm_num at h5
      · rw [legendreSym_five_of_mod (Or.inr h0)] at h5; norm_num at h5
      · exact h0
    omega
  · intro hp5
    have hq5 : ((q : ℤ) % 5) = 4 := by omega
    have h5 : legendreSym 5 q = 1 := by
      rw [legendreSym.mod 5 (q : ℤ), show ((5 : ℕ) : ℤ) = 5 by norm_num, hq5,
        show (4 : ℤ) = 2 ^ 2 by norm_num]
      exact legendreSym_five_four
    have : Fact (2 < q) := ⟨by omega⟩
    rw [isPrimitiveRoot_iff_of_eq_four_mul_add_one hp hqp hne0]
    refine ⟨?_, ten_pow_four_ne_one hp hq hqp⟩
    rw [← heuler, hL, h5]
    simpa using (ZMod.neg_one_ne_one (n := q))

/-- **Chebyshev.** If `p` and `q = 4p + 1` are prime and `p ≡ 2 (mod 5)`, then `10` is a
primitive root modulo `q`. -/
theorem isPrimitiveRoot_ten_of_mod_five_eq_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q = 4 * p + 1) (hp5 : p % 5 = 2) : IsPrimitiveRoot (10 : ZMod q) (q - 1) :=
  (isPrimitiveRoot_ten_iff_mod_five_eq_two hp hq hqp).mpr hp5

@[deprecated isPrimitiveRoot_ten_of_mod_five_eq_two (since := "2026-09-25")]
alias ten_isPrimitiveRoot := isPrimitiveRoot_ten_of_mod_five_eq_two

/-- The smallest instance: `p = 7`, `q = 29`. -/
example : IsPrimitiveRoot (10 : ZMod 29) 28 :=
  isPrimitiveRoot_ten_of_mod_five_eq_two (p := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The converse in action: `p = 3`, `q = 13`, and `3 ≢ 2 (mod 5)`, so `10` is not a primitive
root modulo `13`. -/
example : ¬ IsPrimitiveRoot (10 : ZMod 13) 12 := fun h =>
  absurd ((isPrimitiveRoot_ten_iff_mod_five_eq_two (p := 3) (q := 13) (by norm_num)
    (by norm_num) (by norm_num)).mp h) (by norm_num)

end PrimitiveRootFamilies
