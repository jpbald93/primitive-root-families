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
# Primitive roots modulo primes of the form `2ᵏ l + 1`

Let `l` be an odd prime, `k ≥ 1`, and suppose `p = 2ᵏ l + 1` is prime. Then `p - 1 = 2ᵏ l` has
exactly two prime divisors, `2` and `l`, and a nonzero residue `a` is a primitive root modulo `p`
if and only if `a` is a quadratic nonresidue and `a ^ (2ᵏ) ≢ 1 (mod p)`. The cases `k = 1`
(safe primes) and `k = 2` (the criterion behind Chebyshev's base-10 family) are treated in
`SafePrime.lean` and `Chebyshev.lean`; the bridge theorems at the end restate them as instances.

The criterion yields classical families of primitive roots; compare D. M. Burton, *Elementary
Number Theory*, §9.2, and P. Moree, *Artin's primitive root conjecture — a survey*, Integers 12
(2012), §1. These are standard exercises and we do not claim them as new results.

## Main results
* `isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one`: the criterion above.
* `isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd`: the sufficient direction, with the
  power condition stated as a divisibility over `ℤ`.
* `isPrimitiveRoot_two_of_eq_four_mul_add_one`: if `l` and `p = 4l + 1` are prime, then `2` is a
  primitive root modulo `p`.
* `isPrimitiveRoot_three_of_eq_eight_mul_add_one`: if `l` and `p = 8l + 1` are prime and
  `l ≠ 5`, then `3` is a primitive root modulo `p`. The exception is real: `3` has order `8`
  modulo `41 = 8 · 5 + 1`.
* `isPrimitiveRoot_three_of_eq_sixteen_mul_add_one`: if `l` and `p = 16l + 1` are prime, then
  `3` is a primitive root modulo `p`.
* `isPrimitiveRoot_iff_of_eq_two_mul_add_one'`, `isPrimitiveRoot_iff_of_eq_four_mul_add_one'`:
  the cases `k = 1` and `k = 2` of the criterion.

## Proof outline
By the prime-divisor test (`orderOf_eq_of_pow_and_pow_div_prime`), `a ≠ 0` is a primitive root
iff `a ^ ((p - 1) / 2) ≠ 1` and `a ^ ((p - 1) / l) ≠ 1`. Here `(p - 1) / l = 2ᵏ`, and by Euler's
criterion `a ^ ((p - 1) / 2) = (a | p)`, which is `≠ 1` iff `(a | p) = -1`.
* `a = 2`, `p = 4l + 1`: `l` is odd (`l = 2` gives `9`), so `p ≡ 5 (mod 8)` and `(2 | p) = -1`.
  If `2⁴ ≡ 1` then `p ∣ 15`, impossible for `p ≥ 13`.
* `a = 3`, `p = 8l + 1`: `p ≡ 1 (mod 4)`, so `(3 | p) = (p | 3)` by reciprocity. Now
  `p ≡ 2l + 1 (mod 3)`; `l ≡ 1` gives `3 ∣ p`, and `l = 3` gives `25`, so `p ≡ 2 (mod 3)` and
  `(p | 3) = -1`. If `3⁸ ≡ 1` then `p ∣ 6560 = 2⁵ · 5 · 41`, so `p = 41` and `l = 5`. The case
  `l = 2` (`p = 17`) is outside the criterion and is checked directly.
* `a = 3`, `p = 16l + 1`: `p ≡ l + 1 (mod 3)`; `l ≡ 2` gives `3 ∣ p`, `l = 3` gives `49`, so
  `(3 | p) = -1` as before. If `3¹⁶ ≡ 1` then `p ∣ 2⁶ · 5 · 17 · 41 · 193`, and none of `5`, `17`,
  `41`, `193` has the form `16l + 1` with `l` prime.
-/

namespace PrimitiveRootFamilies

/-- An odd prime dividing `2 ^ n * m` divides `m`. -/
private lemma dvd_of_dvd_two_pow_mul {p n m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ 2 ^ n * m) : p ∣ m := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
  · exact h

private lemma intCast_ne_zero_of_lt' {p x : ℕ} (hx0 : 0 < x) (hxp : x < p) :
    ((x : ℤ) : ZMod p) ≠ 0 := by
  rw [Int.cast_natCast]
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd hx0 h) (by omega)

/-- **Criterion.** Let `l` be an odd prime, `k ≥ 1` and `p = 2ᵏ l + 1` prime. A nonzero residue
`a` is a primitive root modulo `p` if and only if `(a | p) = -1` and `a ^ (2ᵏ) ≠ 1`. -/
theorem isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one {p l k : ℕ} [Fact p.Prime] (hl : l.Prime)
    (hl2 : l ≠ 2) (hk : 1 ≤ k) (hpl : p = 2 ^ k * l + 1) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    IsPrimitiveRoot (a : ZMod p) (p - 1) ↔
      legendreSym p a = -1 ∧ (a : ZMod p) ^ (2 ^ k) ≠ 1 := by
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hc1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hkc : 2 ^ (m + 1) * l = 2 * (2 ^ m * l) := by rw [pow_succ]; ring
  have hcl : l ≤ 2 ^ m * l := Nat.le_mul_of_pos_left l hc1
  have hkl : 2 ^ (m + 1) < 2 ^ (m + 1) * l := by
    have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    nlinarith
  have hp1 : p - 1 = 2 ^ (m + 1) * l := by omega
  have heuler : (a : ZMod p) ^ (2 ^ m * l) = ((legendreSym p a : ℤ) : ZMod p) := by
    rw [legendreSym.eq_pow, show p / 2 = 2 ^ m * l by omega]
  have : Fact (2 < p) := ⟨by omega⟩
  have hne : (-1 : ZMod p) ≠ 1 := ZMod.neg_one_ne_one
  constructor
  · intro h
    refine ⟨?_, h.pow_ne_one_of_pos_of_lt (by positivity) (by omega)⟩
    rcases legendreSym.eq_one_or_neg_one p ha with h1 | h1
    · exfalso
      exact h.pow_ne_one_of_pos_of_lt (l := 2 ^ m * l) (by omega) (by omega)
        (by rw [heuler, h1]; simp)
    · exact h1
  · rintro ⟨hL, h2k⟩
    rw [IsPrimitiveRoot.iff_orderOf, hp1]
    apply orderOf_eq_of_pow_and_pow_div_prime (by omega)
    · rw [← hp1]; exact ZMod.pow_card_sub_one_eq_one ha
    · intro r hr hdvd
      rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
      · have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
        subst hr2
        rw [show 2 ^ (m + 1) * l / 2 = 2 ^ m * l by omega, heuler, hL]
        simpa using hne
      · rw [(Nat.prime_dvd_prime_iff_eq hr hl).mp h, Nat.mul_div_cancel _ hl.pos]
        exact h2k

/-- In the setting of the criterion, a quadratic nonresidue `a` with `p ∤ a ^ (2ᵏ) - 1` is a
primitive root modulo `p`. -/
theorem isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd {p l k : ℕ} [Fact p.Prime]
    (hl : l.Prime) (hl2 : l ≠ 2) (hk : 1 ≤ k) (hpl : p = 2 ^ k * l + 1) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) (hL : legendreSym p a = -1) (hdvd : ¬ (p : ℤ) ∣ a ^ (2 ^ k) - 1) :
    IsPrimitiveRoot (a : ZMod p) (p - 1) := by
  rw [isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one hl hl2 hk hpl ha]
  refine ⟨hL, fun h => hdvd ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_pow, Int.cast_one, h, sub_self]

/-- If `l` and `p = 4l + 1` are prime, then `2` is a primitive root modulo `p`. -/
theorem isPrimitiveRoot_two_of_eq_four_mul_add_one {p l : ℕ} (hl : l.Prime) (hp : p.Prime)
    (hpl : p = 4 * l + 1) : IsPrimitiveRoot (2 : ZMod p) (p - 1) := by
  have := Fact.mk hp
  have hl2 : l ≠ 2 := by rintro rfl; subst hpl; exact absurd hp (by norm_num)
  have hodd : l % 2 = 1 := hl.eq_two_or_odd.resolve_left hl2
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hne : ((2 : ℕ) : ℤ) = 2 := by norm_num
  have ha : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [← hne]; exact intCast_ne_zero_of_lt' (by norm_num) (by omega)
  have hL : legendreSym p 2 = -1 := by
    rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight]
    simp [show p % 8 = 5 by omega, show p % 2 = 1 by omega]
  have h4 : ((2 : ℤ) : ZMod p) ^ (2 ^ 2) ≠ 1 := by
    intro h4
    have h : ((15 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_ofNat]; push_cast at h4; linear_combination h4
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by norm_num) h
    have hl' : l = 3 := by omega
    subst hl'; subst hpl; norm_num at h
  have := (isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one hl hl2 (k := 2) (by norm_num)
    (by rw [hpl]; norm_num) ha).mpr ⟨hL, h4⟩
  simpa using this

/-- `3` is a primitive root modulo `17`. -/
private lemma isPrimitiveRoot_three_seventeen : IsPrimitiveRoot (3 : ZMod 17) (17 - 1) := by
  rw [IsPrimitiveRoot.iff_orderOf]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · decide
  · intro r hr hdvd
    have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow (n := 4) (by simpa using hdvd))
    subst hr2
    decide

/-- `(3 | p) = -1` for a prime `p ≡ 1 (mod 4)` with `p ≡ 2 (mod 3)`. -/
private lemma legendreSym_three_of_mod {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1)
    (hp3 : p % 3 = 2) : legendreSym p 3 = -1 := by
  have hr := legendreSym.quadratic_reciprocity_one_mod_four (p := p) (q := 3) hp4 (by norm_num)
  have hr' : legendreSym 3 (p : ℕ) = legendreSym p (3 : ℕ) := hr
  rw [show ((3 : ℕ) : ℤ) = 3 by norm_num] at hr'
  rw [← hr', legendreSym.mod 3 (p : ℤ), show ((3 : ℕ) : ℤ) = 3 by norm_num,
    show (p : ℤ) % 3 = 2 by omega, legendreSym.at_two (by norm_num),
    ZMod.χ₈_nat_eq_if_mod_eight]
  norm_num

/-- If `l` and `p = 8l + 1` are prime and `l ≠ 5`, then `3` is a primitive root modulo `p`. -/
theorem isPrimitiveRoot_three_of_eq_eight_mul_add_one {p l : ℕ} (hl : l.Prime) (hp : p.Prime)
    (hpl : p = 8 * l + 1) (hl5 : l ≠ 5) : IsPrimitiveRoot (3 : ZMod p) (p - 1) := by
  have := Fact.mk hp
  rcases eq_or_ne l 2 with rfl | hl2
  · subst hpl; exact isPrimitiveRoot_three_seventeen
  have hodd : l % 2 = 1 := hl.eq_two_or_odd.resolve_left hl2
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hp3 : p % 3 = 2 := by
    rcases (by omega : l % 3 = 0 ∨ l % 3 = 1 ∨ l % 3 = 2) with h | h | h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).mp (Nat.dvd_of_mod_eq_zero h)
      subst this; subst hpl; exact absurd hp (by norm_num)
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (by omega)
      omega
    · omega
  have hne : ((3 : ℕ) : ℤ) = 3 := by norm_num
  have ha : ((3 : ℤ) : ZMod p) ≠ 0 := by
    rw [← hne]; exact intCast_ne_zero_of_lt' (by norm_num) (by omega)
  have hL : legendreSym p 3 = -1 := legendreSym_three_of_mod (by omega) hp3
  have h8 : ((3 : ℤ) : ZMod p) ^ (2 ^ 3) ≠ 1 := by
    intro h8
    have h : ((2 ^ 5 * (5 * 41) : ℕ) : ZMod p) = 0 := by
      push_cast at h8 ⊢; linear_combination h8
    rw [ZMod.natCast_eq_zero_iff] at h
    have h := dvd_of_dvd_two_pow_mul hp (by omega) h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h; omega
  have := (isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one hl hl2 (k := 3) (by norm_num)
    (by rw [hpl]; norm_num) ha).mpr ⟨hL, h8⟩
  simpa using this

/-- The exception `l = 5` is genuine: `3 ^ 8 = 1` modulo `41 = 8 · 5 + 1`, so `3` is not a
primitive root modulo `41`. -/
example : ¬ IsPrimitiveRoot (3 : ZMod 41) (41 - 1) := fun h =>
  h.pow_ne_one_of_pos_of_lt (l := 8) (by norm_num) (by norm_num) (by decide)

/-- If `l` and `p = 16l + 1` are prime, then `3` is a primitive root modulo `p`. -/
theorem isPrimitiveRoot_three_of_eq_sixteen_mul_add_one {p l : ℕ} (hl : l.Prime) (hp : p.Prime)
    (hpl : p = 16 * l + 1) : IsPrimitiveRoot (3 : ZMod p) (p - 1) := by
  have := Fact.mk hp
  have hl2 : l ≠ 2 := by rintro rfl; subst hpl; exact absurd hp (by norm_num)
  have hodd : l % 2 = 1 := hl.eq_two_or_odd.resolve_left hl2
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hp3 : p % 3 = 2 := by
    rcases (by omega : l % 3 = 0 ∨ l % 3 = 1 ∨ l % 3 = 2) with h | h | h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).mp (Nat.dvd_of_mod_eq_zero h)
      subst this; subst hpl; exact absurd hp (by norm_num)
    · omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (by omega)
      omega
  have hne : ((3 : ℕ) : ℤ) = 3 := by norm_num
  have ha : ((3 : ℤ) : ZMod p) ≠ 0 := by
    rw [← hne]; exact intCast_ne_zero_of_lt' (by norm_num) (by omega)
  have hL : legendreSym p 3 = -1 := legendreSym_three_of_mod (by omega) hp3
  have h16 : ((3 : ℤ) : ZMod p) ^ (2 ^ 4) ≠ 1 := by
    intro h16
    have h : ((2 ^ 6 * (5 * (17 * (41 * 193))) : ℕ) : ZMod p) = 0 := by
      push_cast at h16 ⊢; linear_combination h16
    rw [ZMod.natCast_eq_zero_iff] at h
    have h := dvd_of_dvd_two_pow_mul hp (by omega) h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h; omega
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
      have : l = 1 := by omega
      exact absurd hl (by rw [this]; exact Nat.not_prime_one)
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
      have : l = 12 := by omega
      exact absurd hl (by rw [this]; norm_num)
  have := (isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one hl hl2 (k := 4) (by norm_num)
    (by rw [hpl]; norm_num) ha).mpr ⟨hL, h16⟩
  simpa using this

/-- The case `k = 1` of the criterion (safe primes `p = 2l + 1` with `l` odd): a nonzero `a` is a
primitive root modulo `p` iff `(a | p) = -1` and `a ^ 2 ≠ 1`. -/
theorem isPrimitiveRoot_iff_of_eq_two_mul_add_one' {p l : ℕ} [Fact p.Prime] (hl : l.Prime)
    (hl2 : l ≠ 2) (hpl : p = 2 * l + 1) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    IsPrimitiveRoot (a : ZMod p) (p - 1) ↔ legendreSym p a = -1 ∧ (a : ZMod p) ^ 2 ≠ 1 := by
  simpa using isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one hl hl2 (k := 1) le_rfl
    (by rw [hpl]; ring) ha

/-- The case `k = 2` of the criterion (`p = 4l + 1`, as in Chebyshev's family): a nonzero `a` is
a primitive root modulo `p` iff `(a | p) = -1` and `a ^ 4 ≠ 1`. -/
theorem isPrimitiveRoot_iff_of_eq_four_mul_add_one' {p l : ℕ} [Fact p.Prime] (hl : l.Prime)
    (hpl : p = 4 * l + 1) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    IsPrimitiveRoot (a : ZMod p) (p - 1) ↔ legendreSym p a = -1 ∧ (a : ZMod p) ^ 4 ≠ 1 := by
  have hl2 : l ≠ 2 := by
    rintro rfl; subst hpl; exact absurd (Fact.out : Nat.Prime (4 * 2 + 1)) (by norm_num)
  simpa using isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one hl hl2 (k := 2) (by norm_num)
    (by rw [hpl]; ring) ha

end PrimitiveRootFamilies
