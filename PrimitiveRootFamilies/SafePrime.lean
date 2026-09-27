/-
Copyright (c) 2026 Josh Bald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Bald
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.RingTheory.ZMod.Torsion

/-!
# Primitive roots modulo safe primes

A *safe prime* is a prime `p = 2q + 1` with `q` also prime.

**Theorem (Ramesh–Makeshwari).** The least positive primitive root modulo a safe prime is prime.

Reference: V. P. Ramesh and M. Makeshwari, *Least primitive root of any safe prime is prime*,
Amer. Math. Monthly 129 (2022), no. 10, 971, doi:10.1080/00029890.2022.2115816.

## Main results
* `isPrimitiveRoot_iff_of_eq_two_mul_add_one`: for a safe prime `p = 2q + 1`, a nonzero residue
  `a` is a primitive root modulo `p` iff `a ^ q ≠ 1` and `a ^ 2 ≠ 1`.
* `isPrimitiveRoot_of_legendreSym_eq_neg_one`: for a safe prime `p`, every quadratic nonresidue
  `x` with `1 < x < p - 1` is a primitive root.
* `prime_of_isLeast_isPrimitiveRoot`: the least positive primitive root modulo a safe prime is
  prime (Ramesh–Makeshwari).
* `exists_isLeast_isPrimitiveRoot`: for every prime `p`, a least positive primitive root exists.
* `exists_isLeast_isPrimitiveRoot_and_prime`: unconditional form for safe primes; the least
  positive primitive root exists and is prime.
* `isPrimitiveRoot_two_of_mod_four_eq_one`: if `p = 2q + 1` is a safe prime with `q ≡ 1 (mod 4)`,
  then `2` is a primitive root modulo `p`. This is a classical corollary of the criterion.

## Proof outline
The unit group has order `p - 1 = 2q`, with prime divisors `2` and `q`. So `a ≠ 0` is a
primitive root iff `a ^ q ≠ 1` and `a ^ 2 ≠ 1`. By Euler's criterion `a ^ q = (a | p)`, so a
primitive root is a nonresidue. Conversely, a nonresidue `x` with `x ≢ ±1 (mod p)` is a
primitive root.

Let `g` be the least positive primitive root. Then `g < p`: reducing `g` modulo `p` gives
another positive primitive root, and it is no larger than `g`. If `g = m n` with `1 < m, n < g`,
then `(m | p)(n | p) = (g | p) = -1`. So one of `m` and `n` is a nonresidue strictly between `1`
and `p - 1`, and is therefore a smaller primitive root. That contradicts minimality.

This Legendre-symbol argument differs in form from the published note, which argues with
multiplicative orders and the quotient `a / m`. The mathematical content is the same.
-/

namespace PrimitiveRootFamilies

/-- For a safe prime `p = 2q + 1`, a nonzero residue `a` is a primitive root modulo `p` if and
only if `a ^ q ≠ 1` and `a ^ 2 ≠ 1`. -/
theorem isPrimitiveRoot_iff_of_eq_two_mul_add_one {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hpq : p = 2 * q + 1) {a : ZMod p} (ha : a ≠ 0) :
    IsPrimitiveRoot a (p - 1) ↔ a ^ q ≠ 1 ∧ a ^ 2 ≠ 1 := by
  have hp1 : p - 1 = 2 * q := by omega
  have h2 := hq.two_le
  constructor
  · intro h
    exact ⟨h.pow_ne_one_of_pos_of_lt (by omega) (by omega),
      h.pow_ne_one_of_pos_of_lt (by omega) (by omega)⟩
  · rintro ⟨hq1, h21⟩
    rw [IsPrimitiveRoot.iff_orderOf, hp1]
    apply orderOf_eq_of_pow_and_pow_div_prime (by omega)
    · rw [← hp1]; exact ZMod.pow_card_sub_one_eq_one ha
    · intro r hr hdvd
      rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h,
          Nat.mul_div_cancel_left _ (by norm_num)]
        exact hq1
      · rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp h, Nat.mul_div_cancel _ hq.pos]
        exact h21

/-- Euler's criterion in the form used here: for `p = 2q + 1`, `x ^ q = (x | p)` in `ZMod p`. -/
private lemma pow_eq_legendreSym {p q : ℕ} [Fact p.Prime] (hpq : p = 2 * q + 1) (x : ℕ) :
    (x : ZMod p) ^ q = ((legendreSym p x : ℤ) : ZMod p) := by
  have e := legendreSym.eq_pow p (x : ℤ)
  rw [show p / 2 = q by omega] at e
  simpa using e.symm

private lemma natCast_ne_zero_of_lt {p x : ℕ} (hx0 : 0 < x) (hxp : x < p) :
    ((x : ℤ) : ZMod p) ≠ 0 := by
  rw [Int.cast_natCast]
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd hx0 h) (by omega)

/-- For a safe prime `p = 2q + 1`, every quadratic nonresidue `x` with `1 < x < p - 1` is a
primitive root modulo `p`. -/
theorem isPrimitiveRoot_of_legendreSym_eq_neg_one {p q x : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hpq : p = 2 * q + 1) (hx1 : 1 < x) (hxp : x < p - 1) (hx : legendreSym p x = -1) :
    IsPrimitiveRoot (x : ZMod p) (p - 1) := by
  have h2 := hq.two_le
  have hne : (x : ZMod p) ≠ 0 := by
    have := natCast_ne_zero_of_lt (p := p) (by omega : 0 < x) (by omega : x < p)
    simpa using this
  have : Fact (2 < p) := ⟨by omega⟩
  rw [isPrimitiveRoot_iff_of_eq_two_mul_add_one hq hpq hne]
  refine ⟨?_, ?_⟩
  · rw [pow_eq_legendreSym hpq, hx]
    simpa using (ZMod.neg_one_ne_one (n := p))
  · intro hsq
    rw [pow_two, mul_self_eq_one_iff] at hsq
    rcases hsq with h | h
    · have h' : ((x : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h
      rw [ZMod.natCast_eq_natCast_iff'] at h'
      rw [Nat.mod_eq_of_lt (by omega : x < p), Nat.mod_eq_of_lt (by omega : 1 < p)] at h'
      omega
    · have h' : ((x + 1 : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact absurd (Nat.le_of_dvd (by omega) h') (by omega)

/-- **Ramesh–Makeshwari.** The least positive primitive root modulo a safe prime `p = 2q + 1`
is prime. -/
theorem prime_of_isLeast_isPrimitiveRoot {p q g : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hpq : p = 2 * q + 1)
    (hg : IsLeast {a : ℕ | 0 < a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)} g) : g.Prime := by
  obtain ⟨⟨hgpos, hgpr⟩, hlow⟩ := hg
  have h2 := hq.two_le
  have hne0 : (g : ZMod p) ≠ 0 := hgpr.ne_zero (by omega)
  -- `g < p`: otherwise `g % p` would be a smaller positive primitive root.
  have hglt : g < p := by
    by_contra hge
    have hmodpos : 0 < g % p := by
      rcases Nat.eq_zero_or_pos (g % p) with h0 | h0
      · exfalso; apply hne0
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero h0
      · exact h0
    have hmem : g % p ∈ {a : ℕ | 0 < a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)} :=
      ⟨hmodpos, by rw [ZMod.natCast_mod]; exact hgpr⟩
    have := hlow hmem
    have := Nat.mod_lt g (by omega : 0 < p)
    omega
  -- `g` is a nonresidue.
  have hgL : legendreSym p g = -1 := by
    have hgq := ((isPrimitiveRoot_iff_of_eq_two_mul_add_one hq hpq hne0).mp hgpr).1
    rcases legendreSym.eq_one_or_neg_one p (natCast_ne_zero_of_lt hgpos hglt) with h | h
    · exfalso; apply hgq; rw [pow_eq_legendreSym hpq, h]; simp
    · exact h
  -- `g ≠ 1`, since `1` is a residue.
  have hg2 : 2 ≤ g := by
    rcases (by omega : g = 1 ∨ 2 ≤ g) with h | h
    · subst h; rw [Nat.cast_one, legendreSym.at_one] at hgL; norm_num at hgL
    · exact h
  -- `g ≠ p - 1`: `p - 1` has order `2`, not `p - 1`.
  have hgne : g ≠ p - 1 := by
    intro h
    have hsq := ((isPrimitiveRoot_iff_of_eq_two_mul_add_one hq hpq hne0).mp hgpr).2
    apply hsq
    have : (g : ZMod p) = -1 := by
      have h' : ((g + 1 : ℕ) : ZMod p) = 0 := by
        rw [show g + 1 = p by omega, ZMod.natCast_self]
      push_cast at h'
      linear_combination h'
    rw [this]; norm_num
  by_contra hnp
  obtain ⟨m, ⟨n, rfl⟩, hm2, hmlt⟩ := Nat.exists_dvd_of_not_prime2 hg2 hnp
  have hn2 : 2 ≤ n := by
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with h | h | h
    · subst h; omega
    · subst h; omega
    · exact h
  have hnlt : n < m * n := by nlinarith
  have hsmaller : ∀ x : ℕ, 1 < x → x < m * n → legendreSym p x = -1 → False := by
    intro x hx1 hxg hx
    have hpr := isPrimitiveRoot_of_legendreSym_eq_neg_one hq hpq hx1 (by omega) hx
    have := hlow ⟨by omega, hpr⟩
    omega
  have hmul : legendreSym p m * legendreSym p n = -1 := by
    have h := hgL
    push_cast at h
    rwa [legendreSym.mul] at h
  rcases legendreSym.eq_one_or_neg_one p (natCast_ne_zero_of_lt (by omega : 0 < m)
      (by omega : m < p)) with hm | hm
  · rw [hm, one_mul] at hmul
    exact hsmaller n (by omega) hnlt hmul
  · exact hsmaller m (by omega) hmlt hm

/-- For every prime `p`, the set of positive primitive roots modulo `p` has a least element. -/
theorem exists_isLeast_isPrimitiveRoot (p : ℕ) [Fact p.Prime] :
    ∃ g, IsLeast {a : ℕ | 0 < a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)} g := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ZMod p) (p - 1)
  have hp := (Fact.out : p.Prime).two_le
  have hne : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hex : ∃ a : ℕ, 0 < a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1) :=
    ⟨ζ.val, Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero]), by rwa [ZMod.natCast_zmod_val]⟩
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex, fun a ha => Nat.find_min' hex ha⟩

/-- **Ramesh–Makeshwari, unconditional form.** For a safe prime `p = 2q + 1`, the least positive
primitive root modulo `p` exists and is prime. -/
theorem exists_isLeast_isPrimitiveRoot_and_prime {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hpq : p = 2 * q + 1) :
    ∃ g, IsLeast {a : ℕ | 0 < a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)} g ∧ g.Prime := by
  obtain ⟨g, hg⟩ := exists_isLeast_isPrimitiveRoot p
  exact ⟨g, hg, prime_of_isLeast_isPrimitiveRoot hq hpq hg⟩

/-- If `p = 2q + 1` is a safe prime with `q ≡ 1 (mod 4)` (equivalently `p ≡ 3 (mod 8)`),
then `2` is a primitive root modulo `p`. -/
theorem isPrimitiveRoot_two_of_mod_four_eq_one {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hpq : p = 2 * q + 1) (hq4 : q % 4 = 1) : IsPrimitiveRoot (2 : ZMod p) (p - 1) := by
  have h5 : 5 ≤ q := by
    rcases (by omega : q = 1 ∨ 5 ≤ q) with h | h
    · subst h; exact absurd hq Nat.not_prime_one
    · exact h
  have hL : legendreSym p (2 : ℕ) = -1 := by
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, legendreSym.at_two (by omega),
      ZMod.χ₈_nat_eq_if_mod_eight]
    simp [show p % 8 = 3 by omega, show p % 2 = 1 by omega]
  simpa using isPrimitiveRoot_of_legendreSym_eq_neg_one (x := 2) hq hpq (by norm_num)
    (by omega) hL

/-- The safe prime `11 = 2 · 5 + 1`, with `5 ≡ 1 (mod 4)`: `2` is a primitive root. -/
example : IsPrimitiveRoot (2 : ZMod 11) 10 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact isPrimitiveRoot_two_of_mod_four_eq_one (q := 5) (by norm_num) (by norm_num) (by norm_num)

end PrimitiveRootFamilies
