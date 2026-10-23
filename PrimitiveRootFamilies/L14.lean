import PrimitiveRootFamilies.Chebyshev
import PrimitiveRootFamilies.SafePrime
import PrimitiveRootFamilies.General
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Layer 14: Mathlib-only restatements and witnesses

Each `l14_*` theorem restates a main theorem in a form whose type mentions only Mathlib:
explicit `Nat.Prime` hypotheses in place of `Fact` instances, `orderOf a = n - 1` in place of
`IsPrimitiveRoot a (n - 1)`, and `jacobiSym` in place of `legendreSym`. Each `l14w_*` theorem
exhibits an explicit configuration satisfying all hypotheses, together with a check that the
conclusion is non-degenerate (for `↔` statements, both truth values occur).
-/

namespace PrimitiveRootFamilies

/-! ### Restatements -/

theorem l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q = 4 * p + 1) {a : ZMod q} (ha : a ≠ 0) :
    orderOf a = q - 1 ↔ a ^ (2 * p) ≠ 1 ∧ a ^ 4 ≠ 1 := by
  have := Fact.mk hq
  rw [← IsPrimitiveRoot.iff_orderOf]
  exact isPrimitiveRoot_iff_of_eq_four_mul_add_one hp hqp ha

theorem l14_legendreSym_ten_of_eq_four_mul_add_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q = 4 * p + 1) : jacobiSym 10 q = -jacobiSym q 5 := by
  have := Fact.mk hq
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym, ← jacobiSym.legendreSym.to_jacobiSym]
  exact legendreSym_ten_of_eq_four_mul_add_one hp hqp

theorem l14_isPrimitiveRoot_ten_iff_mod_five_eq_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q = 4 * p + 1) : orderOf (10 : ZMod q) = q - 1 ↔ p % 5 = 2 := by
  rw [← IsPrimitiveRoot.iff_orderOf]
  exact isPrimitiveRoot_ten_iff_mod_five_eq_two hp hq hqp

theorem l14_isPrimitiveRoot_ten_of_mod_five_eq_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q = 4 * p + 1) (hp5 : p % 5 = 2) : orderOf (10 : ZMod q) = q - 1 :=
  -- Via the `↔` form (of which the library corollary is the `mpr` direction), so that this file
  -- does not depend on the declaration that `tests/tamper.sh` (test `wrap`) replaces.
  IsPrimitiveRoot.iff_orderOf.mp ((isPrimitiveRoot_ten_iff_mod_five_eq_two hp hq hqp).mpr hp5)

theorem l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p = 2 * q + 1) {a : ZMod p} (ha : a ≠ 0) :
    orderOf a = p - 1 ↔ a ^ q ≠ 1 ∧ a ^ 2 ≠ 1 := by
  have := Fact.mk hp
  rw [← IsPrimitiveRoot.iff_orderOf]
  exact isPrimitiveRoot_iff_of_eq_two_mul_add_one hq hpq ha

theorem l14_isPrimitiveRoot_of_legendreSym_eq_neg_one {p q x : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p = 2 * q + 1) (hx1 : 1 < x) (hxp : x < p - 1) (hx : jacobiSym x p = -1) :
    orderOf (x : ZMod p) = p - 1 := by
  have := Fact.mk hp
  rw [← IsPrimitiveRoot.iff_orderOf]
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hx
  exact isPrimitiveRoot_of_legendreSym_eq_neg_one hq hpq hx1 hxp hx

/-- Bridge: the set of positive primitive roots, written with `orderOf`. -/
theorem l14_setOf_orderOf_eq (p : ℕ) :
    {a : ℕ | 0 < a ∧ orderOf (a : ZMod p) = p - 1} =
      {a : ℕ | 0 < a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)} := by
  ext a
  exact and_congr_right fun _ => IsPrimitiveRoot.iff_orderOf.symm

theorem l14_prime_of_isLeast_isPrimitiveRoot {p q g : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p = 2 * q + 1)
    (hg : IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod p) = p - 1} g) : g.Prime := by
  have := Fact.mk hp
  rw [l14_setOf_orderOf_eq] at hg
  exact prime_of_isLeast_isPrimitiveRoot hq hpq hg

theorem l14_exists_isLeast_isPrimitiveRoot {p : ℕ} (hp : p.Prime) :
    ∃ g, IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod p) = p - 1} g := by
  have := Fact.mk hp
  rw [l14_setOf_orderOf_eq]
  exact exists_isLeast_isPrimitiveRoot p

theorem l14_exists_isLeast_isPrimitiveRoot_and_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p = 2 * q + 1) :
    ∃ g, IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod p) = p - 1} g ∧ g.Prime := by
  have := Fact.mk hp
  rw [l14_setOf_orderOf_eq]
  exact exists_isLeast_isPrimitiveRoot_and_prime hq hpq

theorem l14_isPrimitiveRoot_two_of_mod_four_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p = 2 * q + 1) (hq4 : q % 4 = 1) : orderOf (2 : ZMod p) = p - 1 := by
  have := Fact.mk hp
  exact IsPrimitiveRoot.iff_orderOf.mp (isPrimitiveRoot_two_of_mod_four_eq_one hq hpq hq4)

theorem l14_isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one {p l k : ℕ} (hp : p.Prime)
    (hl : l.Prime) (hl2 : l ≠ 2) (hk : 1 ≤ k) (hpl : p = 2 ^ k * l + 1) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) :
    orderOf (a : ZMod p) = p - 1 ↔ jacobiSym a p = -1 ∧ (a : ZMod p) ^ (2 ^ k) ≠ 1 := by
  have := Fact.mk hp
  rw [← IsPrimitiveRoot.iff_orderOf, ← jacobiSym.legendreSym.to_jacobiSym]
  exact isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one hl hl2 hk hpl ha

theorem l14_isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd {p l k : ℕ} (hp : p.Prime)
    (hl : l.Prime) (hl2 : l ≠ 2) (hk : 1 ≤ k) (hpl : p = 2 ^ k * l + 1) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) (hL : jacobiSym a p = -1) (hdvd : ¬ (p : ℤ) ∣ a ^ (2 ^ k) - 1) :
    orderOf (a : ZMod p) = p - 1 := by
  have := Fact.mk hp
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hL
  exact IsPrimitiveRoot.iff_orderOf.mp
    (isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd hl hl2 hk hpl ha hL hdvd)

theorem l14_isPrimitiveRoot_two_of_eq_four_mul_add_one {p l : ℕ} (hl : l.Prime) (hp : p.Prime)
    (hpl : p = 4 * l + 1) : orderOf (2 : ZMod p) = p - 1 :=
  IsPrimitiveRoot.iff_orderOf.mp (isPrimitiveRoot_two_of_eq_four_mul_add_one hl hp hpl)

theorem l14_isPrimitiveRoot_three_of_eq_eight_mul_add_one {p l : ℕ} (hl : l.Prime)
    (hp : p.Prime) (hpl : p = 8 * l + 1) (hl5 : l ≠ 5) : orderOf (3 : ZMod p) = p - 1 :=
  IsPrimitiveRoot.iff_orderOf.mp (isPrimitiveRoot_three_of_eq_eight_mul_add_one hl hp hpl hl5)

theorem l14_isPrimitiveRoot_three_of_eq_sixteen_mul_add_one {p l : ℕ} (hl : l.Prime)
    (hp : p.Prime) (hpl : p = 16 * l + 1) : orderOf (3 : ZMod p) = p - 1 :=
  IsPrimitiveRoot.iff_orderOf.mp (isPrimitiveRoot_three_of_eq_sixteen_mul_add_one hl hp hpl)

theorem l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one' {p l : ℕ} (hp : p.Prime) (hl : l.Prime)
    (hl2 : l ≠ 2) (hpl : p = 2 * l + 1) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    orderOf (a : ZMod p) = p - 1 ↔ jacobiSym a p = -1 ∧ (a : ZMod p) ^ 2 ≠ 1 := by
  have := Fact.mk hp
  rw [← IsPrimitiveRoot.iff_orderOf, ← jacobiSym.legendreSym.to_jacobiSym]
  exact isPrimitiveRoot_iff_of_eq_two_mul_add_one' hl hl2 hpl ha

theorem l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one' {p l : ℕ} (hp : p.Prime) (hl : l.Prime)
    (hpl : p = 4 * l + 1) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    orderOf (a : ZMod p) = p - 1 ↔ jacobiSym a p = -1 ∧ (a : ZMod p) ^ 4 ≠ 1 := by
  have := Fact.mk hp
  rw [← IsPrimitiveRoot.iff_orderOf, ← jacobiSym.legendreSym.to_jacobiSym]
  exact isPrimitiveRoot_iff_of_eq_four_mul_add_one' hl hpl ha

/-! ### Witnesses -/

/-- `p = 3`, `q = 13`: both sides hold for `a = 2` and both fail for `a = 3` (order `3`). -/
theorem l14w_isPrimitiveRoot_iff_of_eq_four_mul_add_one :
    Nat.Prime 3 ∧ Nat.Prime 13 ∧ 13 = 4 * 3 + 1 ∧ (2 : ZMod 13) ≠ 0 ∧ (3 : ZMod 13) ≠ 0 ∧
      (orderOf (2 : ZMod 13) = 13 - 1 ∧ (2 : ZMod 13) ^ (2 * 3) ≠ 1 ∧ (2 : ZMod 13) ^ 4 ≠ 1) ∧
      (orderOf (3 : ZMod 13) ≠ 13 - 1 ∧ ¬ ((3 : ZMod 13) ^ (2 * 3) ≠ 1 ∧ (3 : ZMod 13) ^ 4 ≠ 1)) := by
  have h3 : Nat.Prime 3 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  have r2 : (2 : ZMod 13) ^ (2 * 3) ≠ 1 ∧ (2 : ZMod 13) ^ 4 ≠ 1 := by decide
  have r3 : ¬ ((3 : ZMod 13) ^ (2 * 3) ≠ 1 ∧ (3 : ZMod 13) ^ 4 ≠ 1) := by decide
  refine ⟨h3, h13, rfl, by decide, by decide,
    ⟨(l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one h3 h13 rfl (by decide)).mpr r2, r2⟩,
    fun h => r3 ((l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one h3 h13 rfl (by decide)).mp h),
    r3⟩

/-- `q = 13` gives `(10 | 13) = 1` and `q = 29` gives `(10 | 29) = -1`: both values occur. -/
theorem l14w_legendreSym_ten_of_eq_four_mul_add_one :
    Nat.Prime 3 ∧ Nat.Prime 13 ∧ 13 = 4 * 3 + 1 ∧ Nat.Prime 7 ∧ Nat.Prime 29 ∧ 29 = 4 * 7 + 1 ∧
      jacobiSym 10 13 = -jacobiSym 13 5 ∧ jacobiSym 10 29 = -jacobiSym 29 5 ∧
      jacobiSym 10 13 = 1 ∧ jacobiSym 10 29 = -1 := by
  have h3 : Nat.Prime 3 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h29 : Nat.Prime 29 := by norm_num
  exact ⟨h3, h13, rfl, h7, h29, rfl,
    by exact_mod_cast l14_legendreSym_ten_of_eq_four_mul_add_one h3 h13 rfl,
    by exact_mod_cast l14_legendreSym_ten_of_eq_four_mul_add_one h7 h29 rfl,
    by norm_num, by norm_num⟩

/-- `(p, q) = (7, 29)`: `10` is a primitive root; `(p, q) = (3, 13)`: it is not. -/
theorem l14w_isPrimitiveRoot_ten_iff_mod_five_eq_two :
    Nat.Prime 7 ∧ Nat.Prime 29 ∧ 29 = 4 * 7 + 1 ∧ Nat.Prime 3 ∧ Nat.Prime 13 ∧ 13 = 4 * 3 + 1 ∧
      orderOf (10 : ZMod 29) = 29 - 1 ∧ 7 % 5 = 2 ∧
      orderOf (10 : ZMod 13) ≠ 13 - 1 ∧ 3 % 5 ≠ 2 := by
  have h7 : Nat.Prime 7 := by norm_num
  have h29 : Nat.Prime 29 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  refine ⟨h7, h29, rfl, h3, h13, rfl,
    (l14_isPrimitiveRoot_ten_iff_mod_five_eq_two h7 h29 rfl).mpr rfl, rfl,
    fun h => ?_, by decide⟩
  exact absurd ((l14_isPrimitiveRoot_ten_iff_mod_five_eq_two h3 h13 rfl).mp h) (by decide)

/-- `(p, q) = (7, 29)`; the root `10` is not `1` and the order `28` is not trivial. -/
theorem l14w_isPrimitiveRoot_ten_of_mod_five_eq_two :
    Nat.Prime 7 ∧ Nat.Prime 29 ∧ 29 = 4 * 7 + 1 ∧ 7 % 5 = 2 ∧
      orderOf (10 : ZMod 29) = 29 - 1 ∧ (10 : ZMod 29) ≠ 1 ∧ 1 < 29 - 1 := by
  have h7 : Nat.Prime 7 := by norm_num
  have h29 : Nat.Prime 29 := by norm_num
  exact ⟨h7, h29, rfl, rfl, l14_isPrimitiveRoot_ten_of_mod_five_eq_two h7 h29 rfl rfl,
    by decide, by norm_num⟩

/-- `p = 11`, `q = 5`: both sides hold for `a = 2` and both fail for `a = 10 = -1`. -/
theorem l14w_isPrimitiveRoot_iff_of_eq_two_mul_add_one :
    Nat.Prime 11 ∧ Nat.Prime 5 ∧ 11 = 2 * 5 + 1 ∧ (2 : ZMod 11) ≠ 0 ∧ (10 : ZMod 11) ≠ 0 ∧
      (orderOf (2 : ZMod 11) = 11 - 1 ∧ (2 : ZMod 11) ^ 5 ≠ 1 ∧ (2 : ZMod 11) ^ 2 ≠ 1) ∧
      (orderOf (10 : ZMod 11) ≠ 11 - 1 ∧ ¬ ((10 : ZMod 11) ^ 5 ≠ 1 ∧ (10 : ZMod 11) ^ 2 ≠ 1)) := by
  have h11 : Nat.Prime 11 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have r2 : (2 : ZMod 11) ^ 5 ≠ 1 ∧ (2 : ZMod 11) ^ 2 ≠ 1 := by decide
  have r10 : ¬ ((10 : ZMod 11) ^ 5 ≠ 1 ∧ (10 : ZMod 11) ^ 2 ≠ 1) := by decide
  refine ⟨h11, h5, rfl, by decide, by decide,
    ⟨(l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one h11 h5 rfl (by decide)).mpr r2, r2⟩,
    fun h => r10 ((l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one h11 h5 rfl (by decide)).mp h),
    r10⟩

/-- `p = 23`, `q = 11`, `x = 5`: a nonresidue in `(1, p - 1)`, of order `22`, and `5 ≠ 1`. -/
theorem l14w_isPrimitiveRoot_of_legendreSym_eq_neg_one :
    Nat.Prime 23 ∧ Nat.Prime 11 ∧ 23 = 2 * 11 + 1 ∧ 1 < 5 ∧ 5 < 23 - 1 ∧
      jacobiSym 5 23 = -1 ∧ orderOf ((5 : ℕ) : ZMod 23) = 23 - 1 ∧ ((5 : ℕ) : ZMod 23) ≠ 1 := by
  have h23 : Nat.Prime 23 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have hj : jacobiSym 5 23 = -1 := by norm_num
  exact ⟨h23, h11, rfl, by norm_num, by norm_num, hj,
    l14_isPrimitiveRoot_of_legendreSym_eq_neg_one h23 h11 rfl (by norm_num) (by norm_num)
      (by exact_mod_cast hj), by decide⟩

/-- Modulo the safe prime `23`, the least positive primitive root is `5`. -/
theorem l14w_isLeast_twentythree :
    IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod 23) = 23 - 1} 5 := by
  refine ⟨⟨by norm_num, (l14w_isPrimitiveRoot_of_legendreSym_eq_neg_one).2.2.2.2.2.2.1⟩, ?_⟩
  rintro a ⟨ha0, ha⟩
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  have h11 : (a : ZMod 23) ^ 11 = 1 := by interval_cases a <;> decide
  have := orderOf_dvd_of_pow_eq_one h11
  rw [ha] at this
  norm_num at this

/-- `p = 23`, `q = 11`: the least positive primitive root `5` is prime; `1`, `2`, `3`, `4`
are not primitive roots, so minimality is not attained trivially. -/
theorem l14w_prime_of_isLeast_isPrimitiveRoot :
    Nat.Prime 23 ∧ Nat.Prime 11 ∧ 23 = 2 * 11 + 1 ∧
      IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod 23) = 23 - 1} 5 ∧ Nat.Prime 5 ∧
      orderOf ((4 : ℕ) : ZMod 23) ≠ 23 - 1 := by
  have h23 : Nat.Prime 23 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  refine ⟨h23, h11, rfl, l14w_isLeast_twentythree,
    l14_prime_of_isLeast_isPrimitiveRoot h23 h11 rfl l14w_isLeast_twentythree, fun h => ?_⟩
  have := l14w_isLeast_twentythree.2 ⟨by norm_num, h⟩
  norm_num at this

/-- `p = 23`: the existential is realised by the explicit least element `5`. -/
theorem l14w_exists_isLeast_isPrimitiveRoot :
    Nat.Prime 23 ∧ (∃ g, IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod 23) = 23 - 1} g) ∧
      IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod 23) = 23 - 1} 5 :=
  ⟨by norm_num, l14_exists_isLeast_isPrimitiveRoot (by norm_num), l14w_isLeast_twentythree⟩

/-- `p = 23`, `q = 11`: the least root is `5`, a prime different from `2`. -/
theorem l14w_exists_isLeast_isPrimitiveRoot_and_prime :
    Nat.Prime 23 ∧ Nat.Prime 11 ∧ 23 = 2 * 11 + 1 ∧
      (∃ g, IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod 23) = 23 - 1} g ∧ g.Prime) ∧
      IsLeast {a : ℕ | 0 < a ∧ orderOf (a : ZMod 23) = 23 - 1} 5 ∧ Nat.Prime 5 ∧ 5 ≠ 2 := by
  have h23 : Nat.Prime 23 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  exact ⟨h23, h11, rfl, l14_exists_isLeast_isPrimitiveRoot_and_prime h23 h11 rfl,
    l14w_isLeast_twentythree, by norm_num, by norm_num⟩

/-- `p = 11`, `q = 5`: `2` has order `10`, and `2 ≠ 1`. -/
theorem l14w_isPrimitiveRoot_two_of_mod_four_eq_one :
    Nat.Prime 11 ∧ Nat.Prime 5 ∧ 11 = 2 * 5 + 1 ∧ 5 % 4 = 1 ∧
      orderOf (2 : ZMod 11) = 11 - 1 ∧ (2 : ZMod 11) ≠ 1 := by
  have h11 : Nat.Prime 11 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  exact ⟨h11, h5, rfl, rfl, l14_isPrimitiveRoot_two_of_mod_four_eq_one h11 h5 rfl rfl, by decide⟩

/-- `p = 41 = 2³ · 5 + 1`: both sides hold for `a = 6`; for `a = 3` both fail although
`(3 | 41) = -1`, so the second condition is essential. -/
theorem l14w_isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one :
    Nat.Prime 41 ∧ Nat.Prime 5 ∧ 5 ≠ 2 ∧ 1 ≤ 3 ∧ 41 = 2 ^ 3 * 5 + 1 ∧
      ((6 : ℤ) : ZMod 41) ≠ 0 ∧ ((3 : ℤ) : ZMod 41) ≠ 0 ∧
      (orderOf ((6 : ℤ) : ZMod 41) = 41 - 1 ∧ jacobiSym 6 41 = -1 ∧
        ((6 : ℤ) : ZMod 41) ^ (2 ^ 3) ≠ 1) ∧
      (orderOf ((3 : ℤ) : ZMod 41) ≠ 41 - 1 ∧ jacobiSym 3 41 = -1 ∧
        ((3 : ℤ) : ZMod 41) ^ (2 ^ 3) = 1) := by
  have h41 : Nat.Prime 41 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have j6 : jacobiSym 6 41 = -1 := by norm_num
  have j3 : jacobiSym 3 41 = -1 := by norm_num
  have p6 : ((6 : ℤ) : ZMod 41) ^ (2 ^ 3) ≠ 1 := by push_cast; decide
  have p3 : ((3 : ℤ) : ZMod 41) ^ (2 ^ 3) = 1 := by push_cast; decide
  have n6 : ((6 : ℤ) : ZMod 41) ≠ 0 := by push_cast; decide
  have n3 : ((3 : ℤ) : ZMod 41) ≠ 0 := by push_cast; decide
  refine ⟨h41, h5, by norm_num, by norm_num, rfl, n6, n3,
    ⟨(l14_isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one h41 h5 (by norm_num) (by norm_num) rfl
      n6).mpr ⟨j6, p6⟩, j6, p6⟩, fun h => ?_, j3, p3⟩
  exact ((l14_isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one h41 h5 (by norm_num) (by norm_num)
    rfl n3).mp h).2 p3

/-- `p = 41`, `k = 3`, `l = 5`, `a = 6`: all hypotheses hold, `6` has order `40`, `6 ≠ 1`. -/
theorem l14w_isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd :
    Nat.Prime 41 ∧ Nat.Prime 5 ∧ 5 ≠ 2 ∧ 1 ≤ 3 ∧ 41 = 2 ^ 3 * 5 + 1 ∧
      ((6 : ℤ) : ZMod 41) ≠ 0 ∧ jacobiSym 6 41 = -1 ∧ ¬ ((41 : ℕ) : ℤ) ∣ 6 ^ (2 ^ 3) - 1 ∧
      orderOf ((6 : ℤ) : ZMod 41) = 41 - 1 ∧ ((6 : ℤ) : ZMod 41) ≠ 1 := by
  have h41 : Nat.Prime 41 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have j6 : jacobiSym 6 41 = -1 := by norm_num
  have n6 : ((6 : ℤ) : ZMod 41) ≠ 0 := by push_cast; decide
  have hd : ¬ ((41 : ℕ) : ℤ) ∣ 6 ^ (2 ^ 3) - 1 := by norm_num
  exact ⟨h41, h5, by norm_num, by norm_num, rfl, n6, j6, hd,
    l14_isPrimitiveRoot_of_legendreSym_eq_neg_one_of_not_dvd h41 h5 (by norm_num) (by norm_num)
      rfl n6 (by exact_mod_cast j6) hd, by push_cast; decide⟩

/-- `l = 3`, `p = 13`: `2` has order `12`, and `2 ≠ 1`. -/
theorem l14w_isPrimitiveRoot_two_of_eq_four_mul_add_one :
    Nat.Prime 3 ∧ Nat.Prime 13 ∧ 13 = 4 * 3 + 1 ∧
      orderOf (2 : ZMod 13) = 13 - 1 ∧ (2 : ZMod 13) ≠ 1 := by
  have h3 : Nat.Prime 3 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  exact ⟨h3, h13, rfl, l14_isPrimitiveRoot_two_of_eq_four_mul_add_one h3 h13 rfl, by decide⟩

/-- `l = 11`, `p = 89` (the generic odd branch): `3` has order `88`, `3 ≠ 1`. The excluded case
`l = 5`, `p = 41` genuinely fails. -/
theorem l14w_isPrimitiveRoot_three_of_eq_eight_mul_add_one :
    Nat.Prime 11 ∧ Nat.Prime 89 ∧ 89 = 8 * 11 + 1 ∧ 11 ≠ 5 ∧
      orderOf (3 : ZMod 89) = 89 - 1 ∧ (3 : ZMod 89) ≠ 1 ∧
      Nat.Prime 5 ∧ Nat.Prime 41 ∧ 41 = 8 * 5 + 1 ∧ orderOf (3 : ZMod 41) ≠ 41 - 1 := by
  have h11 : Nat.Prime 11 := by norm_num
  have h89 : Nat.Prime 89 := by norm_num
  refine ⟨h11, h89, rfl, by norm_num,
    l14_isPrimitiveRoot_three_of_eq_eight_mul_add_one h11 h89 rfl (by norm_num), by decide,
    by norm_num, by norm_num, rfl, fun h => ?_⟩
  have := orderOf_dvd_of_pow_eq_one (show (3 : ZMod 41) ^ 8 = 1 by decide)
  rw [h] at this
  norm_num at this

/-- `l = 7`, `p = 113`: `3` has order `112`, and `3 ≠ 1`. -/
theorem l14w_isPrimitiveRoot_three_of_eq_sixteen_mul_add_one :
    Nat.Prime 7 ∧ Nat.Prime 113 ∧ 113 = 16 * 7 + 1 ∧
      orderOf (3 : ZMod 113) = 113 - 1 ∧ (3 : ZMod 113) ≠ 1 := by
  have h7 : Nat.Prime 7 := by norm_num
  have h113 : Nat.Prime 113 := by norm_num
  exact ⟨h7, h113, rfl, l14_isPrimitiveRoot_three_of_eq_sixteen_mul_add_one h7 h113 rfl,
    by decide⟩

/-- `p = 23`, `l = 11`: both sides hold for `a = 5`; for `a = -1` both fail although
`(-1 | 23) = -1`, so the condition `a ^ 2 ≠ 1` is essential. -/
theorem l14w_isPrimitiveRoot_iff_of_eq_two_mul_add_one' :
    Nat.Prime 23 ∧ Nat.Prime 11 ∧ 11 ≠ 2 ∧ 23 = 2 * 11 + 1 ∧
      ((5 : ℤ) : ZMod 23) ≠ 0 ∧ ((-1 : ℤ) : ZMod 23) ≠ 0 ∧
      (orderOf ((5 : ℤ) : ZMod 23) = 23 - 1 ∧ jacobiSym 5 23 = -1 ∧
        ((5 : ℤ) : ZMod 23) ^ 2 ≠ 1) ∧
      (orderOf ((-1 : ℤ) : ZMod 23) ≠ 23 - 1 ∧ jacobiSym (-1) 23 = -1 ∧
        ((-1 : ℤ) : ZMod 23) ^ 2 = 1) := by
  have h23 : Nat.Prime 23 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have j5 : jacobiSym 5 23 = -1 := by norm_num
  have jm : jacobiSym (-1) 23 = -1 := by norm_num
  have p5 : ((5 : ℤ) : ZMod 23) ^ 2 ≠ 1 := by push_cast; decide
  have pm : ((-1 : ℤ) : ZMod 23) ^ 2 = 1 := by push_cast; decide
  have n5 : ((5 : ℤ) : ZMod 23) ≠ 0 := by push_cast; decide
  have nm : ((-1 : ℤ) : ZMod 23) ≠ 0 := by push_cast; decide
  refine ⟨h23, h11, by norm_num, rfl, n5, nm,
    ⟨(l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one' h23 h11 (by norm_num) rfl n5).mpr
      ⟨j5, p5⟩, j5, p5⟩, fun h => ?_, jm, pm⟩
  exact ((l14_isPrimitiveRoot_iff_of_eq_two_mul_add_one' h23 h11 (by norm_num) rfl nm).mp h).2 pm

/-- `p = 13`, `l = 3`: both sides hold for `a = 2`; for `a = 5` both fail although
`(5 | 13) = -1`, so the condition `a ^ 4 ≠ 1` is essential. -/
theorem l14w_isPrimitiveRoot_iff_of_eq_four_mul_add_one' :
    Nat.Prime 13 ∧ Nat.Prime 3 ∧ 13 = 4 * 3 + 1 ∧
      ((2 : ℤ) : ZMod 13) ≠ 0 ∧ ((5 : ℤ) : ZMod 13) ≠ 0 ∧
      (orderOf ((2 : ℤ) : ZMod 13) = 13 - 1 ∧ jacobiSym 2 13 = -1 ∧
        ((2 : ℤ) : ZMod 13) ^ 4 ≠ 1) ∧
      (orderOf ((5 : ℤ) : ZMod 13) ≠ 13 - 1 ∧ jacobiSym 5 13 = -1 ∧
        ((5 : ℤ) : ZMod 13) ^ 4 = 1) := by
  have h13 : Nat.Prime 13 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have j2 : jacobiSym 2 13 = -1 := by norm_num
  have j5 : jacobiSym 5 13 = -1 := by norm_num
  have p2 : ((2 : ℤ) : ZMod 13) ^ 4 ≠ 1 := by push_cast; decide
  have p5 : ((5 : ℤ) : ZMod 13) ^ 4 = 1 := by push_cast; decide
  have n2 : ((2 : ℤ) : ZMod 13) ≠ 0 := by push_cast; decide
  have n5 : ((5 : ℤ) : ZMod 13) ≠ 0 := by push_cast; decide
  refine ⟨h13, h3, rfl, n2, n5,
    ⟨(l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one' h13 h3 rfl n2).mpr ⟨j2, p2⟩, j2, p2⟩,
    fun h => ?_, j5, p5⟩
  exact ((l14_isPrimitiveRoot_iff_of_eq_four_mul_add_one' h13 h3 rfl n5).mp h).2 p5

end PrimitiveRootFamilies
