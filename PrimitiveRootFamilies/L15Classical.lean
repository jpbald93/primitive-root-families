import PrimitiveRootFamilies.Chebyshev
import PrimitiveRootFamilies.SafePrime
import PrimitiveRootFamilies.General
import Mathlib

/-!
# Layer 15: comparison with classical statements

Layer 15. These definitions and statements were written independently, from textbook
statements, by an AI model that did not see this code; they are reproduced verbatim. Each cov_*
theorem proves (or proves part of) one of them from this development.

The only change to the writer's text is packaging: each statement `classical_X` is given as a
`def classical_X : Prop` (the universally quantified statement) instead of a theorem, so that it
can be proved, or refuted, below. The writer's notes: congruences are stated with `Int.ModEq`
(`a ≡ b [ZMOD n]`); the Legendre symbol is Mathlib's `legendreSym p a` (requires the instance
`[Fact p.Prime]`).

One writer statement is false as written: `classical_Prime3_c` (Wertheim's criterion for
`p = 2^k q^l + 1`) fails for `l ≥ 2`; `not_classical_Prime3_c` gives the counterexample
`p = 19`, `a = 8`, and `new_Prime3_c_corrected` proves the corrected form with exponent
`2^k q^(l-1)`. The repository's theorem `isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one`
is the case `l = 1`, which is correct (`cov_Prime3_c_part`).
-/

namespace PrimitiveRootFamilies.Classical

/-- Abbreviation for Mathlib's notion: `g` is a primitive root modulo `p` iff its image in
`ZMod p` is a primitive `(p-1)`-th root of unity, i.e. has multiplicative order `p - 1`
(this forces `p ∤ g` for prime `p`). -/
abbrev IsPrimRootMod (p : ℕ) (g : ℤ) : Prop :=
  IsPrimitiveRoot (g : ZMod p) (p - 1)

/-- Abbreviation (Mathlib's `IsSquare` in `ZMod p`): `a` is a quadratic residue modulo `p`,
i.e. `p ∤ a` and `a` is a square mod `p`. -/
abbrev IsQR (p : ℕ) (a : ℤ) : Prop :=
  (a : ZMod p) ≠ 0 ∧ IsSquare (a : ZMod p)

/-- Abbreviation: `a` is a quadratic non-residue modulo `p` (`p ∤ a`, not a square). -/
abbrev IsQNR (p : ℕ) (a : ℤ) : Prop :=
  (a : ZMod p) ≠ 0 ∧ ¬ IsSquare (a : ZMod p)

/-- OWN DEFINITION: safe prime: `p` prime and `p = 2q + 1` with `q` prime. -/
def IsSafePrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p = 2 * q + 1

/-- OWN DEFINITION: the `k`-th decimal digit (`k ≥ 1`) after the decimal point of a real
number `x`, namely `⌊10^k x⌋ mod 10`. -/
noncomputable def decimalDigit (x : ℝ) (k : ℕ) : ℤ :=
  ⌊(10 : ℝ) ^ k * x⌋ % 10

/-- OWN DEFINITION: the period of the decimal expansion of `x`: the least `n ≥ 1` such that
the digit sequence after the decimal point is `n`-periodic (purely periodic from the first
digit). -- AMBIGUOUS: "eventually periodic" period; for `1/q` with `gcd(q,10)=1` the two
agree. Value `0` (junk) if no period exists. -/
noncomputable def decimalPeriod (x : ℝ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∀ k : ℕ, 1 ≤ k → decimalDigit x (k + n) = decimalDigit x k}

/-! ## Prime1 — Euler's criterion -/

def classical_Prime1_a : Prop := ∀ (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a),
    a ^ ((p - 1) / 2) ≡ legendreSym p a [ZMOD p]

def classical_Prime1_b : Prop := ∀ (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a),
    IsQR p a ↔ a ^ ((p - 1) / 2) ≡ 1 [ZMOD p]

def classical_Prime1_c : Prop := ∀ (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a),
    IsQNR p a ↔ a ^ ((p - 1) / 2) ≡ -1 [ZMOD p]

/-! ## Prime2 — primitive-root test -/

def classical_Prime2_a : Prop := ∀ (p : ℕ) (hp : p.Prime) (g : ℤ) (hg : ¬ (p : ℤ) ∣ g),
    IsPrimRootMod p g ↔
      ∀ r : ℕ, r.Prime → r ∣ p - 1 → ¬ g ^ ((p - 1) / r) ≡ 1 [ZMOD p]

/-- Corollary, Legendre-symbol form. -/
def classical_Prime2_b : Prop := ∀ (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (g : ℤ)
    (hg : IsPrimRootMod p g),
    legendreSym p g = -1

/-- Corollary, power form. -/
def classical_Prime2_c : Prop := ∀ (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (g : ℤ)
    (hg : IsPrimRootMod p g),
    g ^ ((p - 1) / 2) ≡ -1 [ZMOD p]

/-- No quadratic residue is a primitive root (for odd `p`; for `p = 2`, `1` is both). -/
def classical_Prime2_d : Prop := ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ) (ha : IsQR p a),
    ¬ IsPrimRootMod p a

/-! ## Prime3 — primitive roots via the Legendre symbol -/

/-- (a) Fermat primes. -/
def classical_Prime3_a : Prop := ∀ (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) (hpk : p - 1 = 2 ^ k)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a),
    IsPrimRootMod p a ↔ legendreSym p a = -1

/-- (b) Safe primes. -/
def classical_Prime3_b : Prop := ∀ (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hpq : p = 2 * q + 1)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a),
    IsPrimRootMod p a ↔ (legendreSym p a = -1 ∧ ¬ a ≡ -1 [ZMOD p])

/-- (b), remark: for `p = 5`, `-1` is a quadratic residue. -/
def classical_Prime3_b_remark5 : Prop := IsQR 5 (-1)

/-- (b), remark: for a safe prime `p ≥ 7`, `-1` is a non-residue of order 2. -/
def classical_Prime3_b_remark7 : Prop := ∀ (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (hpq : p = 2 * q + 1) (h7 : 7 ≤ p),
    legendreSym p (-1) = -1 ∧ orderOf ((-1 : ℤ) : ZMod p) = 2

/-- (c) Wertheim's generalisation. -/
def classical_Prime3_c : Prop := ∀ (p q k l : ℕ) [Fact p.Prime] (hq : q.Prime) (hq2 : q ≠ 2)
    (hk : 1 ≤ k) (hl : 1 ≤ l) (hpq : p = 2 ^ k * q ^ l + 1)
    (a : ℤ) (ha : legendreSym p a = -1) (ha2 : ¬ a ^ (2 ^ k) ≡ 1 [ZMOD p]),
    IsPrimRootMod p a

/-! ## Prime4 — Tchebychef: 2 is a primitive root of 4q+1 -/

def classical_Prime4 : Prop := ∀ (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hp : (4 * q + 1).Prime),
    IsPrimRootMod (4 * q + 1) 2

/-! ## Prime5 — 10 as a primitive root of 4p+1 -/

def classical_Prime5_a : Prop := ∀ (p : ℕ) (hp : p.Prime) (hq : (4 * p + 1).Prime)
    (h5 : p % 5 = 2),
    IsPrimRootMod (4 * p + 1) 10

def classical_Prime5_b : Prop := ∀ (p : ℕ) (hp : p.Prime) (hq : (4 * p + 1).Prime)
    (h10 : IsPrimRootMod (4 * p + 1) 10),
    p % 5 = 2

def classical_Prime5_iff : Prop := ∀ (p : ℕ) (hp : p.Prime) (hq : (4 * p + 1).Prime),
    IsPrimRootMod (4 * p + 1) 10 ↔ p % 5 = 2

/-- Full-reptend reformulation: 10 is a primitive root mod `q` iff the decimal expansion of
`1/q` has period `q - 1`. Stated for the `q = 4p+1` of the item. -/
def classical_Prime5_reptend : Prop := ∀ (p : ℕ) (hp : p.Prime) (hq : (4 * p + 1).Prime),
    IsPrimRootMod (4 * p + 1) 10 ↔
      decimalPeriod (1 / ((4 * p + 1 : ℕ) : ℝ)) = 4 * p + 1 - 1

/-- Examples `(7,29)`, `(37,149)`, `(67,269)`. -/
def classical_Prime5_examples : Prop :=
    IsPrimRootMod 29 10 ∧ IsPrimRootMod 149 10 ∧ IsPrimRootMod 269 10

/-- Note: under the hypotheses `p` is odd, `q ≡ 5 (mod 8)` and `q ≠ 5`. -/
def classical_Prime5_note : Prop := ∀ (p : ℕ) (hp : p.Prime) (hq : (4 * p + 1).Prime),
    p % 2 = 1 ∧ (4 * p + 1) % 8 = 5 ∧ 4 * p + 1 ≠ 5

/-! ## Prime6 — least primitive root of a safe prime is prime -/

/-- Main theorem (Ramesh–Makeshwari). -/
def classical_Prime6 : Prop := ∀ (p : ℕ) (hp : IsSafePrime p) (g : ℕ)
    (hg : IsLeast {n : ℕ | 0 < n ∧ IsPrimRootMod p n} g),
    g.Prime

/-- Well-formedness: a positive primitive root exists, so the least one exists. -/
def classical_Prime6_obligation : Prop := ∀ (p : ℕ) (hp : p.Prime),
    ∃ g : ℕ, IsLeast {n : ℕ | 0 < n ∧ IsPrimRootMod p n} g

/-- Examples: 5 → 2, 7 → 3, 11 → 2, 23 → 5, 47 → 5. -/
def classical_Prime6_examples : Prop :=
    IsLeast {n : ℕ | 0 < n ∧ IsPrimRootMod 5 n} 2 ∧
    IsLeast {n : ℕ | 0 < n ∧ IsPrimRootMod 7 n} 3 ∧
    IsLeast {n : ℕ | 0 < n ∧ IsPrimRootMod 11 n} 2 ∧
    IsLeast {n : ℕ | 0 < n ∧ IsPrimRootMod 23 n} 5 ∧
    IsLeast {n : ℕ | 0 < n ∧ IsPrimRootMod 47 n} 5

/-- (a) The least positive quadratic non-residue modulo an odd prime is prime. -/
def classical_Prime6_a : Prop := ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ)
    (hn : IsLeast {m : ℕ | 0 < m ∧ IsQNR p m} n),
    n.Prime

/-- Well-formedness for (a): a positive non-residue exists for odd `p`. -/
def classical_Prime6_a_obligation : Prop := ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2),
    ∃ n : ℕ, IsLeast {m : ℕ | 0 < m ∧ IsQNR p m} n

/-- (b) For a safe prime, least positive primitive root = least positive non-residue. -/
def classical_Prime6_b : Prop := ∀ (p : ℕ) (hp : IsSafePrime p) (g : ℕ),
    IsLeast {n : ℕ | 0 < n ∧ IsPrimRootMod p n} g ↔
      IsLeast {m : ℕ | 0 < m ∧ IsQNR p m} g

/-- (b), auxiliary claim used: the least non-residue of a safe prime is `< p - 1`. -/
def classical_Prime6_b_aux : Prop := ∀ (p : ℕ) (hp : IsSafePrime p) (n : ℕ)
    (hn : IsLeast {m : ℕ | 0 < m ∧ IsQNR p m} n),
    n < p - 1


/-! ############## L15 comparison proofs ############## -/

open PrimitiveRootFamilies

local instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance fact_prime_11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance fact_prime_19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩
local instance fact_prime_23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩
local instance fact_prime_47 : Fact (Nat.Prime 47) := ⟨by norm_num⟩

lemma neg_one_sq_five : IsSquare ((-1 : ℤ) : ZMod 5) := ⟨2, by decide⟩

lemma zmod_ne_zero_of_not_dvd {p : ℕ} {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : (a : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-! Prime1 (Mathlib background; the paper uses `legendreSym.eq_pow`). -/

theorem cov_Prime1_a : classical_Prime1_a := by
  intro p _ hp2 a ha
  have hodd := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow, legendreSym.eq_pow,
    show (p - 1) / 2 = p / 2 by omega]

theorem cov_Prime1_b : classical_Prime1_b := by
  intro p _ hp2 a ha
  have h0 := zmod_ne_zero_of_not_dvd ha
  have hodd := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow, Int.cast_one,
    show (p - 1) / 2 = p / 2 by omega, ← ZMod.euler_criterion p h0]
  exact ⟨fun h => h.2, fun h => ⟨h0, h⟩⟩

theorem cov_Prime1_c : classical_Prime1_c := by
  intro p _ hp2 a ha
  have hp := (Fact.out : p.Prime)
  have h0 := zmod_ne_zero_of_not_dvd ha
  have hodd := hp.eq_two_or_odd.resolve_left hp2
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow, Int.cast_neg, Int.cast_one,
    show (p - 1) / 2 = p / 2 by omega]
  have he := ZMod.euler_criterion p h0
  constructor
  · rintro ⟨-, hns⟩
    exact (ZMod.pow_div_two_eq_neg_one_or_one p h0).resolve_left (fun h => hns (he.mpr h))
  · intro h
    refine ⟨h0, fun hs => ZMod.neg_one_ne_one (n := p) ?_⟩
    rw [← h, he.mp hs]

/-! Prime2 (Mathlib background: `orderOf_eq_of_pow_and_pow_div_prime`). -/

theorem cov_Prime2_a : classical_Prime2_a := by
  intro p hp g hg
  have := Fact.mk hp
  have h0 := zmod_ne_zero_of_not_dvd hg
  have hp2 := hp.two_le
  have key : ∀ r : ℕ, (g ^ ((p - 1) / r) ≡ 1 [ZMOD p] ↔ (g : ZMod p) ^ ((p - 1) / r) = 1) :=
    fun r => by rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow, Int.cast_one]
  simp only [key]
  constructor
  · intro h r hr hrd
    apply h.pow_ne_one_of_pos_of_lt
    · exact (Nat.div_pos (Nat.le_of_dvd (by omega) hrd) hr.pos).ne'
    · exact Nat.div_lt_self (by omega) hr.one_lt
  · intro h
    show IsPrimitiveRoot _ _
    rw [IsPrimitiveRoot.iff_orderOf]
    exact orderOf_eq_of_pow_and_pow_div_prime (by omega) (ZMod.pow_card_sub_one_eq_one h0) h

lemma pr_pow_half {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {g : ℤ} (hg : IsPrimRootMod p g) :
    (g : ZMod p) ≠ 0 ∧ (g : ZMod p) ^ (p / 2) = -1 := by
  have hp := (Fact.out : p.Prime)
  have hodd := hp.eq_two_or_odd.resolve_left hp2
  have h3 := hp.two_le
  have h0 : (g : ZMod p) ≠ 0 := hg.ne_zero (by omega)
  exact ⟨h0, (ZMod.pow_div_two_eq_neg_one_or_one p h0).resolve_left
    (hg.pow_ne_one_of_pos_of_lt (by omega) (by omega))⟩

theorem cov_Prime2_b : classical_Prime2_b := by
  intro p _ hp2 g hg
  obtain ⟨h0, h⟩ := pr_pow_half hp2 hg
  have hp := (Fact.out : p.Prime)
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  rcases legendreSym.eq_one_or_neg_one p h0 with h1 | h1
  · exfalso
    have e := legendreSym.eq_pow p g
    rw [h1, h, Int.cast_one] at e
    exact ZMod.neg_one_ne_one e.symm
  · exact h1

theorem cov_Prime2_c : classical_Prime2_c := by
  intro p _ hp2 g hg
  obtain ⟨-, h⟩ := pr_pow_half hp2 hg
  have hodd := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow, Int.cast_neg, Int.cast_one,
    show (p - 1) / 2 = p / 2 by omega, h]

theorem cov_Prime2_d : classical_Prime2_d := by
  intro p hp hp2 a ha hpr
  have := Fact.mk hp
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  obtain ⟨h0, h⟩ := pr_pow_half hp2 hpr
  have h1 := (ZMod.euler_criterion p h0).mp ha.2
  rw [h] at h1
  exact ZMod.neg_one_ne_one h1

/-! Prime3 -/

theorem cov_Prime3_a : classical_Prime3_a := by
  intro p _ k hk hpk a ha
  have hp := (Fact.out : p.Prime)
  have h0 := zmod_ne_zero_of_not_dvd ha
  have h2k : 2 ≤ 2 ^ k :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hp2 : p ≠ 2 := by omega
  have hodd := hp.eq_two_or_odd.resolve_left hp2
  have : Fact (2 < p) := ⟨by omega⟩
  constructor
  · exact fun h => cov_Prime2_b p hp2 a h
  · intro hL
    show IsPrimitiveRoot _ _
    rw [IsPrimitiveRoot.iff_orderOf]
    refine orderOf_eq_of_pow_and_pow_div_prime (by omega) (ZMod.pow_card_sub_one_eq_one h0) ?_
    intro r hr hrd
    rw [hpk] at hrd
    have hr2 : r = 2 :=
      (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hrd)
    rw [hr2, show (p - 1) / 2 = p / 2 by omega, ← legendreSym.eq_pow, hL, Int.cast_neg,
      Int.cast_one]
    exact ZMod.neg_one_ne_one

theorem cov_Prime3_b : classical_Prime3_b := by
  intro p q _ hq hpq a ha
  have h0 := zmod_ne_zero_of_not_dvd ha
  have hm : (a ≡ -1 [ZMOD p]) ↔ (a : ZMod p) = -1 := by
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_neg, Int.cast_one]
  rw [hm]
  rcases eq_or_ne q 2 with rfl | hq2
  · obtain rfl : p = 5 := by omega
    rw [cov_Prime3_a 5 2 (by norm_num) (by norm_num) a ha]
    constructor
    · intro hL
      refine ⟨hL, fun he => ?_⟩
      have h1 : legendreSym 5 a = 1 :=
        (legendreSym.eq_one_iff 5 h0).mpr (by rw [he]; exact neg_one_sq_five)
      rw [hL] at h1
      norm_num at h1
    · exact fun h => h.1
  · show IsPrimitiveRoot _ _ ↔ _
    rw [isPrimitiveRoot_iff_of_eq_two_mul_add_one' hq hq2 hpq h0]
    constructor
    · rintro ⟨hL, hsq⟩
      exact ⟨hL, fun he => hsq (by rw [he]; ring)⟩
    · rintro ⟨hL, hne⟩
      refine ⟨hL, fun hsq => ?_⟩
      rcases mul_self_eq_one_iff.mp (by rw [← sq]; exact hsq : (a : ZMod p) * (a : ZMod p) = 1) with h1 | h1
      · have : legendreSym p a = 1 :=
          (legendreSym.eq_one_iff p h0).mpr (by rw [h1]; exact ⟨1, (one_mul 1).symm⟩)
        rw [hL] at this
        norm_num at this
      · exact hne h1

theorem cov_Prime3_b_remark5 : classical_Prime3_b_remark5 :=
  ⟨by decide, neg_one_sq_five⟩

theorem cov_Prime3_b_remark7 : classical_Prime3_b_remark7 := by
  intro p q _ hq hpq h7
  have hq2 : q ≠ 2 := by omega
  have hodd := hq.eq_two_or_odd.resolve_left hq2
  refine ⟨?_, ?_⟩
  · rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_three_mod_four (by omega)]
  · rw [Int.cast_neg, Int.cast_one, orderOf_neg_one, ZMod.ringChar_zmod_n, if_neg (by omega)]

/-- Prime3(c) restricted to `l = 1` (the paper's Theorem 5.1 / Corollary 5.2). -/
def classical_Prime3_c_l1 : Prop := ∀ (p q k : ℕ) [Fact p.Prime] (hq : q.Prime) (hq2 : q ≠ 2)
    (hk : 1 ≤ k) (hpq : p = 2 ^ k * q ^ 1 + 1)
    (a : ℤ) (ha : legendreSym p a = -1) (ha2 : ¬ a ^ (2 ^ k) ≡ 1 [ZMOD p]),
    IsPrimRootMod p a

theorem cov_Prime3_c_part : classical_Prime3_c_l1 := by
  intro p q k _ hq hq2 hk hpq a ha ha2
  have h0 : (a : ZMod p) ≠ 0 := fun h => by
    rw [(legendreSym.eq_zero_iff p a).mpr h] at ha; norm_num at ha
  rw [pow_one] at hpq
  refine (isPrimitiveRoot_iff_of_eq_two_pow_mul_add_one hq hq2 hk hpq h0).mpr ⟨ha, fun h => ha2 ?_⟩
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow, Int.cast_one]; exact h

-- The writer's statement `classical_Prime3_c` is false as written (counterexample below).
/-- Prime3(c) as written is FALSE for `l ≥ 2`: `p = 19 = 2·3² + 1`, `a = 8`. -/
theorem not_classical_Prime3_c : ¬ classical_Prime3_c := by
  intro h
  have hL : legendreSym 19 8 = -1 := by
    have e := legendreSym.eq_pow 19 8
    rcases legendreSym.eq_one_or_neg_one 19 (a := 8) (by decide) with h1 | h1
    · rw [h1] at e; exact absurd e (by decide)
    · exact h1
  have h8 : ¬ (8 : ℤ) ^ (2 ^ 1) ≡ 1 [ZMOD 19] := by decide
  have hpr := h 19 3 1 2 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) 8 hL h8
  exact hpr.pow_ne_one_of_pos_of_lt (l := 6) (by norm_num) (by norm_num) (by decide)

/-- NEW PROOF: corrected Wertheim, exponent `2^k q^(l-1)`. -/
theorem new_Prime3_c_corrected (p q k l : ℕ) [Fact p.Prime] (hq : q.Prime) (hq2 : q ≠ 2)
    (hk : 1 ≤ k) (hl : 1 ≤ l) (hpq : p = 2 ^ k * q ^ l + 1)
    (a : ℤ) (ha : legendreSym p a = -1) (ha2 : ¬ a ^ (2 ^ k * q ^ (l - 1)) ≡ 1 [ZMOD p]) :
    IsPrimRootMod p a := by
  have h0 : (a : ZMod p) ≠ 0 := fun h => by
    rw [(legendreSym.eq_zero_iff p a).mpr h] at ha; norm_num at ha
  have h2k : 2 ≤ 2 ^ k :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hql : 1 ≤ q ^ l := Nat.one_le_pow _ _ hq.pos
  have hN : 2 ≤ 2 ^ k * q ^ l := by
    calc 2 = 2 * 1 := by norm_num
      _ ≤ 2 ^ k * q ^ l := Nat.mul_le_mul h2k hql
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ k * q ^ l = M := ⟨_, rfl⟩
  rw [hM] at hpq hN
  have hp1 : p - 1 = M := by omega
  have : Fact (2 < p) := ⟨by omega⟩
  have hodd := (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by omega)
  show IsPrimitiveRoot _ _
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_of_pow_and_pow_div_prime (by omega) (ZMod.pow_card_sub_one_eq_one h0) ?_
  intro r hr hrd
  rw [hp1] at hrd ⊢
  rw [← hM] at hrd
  rcases (Nat.Prime.dvd_mul hr).mp hrd with h | h
  · have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
    rw [this, show M / 2 = p / 2 by omega, ← legendreSym.eq_pow, ha, Int.cast_neg, Int.cast_one]
    exact ZMod.neg_one_ne_one
  · have : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h)
    have e : M / q = 2 ^ k * q ^ (l - 1) := by
      rw [← hM]
      obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      rw [pow_succ, ← mul_assoc, Nat.mul_div_cancel _ hq.pos]; simp
    rw [this, e]
    intro h1; apply ha2
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow, Int.cast_one]; exact h1

/-! Prime4, Prime5 -/

theorem cov_Prime4 : classical_Prime4 := by
  intro q hq hq2 hp
  have := isPrimitiveRoot_two_of_eq_four_mul_add_one hq hp rfl
  exact_mod_cast this

theorem cov_Prime5_iff : classical_Prime5_iff := by
  intro p hp hq
  have := isPrimitiveRoot_ten_iff_mod_five_eq_two hp hq rfl
  simp only [IsPrimRootMod]
  exact_mod_cast this

theorem cov_Prime5_a : classical_Prime5_a := fun p hp hq h5 => (cov_Prime5_iff p hp hq).mpr h5

theorem cov_Prime5_b : classical_Prime5_b := fun p hp hq h => (cov_Prime5_iff p hp hq).mp h

theorem cov_Prime5_examples : classical_Prime5_examples :=
  ⟨cov_Prime5_a 7 (by norm_num) (by norm_num) (by norm_num),
   cov_Prime5_a 37 (by norm_num) (by norm_num) (by norm_num),
   cov_Prime5_a 67 (by norm_num) (by norm_num) (by norm_num)⟩

theorem cov_Prime5_note : classical_Prime5_note := by
  intro p hp hq
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h
    · exact absurd hq (by norm_num)
    · exact h
  have := hp.two_le
  omega

/-! Prime6 -/

lemma setPR_eq (p : ℕ) : {n : ℕ | 0 < n ∧ IsPrimRootMod p n} =
    {a : ℕ | 0 < a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)} := by
  ext n; simp only [Set.mem_setOf_eq, IsPrimRootMod, Int.cast_natCast]

theorem cov_Prime6 : classical_Prime6 := by
  intro p hp g hg
  obtain ⟨hpp, q, hq, hpq⟩ := hp
  have := Fact.mk hpp
  rw [setPR_eq] at hg
  exact prime_of_isLeast_isPrimitiveRoot hq hpq hg

theorem cov_Prime6_obligation : classical_Prime6_obligation := by
  intro p hp
  have := Fact.mk hp
  rw [setPR_eq]
  exact exists_isLeast_isPrimitiveRoot p

lemma least_ex {p q g : ℕ} [Fact p.Prime] (hq : q.Prime) (hpq : p = 2 * q + 1)
    (hg : 0 < g) (hgp : g < p) (hgood : (g : ZMod p) ^ q ≠ 1 ∧ (g : ZMod p) ^ 2 ≠ 1)
    (hbad : ∀ n, n < g → 0 < n → ((n : ZMod p) ^ q = 1 ∨ (n : ZMod p) ^ 2 = 1)) :
    IsLeast {n : ℕ | 0 < n ∧ IsPrimRootMod p n} g := by
  rw [setPR_eq]
  have nz : ∀ n, 0 < n → n < p → (n : ZMod p) ≠ 0 := fun n h0 hlt => by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd h0 hd) (by omega)
  refine ⟨⟨hg, (isPrimitiveRoot_iff_of_eq_two_mul_add_one hq hpq (nz g hg hgp)).mpr hgood⟩, ?_⟩
  rintro n ⟨hn0, hn⟩
  by_contra hlt
  push Not at hlt
  have h := (isPrimitiveRoot_iff_of_eq_two_mul_add_one hq hpq (nz n hn0 (by omega))).mp hn
  rcases hbad n hlt hn0 with h1 | h1
  · exact h.1 h1
  · exact h.2 h1

theorem cov_Prime6_examples : classical_Prime6_examples := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact least_ex (q := 2) (by norm_num) rfl (by norm_num) (by norm_num) (by decide) (by decide)
  · exact least_ex (q := 3) (by norm_num) rfl (by norm_num) (by norm_num) (by decide) (by decide)
  · exact least_ex (q := 5) (by norm_num) rfl (by norm_num) (by norm_num) (by decide) (by decide)
  · exact least_ex (q := 11) (by norm_num) rfl (by norm_num) (by norm_num) (by decide) (by decide)
  · exact least_ex (q := 23) (by norm_num) rfl (by norm_num) (by norm_num) (by decide) (by decide)

lemma qnr_least_props {p n : ℕ} (hp : p.Prime) (hn : IsLeast {m : ℕ | 0 < m ∧ IsQNR p m} n) :
    0 < n ∧ n < p ∧ (n : ZMod p) ≠ 0 ∧ ¬ IsSquare (n : ZMod p) ∧
      ∀ m : ℕ, 0 < m → m < n → IsSquare (m : ZMod p) := by
  simp only [IsQNR, Int.cast_natCast] at hn
  obtain ⟨⟨hn0, hnz, hns⟩, hlow⟩ := hn
  have hnp : n < p := by
    by_contra h
    push Not at h
    have hpos : 0 < n % p := by
      rcases Nat.eq_zero_or_pos (n % p) with h0 | h0
      · exact absurd ((ZMod.natCast_eq_zero_iff n p).mpr (Nat.dvd_of_mod_eq_zero h0)) hnz
      · exact h0
    have := hlow ⟨hpos, by rwa [ZMod.natCast_mod], by rwa [ZMod.natCast_mod]⟩
    have := Nat.mod_lt n hp.pos
    omega
  refine ⟨hn0, hnp, hnz, hns, fun m hm0 hmn => ?_⟩
  by_contra hms
  have hmz : (m : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hm0 hd) (by omega)
  have := hlow ⟨hm0, hmz, hms⟩
  omega

/-- NEW PROOF (not in the repository): least positive QNR is prime. -/
theorem cov_Prime6_a : classical_Prime6_a := by
  intro p hp hp2 n hn
  obtain ⟨hn0, hnp, hnz, hns, hsq⟩ := qnr_least_props hp hn
  by_contra hnp'
  have h2 : 2 ≤ n := by
    rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | h
    · exact absurd ⟨1, by simp⟩ hns
    · exact h
  obtain ⟨m, ⟨k, rfl⟩, hm2, hmn⟩ := Nat.exists_dvd_of_not_prime2 h2 hnp'
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn0)
  have hkn : k < m * k := by nlinarith
  exact hns (by rw [Nat.cast_mul]; exact (hsq m (by omega) hmn).mul (hsq k hk0 hkn))

theorem cov_Prime6_a_obligation : classical_Prime6_a_obligation := by
  intro p hp hp2
  have := Fact.mk hp
  classical
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have hex : ∃ m : ℕ, 0 < m ∧ IsQNR p m :=
    ⟨a.val, Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero]),
      by simp only [IsQNR, Int.cast_natCast, ZMod.natCast_zmod_val]; exact ⟨ha0, ha⟩⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min' hex hm⟩

/-- NEW PROOF: the auxiliary bound. -/
theorem cov_Prime6_b_aux : classical_Prime6_b_aux := by
  intro p hp n hn
  obtain ⟨hpp, q, hq, hpq⟩ := hp
  obtain ⟨hn0, hnp, hnz, hns, hsq⟩ := qnr_least_props hpp hn
  have hq2 := hq.two_le
  by_contra hge
  have hn' : n = p - 1 := by omega
  apply hns
  have e : n = 2 * q := by omega
  rw [e, Nat.cast_mul]
  exact (hsq 2 (by norm_num) (by omega)).mul (hsq q (by omega) (by omega))

/-- NEW PROOF: least primitive root = least QNR for safe primes. -/
theorem cov_Prime6_b : classical_Prime6_b := by
  intro p hp g
  have hp' := hp
  obtain ⟨hpp, q, hq, hpq⟩ := hp'
  have := Fact.mk hpp
  have hq2 := hq.two_le
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g0, hg0⟩ := cov_Prime6_obligation p hpp
  obtain ⟨n0, hn0⟩ := cov_Prime6_a_obligation p hpp hp2
  have heq : g0 = n0 := by
    apply le_antisymm
    · -- n0 is a primitive root
      obtain ⟨hpos, hnp, hnz, hns, hsq⟩ := qnr_least_props hpp hn0
      have hn1 : 1 < n0 := by
        rcases (by omega : n0 = 1 ∨ 1 < n0) with rfl | h
        · exact absurd ⟨1, by simp⟩ hns
        · exact h
      have hlt := cov_Prime6_b_aux p hp n0 hn0
      have hL : legendreSym p (n0 : ℕ) = -1 := (legendreSym.eq_neg_one_iff' p).mpr hns
      have hpr := isPrimitiveRoot_of_legendreSym_eq_neg_one hq hpq hn1 hlt hL
      exact hg0.2 ⟨hpos, by simpa only [IsPrimRootMod, Int.cast_natCast] using hpr⟩
    · obtain ⟨⟨hpos, hpr⟩, -⟩ := hg0
      obtain ⟨h0, -⟩ := pr_pow_half hp2 hpr
      refine hn0.2 ⟨hpos, h0, fun hs => cov_Prime2_d p hpp hp2 g0 ⟨h0, hs⟩ hpr⟩
  constructor
  · intro hg; rw [hg.unique hg0, heq]; exact hn0
  · intro hg; rw [hg.unique hn0, ← heq]; exact hg0


/-! Prime5_reptend — NEW PROOF: decimal period of `1/q` equals `orderOf (10 : ZMod q)`. -/

/-- natural-number digit `⌊10^k / q⌋ mod 10`. -/
def ndig (q k : ℕ) : ℕ := 10 ^ k / q % 10

lemma decimalDigit_inv (q k : ℕ) : decimalDigit (1 / (q : ℝ)) k = (ndig q k : ℤ) := by
  unfold decimalDigit ndig
  have h1 : (10 : ℝ) ^ k * (1 / (q : ℝ)) = (((10 ^ k : ℕ) : ℤ) : ℝ) / (q : ℕ) := by
    push_cast; ring
  rw [h1, Int.floor_div_natCast, Int.floor_intCast]
  push_cast
  rfl

lemma ndig_succ (q k : ℕ) (hq : 0 < q) : ndig q (k + 1) = 10 * (10 ^ k % q) / q := by
  unfold ndig
  have hlt : 10 * (10 ^ k % q) / q < 10 := by
    rw [Nat.div_lt_iff_lt_mul hq]
    exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hq) (by norm_num)
  have e : 10 ^ (k + 1) = q * (10 * (10 ^ k / q)) + 10 * (10 ^ k % q) := by
    rw [pow_succ, mul_comm (10 ^ k) 10]
    conv_lhs => rw [← Nat.div_add_mod (10 ^ k) q]
    ring
  rw [e, Nat.mul_add_div hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

lemma rem_succ (q k : ℕ) (hq : 0 < q) :
    ((10 ^ (k + 1) % q : ℕ) : ℤ) = 10 * ((10 ^ k % q : ℕ) : ℤ) - q * (ndig q (k + 1) : ℤ) := by
  have e : 10 ^ (k + 1) = q * (10 * (10 ^ k / q)) + 10 * (10 ^ k % q) := by
    rw [pow_succ, mul_comm (10 ^ k) 10]
    conv_lhs => rw [← Nat.div_add_mod (10 ^ k) q]
    ring
  rw [ndig_succ q k hq, e, Nat.mul_add_mod]
  have := Nat.div_add_mod (10 * (10 ^ k % q)) q
  omega

lemma ndig_periodic_iff (q n : ℕ) (hq : 2 ≤ q) :
    (∀ k : ℕ, 1 ≤ k → ndig q (k + n) = ndig q k) ↔ 10 ^ n % q = 1 := by
  have hq0 : 0 < q := by omega
  constructor
  · intro h
    let e : ℕ → ℤ := fun m => ((10 ^ (m + n) % q : ℕ) : ℤ) - ((10 ^ m % q : ℕ) : ℤ)
    have he : ∀ m, e m = 10 ^ m * e 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hd : ndig q (m + n + 1) = ndig q (m + 1) := by
          rw [show m + n + 1 = (m + 1) + n by ring]; exact h (m + 1) (by omega)
        have r1 := rem_succ q (m + n) hq0
        have r2 := rem_succ q m hq0
        show ((10 ^ (m + 1 + n) % q : ℕ) : ℤ) - ((10 ^ (m + 1) % q : ℕ) : ℤ) = _
        rw [show m + 1 + n = m + n + 1 by ring, r1, r2, hd, pow_succ]
        have : e m = ((10 ^ (m + n) % q : ℕ) : ℤ) - ((10 ^ m % q : ℕ) : ℤ) := rfl
        linear_combination (-10) * this + 10 * ih
    have hb : ∀ m, |e m| < q := by
      intro m
      have h1 := Nat.mod_lt (10 ^ (m + n)) hq0
      have h2 := Nat.mod_lt (10 ^ m) hq0
      rw [abs_lt]; constructor <;> simp only [e] <;> omega
    have h0 : e 0 = 0 := by
      by_contra hne
      have hpos : 1 ≤ |e 0| := Int.one_le_abs hne
      have hq' : (q : ℤ) < 10 ^ q := by exact_mod_cast Nat.lt_pow_self (by norm_num)
      have := hb q
      rw [he q, abs_mul, abs_of_pos (by positivity)] at this
      nlinarith
    simp only [e, zero_add, pow_zero, Nat.one_mod_eq_one.mpr (by omega : q ≠ 1)] at h0
    omega
  · intro h k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show j + 1 + n = (j + n) + 1 by ring, ndig_succ q _ hq0, ndig_succ q _ hq0, pow_add,
      Nat.mul_mod, h, mul_one, Nat.mod_mod]

lemma decimalPeriod_eq_orderOf (q : ℕ) [Fact q.Prime] (h10 : (10 : ZMod q) ≠ 0) :
    decimalPeriod (1 / (q : ℝ)) = orderOf (10 : ZMod q) := by
  have hq2 := (Fact.out : q.Prime).two_le
  have key : ∀ n, (10 : ZMod q) ^ n = 1 ↔ 10 ^ n % q = 1 := by
    intro n
    rw [show (10 : ZMod q) ^ n = ((10 ^ n : ℕ) : ZMod q) by push_cast; rfl,
      show (1 : ZMod q) = ((1 : ℕ) : ZMod q) by simp, ZMod.natCast_eq_natCast_iff, Nat.ModEq,
      Nat.one_mod_eq_one.mpr (by omega : q ≠ 1)]
  have hS : {n : ℕ | 0 < n ∧ ∀ k : ℕ, 1 ≤ k →
      decimalDigit (1 / (q : ℝ)) (k + n) = decimalDigit (1 / (q : ℝ)) k} =
      {n : ℕ | 0 < n ∧ (10 : ZMod q) ^ n = 1} := by
    ext n
    simp only [Set.mem_setOf_eq, decimalDigit_inv, Nat.cast_inj, key]
    rw [ndig_periodic_iff q n hq2]
  unfold decimalPeriod
  rw [hS]
  have hF := ZMod.pow_card_sub_one_eq_one h10
  have hfin : IsOfFinOrder (10 : ZMod q) := isOfFinOrder_iff_pow_eq_one.mpr ⟨q - 1, by omega, hF⟩
  apply le_antisymm
  · exact Nat.sInf_le ⟨hfin.orderOf_pos, pow_orderOf_eq_one _⟩
  · have hne : ({n : ℕ | 0 < n ∧ (10 : ZMod q) ^ n = 1} : Set ℕ).Nonempty := ⟨q - 1, by omega, hF⟩
    have hm := Nat.sInf_mem hne
    exact orderOf_le_of_pow_eq_one hm.1 hm.2

theorem cov_Prime5_reptend : classical_Prime5_reptend := by
  intro p hp hq
  have := Fact.mk hq
  have hodd := (cov_Prime5_note p hp hq).1
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have h10 : (10 : ZMod (4 * p + 1)) ≠ 0 := by
    intro h0
    have h : ((10 : ℕ) : ZMod (4 * p + 1)) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  rw [decimalPeriod_eq_orderOf _ h10]
  show IsPrimitiveRoot _ _ ↔ _
  rw [IsPrimitiveRoot.iff_orderOf]
  simp

end PrimitiveRootFamilies.Classical
