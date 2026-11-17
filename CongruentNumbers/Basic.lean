module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Congruent numbers

This file formalizes the milestone *Congruent numbers* of the plan
<https://github.com/FormalCommons/congruent-numbers-plan/blob/main/atlas/congruent-numbers.md>.

## Main definitions

* `CongruentNumbers.IsCongruent n`: the rational number `n` is the area of a right triangle
  with positive rational sides.

## Main results

* `CongruentNumbers.isCongruent_mul_sq_iff`: `n` is congruent if and only if `q ^ 2 * n` is,
  for every nonzero rational `q`.
* `CongruentNumbers.isCongruent_five`, `CongruentNumbers.isCongruent_six`,
  `CongruentNumbers.isCongruent_seven`: `5`, `6` and `7` are congruent.

## References

* [N. Koblitz, *Introduction to Elliptic Curves and Modular Forms*, §I.1][Koblitz1993]
* [K. Conrad, *The congruent number problem*, §1][Conrad2008]
-/

@[expose] public section

namespace CongruentNumbers

/-- A rational number `n` is *congruent* if it is the area of a right triangle with positive
rational sides: there are positive rationals `a`, `b`, `c` with `a ^ 2 + b ^ 2 = c ^ 2` and
`a * b / 2 = n`. Such an `n` is necessarily positive (see `IsCongruent.pos`). -/
def IsCongruent (n : ℚ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n

/-- A congruent number is positive. -/
theorem IsCongruent.pos {n : ℚ} (h : IsCongruent n) : 0 < n := by
  obtain ⟨a, b, c, ha, hb, -, -, rfl⟩ := h
  positivity

/-- Scaling a right triangle of area `n` by `|q|` gives a right triangle of area `q ^ 2 * n`. -/
theorem IsCongruent.mul_sq {n : ℚ} (h : IsCongruent n) {q : ℚ} (hq : q ≠ 0) :
    IsCongruent (q ^ 2 * n) := by
  obtain ⟨a, b, c, ha, hb, hc, habc, rfl⟩ := h
  have hq' : 0 < |q| := abs_pos.mpr hq
  refine ⟨|q| * a, |q| * b, |q| * c, by positivity, by positivity, by positivity, ?_, ?_⟩
  · simp only [mul_pow, ← habc]
    ring
  · rw [← sq_abs q]
    ring

/-- **Congruent numbers**, part (1): `n` is congruent if and only if `q ^ 2 * n` is congruent,
for every nonzero rational `q`.

This is the milestone *Congruent numbers* (part 1). -/
theorem isCongruent_mul_sq_iff {n q : ℚ} (hq : q ≠ 0) :
    IsCongruent n ↔ IsCongruent (q ^ 2 * n) := by
  refine ⟨fun h => h.mul_sq hq, fun h => ?_⟩
  have := h.mul_sq (inv_ne_zero hq)
  rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hq, one_pow, one_mul] at this

/-- **Congruent numbers**, part (2): `5` is congruent, as the area of the right triangle
`(3/2, 20/3, 41/6)`.

This is the milestone *Congruent numbers* (part 2). -/
theorem isCongruent_five : IsCongruent 5 :=
  ⟨3 / 2, 20 / 3, 41 / 6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Congruent numbers**, part (2): `6` is congruent, as the area of the right triangle
`(3, 4, 5)`.

This is the milestone *Congruent numbers* (part 2). -/
theorem isCongruent_six : IsCongruent 6 :=
  ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Congruent numbers**, part (2): `7` is congruent, as the area of the right triangle
`(24/5, 35/12, 337/60)`.

This is the milestone *Congruent numbers* (part 2). -/
theorem isCongruent_seven : IsCongruent 7 :=
  ⟨24 / 5, 35 / 12, 337 / 60, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end CongruentNumbers

end
