module

public import CongruentNumbers.Basic
public import CongruentNumbers.Curve
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Right triangles and points of `E_n`

This file formalizes the milestone *Right triangles and points of E_n* of the plan
<https://github.com/FormalCommons/congruent-numbers-plan/blob/main/atlas/congruent-numbers.md>.

For a nonzero rational `n`, the maps
`(a, b, c) ↦ (n b / (c - a), 2 n² / (c - a))` and
`(x, y) ↦ ((x² - n²) / y, 2 n x / y, (x² + n²) / y)`
are inverse bijections between the rational solutions of `a² + b² = c²`, `a b / 2 = n` (with no
sign conditions) and the rational solutions of `y² = x³ - n² x` with `y ≠ 0`. Consequently, a
positive rational `n` is congruent if and only if `E_n(ℚ)` has a point with `y ≠ 0`.

## Main definitions

* `CongruentNumbers.triangleEquiv`: the bijection between the two sets of solutions.

## Main results

* `CongruentNumbers.isCongruent_iff_exists_sq_eq`: `n > 0` is congruent if and only if
  `y² = x³ - n² x` has a rational solution with `y ≠ 0`.
* `CongruentNumbers.isCongruent_iff_exists_nonsingular`: the same with the nonsingular points
  `WeierstrassCurve.Affine.Point.some x y h` of `E_n = CongruentNumbers.curve n` over `ℚ`.
* `CongruentNumbers.isCongruent_iff_exists_two_nsmul_ne_zero`: `n > 0` is congruent if and only
  if `E_n(ℚ)` has a point that is not of order dividing two.

## References

* [K. Conrad, *The congruent number problem*, Theorem 4.1][Conrad2008]
-/

@[expose] public section

open WeierstrassCurve

namespace CongruentNumbers

variable {n : ℚ}

/-- If `a² + b² = c²` and `a b / 2 = n ≠ 0`, then `c - a ≠ 0`. -/
theorem sub_ne_zero_of_triangle (hn : n ≠ 0) {a b c : ℚ} (h₁ : a ^ 2 + b ^ 2 = c ^ 2)
    (h₂ : a * b / 2 = n) : c - a ≠ 0 := by
  intro h
  have hb : b ^ 2 = 0 := by
    have hc : c = a := by linear_combination h
    subst hc
    linear_combination h₁
  have : b = 0 := pow_eq_zero_iff two_ne_zero |>.mp hb
  subst this
  exact hn (by rw [← h₂]; ring)

/-- **Right triangles and points of E_n**: for `n ≠ 0`, the maps
`(a, b, c) ↦ (n b / (c - a), 2 n² / (c - a))` and
`(x, y) ↦ ((x² - n²) / y, 2 n x / y, (x² + n²) / y)` are inverse bijections between the rational
solutions of `a² + b² = c²`, `a b / 2 = n` (with no sign conditions) and the rational solutions of
`y² = x³ - n² x` with `y ≠ 0`.

This is the milestone *Right triangles and points of E_n* (the bijection), stated for every
nonzero `n`, which includes the plan's case of positive `n`. -/
def triangleEquiv (hn : n ≠ 0) :
    {t : ℚ × ℚ × ℚ // t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2 ∧ t.1 * t.2.1 / 2 = n} ≃
      {p : ℚ × ℚ // p.2 ^ 2 = p.1 ^ 3 - n ^ 2 * p.1 ∧ p.2 ≠ 0} where
  toFun t := ⟨(n * t.1.2.1 / (t.1.2.2 - t.1.1), 2 * n ^ 2 / (t.1.2.2 - t.1.1)), by
    obtain ⟨⟨a, b, c⟩, h₁, h₂⟩ := t
    dsimp only at h₁ h₂ ⊢
    have hd := sub_ne_zero_of_triangle hn h₁ h₂
    refine ⟨?_, div_ne_zero (by positivity) hd⟩
    subst h₂
    field_simp
    linear_combination (-a ^ 3 * b ^ 4) * h₁⟩
  invFun p := ⟨((p.1.1 ^ 2 - n ^ 2) / p.1.2, 2 * n * p.1.1 / p.1.2, (p.1.1 ^ 2 + n ^ 2) / p.1.2), by
    obtain ⟨⟨x, y⟩, h, hy⟩ := p
    dsimp only at h hy ⊢
    refine ⟨?_, ?_⟩
    · field_simp
      ring
    · rw [div_eq_iff two_ne_zero, div_mul_div_comm, div_eq_iff (by positivity)]
      linear_combination (-2 * n) * h⟩
  left_inv t := by
    obtain ⟨⟨a, b, c⟩, h₁, h₂⟩ := t
    dsimp only at h₁ h₂
    have hd := sub_ne_zero_of_triangle hn h₁ h₂
    have hab : a * b ≠ 0 := fun h ↦ hn (by rw [← h₂, h, zero_div])
    subst h₂
    refine Subtype.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> dsimp only <;> field_simp
    · rw [mul_div_cancel_left₀ _ hab]
      linear_combination h₁
    · exact mul_div_cancel_left₀ b (left_ne_zero_of_mul hab)
    · rw [mul_div_cancel_left₀ _ hab]
      linear_combination h₁
  right_inv p := by
    obtain ⟨⟨x, y⟩, h, hy⟩ := p
    dsimp only at h hy
    refine Subtype.ext (Prod.ext ?_ ?_) <;> dsimp only <;> field_simp <;> ring

/-- The image of a solution `(a, b, c)` under `triangleEquiv` is `(n b / (c - a), 2 n² / (c - a))`.
-/
@[simp]
theorem triangleEquiv_apply (hn : n ≠ 0) (t) :
    (triangleEquiv hn t : ℚ × ℚ) =
      (n * t.1.2.1 / (t.1.2.2 - t.1.1), 2 * n ^ 2 / (t.1.2.2 - t.1.1)) :=
  rfl

/-- The image of a solution `(x, y)` under the inverse of `triangleEquiv` is
`((x² - n²) / y, 2 n x / y, (x² + n²) / y)`. -/
@[simp]
theorem triangleEquiv_symm_apply (hn : n ≠ 0) (p) :
    ((triangleEquiv hn).symm p : ℚ × ℚ × ℚ) =
      ((p.1.1 ^ 2 - n ^ 2) / p.1.2, 2 * n * p.1.1 / p.1.2, (p.1.1 ^ 2 + n ^ 2) / p.1.2) :=
  rfl

/-- For `n > 0`, `n` is congruent if and only if `a² + b² = c²`, `a b / 2 = n` has a rational
solution, with no sign conditions: replace `(a, b, c)` by `(|a|, |b|, |c|)`. -/
theorem isCongruent_iff_exists_triangle (hn : 0 < n) :
    IsCongruent n ↔ ∃ a b c : ℚ, a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n := by
  refine ⟨fun ⟨a, b, c, _, _, _, h₁, h₂⟩ ↦ ⟨a, b, c, h₁, h₂⟩, fun ⟨a, b, c, h₁, h₂⟩ ↦ ?_⟩
  have hab : a * b ≠ 0 := fun h ↦ hn.ne (by rw [← h₂, h, zero_div])
  have ha : a ≠ 0 := left_ne_zero_of_mul hab
  have hb : b ≠ 0 := right_ne_zero_of_mul hab
  have hc : c ≠ 0 := by
    rintro rfl
    have : 0 < a ^ 2 + b ^ 2 := by positivity
    linarith
  refine ⟨|a|, |b|, |c|, abs_pos.mpr ha, abs_pos.mpr hb, abs_pos.mpr hc, by simpa using h₁, ?_⟩
  rw [← abs_mul, ← abs_two, ← abs_div, h₂, abs_of_pos hn]

/-- **Right triangles and points of E_n**: a positive rational `n` is congruent if and only if
`y² = x³ - n² x` has a rational solution with `y ≠ 0`.

This is the milestone *Right triangles and points of E_n* (the consequence for congruent
numbers). -/
theorem isCongruent_iff_exists_sq_eq (hn : 0 < n) :
    IsCongruent n ↔ ∃ x y : ℚ, y ^ 2 = x ^ 3 - n ^ 2 * x ∧ y ≠ 0 := by
  rw [isCongruent_iff_exists_triangle hn]
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨⟨x, y⟩, hxy⟩ := triangleEquiv hn.ne' ⟨(a, b, c), h⟩
    exact ⟨x, y, hxy⟩
  · rintro ⟨x, y, h⟩
    obtain ⟨⟨a, b, c⟩, habc⟩ := (triangleEquiv hn.ne').symm ⟨(x, y), h⟩
    exact ⟨a, b, c, habc⟩

/-- **Right triangles and points of E_n**: a positive rational `n` is congruent if and only if the
curve `E_n : y² = x³ - n² x` over `ℚ` has a point `WeierstrassCurve.Affine.Point.some x y h` with
`y ≠ 0`.

This is the milestone *Right triangles and points of E_n*, stated with Mathlib's points of
`E_n`. -/
theorem isCongruent_iff_exists_nonsingular (hn : 0 < n) :
    IsCongruent n ↔ ∃ (x y : ℚ) (_ : (curve n).toAffine.Nonsingular x y), y ≠ 0 := by
  have : NeZero n := ⟨hn.ne'⟩
  simp only [isCongruent_iff_exists_sq_eq hn, ← Affine.equation_iff_nonsingular, equation_iff,
    exists_prop]

/-- A positive rational `n` is congruent if and only if `E_n(ℚ)` has a point `P` with `2 • P ≠ 0`,
that is, a point that is neither the point at infinity nor one of the points of order two
`(0, 0)`, `(n, 0)` and `(-n, 0)`. -/
theorem isCongruent_iff_exists_two_nsmul_ne_zero (hn : 0 < n) :
    IsCongruent n ↔ ∃ P : (curve n).toAffine.Point, 2 • P ≠ 0 := by
  have : NeZero n := ⟨hn.ne'⟩
  rw [isCongruent_iff_exists_nonsingular hn]
  constructor
  · rintro ⟨x, y, h, hy⟩
    refine ⟨.some x y h, fun h2 ↦ hy ?_⟩
    rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at h2
    simp only [Affine.negY, curve_a₁, curve_a₃, zero_mul, sub_zero, true_and] at h2
    linear_combination h2 / 2
  · rintro ⟨P, hP⟩
    cases P with
    | zero => exact absurd (nsmul_zero 2) (by rwa [← Affine.Point.zero_def] at hP)
    | some x y h =>
      refine ⟨x, y, h, fun hy ↦ hP ?_⟩
      rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq]
      simp only [Affine.negY, curve_a₁, curve_a₃, zero_mul, sub_zero, true_and, hy, neg_zero]

end CongruentNumbers

end
