module

public import CongruentNumbers.Fermat
public import CongruentNumbers.Triangle
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# `E_1` and `E_2` have rank zero

This file formalizes the milestone *E_1 and E_2 have rank zero* of the plan
<https://github.com/FormalCommons/congruent-numbers-plan/blob/main/atlas/rational-points.md>:
`E_1(ℚ) = {O, (0, 0), (1, 0), (-1, 0)}` and `E_2(ℚ) = {O, (0, 0), (2, 0), (-2, 0)}`, so both
groups have rank zero.

The proof follows the plan's route. Since `1` and `2` are not congruent (*Fermat's right triangle
theorem*), *Right triangles and points of E_n* shows that every point `P` of `E_1(ℚ)` or `E_2(ℚ)`
has `2 • P = 0`, so `P` is the point at infinity or one of the three points with `y = 0`. This
uses neither the torsion subgroup nor the Mordell–Weil theorem.

## Main results

* `CongruentNumbers.eq_of_not_isCongruent`: if a positive rational `n` is not congruent, the
  points of `E_n(ℚ)` are `O`, `(0, 0)`, `(n, 0)` and `(-n, 0)`.
* `CongruentNumbers.finrank_eq_zero_of_not_isCongruent`: then `E_n(ℚ)` has rank zero.
* `CongruentNumbers.points_curve_one`, `CongruentNumbers.finrank_curve_one`: the milestone for
  `E_1`.
* `CongruentNumbers.points_curve_two`, `CongruentNumbers.finrank_curve_two`: the milestone for
  `E_2`.

## References

* [K. Conrad, *The congruent number problem*, §4][Conrad2008]
-/

public section

open WeierstrassCurve

namespace CongruentNumbers

variable {n : ℚ}

/-- If a positive rational `n` is not congruent, then every point `P` of `E_n(ℚ)` has
`2 • P = 0`. -/
theorem two_nsmul_eq_zero_of_not_isCongruent (hn : 0 < n) (h : ¬ IsCongruent n)
    (P : (curve n).toAffine.Point) : 2 • P = 0 := by
  by_contra hP
  exact h ((isCongruent_iff_exists_two_nsmul_ne_zero hn).mpr ⟨P, hP⟩)

/-- If a positive rational `n` is not congruent, then the points of `E_n(ℚ)` are the point at
infinity and `(0, 0)`, `(n, 0)` and `(-n, 0)`. -/
theorem eq_of_not_isCongruent (hn : 0 < n) (h : ¬ IsCongruent n) :
    haveI : NeZero n := ⟨hn.ne'⟩
    (Set.univ : Set (curve n).toAffine.Point) = {0, pointZero n, pointPos n, pointNeg n} := by
  have : NeZero n := ⟨hn.ne'⟩
  classical
  ext P
  simpa [eq_comm] using
    (two_nsmul_eq_zero_iff P).mp (two_nsmul_eq_zero_of_not_isCongruent hn h P)

/-- If a positive rational `n` is not congruent, then `E_n(ℚ)` is finite. -/
theorem finite_of_not_isCongruent (hn : 0 < n) (h : ¬ IsCongruent n) :
    Finite (curve n).toAffine.Point := by
  have : NeZero n := ⟨hn.ne'⟩
  rw [← Set.finite_univ_iff, eq_of_not_isCongruent hn h]
  exact Set.toFinite _

/-- If a positive rational `n` is not congruent, then `E_n(ℚ)` has rank zero. -/
theorem finrank_eq_zero_of_not_isCongruent (hn : 0 < n) (h : ¬ IsCongruent n) :
    Module.finrank ℤ (curve n).toAffine.Point = 0 :=
  have := finite_of_not_isCongruent hn h
  Module.finrank_eq_zero_iff.mpr fun P ↦
    ⟨2, two_ne_zero, by rw [ofNat_zsmul, two_nsmul_eq_zero_of_not_isCongruent hn h P]⟩

/-- **E_1 and E_2 have rank zero**: `E_1(ℚ) = {O, (0, 0), (1, 0), (-1, 0)}`.

This is the milestone *E_1 and E_2 have rank zero* (the points of `E_1`). -/
theorem points_curve_one :
    (Set.univ : Set (curve (1 : ℚ)).toAffine.Point) =
      {0, pointZero 1, pointPos 1, pointNeg 1} :=
  eq_of_not_isCongruent one_pos not_isCongruent_one

/-- **E_1 and E_2 have rank zero**: `E_2(ℚ) = {O, (0, 0), (2, 0), (-2, 0)}`.

This is the milestone *E_1 and E_2 have rank zero* (the points of `E_2`). -/
theorem points_curve_two :
    (Set.univ : Set (curve (2 : ℚ)).toAffine.Point) =
      {0, pointZero 2, pointPos 2, pointNeg 2} :=
  eq_of_not_isCongruent two_pos not_isCongruent_two

/-- **E_1 and E_2 have rank zero**: `E_1(ℚ)` has rank zero.

This is the milestone *E_1 and E_2 have rank zero* (the rank of `E_1`). -/
theorem finrank_curve_one : Module.finrank ℤ (curve (1 : ℚ)).toAffine.Point = 0 :=
  finrank_eq_zero_of_not_isCongruent one_pos not_isCongruent_one

/-- **E_1 and E_2 have rank zero**: `E_2(ℚ)` has rank zero.

This is the milestone *E_1 and E_2 have rank zero* (the rank of `E_2`). -/
theorem finrank_curve_two : Module.finrank ℤ (curve (2 : ℚ)).toAffine.Point = 0 :=
  finrank_eq_zero_of_not_isCongruent two_pos not_isCongruent_two

/-- `E_1(ℚ)` is finite. -/
instance : Finite (curve (1 : ℚ)).toAffine.Point :=
  finite_of_not_isCongruent one_pos not_isCongruent_one

/-- `E_2(ℚ)` is finite. -/
instance : Finite (curve (2 : ℚ)).toAffine.Point :=
  finite_of_not_isCongruent two_pos not_isCongruent_two

end CongruentNumbers

end
