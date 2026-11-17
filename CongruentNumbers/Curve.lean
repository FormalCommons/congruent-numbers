module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The curves `E_n : y² = x³ - n² x`

For an element `n` of a commutative ring `R`, the curve `E_n : y² = x³ - n² x` is the Weierstrass
curve `⟨0, 0, 0, -n², 0⟩`. Its discriminant is `64 n⁶ = (2 n)⁶`, so it is an elliptic curve
whenever `2 n` is a unit, in particular over a field of characteristic other than two with
`n ≠ 0`. Over such a field its points of order two are the three points `(0, 0)`, `(n, 0)` and
`(-n, 0)` on the line `y = 0`.

This follows Tau Ceti's `TauCeti.CurveX3SubX`, which treats the case `n = 1`.

## Main definitions

* `CongruentNumbers.curve`: the Weierstrass curve `E_n : y² = x³ - n² x`.
* `CongruentNumbers.pointZero`, `CongruentNumbers.pointPos`, `CongruentNumbers.pointNeg`: the
  points `(0, 0)`, `(n, 0)` and `(-n, 0)` of `E_n`.

## Main results

* `CongruentNumbers.Δ_curve`: the discriminant of `E_n` is `64 n⁶`.
* `CongruentNumbers.isElliptic_curve`: `E_n` is elliptic when `2 n` is a unit.
* `CongruentNumbers.map_curve`, `CongruentNumbers.baseChange_curve`,
  `CongruentNumbers.map_curve_intCast`: base change of `E_n`.
* `CongruentNumbers.nonsingular_zero_iff`: the nonsingular affine points of `E_n` with `y = 0` are
  `(0, 0)`, `(n, 0)` and `(-n, 0)`.
* `CongruentNumbers.neg_eq_self_iff`, `CongruentNumbers.two_nsmul_eq_zero_iff`,
  `CongruentNumbers.two_nsmul_eq_zero_iff_of_ne_zero`: the points of order two of `E_n` are
  `(0, 0)`, `(n, 0)` and `(-n, 0)`.
-/

public section

open WeierstrassCurve

namespace CongruentNumbers

section CommRing

variable {R : Type*} [CommRing R]

/-- The Weierstrass curve `E_n : y² = x³ - n² x`. -/
def curve (n : R) : WeierstrassCurve R := ⟨0, 0, 0, -n ^ 2, 0⟩

variable (n : R)

/-- The coefficient `a₁` of `E_n` is `0`. -/
@[simp]
theorem curve_a₁ : (curve n).a₁ = 0 :=
  (rfl)

/-- The coefficient `a₂` of `E_n` is `0`. -/
@[simp]
theorem curve_a₂ : (curve n).a₂ = 0 :=
  (rfl)

/-- The coefficient `a₃` of `E_n` is `0`. -/
@[simp]
theorem curve_a₃ : (curve n).a₃ = 0 :=
  (rfl)

/-- The coefficient `a₄` of `E_n` is `-n²`. -/
@[simp]
theorem curve_a₄ : (curve n).a₄ = -n ^ 2 :=
  (rfl)

/-- The coefficient `a₆` of `E_n` is `0`. -/
@[simp]
theorem curve_a₆ : (curve n).a₆ = 0 :=
  (rfl)

/-- The discriminant of `E_n` is `64 n⁶`. -/
@[simp]
theorem Δ_curve : (curve n).Δ = 64 * n ^ 6 := by
  simp only [Δ, b₂, b₄, b₆, b₈, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  ring

/-- `E_n` is an elliptic curve when `2 n` is a unit, since its discriminant is `(2 n)⁶`. -/
theorem isElliptic_curve (h : IsUnit (2 * n)) : (curve n).IsElliptic := by
  rw [isElliptic_iff, Δ_curve]
  convert h.pow 6 using 1
  ring

/-- `E_n` is preserved by ring homomorphisms: the image of `E_n` under `f` is `E_{f n}`. -/
@[simp]
theorem map_curve {S : Type*} [CommRing S] (f : R →+* S) : (curve n).map f = curve (f n) := by
  ext <;> simp

/-- The base change of `E_n` to an `R`-algebra `S` is `E_n` for the image of `n` in `S`. -/
@[simp]
theorem baseChange_curve (S : Type*) [CommRing S] [Algebra R S] :
    (curve n).baseChange S = curve (algebraMap R S n) :=
  map_curve n _

/-- The curve `E_n` for an integer `n`, base changed to any ring `S` (such as `ℚ` or `ZMod p`), is
`E_n` for the image of `n` in `S`. -/
@[simp]
theorem map_curve_intCast (n : ℤ) (S : Type*) [CommRing S] :
    (curve n).map (Int.castRingHom S) = curve (n : S) :=
  map_curve n _

/-- The affine points of `E_n` are the solutions of `y² = x³ - n² x`. -/
theorem equation_iff (x y : R) : (curve n).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  rw [Affine.equation_iff]
  simp only [curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  constructor <;> intro h <;> linear_combination h

/-- The point `(x, 0)` lies on `E_n` if and only if `x` is a root of `x³ - n² x`, that is, one of
`0`, `n` and `-n`. -/
theorem equation_zero_iff [IsDomain R] (x : R) :
    (curve n).toAffine.Equation x 0 ↔ x = 0 ∨ x = n ∨ x = -n := by
  rw [equation_iff]
  constructor
  · intro h
    have h' : x * ((x - n) * (x + n)) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h' with h | h
    · exact .inl h
    rcases mul_eq_zero.mp h with h | h
    · exact .inr (.inl (by linear_combination h))
    · exact .inr (.inr (by linear_combination h))
  · rintro (rfl | rfl | rfl) <;> ring

end CommRing

section Field

variable {K : Type*} [Field K]

/-- Over a field of characteristic other than two, `E_n` with `n ≠ 0` is an elliptic curve. -/
instance [NeZero (2 : K)] (n : K) [NeZero n] : (curve n).IsElliptic :=
  isElliptic_curve n (mul_ne_zero (NeZero.ne 2) (NeZero.ne n)).isUnit

variable (n : K) [NeZero (2 : K)] [NeZero n]

/-- Over a field of characteristic other than two with `n ≠ 0`, the nonsingular affine points of
`E_n` with `y = 0` are exactly `(0, 0)`, `(n, 0)` and `(-n, 0)`. -/
theorem nonsingular_zero_iff (x : K) :
    (curve n).toAffine.Nonsingular x 0 ↔ x = 0 ∨ x = n ∨ x = -n := by
  rw [← Affine.equation_iff_nonsingular, equation_zero_iff]

/-- The point `(0, 0)` of `E_n`. -/
def pointZero : (curve n).toAffine.Point :=
  .mk ((equation_zero_iff n 0).mpr (.inl rfl))

/-- The point `(n, 0)` of `E_n`. -/
def pointPos : (curve n).toAffine.Point :=
  .mk ((equation_zero_iff n n).mpr (.inr (.inl rfl)))

/-- The point `(-n, 0)` of `E_n`. -/
def pointNeg : (curve n).toAffine.Point :=
  .mk ((equation_zero_iff n (-n)).mpr (.inr (.inr rfl)))

variable {n}

/-- `(0, 0)` is not the point at infinity. -/
@[simp]
theorem pointZero_ne_zero : pointZero n ≠ 0 :=
  Affine.Point.some_ne_zero _

/-- `(n, 0)` is not the point at infinity. -/
@[simp]
theorem pointPos_ne_zero : pointPos n ≠ 0 :=
  Affine.Point.some_ne_zero _

/-- `(-n, 0)` is not the point at infinity. -/
@[simp]
theorem pointNeg_ne_zero : pointNeg n ≠ 0 :=
  Affine.Point.some_ne_zero _

/-- `(0, 0) ≠ (n, 0)`, since `n ≠ 0`. -/
@[simp]
theorem pointZero_ne_pointPos : pointZero n ≠ pointPos n := by
  simp [pointZero, pointPos, Affine.Point.mk, eq_comm (a := (0 : K)), NeZero.ne n]

/-- `(0, 0) ≠ (-n, 0)`, since `n ≠ 0`. -/
@[simp]
theorem pointZero_ne_pointNeg : pointZero n ≠ pointNeg n := by
  simp [pointZero, pointNeg, Affine.Point.mk, eq_comm (a := (0 : K)), NeZero.ne n]

/-- `(n, 0) ≠ (-n, 0)`, since `n ≠ -n` away from characteristic two. -/
@[simp]
theorem pointPos_ne_pointNeg : pointPos n ≠ pointNeg n := by
  have h : n ≠ -n := fun h ↦
    mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne n) (by linear_combination h)
  simp [pointPos, pointNeg, Affine.Point.mk, h]

/-- **The points of order dividing two on `E_n`** are the point at infinity and the three points
`(0, 0)`, `(n, 0)` and `(-n, 0)`. -/
theorem neg_eq_self_iff (P : (curve n).toAffine.Point) :
    -P = P ↔ P = 0 ∨ P = pointZero n ∨ P = pointPos n ∨ P = pointNeg n := by
  cases P with
  | zero => exact ⟨fun _ ↦ .inl rfl, fun _ ↦ rfl⟩
  | some x y h =>
    simp only [Affine.Point.neg_some, Affine.Point.some.injEq, Affine.negY, pointZero, pointPos,
      pointNeg, Affine.Point.mk, curve_a₁, curve_a₃, reduceCtorEq, false_or, true_and]
    constructor
    · intro hy
      have hy0 : y = 0 := by
        have : (2 : K) * y = 0 := by linear_combination -hy
        simpa [NeZero.ne (2 : K)] using this
      subst hy0
      rcases (nonsingular_zero_iff n x).mp h with hx | hx | hx
      · exact .inl ⟨hx, rfl⟩
      · exact .inr (.inl ⟨hx, rfl⟩)
      · exact .inr (.inr ⟨hx, rfl⟩)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring

variable [DecidableEq K]

/-- The points `P` of `E_n` with `2 • P = 0` are the point at infinity and the three points
`(0, 0)`, `(n, 0)` and `(-n, 0)`. -/
theorem two_nsmul_eq_zero_iff (P : (curve n).toAffine.Point) :
    2 • P = 0 ↔ P = 0 ∨ P = pointZero n ∨ P = pointPos n ∨ P = pointNeg n := by
  rw [← neg_eq_self_iff, two_nsmul, add_eq_zero_iff_eq_neg, eq_comm]

/-- **The points of order two on `E_n`**: the points `P ≠ 0` of `E_n` with `2 • P = 0` are exactly
`(0, 0)`, `(n, 0)` and `(-n, 0)`. -/
theorem two_nsmul_eq_zero_iff_of_ne_zero {P : (curve n).toAffine.Point} (hP : P ≠ 0) :
    2 • P = 0 ↔ P = pointZero n ∨ P = pointPos n ∨ P = pointNeg n := by
  simp [two_nsmul_eq_zero_iff, hP]

end Field

end CongruentNumbers
