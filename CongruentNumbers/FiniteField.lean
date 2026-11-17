module

public import CongruentNumbers.Curve
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction

/-!
# Points of `E_n` over finite fields

Over a finite field `F` with `#F ≡ 3 (mod 4)`, such as `ZMod p` for a prime `p ≡ 3 (mod 4)`,
the curve `E_n : y² = x³ - n² x` has exactly `#F + 1` points, counting the point at infinity.

The proof counts the solutions of `y² = f(x)` with `f(x) = x³ - n² x` through the quadratic
character `χ` of `F`: a value `a` has `χ(a) + 1` square roots, and since `f` is odd and `-1` is
not a square, `∑ₓ χ(f(x)) = 0` (Mathlib's `quadraticChar_sum_comp_eq_zero_of_odd`). Hence there
are `∑ₓ (χ(f(x)) + 1) = #F` affine solutions.

## Main results

* `CongruentNumbers.card_equation_curve`: over a finite field `F` with `#F ≡ 3 (mod 4)`, the
  equation of `E_n` has `#F` affine solutions, for every `n`.
* `CongruentNumbers.pointCount_curve`: in that case Tau Ceti's projective count `pointCount` of
  `E_n` is `#F + 1`.
* `CongruentNumbers.card_point_curve`: the same for Mathlib's point type, when `E_n` is elliptic.
* `CongruentNumbers.card_point_map_curve_zmod`: the milestone *Points of E_n over finite fields*:
  for an integer `n` and a prime `p ∤ 2 n` with `p ≡ 3 (mod 4)`, the reduction of `E_n` modulo `p`
  has `p + 1` points, stated in the form of Tau Ceti's `card_point_reduction_baseChange`.

## References

* [N. Koblitz, *Introduction to Elliptic Curves and Modular Forms*][Koblitz1993], §I.9.
-/

public section

open WeierstrassCurve Finset

namespace CongruentNumbers

section FiniteField

variable {F : Type*} [Field F] [Fintype F]

/-- A finite field with `#F ≡ 3 (mod 4)` does not have characteristic two. -/
private theorem ringChar_ne_two_of_card_mod_four_eq_three (hF : Fintype.card F % 4 = 3) :
    ringChar F ≠ 2 := fun h ↦ by
  have := FiniteField.even_card_iff_char_two.mp h
  omega

/-- Over a finite field `F` with `#F ≡ 3 (mod 4)`, the equation `y² = x³ - n² x` of `E_n` has
exactly `#F` affine solutions, for every `n`. -/
theorem card_equation_curve (hF : Fintype.card F % 4 = 3) (n : F) :
    Nat.card {xy : F × F // (curve n).toAffine.Equation xy.1 xy.2} = Fintype.card F := by
  classical
  have hsq : ¬IsSquare (-1 : F) := by rw [FiniteField.isSquare_neg_one_iff]; omega
  have hchar := ringChar_ne_two_of_card_mod_four_eq_three hF
  have hodd : Function.Odd fun x : F ↦ x ^ 3 - n ^ 2 * x := fun x ↦ by ring
  have hsum := quadraticChar_sum_comp_eq_zero_of_odd hsq hodd
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type]
  simp only [equation_iff]
  have key : ∀ x : F, (∑ y : F, if y ^ 2 = x ^ 3 - n ^ 2 * x then 1 else 0 : ℕ) =
      #{y : F | y ^ 2 = x ^ 3 - n ^ 2 * x}.toFinset := fun x ↦ by
    rw [← Finset.card_filter, Set.toFinset_ofPred]
  simp_rw [key]
  have : ((∑ x : F, #{y : F | y ^ 2 = x ^ 3 - n ^ 2 * x}.toFinset : ℕ) : ℤ) =
      (Fintype.card F : ℤ) := by
    push_cast
    simp_rw [quadraticChar_card_sqrts hchar]
    rw [Finset.sum_add_distrib, hsum]
    simp
  exact_mod_cast this

/-- Over a finite field `F` with `#F ≡ 3 (mod 4)`, the projective count of the points of `E_n`,
the point at infinity included, is `#F + 1`, for every `n`. -/
theorem pointCount_curve (hF : Fintype.card F % 4 = 3) (n : F) :
    (curve n).pointCount = Fintype.card F + 1 := by
  rw [pointCount_def, card_equation_curve hF]

/-- Over a finite field `F` with `#F ≡ 3 (mod 4)`, an elliptic `E_n` (that is, `n ≠ 0`) has
exactly `#F + 1` points, counting the point at infinity. -/
theorem card_point_curve (hF : Fintype.card F % 4 = 3) (n : F) [(curve n).IsElliptic] :
    Nat.card (curve n).toAffine.Point = Fintype.card F + 1 := by
  rw [← pointCount_eq_card_point, pointCount_curve hF]

end FiniteField

section ZMod

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p ∤ 2 n`, the reduction of `E_n` modulo `p` is an elliptic curve. -/
theorem isElliptic_map_curve_zmod {n : ℤ} (hpn : ¬(p : ℤ) ∣ 2 * n) :
    ((curve n).map (Int.castRingHom (ZMod p))).IsElliptic := by
  rw [map_curve_intCast]
  refine isElliptic_curve _ (Ne.isUnit ?_)
  rw [← (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).not] at hpn
  exact_mod_cast hpn

/-- For a prime `p ≡ 3 (mod 4)`, the projective count of the points of `E_n` over `ZMod p` is
`p + 1`, for every integer `n`. -/
theorem pointCount_map_curve_zmod (hp : p % 4 = 3) (n : ℤ) :
    ((curve n).map (Int.castRingHom (ZMod p))).pointCount = p + 1 := by
  rw [map_curve_intCast, pointCount_curve (by rwa [ZMod.card]), ZMod.card]

/-- **Points of `E_n` over finite fields.** Let `p` be a prime with `p ∤ 2 n` and `p ≡ 3 (mod 4)`.
Then `E_n(𝔽_p)` has exactly `p + 1` points, counting the point at infinity.

This is the milestone *Points of E_n over finite fields*. It is stated for the reduction
`(curve n).map (Int.castRingHom (ZMod p))` of the integral equation of `E_n`, the form of the
right-hand side of Tau Ceti's `card_point_reduction_baseChange`. -/
theorem card_point_map_curve_zmod (hp : p % 4 = 3) {n : ℤ} (hpn : ¬(p : ℤ) ∣ 2 * n) :
    Nat.card ((curve n).map (Int.castRingHom (ZMod p))).toAffine.Point = p + 1 := by
  have := isElliptic_map_curve_zmod hpn
  rw [← pointCount_eq_card_point, pointCount_map_curve_zmod hp]

end ZMod

end CongruentNumbers
