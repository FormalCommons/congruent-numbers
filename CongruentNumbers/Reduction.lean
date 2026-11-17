import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction

/-!
# Reduction is injective on torsion, over `ℚ`

Let `E` be a Weierstrass equation over `ℤ` and `p` an odd prime not dividing its discriminant.
Reduction modulo `p` is injective on the torsion subgroup of `E(ℚ)`, and the order of that
subgroup divides the number of points of `E` over `ZMod p`.

Tau Ceti proves this over the fraction field of a Dedekind domain `A` at a height-one prime `u`
(`WeierstrassCurve.Affine.Point.injOn_reductionHom_torsion` and
`WeierstrassCurve.Affine.Point.card_torsion_dvd_card_reduction`), under the hypothesis that
every prime `q` lies outside `u ^ (q - 1)`. This file checks that hypothesis for `A = ℤ` and
`u = (p)` with `p` odd, and specializes the two results to `ℚ`.

## Main results

* `CongruentNumbers.natCast_notMem_span_pow`: for an odd prime `p` and any prime `q`,
  `(q : ℤ) ∉ (p) ^ (q - 1)`.
* `CongruentNumbers.injOn_reductionHom_torsion_rat`: reduction at `(p)` is injective on the
  torsion of `E(ℚ)`.
* `CongruentNumbers.card_torsion_dvd_card_point_zmod`: the order of the torsion of `E(ℚ)`
  divides `#E(𝔽_p)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*], VII.3.1 and IV.6.
-/

open IsDedekindDomain WeierstrassCurve

namespace CongruentNumbers

/-- For an odd prime `p` and any prime `q`, the integer `q` does not lie in `(p) ^ (q - 1)`:
the ramification index of `p` in `ℤ`, which is `1`, is less than `p - 1`. -/
theorem natCast_notMem_span_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (q : ℕ) (hq : q.Prime) :
    (q : ℤ) ∉ Ideal.span {(p : ℤ)} ^ (q - 1) := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← Nat.cast_pow,
    Int.natCast_dvd_natCast]
  intro h
  have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp
    ((dvd_pow_self p (by have := hq.two_le; omega)).trans h)
  subst hpq
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have := Nat.le_of_dvd hp.pos ((pow_dvd_pow p (show 2 ≤ p - 1 by omega)).trans h)
  nlinarith

variable (E : WeierstrassCurve ℤ) (v : HeightOneSpectrum ℤ) {p : ℕ}

/-- **Reduction is injective on torsion**, over `ℚ`. Let `E` be a Weierstrass equation over `ℤ`
and `p` an odd prime that does not divide its discriminant. Then reduction at the prime
`v = (p)`, from `E(ℚ)` to the points of the reduced curve over the residue field `𝔽_p`, is
injective on the torsion subgroup of `E(ℚ)`.

This is the milestone *Reduction is injective on torsion*. -/
theorem injOn_reductionHom_torsion_rat
    [DecidableEq (IsLocalRing.ResidueField (v.valuation ℚ).valuationSubring)]
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hv : v.asIdeal = Ideal.span {(p : ℤ)}) (hΔ : ¬ (p : ℤ) ∣ E.Δ) :
    haveI := E.isElliptic_integralModel_baseChange (K := ℚ) v
      (by rwa [hv, Ideal.mem_span_singleton])
    Set.InjOn (Affine.Point.reductionHom (v.valuation ℚ) (W := (E.baseChange ℚ).toAffine))
      (AddCommGroup.torsion (E.baseChange ℚ).toAffine.Point) := by
  have := E.isElliptic_integralModel_baseChange (K := ℚ) v
    (by rwa [hv, Ideal.mem_span_singleton])
  exact Affine.Point.injOn_reductionHom_torsion v
    (hv ▸ natCast_notMem_span_pow hp hp2)

/-- **Reduction is injective on torsion**, the point count over `ℚ`. Let `E` be a Weierstrass
equation over `ℤ` and `p` an odd prime that does not divide its discriminant. Then the order of
the torsion subgroup of `E(ℚ)` divides the number of points of `E` over `ZMod p`.

This is the milestone *Reduction is injective on torsion*. -/
theorem card_torsion_dvd_card_point_zmod (hp : p.Prime) (hp2 : p ≠ 2)
    (hΔ : ¬ (p : ℤ) ∣ E.Δ) :
    Nat.card (AddCommGroup.torsion (E.baseChange ℚ).toAffine.Point) ∣
      Nat.card (E.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  classical
  let v : HeightOneSpectrum ℤ := HeightOneSpectrum.ofPrime
    (Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp hp))
  have hv : v.asIdeal = Ideal.span {(p : ℤ)} := rfl
  have := E.isElliptic_integralModel_baseChange (K := ℚ) v
    (by rwa [hv, Ideal.mem_span_singleton])
  rw [← E.card_point_reduction_baseChange v p hv]
  exact Affine.Point.card_torsion_dvd_card_reduction v
    (hv ▸ natCast_notMem_span_pow hp hp2)

end CongruentNumbers
