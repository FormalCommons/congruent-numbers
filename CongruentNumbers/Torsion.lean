module

public import CongruentNumbers.FiniteField
public import CongruentNumbers.Reduction
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The torsion of `E_n`

For a nonzero integer `n`, the torsion subgroup of `E_n(ℚ)`, where `E_n : y² = x³ - n² x`, is
`{O, (0, 0), (n, 0), (-n, 0)}`, and is isomorphic to `ℤ/2 × ℤ/2`.

The proof is Koblitz's. Let `T` be the torsion subgroup. For every prime `p ≡ 3 (mod 4)` with
`p ∤ 2 n`, the order of `T` divides `#E_n(𝔽_p) = p + 1`, by the milestones *Reduction is
injective on torsion* (`card_torsion_dvd_card_point_zmod`) and *Points of E_n over finite fields*
(`card_point_map_curve_zmod`). Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_eq_mod`)
then gives primes `p ≡ 2 ℓ + 1 (mod 4 ℓ)`, for an odd prime `ℓ`, and `p ≡ 3 (mod 8)`, which
show that neither an odd prime nor `8` divides `|T|`. So `|T|` divides `4`, and the four points
of order dividing two are all of `T`.

## Main results

* `CongruentNumbers.dvd_four_of_forall_dvd_add_one`: a natural number that divides `p + 1` for
  all large enough primes `p ≡ 3 (mod 4)` divides `4`.
* `CongruentNumbers.card_torsion_dvd_add_one`: `|T|` divides `p + 1` for every prime
  `p ≡ 3 (mod 4)` with `p ∤ 2 n`.
* `CongruentNumbers.mem_torsion_iff`: the milestone *Torsion of E_n*, the torsion points of
  `E_n(ℚ)` are `O`, `(0, 0)`, `(n, 0)` and `(-n, 0)`.
* `CongruentNumbers.coe_torsion`, `CongruentNumbers.card_torsion`: the same, as an equality of
  sets, and `|T| = 4`.
* `CongruentNumbers.mem_torsion_iff_neg_eq_self`: `P` is torsion if and only if `-P = P`.
* `CongruentNumbers.torsionAddEquiv`: the milestone *Torsion of E_n*, `T ≃+ ℤ/2 × ℤ/2`.

## References

* [N. Koblitz, *Introduction to Elliptic Curves and Modular Forms*][Koblitz1993], §I.9, Prop. 17.
-/

public section

open WeierstrassCurve

namespace CongruentNumbers

/-- Dirichlet's theorem for the progression `a (mod q)`, in the form used below: there is a prime
`p > B` with `p % q = a`, when `a < q` is coprime to `q`. -/
private theorem exists_prime_gt_mod_eq {q a : ℕ} [NeZero q] (ha : a < q) (hcop : a.Coprime q)
    (B : ℕ) : ∃ p > B, p.Prime ∧ p % q = a := by
  obtain ⟨p, hpB, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime a q).mpr hcop) B
  refine ⟨p, hpB, hp, ?_⟩
  rw [ZMod.natCast_eq_natCast_iff'] at hpa
  rwa [Nat.mod_eq_of_lt ha] at hpa

/-- A natural number `N` that divides `p + 1` for every prime `p > B` with `p ≡ 3 (mod 4)` divides
`4`. Dirichlet's theorem gives such primes with `p ≡ 1` modulo any odd prime `ℓ`, so that
`ℓ ∤ p + 1`, and with `p ≡ 3 (mod 8)`, so that `8 ∤ p + 1`. -/
theorem dvd_four_of_forall_dvd_add_one {N B : ℕ}
    (h : ∀ p : ℕ, p.Prime → B < p → p % 4 = 3 → N ∣ p + 1) : N ∣ 4 := by
  -- `N ≠ 0`
  have hN : N ≠ 0 := by
    obtain ⟨p, hpB, hp, hp4⟩ := exists_prime_gt_mod_eq (q := 4) (a := 3) (by norm_num)
      (by norm_num) B
    rintro rfl
    simpa using h p hp hpB hp4
  -- no odd prime divides `N`
  have hodd : ∀ {ℓ : ℕ}, ℓ.Prime → ℓ ∣ N → ℓ = 2 := by
    intro ℓ hℓ hℓN
    by_contra hℓ2
    have h3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
    have hℓodd : ℓ % 2 = 1 := by
      by_contra h0
      have := hℓ.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega))
      omega
    have : NeZero (4 * ℓ) := ⟨by omega⟩
    have hcop : (2 * ℓ + 1).Coprime (4 * ℓ) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · have h2 : (2 * ℓ + 1).Coprime 2 :=
          (Nat.coprime_mul_left_add_left 1 2 ℓ).mpr (Nat.coprime_one_left 2)
        simpa using h2.pow_right 2
      · rw [show 2 * ℓ + 1 = 1 + 2 * ℓ by ring, Nat.coprime_add_mul_right_left]
        exact Nat.coprime_one_left ℓ
    obtain ⟨p, hpB, hp, hpa⟩ := exists_prime_gt_mod_eq (by omega) hcop B
    have hp4 : p % 4 = 3 := by
      rw [← Nat.mod_mod_of_dvd p (dvd_mul_right 4 ℓ), hpa]
      omega
    have hpℓ : p % ℓ = 1 := by
      rw [← Nat.mod_mod_of_dvd p (dvd_mul_left ℓ 4), hpa, Nat.add_mod,
        Nat.mul_mod_left, Nat.mod_eq_of_lt (by omega : 1 < ℓ)]
      simp [Nat.mod_eq_of_lt (by omega : 1 < ℓ)]
    have hdvd := (hℓN.trans (h p hp hpB hp4))
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hpℓ, Nat.mod_eq_of_lt (by omega : 1 < ℓ),
      Nat.mod_eq_of_lt (by omega : 1 + 1 < ℓ)] at hdvd
    omega
  -- `8` does not divide `N`
  have h8 : ¬ 8 ∣ N := by
    intro h8
    obtain ⟨p, hpB, hp, hp8⟩ := exists_prime_gt_mod_eq (q := 8) (a := 3) (by norm_num)
      (by norm_num) B
    have := h8.trans (h p hp hpB (by omega))
    omega
  have hNk := Nat.eq_prime_pow_of_unique_prime_dvd hN hodd
  generalize N.primeFactorsList.length = k at hNk
  subst hNk
  have hk : k ≤ 2 := by
    by_contra hk
    exact h8 (dvd_trans (dvd_of_eq (by norm_num)) (pow_dvd_pow 2 (by omega : 3 ≤ k)))
  exact (pow_dvd_pow 2 hk).trans (dvd_of_eq (by norm_num))

variable {n : ℤ}

/-- For a prime `p ≡ 3 (mod 4)` with `p ∤ 2 n`, the order of the torsion subgroup of `E_n(ℚ)`
divides `p + 1`: by *Reduction is injective on torsion* it divides `#E_n(𝔽_p)`, which is `p + 1`
by *Points of E_n over finite fields*. -/
theorem card_torsion_dvd_add_one {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hpn : ¬(p : ℤ) ∣ 2 * n) :
    Nat.card (AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point) ∣ p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hΔ : ¬(p : ℤ) ∣ (curve n).Δ := fun h ↦ by
    rw [Δ_curve, show (64 : ℤ) * n ^ 6 = (2 * n) ^ 6 by ring] at h
    exact hpn ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h)
  have h := card_torsion_dvd_card_point_zmod (curve n) hp (by omega) hΔ
  rwa [card_point_map_curve_zmod hp4 hpn, baseChange_curve, algebraMap_int_eq,
    eq_intCast] at h

variable (n) in
/-- For `n ≠ 0`, the order of the torsion subgroup of `E_n(ℚ)` divides `4`. -/
theorem card_torsion_dvd_four (hn : n ≠ 0) :
    Nat.card (AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point) ∣ 4 := by
  refine dvd_four_of_forall_dvd_add_one (B := (2 * n).natAbs) fun p hp hpB hp4 ↦
    card_torsion_dvd_add_one hp hp4 fun h ↦ ?_
  have := Nat.le_of_dvd (by omega) (Int.ofNat_dvd_left.mp h)
  omega

/-- The image of a nonzero integer in a ring of characteristic zero is nonzero. -/
instance intCast_neZero {R : Type*} [AddGroupWithOne R] [CharZero R] (n : ℤ) [NeZero n] :
    NeZero (n : R) :=
  ⟨Int.cast_ne_zero.mpr (NeZero.ne n)⟩

/-- A point `P` of `E_n(ℚ)` with `-P = P` lies in the torsion subgroup. -/
private theorem mem_torsion_of_neg_eq_self {P : (curve (n : ℚ)).toAffine.Point} (h : -P = P) :
    P ∈ AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point := by
  refine (AddCommGroup.mem_torsion _).mpr
    (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, ?_⟩)
  rw [two_nsmul, ← neg_add_cancel P, h]

variable [NeZero n]

variable (n) in
/-- The four points `O`, `(0, 0)`, `(n, 0)` and `(-n, 0)` of `E_n(ℚ)` are distinct. -/
private theorem ncard_twoTorsion :
    ({0, pointZero (n : ℚ), pointPos (n : ℚ), pointNeg (n : ℚ)} :
      Set (curve (n : ℚ)).toAffine.Point).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair pointPos_ne_pointNeg]
  · simp [pointZero_ne_pointPos, pointZero_ne_pointNeg]
  · simp [pointZero_ne_zero.symm, pointPos_ne_zero.symm, pointNeg_ne_zero.symm]

variable (n) in
/-- The torsion subgroup of `E_n(ℚ)`, as a set, is `{O, (0, 0), (n, 0), (-n, 0)}`. -/
theorem coe_torsion :
    (AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point : Set (curve (n : ℚ)).toAffine.Point) =
      {0, pointZero (n : ℚ), pointPos (n : ℚ), pointNeg (n : ℚ)} := by
  have hcard := card_torsion_dvd_four n (NeZero.ne n)
  have : Finite (AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point) :=
    Nat.finite_of_card_ne_zero (by rintro h; simp [h] at hcard)
  refine (Set.eq_of_subset_of_ncard_le (fun P hP ↦ ?_) ?_ (Set.toFinite _)).symm
  · exact mem_torsion_of_neg_eq_self ((neg_eq_self_iff P).mpr (by simpa using hP))
  · rw [← Nat.card_coe_set_eq, ncard_twoTorsion]
    exact Nat.le_of_dvd (by norm_num) hcard

/-- **Torsion of `E_n`.** For a nonzero integer `n`, the torsion points of `E_n(ℚ)` are the point
at infinity and the three points `(0, 0)`, `(n, 0)` and `(-n, 0)` with `y = 0`.

This is the milestone *Torsion of E_n*, together with `CongruentNumbers.torsionAddEquiv`. -/
theorem mem_torsion_iff (P : (curve (n : ℚ)).toAffine.Point) :
    P ∈ AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point ↔
      P = 0 ∨ P = pointZero (n : ℚ) ∨ P = pointPos (n : ℚ) ∨ P = pointNeg (n : ℚ) := by
  rw [← SetLike.mem_coe, coe_torsion]
  simp

/-- A point `P` of `E_n(ℚ)` is a torsion point if and only if `-P = P`, that is, `P` is the point
at infinity or its `y`-coordinate is `0`. -/
theorem mem_torsion_iff_neg_eq_self (P : (curve (n : ℚ)).toAffine.Point) :
    P ∈ AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point ↔ -P = P := by
  rw [mem_torsion_iff, neg_eq_self_iff]

variable (n) in
/-- For a nonzero integer `n`, the torsion subgroup of `E_n(ℚ)` has order `4`. -/
theorem card_torsion : Nat.card (AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point) = 4 := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, coe_torsion, ncard_twoTorsion]

/-- The homomorphism `ZMod 2 →+ G` that sends `1` to an element `a` with `2 • a = 0`. -/
private noncomputable def zmodTwoHom {G : Type*} [AddCommGroup G] (a : G) (ha : 2 • a = 0) :
    ZMod 2 →+ G :=
  ZMod.lift 2 ⟨zmultiplesHom G a, by simpa [two_zsmul, two_nsmul] using ha⟩

private theorem zmodTwoHom_one {G : Type*} [AddCommGroup G] (a : G) (ha : 2 • a = 0) :
    zmodTwoHom a ha 1 = a := by
  simpa [zmodTwoHom] using
    ZMod.lift_coe 2 ⟨zmultiplesHom G a, by simpa [two_zsmul, two_nsmul] using ha⟩ 1

private theorem two_nsmul_eq_zero_of_neg_eq_self {G : Type*} [AddCommGroup G] {a : G}
    (ha : -a = a) : 2 • a = 0 := by
  rw [two_nsmul]
  nth_rw 1 [← ha]
  exact neg_add_cancel a

/-- The point `(0, 0)`, as an element of the torsion subgroup of `E_n(ℚ)`. -/
private def torsionZero : AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point :=
  ⟨pointZero (n : ℚ), (mem_torsion_iff _).mpr (.inr (.inl rfl))⟩

/-- The point `(n, 0)`, as an element of the torsion subgroup of `E_n(ℚ)`. -/
private def torsionPos : AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point :=
  ⟨pointPos (n : ℚ), (mem_torsion_iff _).mpr (.inr (.inr (.inl rfl)))⟩

private theorem neg_torsion_eq_self (P : AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point) :
    -P = P :=
  Subtype.ext ((mem_torsion_iff_neg_eq_self _).mp P.2)

variable (n) in
/-- The homomorphism `ZMod 2 × ZMod 2 →+ T` onto the torsion subgroup `T` of `E_n(ℚ)` that
sends `(1, 0)` to `(0, 0)` and `(0, 1)` to `(n, 0)`. -/
private noncomputable def torsionHom :
    ZMod 2 × ZMod 2 →+ AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point :=
  (zmodTwoHom torsionZero (two_nsmul_eq_zero_of_neg_eq_self (neg_torsion_eq_self _))).coprod
    (zmodTwoHom torsionPos (two_nsmul_eq_zero_of_neg_eq_self (neg_torsion_eq_self _)))

private theorem bijective_torsionHom : Function.Bijective (torsionHom n) := by
  have : Finite (AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point) :=
    Nat.finite_of_card_ne_zero (by rw [card_torsion]; norm_num)
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨?_, by simp [card_torsion]⟩
  refine (injective_iff_map_eq_zero _).mpr ?_
  have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rintro ⟨u, v⟩ huv
  simp only [torsionHom, AddMonoidHom.coprod_apply] at huv
  rcases h2 u with rfl | rfl <;> rcases h2 v with rfl | rfl <;>
    simp only [map_zero, zmodTwoHom_one, add_zero, zero_add] at huv
  · rfl
  · exact absurd (congrArg Subtype.val huv) pointPos_ne_zero
  · exact absurd (congrArg Subtype.val huv) pointZero_ne_zero
  · have := congrArg Subtype.val ((eq_neg_of_add_eq_zero_left huv).trans (neg_torsion_eq_self _))
    exact absurd this pointZero_ne_pointPos

variable (n) in
/-- **Torsion of `E_n`.** For a nonzero integer `n`, the torsion subgroup of `E_n(ℚ)` is
isomorphic to `ℤ/2 × ℤ/2`. The isomorphism sends `(0, 0)` to `(1, 0)`, `(n, 0)` to `(0, 1)` and
`(-n, 0)` to `(1, 1)`.

This is the milestone *Torsion of E_n*, together with `CongruentNumbers.mem_torsion_iff`. -/
noncomputable def torsionAddEquiv :
    AddCommGroup.torsion (curve (n : ℚ)).toAffine.Point ≃+ ZMod 2 × ZMod 2 :=
  (AddEquiv.ofBijective (torsionHom n) bijective_torsionHom).symm


variable (n) in
/-- The isomorphism `torsionAddEquiv` sends `(1, 0)` back to the point `(0, 0)`. -/
@[simp]
theorem coe_torsionAddEquiv_symm_one_zero :
    ((torsionAddEquiv n).symm (1, 0) : (curve (n : ℚ)).toAffine.Point) = pointZero (n : ℚ) := by
  simp [torsionAddEquiv, torsionHom, zmodTwoHom_one, torsionZero]

variable (n) in
/-- The isomorphism `torsionAddEquiv` sends `(0, 1)` back to the point `(n, 0)`. -/
@[simp]
theorem coe_torsionAddEquiv_symm_zero_one :
    ((torsionAddEquiv n).symm (0, 1) : (curve (n : ℚ)).toAffine.Point) = pointPos (n : ℚ) := by
  simp [torsionAddEquiv, torsionHom, zmodTwoHom_one, torsionPos]

variable (n) in
/-- The isomorphism `torsionAddEquiv` sends `(1, 1)` back to the point `(-n, 0)`. -/
@[simp]
theorem coe_torsionAddEquiv_symm_one_one :
    ((torsionAddEquiv n).symm (1, 1) : (curve (n : ℚ)).toAffine.Point) = pointNeg (n : ℚ) := by
  have hx := (mem_torsion_iff _).mp ((torsionAddEquiv n).symm (1, 1)).2
  have hne : ∀ y : ZMod 2 × ZMod 2, y ≠ (1, 1) →
      ((torsionAddEquiv n).symm (1, 1) : (curve (n : ℚ)).toAffine.Point) ≠
        (torsionAddEquiv n).symm y := fun y hy h ↦
    hy ((torsionAddEquiv n).symm.injective (Subtype.ext h)).symm
  rcases hx with h | h | h | h
  · exact absurd (h.trans (by simp)) (hne 0 (by decide))
  · exact absurd (h.trans (coe_torsionAddEquiv_symm_one_zero n).symm) (hne (1, 0) (by decide))
  · exact absurd (h.trans (coe_torsionAddEquiv_symm_zero_one n).symm) (hne (0, 1) (by decide))
  · exact h

end CongruentNumbers
