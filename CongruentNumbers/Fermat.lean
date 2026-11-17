module

public import CongruentNumbers.Basic
public import Mathlib.NumberTheory.PythagoreanTriples
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Fermat's right triangle theorem: `1` is not congruent

This file proves the first half of the milestone *Fermat's right triangle theorem* of the plan
<https://github.com/FormalCommons/congruent-numbers-plan/blob/main/atlas/congruent-numbers.md>:
no right triangle with integer sides has an area that is a perfect square, and `1` is not a
congruent number.

The proof is Conrad's infinite descent on `a ^ 2 + b ^ 2 = c ^ 2`, `a * b = 2 * d ^ 2`. We work with
the equivalent condition `2 * a * b = e ^ 2` (take `e = 2 * d`). A solution in positive integers
with `a` and `b` not coprime gives a smaller one by dividing by a common prime factor. A solution
with `a` and `b` coprime and `a` odd is `a = m ^ 2 - n ^ 2`, `b = 2 * m * n`, `c = m ^ 2 + n ^ 2`
by the parametrization of primitive Pythagorean triples; then `m`, `n`, `m + n` and `m - n` are
pairwise coprime with product a square, so all four are squares: `m = x ^ 2`, `n = y ^ 2`,
`m + n = u ^ 2`, `m - n = v ^ 2`. The triangle with legs `(u + v) / 2`, `(u - v) / 2` and
hypotenuse `x` is again a solution, with `2 * ((u + v) / 2) * ((u - v) / 2) = y ^ 2` and
`x ≤ m < c`.

## Main results

* `CongruentNumbers.int_mul_ne_two_mul_sq`: if `a ^ 2 + b ^ 2 = c ^ 2` with nonzero integers
  `a` and `b`, then `a * b ≠ 2 * d ^ 2` for every integer `d`.
* `CongruentNumbers.nat_mul_ne_two_mul_sq`: the same for positive natural numbers: no right
  triangle with positive integer sides has an area that is a perfect square.
* `CongruentNumbers.not_isCongruent_one`: `1` is not congruent.

## References

* [K. Conrad, *The congruent number problem*, Theorem 2.1][Conrad2008]
-/

public section

namespace CongruentNumbers

/-- If `a` and `b` are coprime integers whose product is a square and `a` is positive, then `a`
is the square of a positive integer. -/
private theorem exists_pos_sq_of_isCoprime {a b c : ℤ} (h : IsCoprime a b) (heq : a * b = c ^ 2)
    (ha : 0 < a) : ∃ x : ℤ, 0 < x ∧ a = x ^ 2 := by
  obtain ⟨x, hx | hx⟩ := Int.sq_of_isCoprime h heq
  · refine ⟨|x|, abs_pos.mpr ?_, by rw [sq_abs, hx]⟩
    rintro rfl
    simp at hx
    omega
  · nlinarith [sq_nonneg x]

/-- The descent step for a primitive solution with `a` odd: a solution of `a ^ 2 + b ^ 2 = c ^ 2`,
`2 * a * b = e ^ 2` in positive integers with `a` and `b` coprime and `a` odd gives a solution with
a smaller hypotenuse. -/
private theorem exists_smaller_of_odd {a b c e : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 = c ^ 2) (he : 2 * a * b = e ^ 2) (hab : Int.gcd a b = 1)
    (hodd : a % 2 = 1) :
    ∃ a' b' c' e' : ℤ, 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ a' ^ 2 + b' ^ 2 = c' ^ 2 ∧
      2 * a' * b' = e' ^ 2 ∧ c' < c := by
  obtain ⟨m, n, rfl, rfl, rfl, hmn, hpar, hm0⟩ :=
    PythagoreanTriple.coprime_classification' (x := a) (y := b) (z := c)
      (by unfold PythagoreanTriple; linear_combination h) hab hodd hc
  have hn : 0 < n := by nlinarith
  have hm : 0 < m := by nlinarith
  have hnm : n < m := by nlinarith
  -- The four factors `m`, `n`, `m + n`, `m - n` are pairwise coprime.
  obtain ⟨r, s, hrs⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  obtain ⟨j, hj⟩ : ∃ j, m + n = 2 * j + 1 := ⟨(m + n) / 2, by omega⟩
  have c_mn : IsCoprime m n := ⟨r, s, hrs⟩
  have c_mp : IsCoprime m (m + n) := ⟨r - s, s, by linear_combination hrs⟩
  have c_mq : IsCoprime m (m - n) := ⟨r + s, -s, by linear_combination hrs⟩
  have c_np : IsCoprime n (m + n) := ⟨s - r, r, by linear_combination hrs⟩
  have c_nq : IsCoprime n (m - n) := ⟨r + s, r, by linear_combination hrs⟩
  have c_pq : IsCoprime (m + n) (m - n) :=
    ⟨1 - j * (r + s), -j * (r - s), by linear_combination hj - 2 * j * hrs⟩
  -- Their product is a square.
  obtain ⟨f, rfl⟩ : Even e := by
    have : Even (e ^ 2) := ⟨(m ^ 2 - n ^ 2) * (2 * m * n), by linear_combination -he⟩
    exact (Int.even_pow' two_ne_zero).mp this
  have hf : m * n * (m + n) * (m - n) = f ^ 2 :=
    mul_left_cancel₀ (four_ne_zero (α := ℤ)) (by linear_combination he)
  obtain ⟨x, hx0, hx⟩ := exists_pos_sq_of_isCoprime (c_mn.mul_right (c_mp.mul_right c_mq))
    (c := f) (by linear_combination hf) hm
  obtain ⟨y, -, hy⟩ := exists_pos_sq_of_isCoprime
    (c_mn.symm.mul_right (c_np.mul_right c_nq)) (c := f) (by linear_combination hf) hn
  obtain ⟨u, hu0, hu⟩ := exists_pos_sq_of_isCoprime
    (c_mp.symm.mul_right (c_np.symm.mul_right c_pq)) (c := f) (by linear_combination hf)
    (by omega)
  obtain ⟨v, hv0, hv⟩ := exists_pos_sq_of_isCoprime
    (c_mq.symm.mul_right (c_nq.symm.mul_right c_pq.symm)) (c := f) (by linear_combination hf)
    (by omega)
  -- `u` and `v` are odd, with `u > v`.
  have hvu : v < u := by nlinarith
  obtain ⟨p, rfl⟩ : Odd u := by
    rcases Int.even_or_odd u with ⟨p, rfl⟩ | hu'
    · have : m + n = 4 * p ^ 2 := by rw [hu]; ring
      omega
    · exact hu'
  obtain ⟨q, rfl⟩ : Odd v := by
    rcases Int.even_or_odd v with ⟨q, rfl⟩ | hv'
    · have : m - n = 4 * q ^ 2 := by rw [hv]; ring
      omega
    · exact hv'
  refine ⟨p + q + 1, p - q, x, y, by omega, by omega, hx0, by linarith, by linarith, ?_⟩
  nlinarith

/-- The descent step for a primitive solution: a solution of `a ^ 2 + b ^ 2 = c ^ 2`,
`2 * a * b = e ^ 2` in positive integers with `a` and `b` coprime gives a solution with a smaller
hypotenuse. -/
private theorem exists_smaller_of_gcd_eq_one {a b c e : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) (he : 2 * a * b = e ^ 2) (hab : Int.gcd a b = 1) :
    ∃ a' b' c' e' : ℤ, 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ a' ^ 2 + b' ^ 2 = c' ^ 2 ∧
      2 * a' * b' = e' ^ 2 ∧ c' < c := by
  rcases Int.emod_two_eq_zero_or_one a with ha2 | ha2
  · rcases Int.emod_two_eq_zero_or_one b with hb2 | hb2
    · have h2 : (2 : ℤ) ∣ (Int.gcd a b : ℤ) :=
        Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero ha2) (Int.dvd_of_emod_eq_zero hb2)
      rw [hab] at h2
      norm_num at h2
    · exact exists_smaller_of_odd (e := e) hb ha hc (by linear_combination h)
        (by linear_combination he)
        (by rwa [Int.gcd_comm]) hb2
  · exact exists_smaller_of_odd ha hb hc h he hab ha2

/-- The descent step for an imprimitive solution: a solution of `a ^ 2 + b ^ 2 = c ^ 2`,
`2 * a * b = e ^ 2` in positive integers with `a` and `b` not coprime gives a solution with a
smaller hypotenuse, by dividing by a common prime factor. -/
private theorem exists_smaller_of_gcd_ne_one {a b c e : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) (he : 2 * a * b = e ^ 2) (hab : Int.gcd a b ≠ 1) :
    ∃ a' b' c' e' : ℤ, 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ a' ^ 2 + b' ^ 2 = c' ^ 2 ∧
      2 * a' * b' = e' ^ 2 ∧ c' < c := by
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a', rfl⟩ := Int.natCast_dvd.mpr hpa
  obtain ⟨b', rfl⟩ := Int.natCast_dvd.mpr hpb
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨c', rfl⟩ : (p : ℤ) ∣ c := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h]
    exact ⟨a' ^ 2 + b' ^ 2, by ring⟩
  obtain ⟨e', rfl⟩ : (p : ℤ) ∣ e := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← he]
    exact ⟨2 * a' * b', by ring⟩
  have hp2 : (p : ℤ) ^ 2 ≠ 0 := by positivity
  refine ⟨a', b', c', e', pos_of_mul_pos_right ha hp0.le, pos_of_mul_pos_right hb hp0.le,
    pos_of_mul_pos_right hc hp0.le, ?_, ?_, ?_⟩
  · exact mul_left_cancel₀ hp2 (by linear_combination h)
  · exact mul_left_cancel₀ hp2 (by linear_combination he)
  · nlinarith [pos_of_mul_pos_right hc hp0.le]

/-- There is no solution of `a ^ 2 + b ^ 2 = c ^ 2`, `2 * a * b = e ^ 2` in positive integers
`a`, `b`, `c`, by infinite descent on `c`. -/
private theorem no_solution {a b c e : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 = c ^ 2) (he : 2 * a * b = e ^ 2) : False := by
  induction hN : c.natAbs using Nat.strong_induction_on generalizing a b c e with
  | _ N ih =>
    obtain ⟨a', b', c', e', ha', hb', hc', h', he', hlt⟩ :
        ∃ a' b' c' e' : ℤ, 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ a' ^ 2 + b' ^ 2 = c' ^ 2 ∧
          2 * a' * b' = e' ^ 2 ∧ c' < c := by
      by_cases hab : Int.gcd a b = 1
      · exact exists_smaller_of_gcd_eq_one ha hb hc h he hab
      · exact exists_smaller_of_gcd_ne_one ha hb hc h he hab
    exact ih c'.natAbs (by omega) ha' hb' hc' h' he' rfl

/-- **Fermat's right triangle theorem**, integer form: if `a ^ 2 + b ^ 2 = c ^ 2` with nonzero
integers `a` and `b`, then `a * b ≠ 2 * d ^ 2` for every integer `d`. That is, no right triangle
with integer sides has an area that is a perfect square.

This is part of the milestone *Fermat's right triangle theorem*. -/
theorem int_mul_ne_two_mul_sq {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a ^ 2 + b ^ 2 = c ^ 2) (d : ℤ) : a * b ≠ 2 * d ^ 2 := by
  intro hd
  have hab : |a| * |b| = a * b := by
    rw [← abs_mul, abs_of_nonneg (by rw [hd]; positivity)]
  have hc : c ≠ 0 := by
    rintro rfl
    have : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    exact ha (pow_eq_zero_iff two_ne_zero |>.mp this)
  exact no_solution (abs_pos.mpr ha) (abs_pos.mpr hb) (abs_pos.mpr hc) (e := 2 * d)
    (by simpa only [sq_abs] using h) (by linear_combination 2 * hab + 2 * hd)

/-- **Fermat's right triangle theorem**, natural number form: no right triangle with positive
integer sides has an area that is a perfect square. If `a ^ 2 + b ^ 2 = c ^ 2` with `a` and `b`
positive, then `a * b ≠ 2 * d ^ 2`.

This is part of the milestone *Fermat's right triangle theorem*. -/
theorem nat_mul_ne_two_mul_sq {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a ^ 2 + b ^ 2 = c ^ 2)
    (d : ℕ) : a * b ≠ 2 * d ^ 2 := by
  intro hd
  exact int_mul_ne_two_mul_sq (a := a) (b := b) (c := c) (by omega) (by omega)
    (by exact_mod_cast h) d (by exact_mod_cast hd)

/-- **Fermat's right triangle theorem**: `1` is not a congruent number, that is, no right
triangle with rational sides has area `1`.

This is the milestone *Fermat's right triangle theorem* (part 1). -/
theorem not_isCongruent_one : ¬ IsCongruent 1 := by
  rintro ⟨a, b, c, ha, hb, hc, h, hab⟩
  set D : ℤ := a.den * b.den * c.den with hD
  have hA : ((a.num * b.den * c.den : ℤ) : ℚ) = a * D := by
    rw [hD]; push_cast; rw [← Rat.mul_den_eq_num a]; ring
  have hB : ((b.num * a.den * c.den : ℤ) : ℚ) = b * D := by
    rw [hD]; push_cast; rw [← Rat.mul_den_eq_num b]; ring
  have hC : ((c.num * a.den * b.den : ℤ) : ℚ) = c * D := by
    rw [hD]; push_cast; rw [← Rat.mul_den_eq_num c]; ring
  have hD0 : (D : ℚ) ≠ 0 := by rw [hD]; push_cast; positivity
  refine int_mul_ne_two_mul_sq (a := a.num * b.den * c.den) (b := b.num * a.den * c.den)
    (c := c.num * a.den * b.den) ?_ ?_ ?_ D ?_
  · exact_mod_cast hA ▸ mul_ne_zero ha.ne' hD0
  · exact_mod_cast hB ▸ mul_ne_zero hb.ne' hD0
  · have : ((a.num * b.den * c.den : ℤ) : ℚ) ^ 2 + ((b.num * a.den * c.den : ℤ) : ℚ) ^ 2 =
        ((c.num * a.den * b.den : ℤ) : ℚ) ^ 2 := by
      rw [hA, hB, hC]; linear_combination (D : ℚ) ^ 2 * h
    exact_mod_cast this
  · have : ((a.num * b.den * c.den : ℤ) : ℚ) * ((b.num * a.den * c.den : ℤ) : ℚ) =
        2 * (D : ℚ) ^ 2 := by
      rw [hA, hB]; linear_combination 2 * (D : ℚ) ^ 2 * hab
    exact_mod_cast this

end CongruentNumbers

end
