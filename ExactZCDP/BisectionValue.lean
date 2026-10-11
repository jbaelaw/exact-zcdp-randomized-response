import ExactZCDP.Base

/-! Algebraic value certificates associated with a positive bisection bracket. -/

namespace ExactZCDP

noncomputable section

/-- Monotonicity of `p` on a bracket encloses the scaled value at every point
of the bracket, with the denominator evaluated at the opposite endpoint. -/
theorem bisection_value_enclosure (p : ℝ → ℝ) {ε L x R : ℝ}
    (hε : 0 < ε) (hL : ε / 2 ≤ L) (hLx : L ≤ x) (hxR : x ≤ R)
    (hpL : 0 ≤ p L) (hpLx : p L ≤ p x) (hpxR : p x ≤ p R) :
    ε ^ 2 * p L / (2 * R) ≤ ε ^ 2 * (p x / (2 * x)) ∧
      ε ^ 2 * (p x / (2 * x)) ≤ ε ^ 2 * p R / (2 * L) := by
  have hLpos : 0 < L := by linarith
  have hxpos : 0 < x := lt_of_lt_of_le hLpos hLx
  have hRpos : 0 < R := lt_of_lt_of_le hxpos hxR
  have hpx : 0 ≤ p x := le_trans hpL hpLx
  have hpR : 0 ≤ p R := le_trans hpx hpxR
  have hcrossL : p L * x ≤ p x * R := by
    calc
      p L * x ≤ p x * x := mul_le_mul_of_nonneg_right hpLx hxpos.le
      _ ≤ p x * R := mul_le_mul_of_nonneg_left hxR hpx
  have hcrossR : p x * L ≤ p R * x := by
    calc
      p x * L ≤ p R * L := mul_le_mul_of_nonneg_right hpxR hLpos.le
      _ ≤ p R * x := mul_le_mul_of_nonneg_left hLx hpR
  have hlo : p L / (2 * R) ≤ p x / (2 * x) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hhi : p x / (2 * x) ≤ p R / (2 * L) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  constructor
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hlo (sq_nonneg ε)
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hhi (sq_nonneg ε)

/-- A one-Lipschitz numerator in `[0,1]` gives an explicit value-certificate
width, uniformly over positive brackets with `ε / 2 ≤ L`. -/
theorem bisection_value_width (p : ℝ → ℝ) {ε L R : ℝ}
    (hε : 0 < ε) (hL : ε / 2 ≤ L) (hLR : L ≤ R)
    (_hpL : 0 ≤ p L) (hpR : p R ≤ 1) (hpLR : p L ≤ p R)
    (hLip : p R - p L ≤ R - L) :
    ε ^ 2 * p R / (2 * L) - ε ^ 2 * p L / (2 * R) ≤
      (ε + 2) * (R - L) := by
  have hLpos : 0 < L := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le hLpos hLR
  have hD : 0 ≤ R - L := sub_nonneg.mpr hLR
  have hpLone : p L ≤ 1 := le_trans hpLR hpR
  have hεL : ε ≤ 2 * L := by linarith
  have hεR : ε ≤ 2 * R := by linarith
  have hεsq : ε ^ 2 ≤ 4 * L * R := by
    have hmul := mul_le_mul hεL hεR hε.le (by positivity : 0 ≤ 2 * L)
    nlinarith
  have hcoef₁ : ε ^ 2 / (2 * L) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hεL hε.le]
  have hcoef₂ : ε ^ 2 * p L / (2 * L * R) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).2
    have hnum := mul_le_mul_of_nonneg_left hpLone (sq_nonneg ε)
    nlinarith
  have hcoef₁nonneg : 0 ≤ ε ^ 2 / (2 * L) := by positivity
  calc
    ε ^ 2 * p R / (2 * L) - ε ^ 2 * p L / (2 * R) =
        (ε ^ 2 / (2 * L)) * (p R - p L) +
          (ε ^ 2 * p L / (2 * L * R)) * (R - L) := by
      field_simp
      ring
    _ ≤ (ε ^ 2 / (2 * L)) * (R - L) +
          (ε ^ 2 * p L / (2 * L * R)) * (R - L) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hLip hcoef₁nonneg) le_rfl
    _ ≤ ε * (R - L) + 2 * (R - L) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hcoef₁ hD)
        (mul_le_mul_of_nonneg_right hcoef₂ hD)
    _ = (ε + 2) * (R - L) := by ring

end
end ExactZCDP
