import ExactZCDP.Base

namespace ExactZCDP

noncomputable section

/-- The equation printed in Theorem 1 of the manuscript. -/
def RootEquation (a c x : ℝ) : Prop :=
  (x ^ 2 - a ^ 2) * Real.sinh x =
    2 * x * (c + Real.cosh x) *
      Real.log ((c + Real.cosh x) / (c + Real.cosh a))

theorem F_eq_zero_iff_rootEquation {a c x : ℝ}
    (hc : 0 ≤ c) (hx : 0 < x) :
    F a c x = 0 ↔ RootEquation a c x := by
  have hcx : 0 < c + Real.cosh x := add_pos_of_nonneg_of_pos hc (Real.cosh_pos x)
  have hca : 0 < c + Real.cosh a := add_pos_of_nonneg_of_pos hc (Real.cosh_pos a)
  have hd : 2 * x * (c + Real.cosh x) ≠ 0 := ne_of_gt (by positivity)
  unfold RootEquation F d h
  rw [Real.log_div (ne_of_gt hcx) (ne_of_gt hca)]
  constructor
  · intro hF
    have he : (x ^ 2 - a ^ 2) * Real.sinh x /
        (2 * x * (c + Real.cosh x)) =
        Real.log (c + Real.cosh x) - Real.log (c + Real.cosh a) := by
      rw [← mul_div_assoc] at hF
      linarith
    exact (div_eq_iff hd).mp he |>.trans (mul_comm _ _)
  · intro he
    have hdiv := (div_eq_iff hd).mpr (he.trans (mul_comm _ _))
    rw [← mul_div_assoc]
    linarith

end
end ExactZCDP
