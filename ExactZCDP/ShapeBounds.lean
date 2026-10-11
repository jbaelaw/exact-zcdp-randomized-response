import ExactZCDP.Calculus

namespace ExactZCDP
noncomputable section
open Filter Set
open scoped Topology

lemma exp_lt_two_denom {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    Real.exp x < 2 * (c + Real.cosh x) := by
  rw [Real.cosh_eq]
  have := Real.exp_pos (-x)
  linarith

lemma log_two_denom_gt {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    x < Real.log (2 * (c + Real.cosh x)) := by
  simpa only [Real.log_exp] using
    Real.log_lt_log (Real.exp_pos x) (exp_lt_two_denom hc x)

lemma h_lower {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    x - Real.log 2 < h c x := by
  have hh := log_two_denom_gt hc x
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (denom_pos hc x))] at hh
  unfold h
  linarith

lemma U_gt {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) : a < U a c := by
  have := log_two_denom_gt hc a
  unfold U
  linarith

lemma d_nonneg {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) : 0 ≤ d c x := by
  unfold d
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx.le) (by positivity)

lemma two_mul_mul_d_le_one {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) :
    2 * x * d c x ≤ 1 := by
  have he : 2 * x * d c x = hp c x := by
    unfold d hp
    field_simp [ne_of_gt hx, ne_of_gt (denom_pos hc x)]
  rw [he]
  exact hp_le_one hc x

lemma F_upper {a c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) :
    F a c x < -x / 2 + Real.log (2 * (c + Real.cosh a)) := by
  have hd := d_nonneg hc hx
  have hb := two_mul_mul_d_le_one hc hx
  have hh := h_lower hc x
  have hm := mul_le_mul_of_nonneg_left hb hx.le
  have hs : 0 ≤ a ^ 2 * d c x := mul_nonneg (sq_nonneg a) hd
  have hlog : Real.log (2 * (c + Real.cosh a)) = Real.log 2 + h c a := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (denom_pos hc a))]
    rfl
  unfold F
  rw [hlog]
  nlinarith

lemma F_U_neg {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) : F a c (U a c) < 0 := by
  have hu := U_gt ha hc
  have hh := F_upper (a := a) hc (lt_trans ha hu)
  have he : -(U a c) / 2 + Real.log (2 * (c + Real.cosh a)) = 0 := by
    unfold U
    ring
  rw [he] at hh
  exact hh

lemma tendsto_Q_right {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    Tendsto (Q a c) (𝓝[>] a) (𝓝 (d c a)) := by
  have hs := (hasDerivAt_h hc a).tendsto_slope.mono_left (nhdsGT_le_nhdsNE a)
  have ht : Tendsto (fun x : ℝ => x + a) (𝓝[>] a) (𝓝 (a + a)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).add_const a
  have hl := hs.div ht (by linarith : a + a ≠ 0)
  have he : hp c a / (a + a) = d c a := by
    unfold hp d
    rw [div_div]
    congr 1
    ring
  rw [he] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change a < x at hx
  have hxa : x - a ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hxx : x ^ 2 - a ^ 2 ≠ 0 := by
    have := mul_pos (sub_pos.mpr hx) (by linarith : 0 < x + a)
    nlinarith
  have hsum : x + a ≠ 0 := by linarith [hx]
  change slope (h c) a x / (x + a) = Q a c x
  unfold Q
  rw [slope_def_field]
  field_simp [hxa, hxx, hsum]
  ring

end
end ExactZCDP
