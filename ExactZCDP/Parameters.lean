import ExactZCDP.Calculus

namespace ExactZCDP

noncomputable section

theorem paramA_pos {ε : ℝ} (he : 0 < ε) : 0 < paramA ε := by
  dsimp [paramA]
  positivity

theorem paramC_nonneg {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) : 0 ≤ paramC k ε := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold paramC
  exact div_nonneg (sub_nonneg.mpr hk') (by positivity)

theorem normalizer_pos {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) : 0 < normalizer k ε := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have := Real.exp_pos ε
  unfold normalizer
  linarith

theorem exp_paramA_sq (ε : ℝ) : Real.exp ε = Real.exp (paramA ε) ^ 2 := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  dsimp [paramA]
  ring

theorem exp_paramA_cosh (ε : ℝ) :
    2 * Real.exp (paramA ε) * Real.cosh (paramA ε) = Real.exp ε + 1 := by
  rw [Real.cosh_eq, Real.exp_neg, exp_paramA_sq ε]
  field_simp

theorem exp_paramA_sinh (ε : ℝ) :
    2 * Real.exp (paramA ε) * Real.sinh (paramA ε) = Real.exp ε - 1 := by
  rw [Real.sinh_eq, Real.exp_neg, exp_paramA_sq ε]
  field_simp

theorem threshold_denominator_identity (ε : ℝ) :
    ε * (Real.exp ε + 1) - 2 * Real.exp ε + 2 =
      4 * Real.exp (paramA ε) *
        (paramA ε * Real.cosh (paramA ε) - Real.sinh (paramA ε)) := by
  calc
    _ = ε * (Real.exp ε + 1) - 2 * (Real.exp ε - 1) := by ring
    _ = _ := by
      rw [← exp_paramA_cosh ε, ← exp_paramA_sinh ε]
      unfold paramA
      ring

theorem threshold_gap_identity (k : ℕ) (ε : ℝ) :
    (k : ℝ) * (ε * (Real.exp ε + 1) - 2 * Real.exp ε + 2) -
      2 * (Real.exp ε - 1) * (Real.exp ε - 1 - ε) =
        8 * Real.exp (paramA ε) ^ 2 * g (paramC k ε) (paramA ε) := by
  unfold g paramC
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg, exp_paramA_sq ε]
  field_simp
  unfold paramA
  ring

theorem threshold_denominator_pos {ε : ℝ} (he : 0 < ε) :
    0 < ε * (Real.exp ε + 1) - 2 * Real.exp ε + 2 := by
  rw [threshold_denominator_identity]
  exact mul_pos (by positivity) (x_cosh_sub_sinh_pos (paramA_pos he))

theorem g_param_nonpos_iff {k : ℕ} {ε : ℝ} (he : 0 < ε) :
    g (paramC k ε) (paramA ε) ≤ 0 ↔ (k : ℝ) ≤ threshold ε := by
  have hD := threshold_denominator_pos he
  have hM : 0 < 8 * Real.exp (paramA ε) ^ 2 := by positivity
  have hgap := threshold_gap_identity k ε
  rw [threshold, le_div_iff₀ hD]
  constructor
  · intro hg
    have := mul_nonpos_of_nonneg_of_nonpos hM.le hg
    linarith
  · intro h
    by_contra hn
    have hg : 0 < g (paramC k ε) (paramA ε) := lt_of_not_ge hn
    have := mul_pos hM hg
    linarith

theorem g_param_pos_iff {k : ℕ} {ε : ℝ} (he : 0 < ε) :
    0 < g (paramC k ε) (paramA ε) ↔ threshold ε < (k : ℝ) := by
  simpa only [not_le] using not_congr (g_param_nonpos_iff (k := k) he)

theorem normalizer_eq_hyperbolic (k : ℕ) (ε : ℝ) :
    normalizer k ε =
      2 * Real.exp (paramA ε) * (paramC k ε + Real.cosh (paramA ε)) := by
  calc
    _ = (k - 2 : ℝ) + 2 * Real.exp (paramA ε) * Real.cosh (paramA ε) := by
      rw [exp_paramA_cosh ε]
      unfold normalizer
      ring
    _ = _ := by
      unfold paramC
      field_simp

theorem param_hyperbolic_pos {k : ℕ} (hk : 2 ≤ k) (ε x : ℝ) :
    0 < paramC k ε + Real.cosh x := by
  have hc := paramC_nonneg hk ε
  have hx := Real.cosh_pos x
  linarith

theorem endpoint_identity {k : ℕ} {ε : ℝ} (hk : 2 ≤ k) (he : 0 < ε) :
    ε ^ 2 * d (paramC k ε) (paramA ε) = endpointValue k ε := by
  have hh := param_hyperbolic_pos hk ε (paramA ε)
  have hε : ε ≠ 0 := ne_of_gt he
  have ha : 2 * paramA ε = ε := by unfold paramA; ring
  unfold d endpointValue
  rw [ha, normalizer_eq_hyperbolic, ← exp_paramA_sinh ε]
  field_simp

theorem pointOrder_orderPoint {ε : ℝ} (he : 0 < ε) (α : ℝ) :
    pointOrder ε (orderPoint ε α) = α := by
  have hε : ε ≠ 0 := ne_of_gt he
  unfold pointOrder orderPoint
  field_simp
  ring

theorem orderPoint_pointOrder {ε : ℝ} (he : 0 < ε) (x : ℝ) :
    orderPoint ε (pointOrder ε x) = x := by
  have hε : ε ≠ 0 := ne_of_gt he
  unfold pointOrder orderPoint
  field_simp
  ring

theorem orderPoint_gt_paramA_iff {ε α : ℝ} (he : 0 < ε) :
    paramA ε < orderPoint ε α ↔ 1 < α := by
  unfold paramA orderPoint
  constructor <;> intro h
  · nlinarith
  · nlinarith

theorem pointOrder_gt_one_iff {ε x : ℝ} (he : 0 < ε) :
    1 < pointOrder ε x ↔ paramA ε < x := by
  rw [← orderPoint_gt_paramA_iff he, orderPoint_pointOrder he]

theorem orderPoint_strictMono {ε : ℝ} (he : 0 < ε) : StrictMono (orderPoint ε) := by
  intro α β hαβ
  unfold orderPoint
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hαβ _) he

theorem pointOrder_strictMono {ε : ℝ} (he : 0 < ε) : StrictMono (pointOrder ε) := by
  intro x y hxy
  unfold pointOrder
  linarith [div_lt_div_of_pos_right hxy he]

theorem orderPoint_sq_sub (ε α : ℝ) :
    orderPoint ε α ^ 2 - paramA ε ^ 2 = ε ^ 2 * (α * (α - 1)) := by
  unfold orderPoint paramA
  ring

theorem profile_numerator_eq (k : ℕ) (ε α : ℝ) :
    Real.exp (α * ε) + Real.exp ((1 - α) * ε) + k - 2 =
      2 * Real.exp (paramA ε) * (paramC k ε + Real.cosh (orderPoint ε α)) := by
  have h₁ : α * ε = paramA ε + orderPoint ε α := by
    unfold paramA orderPoint
    ring
  have h₂ : (1 - α) * ε = paramA ε + -(orderPoint ε α) := by
    unfold paramA orderPoint
    ring
  rw [h₁, h₂, Real.exp_add, Real.exp_add, Real.cosh_eq]
  unfold paramC
  field_simp
  ring

theorem profile_eq_Q {k : ℕ} {ε α : ℝ} (hk : 2 ≤ k) (he : 0 < ε)
    (hα : 1 < α) :
    profile k ε α = ε ^ 2 * Q (paramA ε) (paramC k ε) (orderPoint ε α) := by
  have hc₁ := param_hyperbolic_pos hk ε (orderPoint ε α)
  have hc₂ := param_hyperbolic_pos hk ε (paramA ε)
  have he' := Real.exp_ne_zero (paramA ε)
  have hε : ε ≠ 0 := ne_of_gt he
  have hα' : α ≠ 0 := by linarith
  have hα₁ : α - 1 ≠ 0 := by linarith
  unfold profile
  rw [profile_numerator_eq, normalizer_eq_hyperbolic]
  rw [mul_div_mul_left _ _ (by positivity : 2 * Real.exp (paramA ε) ≠ 0)]
  rw [Real.log_div (ne_of_gt hc₁) (ne_of_gt hc₂)]
  unfold Q h
  rw [orderPoint_sq_sub]
  field_simp

theorem U_parameters {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) :
    U (paramA ε) (paramC k ε) = 2 * Real.log (k - 1 + Real.exp ε) - ε := by
  have hn := normalizer_pos hk ε
  have he := Real.exp_ne_zero (paramA ε)
  have hid : 2 * (paramC k ε + Real.cosh (paramA ε)) =
      normalizer k ε / Real.exp (paramA ε) := by
    rw [normalizer_eq_hyperbolic]
    field_simp
  unfold U
  rw [hid, Real.log_div (ne_of_gt hn) he, Real.log_exp]
  have hnorm : normalizer k ε = k - 1 + Real.exp ε := by unfold normalizer; ring
  rw [hnorm]
  unfold paramA
  ring

end
end ExactZCDP
